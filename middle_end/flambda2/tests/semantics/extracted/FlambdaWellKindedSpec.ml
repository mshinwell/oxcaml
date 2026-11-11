open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveSpec
open FlambdaSemanticsSpec
open FlambdaValueSpec
open List
open ListDef
open OxCamlOption
open PeanoNat

type kind_env = flambda_kind finite_map

type arity_env = flambda_kind list finite_map

type slot_kinds = flambda_kind finite_map

(** val has_kind : flambda_kind option -> flambda_kind -> bool **)

let has_kind found kind =
  match found with Some kind' -> kind_eqb kind' kind | None -> false

(** val has_arity : flambda_kind list option -> flambda_kind list -> bool **)

let has_arity found expected =
  match found with Some found0 -> kinds_eqb found0 expected | None -> false

(** val kind_of_simple : kind_env -> simple -> flambda_kind option **)

let kind_of_simple kinds = function
  | Var x -> lookup x kinds
  | Symbol _ -> Some Value
  | Const c -> Some (kind_of_const c)

(** val kinds_of_simples : kind_env -> simple list -> flambda_kind list option **)

let rec kinds_of_simples kinds = function
  | [] -> Some []
  | s :: args0 -> (
    match kind_of_simple kinds s with
    | Some k -> (
      match kinds_of_simples kinds args0 with
      | Some ks -> Some (k :: ks)
      | None -> None)
    | None -> None)

(** val bind_param_kinds : variable list -> flambda_kind list -> kind_env ->
    kind_env option **)

let rec bind_param_kinds params params_kinds kinds =
  match params with
  | [] -> ( match params_kinds with [] -> Some kinds | _ :: _ -> None)
  | x :: params0 -> (
    match params_kinds with
    | [] -> None
    | k :: params_kinds0 ->
      bind_param_kinds params0 params_kinds0 ((x, k) :: kinds))

(** val handler_arities : (continuation * continuation_handler) list ->
    arity_env **)

let handler_arities handlers = map_values handler_kinds handlers

(** val value_slots_well_kinded : slot_kinds -> kind_env -> (value_slot *
    simple) list -> bool **)

let value_slots_well_kinded slots kinds value_slots =
  forallb
    (fun pat ->
      let slot, s = pat in
      match lookup slot slots with
      | Some kind -> has_kind (kind_of_simple kinds s) kind
      | None -> false)
    value_slots

(** val kind_of_named : slot_kinds -> kind_env -> named -> flambda_kind option **)

let kind_of_named slots kinds = function
  | Simple s -> kind_of_simple kinds s
  | Prim (p, args) -> (
    match kinds_of_simples kinds args with
    | Some _ -> Some (prim_result_kind p)
    | None -> None)
  | Set_of_closures (_, value_slots) ->
    if value_slots_well_kinded slots kinds value_slots then Some Value else None
  | Closure_of_set (_, _, value_slots) ->
    if value_slots_well_kinded slots kinds value_slots then Some Value else None
  | Project_value_slot (slot, closure) -> (
    match kind_of_simple kinds closure with
    | Some _ -> lookup slot slots
    | None -> None)
  | Project_value_slot_from (_, slot, closure) -> (
    match kind_of_simple kinds closure with
    | Some _ -> lookup slot slots
    | None -> None)
  | Project_function_slot (_, _, closure) -> (
    match kind_of_simple kinds closure with
    | Some _ -> Some Value
    | None -> None)

(** val static_const_well_kinded : slot_kinds -> kind_env -> static_const ->
    bool **)

let static_const_well_kinded slots kinds = function
  | Static_const_set_of_closures (_, value_slots) ->
    value_slots_well_kinded slots kinds value_slots
  | Static_const_closure_of_set (_, _, _, value_slots) ->
    value_slots_well_kinded slots kinds value_slots
  | Static_const_block (_, fields) ->
    forallb (fun s -> has_kind (kind_of_simple kinds s) Value) fields
  | Static_const_boxed_number contents -> (
    match kind_of_simple kinds contents with
    | Some kind -> is_some (boxable_number_of_kind kind)
    | None -> false)
  | Static_const_immutable_string _ -> true

(** val trap_action_in_scope : arity_env -> apply_cont -> bool **)

let trap_action_in_scope conts ac =
  match ac.ac_trap_action with
  | Some action -> is_bound (trap_action_handler action) conts
  | None -> true

(** val apply_cont_well_kinded : kind_env -> arity_env -> apply_cont -> bool **)

let apply_cont_well_kinded kinds conts ac =
  trap_action_in_scope conts ac
  &&
  match lookup ac.ac_continuation conts with
  | Some params_kinds ->
    has_arity (kinds_of_simples kinds ac.ac_args) params_kinds
  | None -> false

(** val apply_well_kinded : kind_env -> arity_env -> apply_expr -> bool **)

let apply_well_kinded kinds conts ap =
  (((is_some (kind_of_simple kinds ap.ap_callee)
    && is_some (kinds_of_simples kinds ap.ap_args))
   && has_arity
        (kinds_of_simples kinds (exn_extra_simples ap))
        (map snd ap.ap_exn_extra_args))
  && has_arity (lookup ap.ap_continuation conts) (unarize ap.ap_return_arity))
  && has_arity
       (lookup ap.ap_exn_continuation conts)
       (Value :: map snd ap.ap_exn_extra_args)

(** val well_kinded : slot_kinds -> kind_env -> arity_env -> expr -> bool **)

let well_kinded slots =
  let rec well_kinded0 kinds conts = function
    | Let (x, kind, defining_expr, body) ->
      has_kind (kind_of_named slots kinds defining_expr) kind
      && well_kinded0 ((x, kind) :: kinds) conts body
    | Let_static (bindings, body) ->
      forallb (binding_well_kinded kinds) bindings
      && well_kinded0 kinds conts body
    | Let_cont_non_recursive (k, h, body) ->
      handler_well_kinded kinds conts h
      && well_kinded0 kinds ((k, handler_kinds h) :: conts) body
    | Let_cont_recursive (handlers, body) ->
      forallb
        (fun pat ->
          let _, h = pat in
          handler_well_kinded kinds (app (handler_arities handlers) conts) h)
        handlers
      && well_kinded0 kinds (app (handler_arities handlers) conts) body
    | Apply ap -> apply_well_kinded kinds conts ap
    | Apply_cont ac -> apply_cont_well_kinded kinds conts ac
    | Switch (scrutinee, arms) ->
      has_kind
        (kind_of_simple kinds scrutinee)
        (Naked_number Kind_naked_immediate)
      && forallb (fun arm -> apply_cont_well_kinded kinds conts (snd arm)) arms
    | Invalid -> true
  and handler_well_kinded kinds conts = function
    | Handler (params, metadata, handler) -> (
      distinct params
      &&
      match bind_param_kinds params metadata.hm_params_kinds kinds with
      | Some handler_kinds0 -> well_kinded0 handler_kinds0 conts handler
      | None -> false)
  and binding_well_kinded kinds = function
    | Bind_code (_, c) -> code_well_kinded c
    | Bind_deleted_code _ -> true
    | Bind_symbol (_, const) -> static_const_well_kinded slots kinds const
  and code_well_kinded = function
    | Code
        ( params,
          my_closure,
          return_continuation,
          exn_continuation,
          metadata,
          body ) -> (
      distinct (my_closure :: params)
      &&
      match
        bind_param_kinds params
          (unarize metadata.cm_params_arity)
          ((my_closure, Value) :: [])
      with
      | Some body_kinds ->
        well_kinded0 body_kinds
          [ return_continuation, unarize metadata.cm_result_arity;
            exn_continuation, Value :: [] ]
          body
      | None -> false)
  in
  well_kinded0

(** val unit_arities : continuation -> continuation -> arity_env **)

let unit_arities unit_return unit_exn =
  [unit_return, Value :: []; unit_exn, Value :: []]

(** val well_kinded_unit : slot_kinds -> continuation -> continuation -> expr ->
    bool **)

let well_kinded_unit slots unit_return unit_exn e =
  well_kinded slots [] (unit_arities unit_return unit_exn) e

(** val kinds_agree_on_prefix : flambda_kind list list -> flambda_kind list list
    -> bool **)

let rec kinds_agree_on_prefix params args =
  match params with
  | [] -> true
  | param :: params0 -> (
    match args with
    | [] -> true
    | arg :: args0 -> kinds_eqb param arg && kinds_agree_on_prefix params0 args0
    )

(** val is_one_param_of_kind_value : arity -> bool **)

let is_one_param_of_kind_value = function
  | [] -> false
  | a0 :: l -> (
    match a0 with
    | Singleton k -> (
      match k with
      | Value -> ( match l with [] -> true | _ :: _ -> false)
      | _ -> false)
    | Unboxed_product _ -> false)

(** val partial_or_over_application : arity -> arity -> arity -> arity -> bool **)

let partial_or_over_application args_arity return_arity params_arity
    result_arity =
  let provided = length args_arity in
  let params = length params_arity in
  kinds_agree_on_prefix
    (unarize_per_parameter params_arity)
    (unarize_per_parameter args_arity)
  &&
  if Nat.ltb params provided
  then is_one_param_of_kind_value result_arity
  else
    (Nat.ltb O provided && Nat.ltb provided params)
    && is_one_param_of_kind_value return_arity

(** val at_partial_or_over_application : state -> bool **)

let at_partial_or_over_application s =
  match s.state_expr with
  | Apply ap -> (
    match eval_simple s.state_vars ap.ap_callee with
    | Some callee -> (
      match eval_simples s.state_vars ap.ap_args with
      | Some vs -> (
        match closure_of s.state_statics callee with
        | Some p -> (
          let called, _ = p in
          match lookup called s.state_statics.static_code with
          | Some c ->
            kinds_eqb (map kind_of_value vs) (unarize ap.ap_args_arity)
            && partial_or_over_application ap.ap_args_arity ap.ap_return_arity
                 (code_params_arity c) (code_result_arity c)
          | None -> false)
        | None -> false)
      | None -> false)
    | None -> false)
  | _ -> false
