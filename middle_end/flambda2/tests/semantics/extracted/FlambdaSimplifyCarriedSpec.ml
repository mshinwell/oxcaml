open BinPos
open Bool
open Datatypes
open FlambdaBindingTime
open FlambdaKindModel
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaSemanticsSpec
open FlambdaSimplifyApplySpec
open FlambdaSimplifyPassSpec
open FlambdaSimplifyPrimitivesSpec
open FlambdaSimplifyPruningSpec
open FlambdaSimplifyStaticsSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv
open FlambdaTypingEnvInvariantSpec
open FlambdaUnusedContsSpec
open List
open ListDef
open PeanoNat

(** val well_formed_or_known : bool -> Typing_env.t -> bool **)

let well_formed_or_known fit tenv = fit || typing_env_well_formed tenv

(** val let_step_of : Typing_env.t -> variable -> named -> outcome -> let_step **)

let let_step_of tenv x defining_expr = function
  | Becomes_invalid -> Step_invalid
  | Becomes_simple s -> bind_simple tenv x s
  | Stays_with_type ty ->
    if type_in_scope_b tenv ty
    then
      Step_let
        ( canonical_named tenv defining_expr,
          Typing_env.replace_equation
            (Typing_env.add_variable_definition tenv x (kind ty)
               Name_mode.normal)
            (Name_var x) ty )
    else Step_stop
  | Stays_with_kind kind0 ->
    Step_let
      ( canonical_named tenv defining_expr,
        Typing_env.add_variable_definition tenv x kind0 Name_mode.normal )
  | Not_known -> Step_stop

(** val outcome_keeps_fit : Typing_env.t -> variable -> outcome -> bool **)

let outcome_keeps_fit tenv x = function
  | Becomes_simple s -> (
    match simplify_simple tenv s with
    | Some p ->
      let ty, canonical = p in
      alias_keeps_fit
        (Typing_env.add_variable_definition tenv x (kind ty) Name_mode.normal)
        (Var x) canonical (kind ty)
    | None -> false)
  | Stays_with_type ty ->
    equation_keeps_fit
      (Typing_env.add_variable_definition tenv x (kind ty) Name_mode.normal)
      (Name_var x) ty
  | Stays_with_kind _ -> true
  | _ -> false

(** val simplify_let_carried : bool -> Typing_env.t -> variable -> named ->
    let_step * bool **)

let simplify_let_carried fit tenv x defining_expr =
  if
    well_formed_or_known fit tenv
    && negb (Typing_env.mem None tenv (Name_var x))
  then
    let answer = simplify_named tenv defining_expr in
    let_step_of tenv x defining_expr answer, outcome_keeps_fit tenv x answer
  else Step_stop, false

(** val declare_variable_carried : bool -> Typing_env.t -> variable ->
    flambda_kind -> Typing_env.t option **)

let declare_variable_carried fit tenv x declared =
  if
    well_formed_or_known fit tenv
    && negb (Typing_env.mem None tenv (Name_var x))
  then
    Some (Typing_env.add_variable_definition tenv x declared Name_mode.normal)
  else None

(** val let_env_carried : bool -> Typing_env.t -> variable -> flambda_kind ->
    named -> (Typing_env.t * bool) option **)

let let_env_carried fit tenv x declared defining_expr =
  let l, keeps =
    simplify_let_carried fit tenv x
      (resolve_value_slot tenv declared defining_expr)
  in
  match l with
  | Step_invalid -> None
  | Step_let (_, tenv') -> Some (tenv', fit && keeps)
  | Step_stop -> (
    match declare_variable_carried fit tenv x declared with
    | Some tenv' -> Some (tenv', fit)
    | None -> None)

(** val define_variables_carried : bool -> Typing_env.t -> (variable *
    flambda_kind) list -> Typing_env.t option **)

let rec define_variables_carried fit tenv = function
  | [] -> Some tenv
  | p :: definitions0 ->
    let x, kind0 = p in
    if
      well_formed_or_known fit tenv
      && negb (Typing_env.mem None tenv (Name_var x))
    then
      define_variables_carried fit
        (Typing_env.add_variable_definition tenv x kind0 Name_mode.normal)
        definitions0
    else None

(** val code_env_in_carried : bool -> Typing_env.t -> variable list -> variable
    -> code_metadata -> Typing_env.t option **)

let code_env_in_carried fit tenv params my_closure metadata =
  let kinds = unarize metadata.cm_params_arity in
  if Nat.eqb (length kinds) (length params)
  then
    define_variables_carried fit
      (Typing_env.closure_env tenv)
      ((my_closure, Value) :: combine params kinds)
  else None

(** val handler_env_carried : bool -> Typing_env.t -> variable list ->
    handler_metadata -> Typing_env.t option **)

let handler_env_carried fit tenv params metadata =
  let kinds = metadata.hm_params_kinds in
  if Nat.eqb (length kinds) (length params)
  then define_variables_carried fit tenv (combine params kinds)
  else None

(** val bind_params_to_args_carried : bool -> (simple -> bool) -> Typing_env.t
    -> ((variable * flambda_kind) * simple) list -> (Typing_env.t * bool) option
    **)

let rec bind_params_to_args_carried fit aliased tenv = function
  | [] -> Some (tenv, fit)
  | p :: bindings0 ->
    let p0, canonical = p in
    let x, kind0 = p0 in
    if
      well_formed_or_known fit tenv
      && negb (Typing_env.mem None tenv (Name_var x))
    then
      let defined =
        Typing_env.add_variable_definition tenv x kind0 Name_mode.normal
      in
      if
        (aliased canonical && simple_in_terms_b tenv canonical)
        && simple_of_kind_b tenv canonical kind0
      then
        match Typing_env.add_alias defined (Var x) canonical with
        | Some o -> (
          match o with
          | Ok result ->
            bind_params_to_args_carried
              (fit && alias_keeps_fit defined (Var x) canonical kind0)
              aliased result.Typing_env.add_alias_result_t bindings0
          | _ -> bind_params_to_args_carried fit aliased defined bindings0)
        | None -> bind_params_to_args_carried fit aliased defined bindings0
      else bind_params_to_args_carried fit aliased defined bindings0
    else None

(** val use_env_carried : bool -> Typing_env.t -> Typing_env.t -> variable list
    -> handler_metadata -> simple list -> (Typing_env.t * bool) option **)

let use_env_carried fit scope tenv params metadata args =
  let kinds = metadata.hm_params_kinds in
  match simplify_simples tenv args with
  | Some answers ->
    if
      Nat.eqb (length kinds) (length params)
      && Nat.eqb (length answers) (length params)
    then
      bind_params_to_args_carried fit
        (fun canonical ->
          simple_in_terms_b scope canonical && not_among params canonical)
        tenv
        (combine (combine params kinds) (map snd answers))
    else None
  | None -> None

(** val find_use_carried : bool -> Typing_env.t -> Typing_env.t -> continuation
    -> continuation_handler -> expr -> (((Typing_env.t * bool) * variable list)
    * continuation list) option **)

let rec find_use_carried fit scope tenv k h body =
  match body with
  | Let (x, declared, defining_expr, rest) -> (
    if var_free_in_handler_b x h
    then None
    else
      match let_env_carried fit tenv x declared defining_expr with
      | Some p -> (
        let tenv', fit' = p in
        match find_use_carried fit' scope tenv' k h rest with
        | Some p0 ->
          let p1, ks = p0 in
          let p2, xs = p1 in
          Some ((p2, x :: xs), ks)
        | None -> None)
      | None -> None)
  | Let_cont_non_recursive (k', h', rest) ->
    if
      (negb (Pos.eqb k k') && negb (cont_free_in_handler_b k h'))
      && negb (cont_free_in_handler_b k' h)
    then
      match find_use_carried fit scope tenv k h rest with
      | Some p ->
        let p0, ks = p in
        Some (p0, k' :: ks)
      | None -> None
    else None
  | Apply_cont _ -> (
    let (Handler (params, metadata, _)) = h in
    match leaf_uses tenv k body with
    | Some l -> (
      match l with
      | [] -> None
      | p :: l0 -> (
        let tenv_use, args = p in
        match l0 with
        | [] -> (
          match
            use_env_carried
              (fit && leaf_uses_keep_fit tenv k body)
              scope tenv_use params metadata args
          with
          | Some p0 -> Some ((p0, []), [])
          | None -> None)
        | _ :: _ -> None))
    | None -> None)
  | Switch (_, _) -> (
    let (Handler (params, metadata, _)) = h in
    match leaf_uses tenv k body with
    | Some l -> (
      match l with
      | [] -> None
      | p :: l0 -> (
        let tenv_use, args = p in
        match l0 with
        | [] -> (
          match
            use_env_carried
              (fit && leaf_uses_keep_fit tenv k body)
              scope tenv_use params metadata args
          with
          | Some p0 -> Some ((p0, []), [])
          | None -> None)
        | _ :: _ -> None))
    | None -> None)
  | _ -> None

(** val gather_uses_carried : bool -> Typing_env.t -> continuation ->
    continuation_handler -> expr -> ((((Typing_env.t * bool) * simple list) list
    * variable list) * continuation list) option **)

let rec gather_uses_carried fit tenv k h body =
  match body with
  | Let (x, declared, defining_expr, rest) -> (
    if var_free_in_handler_b x h
    then None
    else
      match let_env_carried fit tenv x declared defining_expr with
      | Some p -> (
        let tenv', fit' = p in
        match gather_uses_carried fit' tenv' k h rest with
        | Some p0 ->
          let p1, ks = p0 in
          let uses, xs = p1 in
          Some ((uses, x :: xs), ks)
        | None -> None)
      | None -> None)
  | Let_cont_non_recursive (k', h', rest) ->
    if negb (Pos.eqb k k') && negb (cont_free_in_handler_b k' h)
    then
      match gather_uses_carried fit tenv k h rest with
      | Some p ->
        let p0, ks = p in
        let uses, xs = p0 in
        if cont_free_in_handler_b k h'
        then
          let (Handler (params', metadata', body')) = h' in
          if
            negb (cont_free_in_handler_b k h)
            && forallb (fun x -> negb (var_free_in_handler_b x h)) params'
          then
            match handler_env_carried fit tenv params' metadata' with
            | Some tenv_handler -> (
              match gather_uses_carried fit tenv_handler k h body' with
              | Some p1 ->
                let p2, ks' = p1 in
                let uses', xs' = p2 in
                Some
                  ( (app uses' uses, app params' (app xs' xs)),
                    k :: k' :: app ks' ks )
              | None -> None)
            | None -> None
          else None
        else Some ((uses, xs), k' :: ks)
      | None -> None
    else None
  | Apply_cont _ -> (
    match leaf_uses tenv k body with
    | Some uses ->
      Some
        ( ( map
              (fun use ->
                (fst use, fit && leaf_uses_keep_fit tenv k body), snd use)
              uses,
            [] ),
          [] )
    | None -> None)
  | Switch (_, _) -> (
    match leaf_uses tenv k body with
    | Some uses ->
      Some
        ( ( map
              (fun use ->
                (fst use, fit && leaf_uses_keep_fit tenv k body), snd use)
              uses,
            [] ),
          [] )
    | None -> None)
  | _ -> None

(** val find_gathered_use_carried : bool -> Typing_env.t -> continuation ->
    continuation_handler -> expr -> (((Typing_env.t * bool) * variable list) *
    continuation list) option **)

let find_gathered_use_carried fit tenv k h body =
  let (Handler (params, metadata, handler)) = h in
  match
    gather_uses_carried fit tenv k (Handler (params, metadata, handler)) body
  with
  | Some p -> (
    let p0, ks = p in
    let l, xs = p0 in
    match l with
    | [] -> None
    | p1 :: l0 -> (
      let p2, args = p1 in
      let tenv_use, fit_use = p2 in
      match l0 with
      | [] -> (
        match use_env_carried fit_use tenv tenv_use params metadata args with
        | Some p3 -> Some ((p3, xs), ks)
        | None -> None)
      | _ :: _ -> None))
  | None -> None

(** val find_one_use_carried : bool -> Typing_env.t -> continuation ->
    continuation_handler -> expr -> (((Typing_env.t * bool) * variable list) *
    continuation list) option **)

let find_one_use_carried fit tenv k h body =
  match find_use_carried fit tenv tenv k h body with
  | Some found -> Some found
  | None -> find_gathered_use_carried fit tenv k h body

(** val simplify_expr_carried : bool -> Typing_env.t -> expr -> expr **)

let rec simplify_expr_carried fit tenv e =
  match e with
  | Let (x, declared, defining_expr, body) -> (
    let l, keeps =
      simplify_let_carried fit tenv x
        (resolve_value_slot tenv declared defining_expr)
    in
    match l with
    | Step_invalid -> Invalid
    | Step_let (defining_expr', tenv') ->
      Let
        ( x,
          declared,
          defining_expr',
          simplify_expr_carried (fit && keeps) tenv' body )
    | Step_stop -> (
      match declare_variable_carried fit tenv x declared with
      | Some tenv' ->
        Let (x, declared, defining_expr, simplify_expr_carried fit tenv' body)
      | None -> e))
  | Let_static (bindings, body) ->
    let tenv' = add_static_bindings tenv bindings in
    let fit' = fit && statics_keep_fit tenv bindings in
    Let_static
      ( map (simplify_static_binding_carried fit' tenv') bindings,
        simplify_expr_carried fit' tenv' body )
  | Let_cont_non_recursive (k, handler, body) ->
    let body' = simplify_expr_carried fit tenv body in
    Let_cont_non_recursive
      ( k,
        (let (Handler (params, metadata, handler_body)) = handler in
         match find_one_use_carried fit tenv k handler body' with
         | Some p ->
           let p0, ks = p in
           let p1, xs = p0 in
           let target, fit_target = p1 in
           let rewritten =
             Handler
               ( params,
                 metadata,
                 simplify_expr_carried fit_target target handler_body )
           in
           if binders_not_free xs ks rewritten
           then rewritten
           else simplify_handler_carried false fit tenv handler
         | None -> simplify_handler_carried false fit tenv handler),
        body' )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, simplify_handler_carried true fit tenv h)
          handlers,
        simplify_expr_carried fit tenv body )
  | Apply ap -> simplify_apply tenv ap
  | Apply_cont ac -> Apply_cont (simplify_apply_cont tenv ac)
  | Switch (scrutinee, arms) -> simplify_switch tenv scrutinee arms
  | Invalid -> Invalid

(** val simplify_handler_carried : bool -> bool -> Typing_env.t ->
    continuation_handler -> continuation_handler **)

and simplify_handler_carried recursive fit tenv h =
  match h with
  | Handler (params, metadata, handler) -> (
    match handler_env_carried fit tenv params metadata with
    | Some tenv_handler ->
      let handler' = simplify_expr_carried fit tenv_handler handler in
      if negb recursive || eqb (binds_statics handler) (binds_statics handler')
      then Handler (params, metadata, handler')
      else h
    | None -> h)

(** val simplify_static_binding_carried : bool -> Typing_env.t -> static_binding
    -> static_binding **)

and simplify_static_binding_carried fit tenv binding =
  match binding with
  | Bind_code (id, c) -> Bind_code (id, simplify_code_carried fit tenv c)
  | _ -> binding

(** val simplify_code_carried : bool -> Typing_env.t -> code -> code **)

and simplify_code_carried fit tenv c =
  match c with
  | Code (params, my_closure, ret, exn, metadata, body) -> (
    match code_env_in_carried fit tenv params my_closure metadata with
    | Some tenv_code ->
      let body' = simplify_expr_carried fit tenv_code body in
      if negb (binds_statics body) && negb (binds_statics body')
      then Code (params, my_closure, ret, exn, metadata, body')
      else c
    | None -> c)

(** val simplify_by_types_carried : expr -> expr **)

let simplify_by_types_carried e = simplify_expr_carried true Typing_env.create e
