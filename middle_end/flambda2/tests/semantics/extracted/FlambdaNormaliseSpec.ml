open BinNums
open BinPos
open Datatypes
open FlambdaApplySpec
open FlambdaCompareSpec
open FlambdaModel
open FlambdaNominalSpec
open FlambdaSemanticsSpec
open List
open ListDef
open PeanoNat

(** val name_in : positive -> positive list -> bool **)

let name_in name names = existsb (Pos.eqb name) names

(** val simple_in_scope : variable list -> simple -> bool **)

let simple_in_scope vs = function Var x -> name_in x vs | _ -> true

(** val simples_in_scope : variable list -> simple list -> bool **)

let simples_in_scope vs args = forallb (simple_in_scope vs) args

(** val named_in_scope : variable list -> named -> bool **)

let named_in_scope vs = function
  | Simple s -> simple_in_scope vs s
  | Prim (_, args) -> simples_in_scope vs args
  | Set_of_closures (_, slots) ->
    forallb (fun slot -> simple_in_scope vs (snd slot)) slots
  | Project_value_slot (_, closure) -> simple_in_scope vs closure

(** val static_binding_in_scope : variable list -> static_binding -> bool **)

let static_binding_in_scope vs = function
  | Bind_symbol (_, const0) -> (
    match const0 with
    | Static_const_set_of_closures (_, slots) ->
      forallb (fun slot -> simple_in_scope vs (snd slot)) slots
    | Static_const_block (_, fields) -> simples_in_scope vs fields
    | Static_const_boxed_number contents -> simple_in_scope vs contents
    | Static_const_immutable_string _ -> true)
  | _ -> true

(** val apply_cont_in_scope : variable list -> continuation list -> apply_cont
    -> bool **)

let apply_cont_in_scope vs ks ac =
  name_in ac.ac_continuation ks && simples_in_scope vs ac.ac_args

(** val expr_in_scope : variable list -> continuation list -> expr -> bool **)

let rec expr_in_scope vs ks = function
  | Let (x, d, body) -> named_in_scope vs d && expr_in_scope (x :: vs) ks body
  | Let_static (bindings, body) ->
    forallb (static_binding_in_scope vs) bindings && expr_in_scope vs ks body
  | Let_cont_non_recursive (k, h, body) ->
    handler_in_scope vs ks h && expr_in_scope vs (k :: ks) body
  | Let_cont_recursive (handlers, body) ->
    let ks' = app (map fst handlers) ks in
    forallb
      (fun pat ->
        let _, h = pat in
        handler_in_scope vs ks' h)
      handlers
    && expr_in_scope vs ks' body
  | Apply ap ->
    ((simple_in_scope vs ap.ap_callee && simples_in_scope vs ap.ap_args)
    && name_in ap.ap_continuation ks)
    && name_in ap.ap_exn_continuation ks
  | Apply_cont ac -> apply_cont_in_scope vs ks ac
  | Switch (scrutinee, arms) ->
    simple_in_scope vs scrutinee
    && forallb (fun arm -> apply_cont_in_scope vs ks (snd arm)) arms
  | Invalid -> true

(** val handler_in_scope : variable list -> continuation list ->
    continuation_handler -> bool **)

and handler_in_scope vs ks = function
  | Handler (params, handler) -> expr_in_scope (app params vs) ks handler

(** val inline_renaming : continuation -> continuation -> continuation ->
    continuation -> renaming **)

let inline_renaming ret exn k k_exn =
  { variable_permutation = [];
    continuation_permutation = [swap ret k exn, k_exn; ret, k]
  }

(** val var_in_simples : variable -> simple list -> bool **)

let var_in_simples x args =
  existsb (fun s -> match s with Var y -> Pos.eqb x y | _ -> false) args

(** val inlinable_b : apply_expr -> code -> bool **)

let inlinable_b ap c =
  ((((expr_in_scope
        (code_my_closure c :: code_params c)
        [code_return_continuation c; code_exn_continuation c]
        (code_body c)
     && negb (Pos.eqb (code_return_continuation c) (code_exn_continuation c)))
    && negb (Pos.eqb ap.ap_continuation ap.ap_exn_continuation))
   && negb (var_in_simples (code_my_closure c) ap.ap_args))
  && forallb
       (fun param -> negb (var_in_simples param ap.ap_args))
       (code_params c))
  && Nat.eqb (length (code_params c)) (length ap.ap_args)

(** val codes_of : static_binding list -> (code_id * code) list -> (code_id *
    code) list **)

let rec codes_of bindings known =
  match bindings with
  | [] -> known
  | s :: bindings0 -> (
    match s with
    | Bind_code (id, c) -> codes_of bindings0 ((id, c) :: known)
    | _ -> codes_of bindings0 known)

(** val inline_apply : (code_id * code) list -> apply_expr -> expr **)

let inline_apply known ap =
  match ap.ap_call_kind with
  | Direct called -> (
    match lookup called known with
    | Some c ->
      if inlinable_b ap c
      then
        inlined_body c
          (inline_renaming
             (code_return_continuation c)
             (code_exn_continuation c) ap.ap_continuation ap.ap_exn_continuation)
          ap
      else Apply ap
    | None -> Apply ap)
  | Indirect -> Apply ap

(** val inline_calls : (code_id * code) list -> expr -> expr **)

let rec inline_calls known e =
  match e with
  | Let (x, d, body) -> Let (x, d, inline_calls known body)
  | Let_static (bindings, body) ->
    Let_static (bindings, inline_calls (codes_of bindings known) body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, inline_calls_in_handler known h, inline_calls known body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, inline_calls_in_handler known h)
          handlers,
        inline_calls known body )
  | Apply ap -> inline_apply known ap
  | _ -> e

(** val inline_calls_in_handler : (code_id * code) list -> continuation_handler
    -> continuation_handler **)

and inline_calls_in_handler known = function
  | Handler (params, handler) -> Handler (params, inline_calls known handler)

(** val var_in_simple : variable -> simple -> bool **)

let var_in_simple x = function Var y -> Pos.eqb x y | _ -> false

(** val var_in_value_slots : variable -> (value_slot * simple) list -> bool **)

let var_in_value_slots x slots =
  existsb (fun slot -> var_in_simple x (snd slot)) slots

(** val var_in_named : variable -> named -> bool **)

let var_in_named x = function
  | Simple s -> var_in_simple x s
  | Prim (_, args) -> var_in_simples x args
  | Set_of_closures (_, slots) -> var_in_value_slots x slots
  | Project_value_slot (_, closure) -> var_in_simple x closure

(** val var_in_static_binding : variable -> static_binding -> bool **)

let var_in_static_binding x = function
  | Bind_symbol (_, const0) -> (
    match const0 with
    | Static_const_set_of_closures (_, slots) -> var_in_value_slots x slots
    | Static_const_block (_, fields) -> var_in_simples x fields
    | Static_const_boxed_number contents -> var_in_simple x contents
    | Static_const_immutable_string _ -> false)
  | _ -> false

(** val var_free_b : variable -> expr -> bool **)

let rec var_free_b x = function
  | Let (y, d, body) ->
    var_in_named x d || (negb (Pos.eqb x y) && var_free_b x body)
  | Let_static (bindings, body) ->
    existsb (var_in_static_binding x) bindings || var_free_b x body
  | Let_cont_non_recursive (_, h, body) ->
    var_free_in_handler_b x h || var_free_b x body
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let _, h = pat in
        var_free_in_handler_b x h)
      handlers
    || var_free_b x body
  | Apply ap -> var_in_simple x ap.ap_callee || var_in_simples x ap.ap_args
  | Apply_cont ac -> var_in_simples x ac.ac_args
  | Switch (scrutinee, arms) ->
    var_in_simple x scrutinee
    || existsb (fun arm -> var_in_simples x (snd arm).ac_args) arms
  | Invalid -> false

(** val var_free_in_handler_b : variable -> continuation_handler -> bool **)

and var_free_in_handler_b x = function
  | Handler (params, handler) -> negb (name_in x params) && var_free_b x handler

(** val prim_may_fold : prim -> bool **)

let prim_may_fold = fun p -> !Prim_hook.prim_may_fold p

(** val named_may_go : named -> bool **)

let named_may_go = function Prim (p, _) -> prim_may_fold p | _ -> true

(** val remove_unused_lets : expr -> expr **)

let rec remove_unused_lets e =
  match e with
  | Let (x, d, body) ->
    let body' = remove_unused_lets body in
    if var_free_b x body' || negb (named_may_go d)
    then Let (x, d, body')
    else body'
  | Let_static (bindings, body) -> Let_static (bindings, remove_unused_lets body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, remove_unused_lets_in_handler h, remove_unused_lets body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, remove_unused_lets body)
  | _ -> e

(** val remove_unused_lets_in_handler : continuation_handler ->
    continuation_handler **)

and remove_unused_lets_in_handler = function
  | Handler (params, handler) -> Handler (params, remove_unused_lets handler)

(** val inline_cont_at_tail : continuation -> variable list -> expr -> expr ->
    expr option **)

let rec inline_cont_at_tail k params handler = function
  | Let (x, d, body0) ->
    if var_free_in_handler_b x (Handler (params, handler))
    then None
    else
      option_map
        (fun x0 -> Let (x, d, x0))
        (inline_cont_at_tail k params handler body0)
  | Let_static (bindings, body0) ->
    option_map
      (fun x -> Let_static (bindings, x))
      (inline_cont_at_tail k params handler body0)
  | Apply_cont ac ->
    if
      (Pos.eqb ac.ac_continuation k
      && Nat.eqb (length params) (length ac.ac_args))
      && forallb (fun param -> negb (var_in_simples param ac.ac_args)) params
    then Some (let_params params ac.ac_args handler)
    else None
  | _ -> None

(** val inline_tail_conts : expr -> expr **)

let rec inline_tail_conts e =
  match e with
  | Let (x, d, body) -> Let (x, d, inline_tail_conts body)
  | Let_static (bindings, body) -> Let_static (bindings, inline_tail_conts body)
  | Let_cont_non_recursive (k, handler0, body) -> (
    let (Handler (params, handler)) = handler0 in
    let handler' = inline_tail_conts handler in
    let body' = inline_tail_conts body in
    match inline_cont_at_tail k params handler' body' with
    | Some inlined -> inlined
    | None -> Let_cont_non_recursive (k, Handler (params, handler'), body'))
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, inline_tail_conts body)
  | _ -> e

(** val binds_something : static_binding -> bool **)

let binds_something = function Bind_deleted_code _ -> false | _ -> true

(** val let_static_if_any : static_binding list -> expr -> expr **)

let let_static_if_any bindings body =
  match bindings with [] -> body | _ :: _ -> Let_static (bindings, body)

(** val drop_deleted_code : expr -> expr **)

let rec drop_deleted_code e =
  match e with
  | Let (x, d, body) -> Let (x, d, drop_deleted_code body)
  | Let_static (bindings, body) ->
    let_static_if_any (filter binds_something bindings) (drop_deleted_code body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, handler)) = handler0 in
    Let_cont_non_recursive
      (k, Handler (params, drop_deleted_code handler), drop_deleted_code body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, drop_deleted_code body)
  | _ -> e

(** val consts_of_simples : simple list -> const list option **)

let rec consts_of_simples = function
  | [] -> Some []
  | s :: args0 -> (
    match s with
    | Const c -> option_map (fun x -> c :: x) (consts_of_simples args0)
    | _ -> None)

(** val fold_named : named -> named **)

let fold_named d =
  match d with
  | Prim (p, args) -> (
    match if prim_may_fold p then consts_of_simples args else None with
    | Some cs -> (
      match eval_prim p (map (fun x -> Value_const x) cs) with
      | Some v -> ( match v with Value_const c -> Simple (Const c) | _ -> d)
      | None -> d)
    | None -> d)
  | _ -> d

(** val fold_switch : simple -> (coq_Z * apply_cont) list -> expr **)

let fold_switch scrutinee arms =
  match scrutinee with
  | Const c -> (
    match c with
    | Naked_immediate i -> (
      match find_arm i arms with
      | Some ac -> Apply_cont ac
      | None -> Switch (scrutinee, arms))
    | _ -> Switch (scrutinee, arms))
  | _ -> Switch (scrutinee, arms)

(** val fold_constants : expr -> expr **)

let rec fold_constants e =
  match e with
  | Let (x, d, body) -> Let (x, fold_named d, fold_constants body)
  | Let_static (bindings, body) -> Let_static (bindings, fold_constants body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, handler)) = handler0 in
    Let_cont_non_recursive
      (k, Handler (params, fold_constants handler), fold_constants body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, fold_constants body)
  | Switch (scrutinee, arms) -> fold_switch scrutinee arms
  | _ -> e

(** val named_is_total : named -> bool **)

let named_is_total = function
  | Simple s -> ( match s with Var _ -> false | _ -> true)
  | _ -> false

(** val remove_unused_total_lets : expr -> expr **)

let rec remove_unused_total_lets e =
  match e with
  | Let (x, d, body) ->
    let body' = remove_unused_total_lets body in
    if named_is_total d && negb (var_free_b x body')
    then body'
    else Let (x, d, body')
  | Let_static (bindings, body) ->
    Let_static (bindings, remove_unused_total_lets body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler (params, remove_unused_total_lets handler),
        remove_unused_total_lets body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, remove_unused_total_lets body)
  | _ -> e

(** val named_defined : variable list -> named -> bool **)

let named_defined vs = function
  | Simple s -> simple_in_scope vs s
  | Set_of_closures (_, slots) ->
    forallb (fun slot -> simple_in_scope vs (snd slot)) slots
  | _ -> false

(** val remove_unused_defined_lets : variable list -> expr -> expr **)

let rec remove_unused_defined_lets vs e =
  match e with
  | Let (x, d, body) ->
    let body' = remove_unused_defined_lets (x :: vs) body in
    if named_defined vs d && negb (var_free_b x body')
    then body'
    else Let (x, d, body')
  | Let_static (bindings, body) ->
    Let_static (bindings, remove_unused_defined_lets vs body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler (params, remove_unused_defined_lets (app params vs) handler),
        remove_unused_defined_lets vs body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, remove_unused_defined_lets vs body)
  | _ -> e

(** val symbols_of : static_binding list -> (symbol * code_id option) list ->
    (symbol * code_id option) list **)

let rec symbols_of bindings known =
  match bindings with
  | [] -> known
  | s0 :: bindings0 -> (
    match s0 with
    | Bind_symbol (s, const0) -> (
      match const0 with
      | Static_const_set_of_closures (code0, _) ->
        symbols_of bindings0 ((s, Some code0) :: known)
      | _ -> symbols_of bindings0 ((s, None) :: known))
    | _ -> symbols_of bindings0 known)

(** val inline_known_apply : (code_id * code) list -> (symbol * code_id option)
    list -> apply_expr -> expr **)

let inline_known_apply known_code known_symbols ap =
  match ap.ap_callee with
  | Symbol s -> (
    match ap.ap_call_kind with
    | Direct called -> (
      match lookup s known_symbols with
      | Some o -> (
        match o with
        | Some code0 -> (
          match lookup called known_code with
          | Some c ->
            if Pos.eqb code0 called && inlinable_b ap c
            then
              inlined_body c
                (inline_renaming
                   (code_return_continuation c)
                   (code_exn_continuation c) ap.ap_continuation
                   ap.ap_exn_continuation)
                ap
            else Apply ap
          | None -> Apply ap)
        | None -> Apply ap)
      | None -> Apply ap)
    | Indirect -> Apply ap)
  | _ -> Apply ap

(** val inline_known_calls : (code_id * code) list -> (symbol * code_id option)
    list -> expr -> expr **)

let rec inline_known_calls known_code known_symbols e =
  match e with
  | Let (x, d, body) ->
    Let (x, d, inline_known_calls known_code known_symbols body)
  | Let_static (bindings, body) ->
    Let_static
      ( bindings,
        inline_known_calls
          (codes_of bindings known_code)
          (symbols_of bindings known_symbols)
          body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        inline_known_calls_in_handler known_code known_symbols h,
        inline_known_calls known_code known_symbols body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, inline_known_calls_in_handler known_code known_symbols h)
          handlers,
        inline_known_calls known_code known_symbols body )
  | Apply ap -> inline_known_apply known_code known_symbols ap
  | _ -> e

(** val inline_known_calls_in_handler : (code_id * code) list -> (symbol *
    code_id option) list -> continuation_handler -> continuation_handler **)

and inline_known_calls_in_handler known_code known_symbols = function
  | Handler (params, handler) ->
    Handler (params, inline_known_calls known_code known_symbols handler)

(** val binds_code : static_binding -> bool **)

let binds_code = function Bind_symbol (_, _) -> false | _ -> true

(** val code_first : static_binding list -> static_binding list **)

let code_first bindings =
  app
    (filter binds_code bindings)
    (filter (fun binding -> negb (binds_code binding)) bindings)

(** val merge_statics : expr -> expr **)

let rec merge_statics e =
  match e with
  | Let (x, d, body) -> Let (x, d, merge_statics body)
  | Let_static (bindings, body) -> (
    match merge_statics body with
    | Let_static (bindings', body') ->
      Let_static (code_first (app bindings bindings'), body')
    | x -> Let_static (code_first bindings, x))
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, handler)) = handler0 in
    Let_cont_non_recursive
      (k, Handler (params, merge_statics handler), merge_statics body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, merge_statics body)
  | _ -> e

(** val simple_eq_dec : simple -> simple -> bool **)

let simple_eq_dec s s' =
  match s with
  | Var x -> ( match s' with Var x0 -> Pos.eq_dec x x0 | _ -> false)
  | Symbol s0 -> ( match s' with Symbol s1 -> Pos.eq_dec s0 s1 | _ -> false)
  | Const c -> ( match s' with Const c0 -> const_eq_dec c c0 | _ -> false)

(** val apply_cont_eq_dec : apply_cont -> apply_cont -> bool **)

let apply_cont_eq_dec ac ac' =
  let { ac_continuation = ac_continuation0; ac_args = ac_args0 } = ac in
  let { ac_continuation = ac_continuation1; ac_args = ac_args1 } = ac' in
  if Pos.eq_dec ac_continuation0 ac_continuation1
  then list_eq_dec simple_eq_dec ac_args0 ac_args1
  else false

(** val collapse_switch : simple -> (coq_Z * apply_cont) list -> expr **)

let collapse_switch scrutinee arms =
  match arms with
  | [] -> Switch (scrutinee, arms)
  | p :: others ->
    let _, ac = p in
    if
      forallb
        (fun arm -> if apply_cont_eq_dec (snd arm) ac then true else false)
        others
    then Apply_cont ac
    else Switch (scrutinee, arms)

(** val collapse_switches : expr -> expr **)

let rec collapse_switches e =
  match e with
  | Let (x, d, body) -> Let (x, d, collapse_switches body)
  | Let_static (bindings, body) -> Let_static (bindings, collapse_switches body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, handler)) = handler0 in
    Let_cont_non_recursive
      (k, Handler (params, collapse_switches handler), collapse_switches body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, collapse_switches body)
  | Switch (scrutinee, arms) -> collapse_switch scrutinee arms
  | _ -> e
