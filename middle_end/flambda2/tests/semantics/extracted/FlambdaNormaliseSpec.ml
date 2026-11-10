open BinNums
open BinPos
open Datatypes
open FlambdaApplySpec
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
  | Bind_symbol (_, const) -> (
    match const with
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
    Let_cont_non_recursive (k, h, inline_calls known body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, inline_calls known body)
  | Apply ap -> inline_apply known ap
  | _ -> e
