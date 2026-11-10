open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaTypesSpec
open List
open ListDef

(** val var_in_type : variable -> flambda_type -> bool **)

let var_in_type x = function Equals s -> var_in_simple x s | _ -> false

(** val drop_var : variable -> typing_env -> typing_env **)

let drop_var x tenv =
  filter
    (fun pat ->
      let y, t = pat in
      negb (Pos.eqb x y) && negb (var_in_type x t))
    tenv

(** val drop_vars : variable list -> typing_env -> typing_env **)

let drop_vars xs tenv = fold_right drop_var tenv xs

(** val canonical_value_slots : typing_env -> (value_slot * simple) list ->
    (value_slot * simple) list **)

let canonical_value_slots tenv slots =
  map (fun slot -> fst slot, canonical_simple tenv (snd slot)) slots

(** val canonical_named : typing_env -> named -> named **)

let canonical_named tenv = function
  | Simple s -> Simple (canonical_simple tenv s)
  | Prim (p, args) -> Prim (p, map (canonical_simple tenv) args)
  | Set_of_closures (code, slots) ->
    Set_of_closures (code, canonical_value_slots tenv slots)
  | Project_value_slot (slot, closure) ->
    Project_value_slot (slot, canonical_simple tenv closure)

(** val canonical_static_const : typing_env -> static_const -> static_const **)

let canonical_static_const tenv = function
  | Static_const_set_of_closures (code, slots) ->
    Static_const_set_of_closures (code, canonical_value_slots tenv slots)
  | Static_const_block (tag, fields) ->
    Static_const_block (tag, map (canonical_simple tenv) fields)
  | Static_const_boxed_number contents ->
    Static_const_boxed_number (canonical_simple tenv contents)
  | Static_const_immutable_string bytes -> Static_const_immutable_string bytes

(** val canonical_static_binding : typing_env -> static_binding ->
    static_binding **)

let canonical_static_binding tenv = function
  | Bind_symbol (s, const) -> Bind_symbol (s, canonical_static_const tenv const)
  | x -> x

(** val canonical_apply_cont : typing_env -> apply_cont -> apply_cont **)

let canonical_apply_cont tenv ac =
  { ac_continuation = ac.ac_continuation;
    ac_args = map (canonical_simple tenv) ac.ac_args
  }

(** val canonical_apply : typing_env -> apply_expr -> apply_expr **)

let canonical_apply tenv ap =
  { ap_callee = canonical_simple tenv ap.ap_callee;
    ap_call_kind = ap.ap_call_kind;
    ap_args = map (canonical_simple tenv) ap.ap_args;
    ap_continuation = ap.ap_continuation;
    ap_exn_continuation = ap.ap_exn_continuation
  }

(** val typing_env_under_let : typing_env -> variable -> named -> typing_env **)

let typing_env_under_let tenv x = function
  | Simple s ->
    if var_in_simple x s
    then drop_var x tenv
    else (x, Equals s) :: drop_var x tenv
  | _ -> drop_var x tenv

(** val follow_aliases : typing_env -> expr -> expr **)

let rec follow_aliases tenv = function
  | Let (x, d, body) ->
    let d' = canonical_named tenv d in
    Let (x, d', follow_aliases (typing_env_under_let tenv x d') body)
  | Let_static (bindings, body) ->
    Let_static
      (map (canonical_static_binding tenv) bindings, follow_aliases tenv body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, follow_aliases_in_handler tenv h, follow_aliases tenv body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, follow_aliases tenv body)
  | Apply ap -> Apply (canonical_apply tenv ap)
  | Apply_cont ac -> Apply_cont (canonical_apply_cont tenv ac)
  | Switch (scrutinee, arms) ->
    Switch
      ( canonical_simple tenv scrutinee,
        map (fun arm -> fst arm, canonical_apply_cont tenv (snd arm)) arms )
  | Invalid -> Invalid

(** val follow_aliases_in_handler : typing_env -> continuation_handler ->
    continuation_handler **)

and follow_aliases_in_handler tenv = function
  | Handler (params, handler) ->
    Handler (params, follow_aliases (drop_vars params tenv) handler)
