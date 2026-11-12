open BinNums
open BinPos
open Datatypes
open FlambdaModel
open ListDef

type permutation = (positive * positive) list

(** val swap : positive -> positive -> positive -> positive **)

let swap a b name =
  if Pos.eqb name a then b else if Pos.eqb name b then a else name

(** val permute : permutation -> positive -> positive **)

let rec permute p name =
  match p with
  | [] -> name
  | p0 :: p1 ->
    let a, b = p0 in
    swap a b (permute p1 name)

type renaming =
  { variable_permutation : permutation;
    continuation_permutation : permutation
  }

(** val identity_renaming : renaming **)

let identity_renaming =
  { variable_permutation = []; continuation_permutation = [] }

(** val rename_variable : renaming -> variable -> variable **)

let rename_variable r x = permute r.variable_permutation x

(** val rename_continuation : renaming -> continuation -> continuation **)

let rename_continuation r k = permute r.continuation_permutation k

(** val rename_simple : renaming -> simple -> simple **)

let rename_simple r = function Var x -> Var (rename_variable r x) | x -> x

(** val rename_named : renaming -> named -> named **)

let rename_named r = function
  | Simple s -> Simple (rename_simple r s)
  | Prim (p, args) -> Prim (p, map (rename_simple r) args)
  | Set_of_closures (code0, value_slots) ->
    Set_of_closures
      (code0, map (fun slot -> fst slot, rename_simple r (snd slot)) value_slots)
  | Closure_of_set (slot, function_decls, value_slots) ->
    Closure_of_set
      ( slot,
        function_decls,
        map (fun slot0 -> fst slot0, rename_simple r (snd slot0)) value_slots )
  | Project_value_slot (slot, closure) ->
    Project_value_slot (slot, rename_simple r closure)
  | Project_value_slot_from (project_from, slot, closure) ->
    Project_value_slot_from (project_from, slot, rename_simple r closure)
  | Project_function_slot (move_from, move_to, closure) ->
    Project_function_slot (move_from, move_to, rename_simple r closure)

(** val rename_trap_action : renaming -> trap_action -> trap_action **)

let rename_trap_action r = function
  | Push exn_handler -> Push (rename_continuation r exn_handler)
  | Pop (exn_handler, kind) -> Pop (rename_continuation r exn_handler, kind)

(** val rename_apply_cont : renaming -> apply_cont -> apply_cont **)

let rename_apply_cont r ac =
  { ac_continuation = rename_continuation r ac.ac_continuation;
    ac_args = map (rename_simple r) ac.ac_args;
    ac_trap_action = option_map (rename_trap_action r) ac.ac_trap_action
  }

(** val rename_static_const : renaming -> static_const -> static_const **)

let rename_static_const r = function
  | Static_const_set_of_closures (code0, value_slots) ->
    Static_const_set_of_closures
      (code0, map (fun slot -> fst slot, rename_simple r (snd slot)) value_slots)
  | Static_const_closure_of_set
      (slot, closure_symbols, function_decls, value_slots) ->
    Static_const_closure_of_set
      ( slot,
        closure_symbols,
        function_decls,
        map (fun slot0 -> fst slot0, rename_simple r (snd slot0)) value_slots )
  | Static_const_block (tag, fields) ->
    Static_const_block (tag, map (rename_simple r) fields)
  | Static_const_boxed_number contents ->
    Static_const_boxed_number (rename_simple r contents)
  | Static_const_immutable_string bytes -> Static_const_immutable_string bytes

(** val rename_apply : renaming -> apply_expr -> apply_expr **)

let rename_apply r ap =
  { ap_callee = rename_simple r ap.ap_callee;
    ap_call_kind = ap.ap_call_kind;
    ap_args = map (rename_simple r) ap.ap_args;
    ap_continuation = rename_continuation r ap.ap_continuation;
    ap_exn_continuation = rename_continuation r ap.ap_exn_continuation;
    ap_exn_extra_args =
      map (fun arg -> rename_simple r (fst arg), snd arg) ap.ap_exn_extra_args;
    ap_args_arity = ap.ap_args_arity;
    ap_return_arity = ap.ap_return_arity
  }

(** val rename_expr : renaming -> expr -> expr **)

let rec rename_expr r = function
  | Let (x, kind, defining_expr, body) ->
    Let
      ( rename_variable r x,
        kind,
        rename_named r defining_expr,
        rename_expr r body )
  | Let_static (bindings, body) ->
    Let_static (map (rename_static_binding r) bindings, rename_expr r body)
  | Let_cont_non_recursive (k, handler, body) ->
    Let_cont_non_recursive
      (rename_continuation r k, rename_handler r handler, rename_expr r body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            rename_continuation r k, rename_handler r h)
          handlers,
        rename_expr r body )
  | Apply ap -> Apply (rename_apply r ap)
  | Apply_cont ac -> Apply_cont (rename_apply_cont r ac)
  | Switch (scrutinee, arms) ->
    Switch
      ( rename_simple r scrutinee,
        map (fun arm -> fst arm, rename_apply_cont r (snd arm)) arms )
  | Invalid -> Invalid

(** val rename_handler : renaming -> continuation_handler ->
    continuation_handler **)

and rename_handler r = function
  | Handler (params, metadata, handler) ->
    Handler (map (rename_variable r) params, metadata, rename_expr r handler)

(** val rename_static_binding : renaming -> static_binding -> static_binding **)

and rename_static_binding r = function
  | Bind_code (id, c) -> Bind_code (id, rename_code r c)
  | Bind_deleted_code id -> Bind_deleted_code id
  | Bind_symbol (s, const) -> Bind_symbol (s, rename_static_const r const)

(** val rename_code : renaming -> code -> code **)

and rename_code r = function
  | Code
      (params, my_closure, return_continuation, exn_continuation, metadata, body)
    ->
    Code
      ( map (rename_variable r) params,
        rename_variable r my_closure,
        rename_continuation r return_continuation,
        rename_continuation r exn_continuation,
        metadata,
        rename_expr r body )
