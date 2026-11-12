open Datatypes
open FlambdaLiftSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaUnusedStaticsSpec
open FlambdaWellFormedSpec
open List

(** val head_bindings : expr -> static_binding list **)

let rec head_bindings = function
  | Let_static (bindings, body) -> app bindings (head_bindings body)
  | _ -> []

(** val under_head : expr -> expr **)

let rec under_head e =
  match e with Let_static (_, body) -> under_head body | _ -> e

(** val value_slots_plain : (value_slot * simple) list -> bool **)

let value_slots_plain slots =
  forallb (fun slot -> plain_simple (snd slot)) slots

(** val static_const_total : static_const -> bool **)

let static_const_total = function
  | Static_const_set_of_closures (_, slots) -> value_slots_plain slots
  | Static_const_closure_of_set (slot, _, decls, slots) -> (
    match lookup slot decls with
    | Some _ -> value_slots_plain slots
    | None -> false)
  | Static_const_block (_, fields) -> forallb plain_simple fields
  | Static_const_boxed_number contents -> plain_simple contents
  | Static_const_immutable_string _ -> true

(** val removed_binding_total : dropped -> static_binding -> bool **)

let removed_binding_total d = function
  | Bind_symbol (s, const) -> symbol_kept d s || static_const_total const
  | _ -> true

(** val kept_code_binds_only_kept : dropped -> static_binding -> bool **)

let kept_code_binds_only_kept d = function
  | Bind_code (id, c) -> negb (code_kept d id) || code_binds_only_kept d c
  | _ -> true

(** val head_statics_removable : dropped -> expr -> bool **)

let head_statics_removable d e =
  ((((expr_avoids d e && binds_only_kept d (under_head e))
    && forallb (kept_code_binds_only_kept d) (head_bindings e))
   && distinct (flat_map symbols_of_binding (head_bindings e)))
  && distinct (flat_map code_ids_of_binding (head_bindings e)))
  && forallb (removed_binding_total d) (head_bindings e)
