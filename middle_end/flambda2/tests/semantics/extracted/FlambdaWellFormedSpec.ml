open BinNums
open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveSpec
open List
open ListDef

(** val free_continuations : expr -> continuation list **)

let rec free_continuations = function
  | Let (_, _, body) -> free_continuations body
  | Let_static (_, body) -> free_continuations body
  | Let_cont_non_recursive (k, h, body) ->
    app
      (handler_free_continuations h)
      (without (k :: []) (free_continuations body))
  | Let_cont_recursive (handlers, body) ->
    without (map fst handlers)
      (app
         (flat_map
            (fun pat ->
              let _, h = pat in
              handler_free_continuations h)
            handlers)
         (free_continuations body))
  | Apply ap -> [ap.ap_continuation; ap.ap_exn_continuation]
  | Apply_cont ac -> ac.ac_continuation :: []
  | Switch (_, arms) -> map (fun arm -> (snd arm).ac_continuation) arms
  | Invalid -> []

(** val handler_free_continuations : continuation_handler -> continuation list **)

and handler_free_continuations = function
  | Handler (_, handler) -> free_continuations handler

(** val raises_to : continuation -> expr -> bool **)

let rec raises_to k = function
  | Let (_, _, body) -> raises_to k body
  | Let_static (_, body) -> raises_to k body
  | Let_cont_non_recursive (_, h, body) ->
    handler_raises_to k h || raises_to k body
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let _, h = pat in
        handler_raises_to k h)
      handlers
    || raises_to k body
  | Apply ap -> Pos.eqb k ap.ap_exn_continuation
  | _ -> false

(** val handler_raises_to : continuation -> continuation_handler -> bool **)

and handler_raises_to k = function Handler (_, handler) -> raises_to k handler

(** val handler_at_toplevel : continuation -> continuation -> expr -> bool **)

let handler_at_toplevel unit_exn k body =
  negb (raises_to k body) && all_among (free_continuations body) [k; unit_exn]

(** val statics_at_toplevel : continuation -> bool -> expr -> bool **)

let rec statics_at_toplevel unit_exn toplevel = function
  | Let (_, _, body) -> statics_at_toplevel unit_exn toplevel body
  | Let_static (bindings, body) ->
    (toplevel && forallb (binding_statics_at_toplevel unit_exn) bindings)
    && statics_at_toplevel unit_exn toplevel body
  | Let_cont_non_recursive (k, h, body) ->
    handler_statics_at_toplevel unit_exn
      (toplevel && handler_at_toplevel unit_exn k body)
      h
    && statics_at_toplevel unit_exn toplevel body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        handler_statics_at_toplevel unit_exn false h)
      handlers
    && statics_at_toplevel unit_exn toplevel body
  | _ -> true

(** val handler_statics_at_toplevel : continuation -> bool ->
    continuation_handler -> bool **)

and handler_statics_at_toplevel unit_exn toplevel = function
  | Handler (_, handler) -> statics_at_toplevel unit_exn toplevel handler

(** val binding_statics_at_toplevel : continuation -> static_binding -> bool **)

and binding_statics_at_toplevel unit_exn = function
  | Bind_code (_, c) -> code_statics_at_toplevel unit_exn c
  | _ -> true

(** val code_statics_at_toplevel : continuation -> code -> bool **)

and code_statics_at_toplevel unit_exn = function
  | Code (_, _, _, _, body) -> statics_at_toplevel unit_exn false body

(** val code_ids_of_binding : static_binding -> code_id list **)

let code_ids_of_binding = function Bind_code (id, _) -> id :: [] | _ -> []

(** val symbols_of_binding : static_binding -> symbol list **)

let symbols_of_binding = function Bind_symbol (s, _) -> s :: [] | _ -> []

(** val static_names : (static_binding -> positive list) -> expr -> positive
    list **)

let rec static_names names_of = function
  | Let (_, _, body) -> static_names names_of body
  | Let_static (bindings, body) ->
    app (flat_map names_of bindings) (static_names names_of body)
  | Let_cont_non_recursive (_, h, body) ->
    app (handler_static_names names_of h) (static_names names_of body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map
         (fun pat ->
           let _, h = pat in
           handler_static_names names_of h)
         handlers)
      (static_names names_of body)
  | _ -> []

(** val handler_static_names : (static_binding -> positive list) ->
    continuation_handler -> positive list **)

and handler_static_names names_of = function
  | Handler (_, handler) -> static_names names_of handler

(** val set_well_formed : function_slot -> (function_slot * code_id) list ->
    bool **)

let set_well_formed slot function_decls =
  (is_bound slot function_decls && distinct (map fst function_decls))
  && distinct (map snd function_decls)

(** val named_sets_well_formed : named -> bool **)

let named_sets_well_formed = function
  | Closure_of_set (slot, function_decls, _) ->
    set_well_formed slot function_decls
  | _ -> true

(** val binds_symbol_to : symbol -> static_const -> static_binding -> bool **)

let binds_symbol_to s const = function
  | Bind_symbol (s', const') ->
    Pos.eqb s s' && if static_const_eq_dec const const' then true else false
  | _ -> false

(** val static_set_whole : static_binding list -> static_binding -> bool **)

let static_set_whole bindings = function
  | Bind_symbol (s, const) -> (
    match const with
    | Static_const_closure_of_set
        (slot, closure_symbols, function_decls, value_slots) ->
      ((set_well_formed slot function_decls
       &&
       if
         list_eq_dec Pos.eq_dec (map fst closure_symbols)
           (map fst function_decls)
       then true
       else false)
      &&
      match lookup slot closure_symbols with
      | Some s' -> Pos.eqb s s'
      | None -> false)
      && forallb
           (fun pat ->
             let slot', s' = pat in
             existsb
               (binds_symbol_to s'
                  (Static_const_closure_of_set
                     (slot', closure_symbols, function_decls, value_slots)))
               bindings)
           closure_symbols
    | _ -> true)
  | _ -> true

(** val static_set_code_ids : static_binding -> code_id list **)

let static_set_code_ids = function
  | Bind_symbol (_, const) -> (
    match const with
    | Static_const_set_of_closures (code0, _) -> code0 :: []
    | Static_const_closure_of_set (_, _, function_decls, _) ->
      map snd function_decls
    | _ -> [])
  | _ -> []

(** val binds_symbol_of_set : static_binding -> static_binding -> bool **)

let binds_symbol_of_set binding binding' =
  match binding with
  | Bind_symbol (_, const) -> (
    match const with
    | Static_const_closure_of_set (_, closure_symbols, _, _) -> (
      match binding' with
      | Bind_symbol (s', _) -> among s' (map snd closure_symbols)
      | _ -> false)
    | _ -> false)
  | _ -> false

(** val static_sets_code_disjoint : static_binding list -> bool **)

let rec static_sets_code_disjoint = function
  | [] -> true
  | binding :: bindings0 ->
    forallb
      (fun binding' ->
        binds_symbol_of_set binding binding'
        ||
        match
          inter (static_set_code_ids binding) (static_set_code_ids binding')
        with
        | [] -> true
        | _ :: _ -> false)
      bindings0
    && static_sets_code_disjoint bindings0

(** val sets_well_formed : expr -> bool **)

let rec sets_well_formed = function
  | Let (_, d, body) -> named_sets_well_formed d && sets_well_formed body
  | Let_static (bindings, body) ->
    ((forallb (static_set_whole bindings) bindings
     && static_sets_code_disjoint bindings)
    && forallb binding_sets_well_formed bindings)
    && sets_well_formed body
  | Let_cont_non_recursive (_, h, body) ->
    handler_sets_well_formed h && sets_well_formed body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        handler_sets_well_formed h)
      handlers
    && sets_well_formed body
  | _ -> true

(** val handler_sets_well_formed : continuation_handler -> bool **)

and handler_sets_well_formed = function
  | Handler (_, handler) -> sets_well_formed handler

(** val binding_sets_well_formed : static_binding -> bool **)

and binding_sets_well_formed = function
  | Bind_code (_, c) -> code_sets_well_formed c
  | _ -> true

(** val code_sets_well_formed : code -> bool **)

and code_sets_well_formed = function
  | Code (_, _, _, _, body) -> sets_well_formed body

(** val simple_in_range : simple -> bool **)

let simple_in_range = function Const c -> const_in_range c | _ -> true

(** val value_slots_in_range : (value_slot * simple) list -> bool **)

let value_slots_in_range value_slots =
  forallb (fun slot -> simple_in_range (snd slot)) value_slots

(** val named_in_range : named -> bool **)

let named_in_range = function
  | Simple s -> simple_in_range s
  | Prim (p, args) -> prim_in_range p && forallb simple_in_range args
  | Set_of_closures (_, value_slots) -> value_slots_in_range value_slots
  | Closure_of_set (_, _, value_slots) -> value_slots_in_range value_slots
  | Project_value_slot (_, closure) -> simple_in_range closure
  | Project_value_slot_from (_, _, closure) -> simple_in_range closure
  | Project_function_slot (_, _, closure) -> simple_in_range closure

(** val static_const_in_range : static_const -> bool **)

let static_const_in_range = function
  | Static_const_set_of_closures (_, value_slots) ->
    value_slots_in_range value_slots
  | Static_const_closure_of_set (_, _, _, value_slots) ->
    value_slots_in_range value_slots
  | Static_const_block (tag, fields) ->
    tag_in_range tag && forallb simple_in_range fields
  | Static_const_boxed_number contents -> simple_in_range contents
  | Static_const_immutable_string bytes -> forallb byte_in_range bytes

(** val apply_cont_in_range : apply_cont -> bool **)

let apply_cont_in_range ac = forallb simple_in_range ac.ac_args

(** val apply_in_range : apply_expr -> bool **)

let apply_in_range ap =
  simple_in_range ap.ap_callee && forallb simple_in_range ap.ap_args

(** val arm_in_range : (coq_Z * apply_cont) -> bool **)

let arm_in_range arm =
  ocaml_int_in_range (fst arm) && apply_cont_in_range (snd arm)

(** val numbers_in_range : expr -> bool **)

let rec numbers_in_range = function
  | Let (_, d, body) -> named_in_range d && numbers_in_range body
  | Let_static (bindings, body) ->
    forallb binding_numbers_in_range bindings && numbers_in_range body
  | Let_cont_non_recursive (_, h, body) ->
    handler_numbers_in_range h && numbers_in_range body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        handler_numbers_in_range h)
      handlers
    && numbers_in_range body
  | Apply ap -> apply_in_range ap
  | Apply_cont ac -> apply_cont_in_range ac
  | Switch (scrutinee, arms) ->
    simple_in_range scrutinee && forallb arm_in_range arms
  | Invalid -> true

(** val handler_numbers_in_range : continuation_handler -> bool **)

and handler_numbers_in_range = function
  | Handler (_, handler) -> numbers_in_range handler

(** val binding_numbers_in_range : static_binding -> bool **)

and binding_numbers_in_range = function
  | Bind_code (_, c) -> code_numbers_in_range c
  | Bind_deleted_code _ -> true
  | Bind_symbol (_, const) -> static_const_in_range const

(** val code_numbers_in_range : code -> bool **)

and code_numbers_in_range = function
  | Code (_, _, _, _, body) -> numbers_in_range body

(** val well_formed_unit : continuation -> expr -> bool **)

let well_formed_unit unit_exn e =
  (((statics_at_toplevel unit_exn true e
    && distinct (static_names code_ids_of_binding e))
   && distinct (static_names symbols_of_binding e))
  && sets_well_formed e)
  && numbers_in_range e
