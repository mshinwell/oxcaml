open BinInt
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaSimplifyApplySpec
open FlambdaSimplifyPrimitivesSpec
open FlambdaSimplifyProjectionsSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv
open List
open ListDef

(** val static_const_simples : static_const -> simple list **)

let static_const_simples = function
  | Static_const_set_of_closures (_, value_slots) -> map snd value_slots
  | Static_const_closure_of_set (_, _, _, value_slots) -> map snd value_slots
  | Static_const_block (_, fields) -> fields
  | Static_const_boxed_number contents -> contents :: []
  | Static_const_immutable_string _ -> []

(** val static_const_type : static_const -> flambda_type list -> flambda_type
    option **)

let static_const_type const tys =
  match const with
  | Static_const_set_of_closures (code, value_slots) ->
    Some (set_of_closures_type code (map fst value_slots) tys)
  | Static_const_closure_of_set (slot, _, function_decls, value_slots) ->
    Some (closure_of_set_type slot function_decls (map fst value_slots) tys)
  | Static_const_block (tag, _) ->
    if Z.ltb tag no_scan_tag && forallb (fun ty -> kind_eqb (kind ty) Value) tys
    then Some (make_block_type tag tys)
    else None
  | Static_const_boxed_number _ -> (
    match tys with
    | [] -> None
    | ty :: l -> (
      match l with
      | [] -> (
        match boxable_number_of_kind (kind ty) with
        | Some k -> Some (box_number k ty Alloc_mode.Heap)
        | None -> None)
      | _ :: _ -> None))
  | Static_const_immutable_string bytes -> Some (this_immutable_string bytes)

(** val static_const_type_in : Typing_env.t -> static_const -> flambda_type
    option **)

let static_const_type_in tenv const =
  match simplify_simples tenv (static_const_simples const) with
  | Some answers -> static_const_type const (map fst answers)
  | None -> None

(** val define_symbol_with_type : Typing_env.t -> symbol -> flambda_type ->
    Typing_env.t **)

let define_symbol_with_type tenv s ty =
  Typing_env.replace_equation
    (Typing_env.add_symbol_definition tenv s)
    (Name_symbol s) ty

(** val is_closure_const : static_const -> bool **)

let is_closure_const = function
  | Static_const_set_of_closures (_, _) -> true
  | Static_const_closure_of_set (_, _, _, _) -> true
  | _ -> false

(** val closure_symbols_of : static_binding list -> symbol list **)

let rec closure_symbols_of = function
  | [] -> []
  | s0 :: bindings0 -> (
    match s0 with
    | Bind_symbol (s, const) ->
      if is_closure_const const
      then s :: closure_symbols_of bindings0
      else closure_symbols_of bindings0
    | _ -> closure_symbols_of bindings0)

(** val add_block_like_bindings : Typing_env.t -> static_binding list ->
    Typing_env.t **)

let rec add_block_like_bindings tenv = function
  | [] -> tenv
  | s0 :: bindings0 -> (
    match s0 with
    | Bind_symbol (s, const) ->
      let tenv0 =
        if is_closure_const const
        then tenv
        else
          match static_const_type_in tenv const with
          | Some ty -> define_symbol_with_type tenv s ty
          | None -> Typing_env.add_symbol_definition tenv s
      in
      add_block_like_bindings tenv0 bindings0
    | _ -> add_block_like_bindings tenv bindings0)

(** val add_closure_bindings : Typing_env.t -> Typing_env.t -> static_binding
    list -> Typing_env.t **)

let rec add_closure_bindings prior tenv = function
  | [] -> tenv
  | s0 :: bindings0 -> (
    match s0 with
    | Bind_symbol (s, const) ->
      let tenv0 =
        if is_closure_const const
        then
          match static_const_type_in prior const with
          | Some ty -> Typing_env.replace_equation tenv (Name_symbol s) ty
          | None -> tenv
        else tenv
      in
      add_closure_bindings prior tenv0 bindings0
    | _ -> add_closure_bindings prior tenv bindings0)

(** val add_static_bindings : Typing_env.t -> static_binding list ->
    Typing_env.t **)

let add_static_bindings tenv bindings =
  let prior =
    add_block_like_bindings
      (Typing_env.add_symbol_definitions tenv (closure_symbols_of bindings))
      bindings
  in
  add_closure_bindings prior prior bindings
