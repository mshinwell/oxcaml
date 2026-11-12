open BinNums
open Datatypes
open FlambdaCompareSpec
open FlambdaFreshQuantifierSpec
open FlambdaModel
open FlambdaNominalSpec
open List
open ListDef
open Nat

(** val variables_in_simple : simple -> variable list **)

let variables_in_simple = function Var x -> x :: [] | _ -> []

(** val variables_in_simples : simple list -> variable list **)

let variables_in_simples args = flat_map variables_in_simple args

(** val variables_in_slots : (value_slot * simple) list -> variable list **)

let variables_in_slots slots =
  flat_map (fun slot -> variables_in_simple (snd slot)) slots

(** val variables_in_named : named -> variable list **)

let variables_in_named = function
  | Simple s -> variables_in_simple s
  | Prim (_, args) -> variables_in_simples args
  | Set_of_closures (_, slots) -> variables_in_slots slots
  | Closure_of_set (_, _, slots) -> variables_in_slots slots
  | Project_value_slot (_, closure) -> variables_in_simple closure
  | Project_value_slot_from (_, _, closure) -> variables_in_simple closure
  | Project_function_slot (_, _, closure) -> variables_in_simple closure

(** val variables_in_static_const : static_const -> variable list **)

let variables_in_static_const = function
  | Static_const_set_of_closures (_, slots) -> variables_in_slots slots
  | Static_const_closure_of_set (_, _, _, slots) -> variables_in_slots slots
  | Static_const_block (_, fields) -> variables_in_simples fields
  | Static_const_boxed_number contents -> variables_in_simple contents
  | Static_const_immutable_string _ -> []

(** val variables_in_apply_cont : apply_cont -> variable list **)

let variables_in_apply_cont ac = variables_in_simples ac.ac_args

(** val variables_in_apply : apply_expr -> variable list **)

let variables_in_apply ap =
  app
    (variables_in_simple ap.ap_callee)
    (app
       (variables_in_simples ap.ap_args)
       (variables_in_simples (exn_extra_simples ap)))

(** val variables_of : expr -> variable list **)

let rec variables_of = function
  | Let (x, _, d, body) -> x :: app (variables_in_named d) (variables_of body)
  | Let_static (bindings, body) ->
    app (flat_map variables_in_binding bindings) (variables_of body)
  | Let_cont_non_recursive (_, h, body) ->
    app (variables_in_handler h) (variables_of body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map (fun kh -> variables_in_handler (snd kh)) handlers)
      (variables_of body)
  | Apply ap -> variables_in_apply ap
  | Apply_cont ac -> variables_in_apply_cont ac
  | Switch (scrutinee, arms) ->
    app
      (variables_in_simple scrutinee)
      (flat_map (fun arm -> variables_in_apply_cont (snd arm)) arms)
  | Invalid -> []

(** val variables_in_handler : continuation_handler -> variable list **)

and variables_in_handler = function
  | Handler (params, _, handler) -> app params (variables_of handler)

(** val variables_in_binding : static_binding -> variable list **)

and variables_in_binding = function
  | Bind_code (_, c) -> variables_in_code c
  | Bind_deleted_code _ -> []
  | Bind_symbol (_, const) -> variables_in_static_const const

(** val variables_in_code : code -> variable list **)

and variables_in_code = function
  | Code (params, my_closure, _, _, _, body) ->
    my_closure :: app params (variables_of body)

(** val continuations_in_apply : apply_expr -> continuation list **)

let continuations_in_apply ap = [ap.ap_continuation; ap.ap_exn_continuation]

(** val continuations_of : expr -> continuation list **)

let rec continuations_of = function
  | Let (_, _, _, body) -> continuations_of body
  | Let_static (bindings, body) ->
    app (flat_map continuations_in_binding bindings) (continuations_of body)
  | Let_cont_non_recursive (k, h, body) ->
    k :: app (continuations_in_handler h) (continuations_of body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map
         (fun kh -> fst kh :: continuations_in_handler (snd kh))
         handlers)
      (continuations_of body)
  | Apply ap -> continuations_in_apply ap
  | Apply_cont ac -> apply_cont_continuations ac
  | Switch (_, arms) ->
    flat_map (fun arm -> apply_cont_continuations (snd arm)) arms
  | Invalid -> []

(** val continuations_in_handler : continuation_handler -> continuation list **)

and continuations_in_handler = function
  | Handler (_, _, handler) -> continuations_of handler

(** val continuations_in_binding : static_binding -> continuation list **)

and continuations_in_binding = function
  | Bind_code (_, c) -> continuations_in_code c
  | _ -> []

(** val continuations_in_code : code -> continuation list **)

and continuations_in_code = function
  | Code (_, _, return_continuation, exn_continuation, _, body) ->
    return_continuation :: exn_continuation :: continuations_of body

(** val names_of : expr -> positive list **)

let names_of e = app (variables_of e) (continuations_of e)

(** val binders : expr -> nat **)

let rec binders = function
  | Let (_, _, _, body) -> S (binders body)
  | Let_static (bindings, body) ->
    add (list_sum (map binders_in_binding bindings)) (binders body)
  | Let_cont_non_recursive (_, h, body) ->
    add (binders_in_handler h) (S (binders body))
  | Let_cont_recursive (handlers, body) ->
    add
      (add (length handlers)
         (list_sum (map (fun kh -> binders_in_handler (snd kh)) handlers)))
      (binders body)
  | _ -> O

(** val binders_in_handler : continuation_handler -> nat **)

and binders_in_handler = function
  | Handler (params, _, handler) -> add (length params) (binders handler)

(** val binders_in_binding : static_binding -> nat **)

and binders_in_binding = function
  | Bind_code (_, c) -> binders_in_code c
  | _ -> O

(** val binders_in_code : code -> nat **)

and binders_in_code = function
  | Code (params, _, _, _, _, body) ->
    S (add (length params) (S (S (binders body))))

(** val bind_variable : renaming -> variable -> variable -> renaming **)

let bind_variable r x x' =
  { variable_permutation = (rename_variable r x, x') :: r.variable_permutation;
    continuation_permutation = r.continuation_permutation
  }

(** val bind_continuation : renaming -> continuation -> continuation -> renaming
    **)

let bind_continuation r k k' =
  { variable_permutation = r.variable_permutation;
    continuation_permutation =
      (rename_continuation r k, k') :: r.continuation_permutation
  }

(** val new_variable : renaming -> positive list -> variable -> variable **)

let new_variable r news x = hd (rename_variable r x) news

(** val new_continuation : renaming -> positive list -> continuation ->
    continuation **)

let new_continuation r news k = hd (rename_continuation r k) news

(** val bind_variables : renaming -> positive list -> variable list -> (positive
    list * variable list) * renaming **)

let rec bind_variables r news = function
  | [] -> (news, []), r
  | x :: xs0 ->
    let x' = new_variable r news x in
    let p, r' = bind_variables (bind_variable r x x') (tl news) xs0 in
    let rest, xs' = p in
    (rest, x' :: xs'), r'

(** val bind_continuations : renaming -> positive list -> continuation list ->
    (positive list * continuation list) * renaming **)

let rec bind_continuations r news = function
  | [] -> (news, []), r
  | k :: ks0 ->
    let k' = new_continuation r news k in
    let p, r' = bind_continuations (bind_continuation r k k') (tl news) ks0 in
    let rest, ks' = p in
    (rest, k' :: ks'), r'

(** val thread : (positive list -> 'a1 -> positive list * 'a2) -> positive list
    -> 'a1 list -> positive list * 'a2 list **)

let rec thread f news = function
  | [] -> news, []
  | a :: l0 ->
    let rest, b = f news a in
    let rest', bs = thread f rest l0 in
    rest', b :: bs

(** val apart : renaming -> positive list -> expr -> positive list * expr **)

let rec apart r news = function
  | Let (x, kind, d, body) ->
    let x' = new_variable r news x in
    let rest, body' = apart (bind_variable r x x') (tl news) body in
    rest, Let (x', kind, rename_named r d, body')
  | Let_static (bindings, body) ->
    let rest, bindings' = thread (apart_binding r) news bindings in
    let rest', body' = apart r rest body in
    rest', Let_static (bindings', body')
  | Let_cont_non_recursive (k, h, body) ->
    let rest, h' = apart_handler r news h in
    let k' = new_continuation r rest k in
    let rest', body' = apart (bind_continuation r k k') (tl rest) body in
    rest', Let_cont_non_recursive (k', h', body')
  | Let_cont_recursive (handlers, body) ->
    let p, r' = bind_continuations r news (map fst handlers) in
    let rest, ks' = p in
    let rest', hs' =
      thread (fun news0 kh -> apart_handler r' news0 (snd kh)) rest handlers
    in
    let rest'', body' = apart r' rest' body in
    rest'', Let_cont_recursive (combine ks' hs', body')
  | Apply ap -> news, Apply (rename_apply r ap)
  | Apply_cont ac -> news, Apply_cont (rename_apply_cont r ac)
  | Switch (scrutinee, arms) ->
    ( news,
      Switch
        ( rename_simple r scrutinee,
          map (fun arm -> fst arm, rename_apply_cont r (snd arm)) arms ) )
  | Invalid -> news, Invalid

(** val apart_handler : renaming -> positive list -> continuation_handler ->
    positive list * continuation_handler **)

and apart_handler r news = function
  | Handler (params, metadata, handler) ->
    let p, r' = bind_variables r news params in
    let rest, params' = p in
    let rest', handler' = apart r' rest handler in
    rest', Handler (params', metadata, handler')

(** val apart_binding : renaming -> positive list -> static_binding -> positive
    list * static_binding **)

and apart_binding r news binding =
  match binding with
  | Bind_code (id, c) ->
    let rest, c' = apart_code r news c in
    rest, Bind_code (id, c')
  | Bind_deleted_code _ -> news, binding
  | Bind_symbol (s, const) -> news, Bind_symbol (s, rename_static_const r const)

(** val apart_code : renaming -> positive list -> code -> positive list * code **)

and apart_code r news = function
  | Code
      (params, my_closure, return_continuation, exn_continuation, metadata, body)
    ->
    let my_closure' = new_variable r news my_closure in
    let r0 = bind_variable r my_closure my_closure' in
    let p, r1 = bind_variables r0 (tl news) params in
    let rest, params' = p in
    let return_continuation' = new_continuation r1 rest return_continuation in
    let r2 = bind_continuation r1 return_continuation return_continuation' in
    let exn_continuation' = new_continuation r2 (tl rest) exn_continuation in
    let r3 = bind_continuation r2 exn_continuation exn_continuation' in
    let rest', body' = apart r3 (tl (tl rest)) body in
    ( rest',
      Code
        ( params',
          my_closure',
          return_continuation',
          exn_continuation',
          metadata,
          body' ) )

(** val renamed_apart_avoiding : continuation list -> expr -> expr **)

let renamed_apart_avoiding avoid e =
  snd
    (apart identity_renaming
       (fresh_names (binders e) (app avoid (names_of e)))
       e)

(** val rename_apart_avoiding : continuation list -> expr -> expr **)

let rename_apart_avoiding avoid e =
  let e' = renamed_apart_avoiding avoid e in
  if expr_eqb [] [] e e' then e' else e
