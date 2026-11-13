open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaUnboxParamsSpec
open FlambdaUnboxVariantsSpec
open List
open ListDef

(** val on_spine : variable -> expr -> bool **)

let rec on_spine x = function
  | Let (y, _, _, body) -> Pos.eqb x y || on_spine x body
  | _ -> false

(** val unbox_loop_read : facts -> continuation -> variable list ->
    handler_metadata -> expr -> expr -> read -> (((variable list *
    handler_metadata) * expr) * expr) option **)

let unbox_loop_read known k params metadata handler body r =
  let f = r.read_variable in
  let p = r.read_primitive in
  let i = r.read_position in
  match nth_error params i with
  | Some x ->
    if
      (may_take params metadata f && negb (var_free_b f handler))
      && on_spine f handler
    then
      match extend_applications known k i p body with
      | Some body0 -> (
        match
          extend_applications
            (facts_under_let
               (facts_under_params known params)
               f
               (Prim (Unary p, Var x :: [])))
            k i p r.read_without
        with
        | Some without ->
          Some
            ( ( (app params (f :: []), with_one_more metadata r.read_kind),
                without ),
              body0 )
        | None -> None)
      | None -> None
    else None
  | None -> None

type loop_state = ((variable list * handler_metadata) * expr) * expr

(** val loop_of : continuation -> loop_state -> expr **)

let loop_of k = function
  | p, body ->
    let p0, handler = p in
    let params, metadata = p0 in
    Let_cont_recursive ((k, Handler (params, metadata, handler)) :: [], body)

(** val unbox_loop_param : nat -> facts -> continuation -> nat -> loop_state ->
    loop_state **)

let rec unbox_loop_param fuel known k i state =
  match fuel with
  | O -> state
  | S fuel0 -> (
    let p, body = state in
    let p0, handler = p in
    let params, metadata = p0 in
    match
      match nth_error params i with
      | Some param -> (
        match next_read (param :: []) handler with
        | Some r ->
          unbox_loop_read known k params metadata handler body
            { read_variable = r.read_variable;
              read_kind = r.read_kind;
              read_primitive = r.read_primitive;
              read_position = i;
              read_without = r.read_without
            }
        | None -> None)
      | None -> None
    with
    | Some state0 -> unbox_loop_param fuel0 known k i state0
    | None -> state)

(** val reads_var_named : variable -> named -> bool **)

let reads_var_named x = function
  | Prim (p0, args) -> (
    match p0 with
    | Unary p -> (
      match args with
      | [] -> false
      | s :: l -> (
        match s with
        | Var y -> (
          match l with [] -> reads_a_box p && Pos.eqb y x | _ :: _ -> false)
        | _ -> false))
    | _ -> false)
  | _ -> false

(** val reads_var : variable -> expr -> bool **)

let rec reads_var x = function
  | Let (y, _, d, body) ->
    reads_var_named x d || (negb (Pos.eqb y x) && reads_var x body)
  | Let_static (_, body) -> reads_var x body
  | Let_cont_non_recursive (_, h, body) ->
    handler_reads_var x h || reads_var x body
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let _, h = pat in
        handler_reads_var x h)
      handlers
    || reads_var x body
  | _ -> false

(** val handler_reads_var : variable -> continuation_handler -> bool **)

and handler_reads_var x = function
  | Handler (params, _, handler) -> negb (among x params) && reads_var x handler

(** val reads_left : nat -> loop_state -> bool **)

let reads_left i = function
  | p, _ -> (
    let p0, handler = p in
    let params, _ = p0 in
    match nth_error params i with
    | Some param -> reads_var param handler
    | None -> false)

(** val unbox_loop_param_all : nat -> facts -> continuation -> nat -> loop_state
    -> loop_state **)

let unbox_loop_param_all fuel known k i state =
  let unboxed = unbox_loop_param fuel known k i state in
  if reads_left i unboxed then state else unboxed

(** val unbox_loop_params : nat -> facts -> continuation -> nat list ->
    loop_state -> loop_state **)

let rec unbox_loop_params fuel known k positions state =
  match positions with
  | [] -> state
  | i :: positions0 ->
    unbox_loop_params fuel known k positions0
      (unbox_loop_param_all fuel known k i state)

(** val unbox_loop_reads : facts -> continuation -> variable list ->
    handler_metadata -> expr -> expr -> expr **)

let unbox_loop_reads known k params metadata handler body =
  loop_of k
    (unbox_loop_params (lets_in handler) known k
       (seq O (length params))
       (((params, metadata), handler), body))

(** val unbox_loops_knowing : facts -> expr -> expr **)

let rec unbox_loops_knowing known e =
  match e with
  | Let (x, kind, d, body) ->
    Let (x, kind, d, unbox_loops_knowing (facts_under_let known x d) body)
  | Let_static (bindings, body) ->
    Let_static
      (bindings, unbox_loops_knowing (facts_under_statics known bindings) body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler
          ( params,
            metadata,
            unbox_loops_knowing (facts_under_params known params) handler ),
        unbox_loops_knowing known body )
  | Let_cont_recursive (handlers, body) -> (
    match handlers with
    | [] -> Let_cont_recursive (handlers, unbox_loops_knowing known body)
    | p :: l -> (
      let k, c = p in
      let (Handler (params, metadata, handler)) = c in
      match l with
      | [] ->
        unbox_loop_reads known k params metadata handler
          (unbox_loops_knowing known body)
      | _ :: _ -> Let_cont_recursive (handlers, unbox_loops_knowing known body))
    )
  | _ -> e
