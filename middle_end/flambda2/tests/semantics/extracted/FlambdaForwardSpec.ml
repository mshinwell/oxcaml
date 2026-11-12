open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaParamAliasesSpec
open List
open ListDef
open PeanoNat

(** val binds_cont : continuation -> expr -> bool **)

let rec binds_cont k = function
  | Let (_, _, _, body) -> binds_cont k body
  | Let_static (_, body) -> binds_cont k body
  | Let_cont_non_recursive (k', h, body) ->
    (Pos.eqb k k' || binds_cont_in_handler k h) || binds_cont k body
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let k', h = pat in
        Pos.eqb k k' || binds_cont_in_handler k h)
      handlers
    || binds_cont k body
  | _ -> false

(** val binds_cont_in_handler : continuation -> continuation_handler -> bool **)

and binds_cont_in_handler k = function
  | Handler (_, _, handler) -> binds_cont k handler

(** val subst_simple : variable list -> simple list -> simple -> simple **)

let subst_simple params args s =
  match s with
  | Var x -> (
    match lookup x (combine params args) with Some arg -> arg | None -> s)
  | _ -> s

(** val forwarded : variable list -> simple list -> apply_cont -> apply_cont **)

let forwarded params args target =
  { ac_continuation = target.ac_continuation;
    ac_args = map (subst_simple params args) target.ac_args;
    ac_trap_action = target.ac_trap_action
  }

type forwards = (continuation * (variable list * apply_cont) option) list

(** val forward_of : forwards -> continuation -> (variable list * apply_cont)
    option **)

let forward_of f k = match lookup k f with Some entry -> entry | None -> None

(** val forward_apply_cont : forwards -> apply_cont -> apply_cont **)

let forward_apply_cont f ac =
  match forward_of f ac.ac_continuation with
  | Some p ->
    let params, target = p in
    if
      (Nat.eqb (length ac.ac_args) (length params) && no_trap_action ac)
      && no_trap_action target
    then forwarded params ac.ac_args target
    else ac
  | None -> ac

(** val forward_arm : forwards -> apply_cont -> apply_cont **)

let forward_arm f ac =
  match forward_of f ac.ac_continuation with
  | Some p -> (
    let l, target = p in
    match l with
    | [] -> (
      match ac.ac_args with
      | [] -> if no_trap_action ac then forwarded [] [] target else ac
      | _ :: _ -> forward_apply_cont f ac)
    | _ :: _ -> forward_apply_cont f ac)
  | None -> forward_apply_cont f ac

(** val forwarding : continuation -> variable list -> handler_metadata -> expr
    -> expr -> (variable list * apply_cont) option **)

let forwarding k params metadata handler body =
  match handler with
  | Apply_cont target ->
    if
      (((metadata.hm_is_exn_handler || among k (apply_cont_continuations target))
       || negb (distinct params))
      || existsb (fun j -> binds_cont j body) (apply_cont_continuations target)
      )
      || existsb
           (fun s ->
             match s with
             | Var x -> negb (among x params) && binds_var x body
             | _ -> false)
           target.ac_args
    then None
    else Some (params, target)
  | _ -> None

(** val given_one_inner_variable : continuation -> variable list -> expr -> bool
    **)

let given_one_inner_variable k params body =
  match some_args k body with
  | Some args ->
    existsb
      (fun i ->
        match nth_error args i with
        | Some s -> (
          match s with
          | Var x ->
            binds_var x body
            && always_given k i (fun arg -> simple_eqb arg (Var x)) body
          | _ -> false)
        | None -> false)
      (seq O (length params))
  | None -> false

(** val forward_entry : continuation -> variable list -> handler_metadata ->
    expr -> expr -> (variable list * apply_cont) option **)

let forward_entry k params metadata handler body =
  if given_one_inner_variable k params body
  then None
  else forwarding k params metadata handler body

(** val forward_applications_under : forwards -> expr -> expr **)

let rec forward_applications_under f e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, forward_applications_under f body)
  | Let_static (bindings, body) ->
    Let_static (bindings, forward_applications_under f body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    let handler1 = forward_applications_under f handler in
    Let_cont_non_recursive
      ( k,
        Handler (params, metadata, handler1),
        forward_applications_under
          ((k, forward_entry k params metadata handler1 body) :: f)
          body )
  | Let_cont_recursive (handlers, body) ->
    let f0 =
      app
        (map
           (fun pat ->
             let k, _ = pat in
             k, None)
           handlers)
        f
    in
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, forward_applications_in_handler f0 h)
          handlers,
        forward_applications_under f0 body )
  | Apply_cont ac -> Apply_cont (forward_apply_cont f ac)
  | Switch (scrutinee, arms) ->
    Switch (scrutinee, map (fun arm -> fst arm, forward_arm f (snd arm)) arms)
  | _ -> e

(** val forward_applications_in_handler : forwards -> continuation_handler ->
    continuation_handler **)

and forward_applications_in_handler f = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, forward_applications_under f handler)

(** val forward_applications : expr -> expr **)

let forward_applications e = forward_applications_under [] e
