open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedParamsSpec
open List
open ListDef
open PeanoNat

(** val simple_eqb : simple -> simple -> bool **)

let simple_eqb s s' = if simple_eq_dec s s' then true else false

(** val binds_var : variable -> expr -> bool **)

let rec binds_var x = function
  | Let (y, _, _, body) -> Pos.eqb x y || binds_var x body
  | Let_static (_, body) -> binds_var x body
  | Let_cont_non_recursive (_, h, body) ->
    binds_var_in_handler x h || binds_var x body
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let _, h = pat in
        binds_var_in_handler x h)
      handlers
    || binds_var x body
  | _ -> false

(** val binds_var_in_handler : variable -> continuation_handler -> bool **)

and binds_var_in_handler x = function
  | Handler (params, _, handler) -> among x params || binds_var x handler

(** val stable : simple -> expr -> bool **)

let stable s e = match s with Var x -> negb (binds_var x e) | _ -> true

(** val args_if_applies : continuation -> apply_cont -> simple list option **)

let args_if_applies k ac =
  if Pos.eqb ac.ac_continuation k then Some ac.ac_args else None

(** val first_some : 'a1 option -> 'a1 option -> 'a1 option **)

let first_some a b = match a with Some _ -> a | None -> b

(** val some_args : continuation -> expr -> simple list option **)

let rec some_args k = function
  | Let (_, _, _, body) -> some_args k body
  | Let_static (_, body) -> some_args k body
  | Let_cont_non_recursive (_, h, body) ->
    first_some (some_args k body) (some_args_in_handler k h)
  | Let_cont_recursive (handlers, body) ->
    first_some (some_args k body)
      (fold_right
         (fun pat found ->
           let _, h = pat in
           first_some (some_args_in_handler k h) found)
         None handlers)
  | Apply_cont ac -> args_if_applies k ac
  | Switch (_, arms) ->
    fold_right
      (fun arm found -> first_some (args_if_applies k (snd arm)) found)
      None arms
  | _ -> None

(** val some_args_in_handler : continuation -> continuation_handler -> simple
    list option **)

and some_args_in_handler k = function
  | Handler (_, _, handler) -> some_args k handler

(** val given : continuation -> nat -> (simple -> bool) -> apply_cont -> bool **)

let given k i ok ac =
  negb (Pos.eqb ac.ac_continuation k)
  || match nth_error ac.ac_args i with Some arg -> ok arg | None -> false

(** val always_given : continuation -> nat -> (simple -> bool) -> expr -> bool **)

let rec always_given k i ok = function
  | Let (_, _, _, body) -> always_given k i ok body
  | Let_static (_, body) -> always_given k i ok body
  | Let_cont_non_recursive (_, h, body) ->
    always_given_in_handler k i ok h && always_given k i ok body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        always_given_in_handler k i ok h)
      handlers
    && always_given k i ok body
  | Apply_cont ac -> given k i ok ac
  | Switch (_, arms) -> forallb (fun arm -> given k i ok (snd arm)) arms
  | _ -> true

(** val always_given_in_handler : continuation -> nat -> (simple -> bool) ->
    continuation_handler -> bool **)

and always_given_in_handler k i ok = function
  | Handler (_, _, handler) -> always_given k i ok handler

(** val aliases_from : nat -> variable list -> (nat -> variable -> simple
    option) -> simple option list **)

let rec aliases_from i params alias_at =
  match params with
  | [] -> []
  | param :: params0 -> alias_at i param :: aliases_from (S i) params0 alias_at

(** val aliases_of : continuation -> variable list -> handler_metadata -> expr
    option -> expr -> expr -> simple option list **)

let aliases_of k params metadata loop body whole =
  if
    ((returned_to k whole || metadata.hm_is_exn_handler)
    || negb (distinct params))
    || negb (Nat.eqb (length metadata.hm_params_kinds) (length params))
  then []
  else
    match some_args k body with
    | Some args ->
      aliases_from O params (fun i param ->
          match nth_error args i with
          | Some s ->
            if
              (stable s whole
              && always_given k i (fun arg -> simple_eqb arg s) body)
              &&
              match loop with
              | Some handler ->
                always_given k i
                  (fun arg -> simple_eqb arg s || simple_eqb arg (Var param))
                  handler
                && negb (binds_var param handler)
              | None -> true
            then Some s
            else None
          | None -> None)
    | None -> []

(** val bind_aliases : variable list -> flambda_kind list -> simple option list
    -> expr -> expr **)

let rec bind_aliases params kinds aliases handler =
  match params with
  | [] -> handler
  | param :: params0 -> (
    match kinds with
    | [] -> handler
    | kind :: kinds0 -> (
      match aliases with
      | [] -> handler
      | alias :: aliases0 -> (
        let handler0 = bind_aliases params0 kinds0 aliases0 handler in
        match alias with
        | Some s -> Let (param, kind, Simple s, handler0)
        | None -> handler0)))

(** val alone : 'a1 list -> bool **)

let alone = function
  | [] -> false
  | _ :: l0 -> ( match l0 with [] -> true | _ :: _ -> false)

(** val bind_aliased_params : expr -> expr **)

let rec bind_aliased_params e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, bind_aliased_params body)
  | Let_static (bindings, body) ->
    Let_static (bindings, bind_aliased_params body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler
          ( params,
            metadata,
            bind_aliases params metadata.hm_params_kinds
              (aliases_of k params metadata None body e)
              (bind_aliased_params handler) ),
        bind_aliased_params body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, bind_aliased_params_in_loop (alone handlers) k body e h)
          handlers,
        bind_aliased_params body )
  | _ -> e

(** val bind_aliased_params_in_loop : bool -> continuation -> expr -> expr ->
    continuation_handler -> continuation_handler **)

and bind_aliased_params_in_loop alone0 k body whole = function
  | Handler (params, metadata, handler) ->
    let aliases =
      if alone0
      then aliases_of k params metadata (Some handler) body whole
      else []
    in
    Handler
      ( params,
        metadata,
        bind_aliases params metadata.hm_params_kinds aliases
          (bind_aliased_params handler) )
