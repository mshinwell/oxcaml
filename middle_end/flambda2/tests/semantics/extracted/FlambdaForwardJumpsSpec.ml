open Datatypes
open FlambdaForwardSpec
open FlambdaModel
open ListDef

(** val jump_entry : continuation -> variable list -> handler_metadata -> expr
    -> expr -> (variable list * apply_cont) option **)

let jump_entry k params metadata handler body =
  match params with
  | [] -> (
    match metadata.hm_params_kinds with
    | [] -> forwarding k [] metadata handler body
    | _ :: _ -> None)
  | _ :: _ -> None

(** val forward_jumps_under : forwards -> expr -> expr **)

let rec forward_jumps_under f e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, forward_jumps_under f body)
  | Let_static (bindings, body) ->
    Let_static (bindings, forward_jumps_under f body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    let handler1 = forward_jumps_under f handler in
    Let_cont_non_recursive
      ( k,
        Handler (params, metadata, handler1),
        forward_jumps_under
          ((k, jump_entry k params metadata handler1 body) :: f)
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
            k, forward_jumps_in_handler f0 h)
          handlers,
        forward_jumps_under f0 body )
  | Apply_cont ac -> Apply_cont (forward_apply_cont f ac)
  | Switch (scrutinee, arms) ->
    Switch
      (scrutinee, map (fun arm -> fst arm, forward_apply_cont f (snd arm)) arms)
  | _ -> e

(** val forward_jumps_in_handler : forwards -> continuation_handler ->
    continuation_handler **)

and forward_jumps_in_handler f = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, forward_jumps_under f handler)

(** val forward_jumps : expr -> expr **)

let forward_jumps e = forward_jumps_under [] e
