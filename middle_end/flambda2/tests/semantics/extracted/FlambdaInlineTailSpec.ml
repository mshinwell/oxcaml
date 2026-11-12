open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open PeanoNat

(** val inline_tail_conts_kinded : expr -> expr **)

let rec inline_tail_conts_kinded e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, inline_tail_conts_kinded body)
  | Let_static (bindings, body) ->
    Let_static (bindings, inline_tail_conts_kinded body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    let handler' = inline_tail_conts_kinded handler in
    let body' = inline_tail_conts_kinded body in
    let kept =
      Let_cont_non_recursive (k, Handler (params, metadata, handler'), body')
    in
    if Nat.eqb (length params) (length metadata.hm_params_kinds)
    then
      match inline_cont_at_tail k params metadata handler' body' with
      | Some inlined -> inlined
      | None -> kept
    else kept
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, inline_tail_conts_kinded body)
  | _ -> e
