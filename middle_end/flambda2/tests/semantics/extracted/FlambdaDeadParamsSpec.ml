open BinPos
open Bool
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedParamsSpec
open List
open ListDef
open Nat

(** val bools_eqb : bool list -> bool list -> bool **)

let rec bools_eqb l l' =
  match l with
  | [] -> ( match l' with [] -> true | _ :: _ -> false)
  | b :: l0 -> (
    match l' with [] -> false | b' :: l'0 -> eqb b b' && bools_eqb l0 l'0)

(** val mask_eqb : bool list option -> bool list option -> bool **)

let mask_eqb mask mask' =
  match mask with
  | Some mask0 -> (
    match mask' with Some mask'0 -> bools_eqb mask0 mask'0 | None -> false)
  | None -> ( match mask' with Some _ -> false | None -> true)

(** val masks_eqb : masks -> masks -> bool **)

let rec masks_eqb known known' =
  match known with
  | [] -> ( match known' with [] -> true | _ :: _ -> false)
  | p :: known0 -> (
    let k, mask = p in
    match known' with
    | [] -> false
    | p0 :: known'0 ->
      let k', mask' = p0 in
      (Pos.eqb k k' && mask_eqb mask mask') && masks_eqb known0 known'0)

(** val settle : nat -> (masks -> masks) -> masks -> masks option **)

let rec settle fuel next loop =
  match fuel with
  | O -> None
  | S fuel0 ->
    let loop' = next loop in
    if masks_eqb loop' loop then Some loop else settle fuel0 next loop'

(** val count_params : (continuation * continuation_handler) list -> nat **)

let count_params handlers =
  fold_right
    (fun pat n ->
      let _, y0 = pat in
      let (Handler (params, _, _)) = y0 in
      add (length params) n)
    O handlers

(** val drop_dead : masks -> expr -> expr **)

let rec drop_dead known e =
  match e with
  | Let (x, kind, d, body) ->
    let body0 = drop_dead known body in
    if var_free_b x body0 || negb (named_may_go d)
    then Let (x, kind, d, body0)
    else body0
  | Let_static (bindings, body) -> Let_static (bindings, drop_dead known body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    let handler1 = drop_dead known handler in
    let mask =
      if returned_to k body
      then None
      else used_params metadata.hm_is_exn_handler params handler1
    in
    Let_cont_non_recursive
      ( k,
        Handler (keep_all_or mask params, keep_kinds mask metadata, handler1),
        drop_dead ((k, mask) :: known) body )
  | Let_cont_recursive (handlers, body) ->
    let next =
     fun loop ->
      map
        (fun pat ->
          let k, h = pat in
          k, live_params (app loop known) (returned_to k e) h)
        handlers
    in
    let settled =
      settle
        (S (S (count_params handlers)))
        next
        (map
           (fun pat ->
             let k, _ = pat in
             k, Some [])
           handlers)
    in
    let kept =
     fun k -> match settled with Some _ -> returned_to k e | None -> true
    in
    let loop =
      match settled with
      | Some loop -> loop
      | None ->
        map
          (fun pat ->
            let k, _ = pat in
            k, None)
          handlers
    in
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, drop_dead_in_loop (app loop known) (kept k) h)
          handlers,
        drop_dead (app loop known) body )
  | Apply_cont ac -> Apply_cont (drop_args known ac)
  | Switch (scrutinee, arms) ->
    Switch (scrutinee, map (fun arm -> fst arm, drop_args known (snd arm)) arms)
  | _ -> e

(** val live_params : masks -> bool -> continuation_handler -> bool list option
    **)

and live_params inside kept = function
  | Handler (params, metadata, handler) ->
    if kept
    then None
    else
      used_params metadata.hm_is_exn_handler params (drop_dead inside handler)

(** val drop_dead_in_loop : masks -> bool -> continuation_handler ->
    continuation_handler **)

and drop_dead_in_loop inside kept = function
  | Handler (params, metadata, handler) ->
    let handler0 = drop_dead inside handler in
    let mask =
      if kept
      then None
      else used_params metadata.hm_is_exn_handler params handler0
    in
    Handler (keep_all_or mask params, keep_kinds mask metadata, handler0)

(** val drop_dead_params : expr -> expr **)

let drop_dead_params e = drop_dead [] e
