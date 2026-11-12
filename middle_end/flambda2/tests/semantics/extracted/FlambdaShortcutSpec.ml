open BinNums
open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open ListDef

(** val shortcut_arm : continuation -> apply_cont -> (coq_Z * apply_cont) ->
    coq_Z * apply_cont **)

let shortcut_arm k target arm =
  match (snd arm).ac_args with
  | [] ->
    if Pos.eqb (snd arm).ac_continuation k && no_trap_action (snd arm)
    then fst arm, target
    else arm
  | _ :: _ -> arm

(** val shortcut_switch : continuation -> continuation_handler -> expr -> expr **)

let shortcut_switch k h body =
  let (Handler (params, metadata, handler)) = h in
  match params with
  | [] -> (
    match handler with
    | Apply_cont target -> (
      match body with
      | Switch (scrutinee, arms) ->
        if
          (Pos.eqb target.ac_continuation k || metadata.hm_is_exn_handler)
          || negb (no_trap_action target)
        then Let_cont_non_recursive (k, h, body)
        else
          let arms0 = map (shortcut_arm k target) arms in
          if arms_apply k arms0
          then Let_cont_non_recursive (k, h, Switch (scrutinee, arms0))
          else Switch (scrutinee, arms0)
      | _ -> Let_cont_non_recursive (k, h, body))
    | _ -> Let_cont_non_recursive (k, h, body))
  | _ :: _ -> Let_cont_non_recursive (k, h, body)

(** val shortcut_switches : expr -> expr **)

let rec shortcut_switches e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, shortcut_switches body)
  | Let_static (bindings, body) -> Let_static (bindings, shortcut_switches body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    shortcut_switch k
      (Handler (params, metadata, shortcut_switches handler))
      (shortcut_switches body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, shortcut_switches body)
  | _ -> e
