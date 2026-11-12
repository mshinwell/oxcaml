open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List
open ListDef

type merge_by =
  | By_tagging
  | By_tagging_and_negating

(** val constant_of_arm : merge_by -> coq_Z -> const option **)

let constant_of_arm how i =
  match how with
  | By_tagging ->
    if in_range (int_width Standard_naked_immediate) i
    then Some (Tagged_immediate i)
    else None
  | By_tagging_and_negating ->
    if Z.eqb i Z0
    then Some (Tagged_immediate (Zpos Coq_xH))
    else if Z.eqb i (Zpos Coq_xH)
    then Some (Tagged_immediate Z0)
    else None

(** val merged_arguments : variable -> simple list -> simple list -> simple list
    **)

let rec merged_arguments v args args' =
  match args with
  | [] -> []
  | s :: args0 -> (
    match args' with
    | [] -> []
    | s' :: args'0 ->
      (if simple_eq_dec s s' then s else Var v)
      :: merged_arguments v args0 args'0)

(** val constant_for : variable -> const -> simple -> simple **)

let constant_for v c s =
  match s with Var x -> if Pos.eqb x v then Const c else s | _ -> s

(** val arm_is_merged : merge_by -> variable -> apply_cont -> (coq_Z *
    apply_cont) -> bool **)

let arm_is_merged how v merged arm =
  match constant_of_arm how (fst arm) with
  | Some c ->
    if
      apply_cont_eq_dec (snd arm)
        { ac_continuation = merged.ac_continuation;
          ac_args = map (constant_for v c) merged.ac_args;
          ac_trap_action = merged.ac_trap_action
        }
    then true
    else false
  | None -> false

(** val bind_tagged : variable -> expr -> expr **)

let bind_tagged v body =
  Let (v, Value, Prim (Unary Tag_immediate, Var v :: []), body)

(** val bind_negated : variable -> expr -> expr **)

let bind_negated v body =
  Let (v, Value, Prim (Unary Boolean_not, Var v :: []), body)

(** val merge_switch : simple -> (coq_Z * apply_cont) list -> expr **)

let merge_switch scrutinee arms =
  match scrutinee with
  | Var v -> (
    match arms with
    | [] -> Switch (scrutinee, arms)
    | p :: l -> (
      let _, ac = p in
      match l with
      | [] -> Switch (scrutinee, arms)
      | p0 :: _ ->
        let _, ac' = p0 in
        let merged =
          { ac_continuation = ac.ac_continuation;
            ac_args = merged_arguments v ac.ac_args ac'.ac_args;
            ac_trap_action = None
          }
        in
        if var_in_simples v merged.ac_args
        then
          if forallb (arm_is_merged By_tagging v merged) arms
          then bind_tagged v (Apply_cont merged)
          else if forallb (arm_is_merged By_tagging_and_negating v merged) arms
          then bind_tagged v (bind_negated v (Apply_cont merged))
          else Switch (scrutinee, arms)
        else Switch (scrutinee, arms)))
  | _ -> Switch (scrutinee, arms)

(** val merge_switches : expr -> expr **)

let rec merge_switches e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, merge_switches body)
  | Let_static (bindings, body) -> Let_static (bindings, merge_switches body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler (params, metadata, merge_switches handler),
        merge_switches body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, merge_switches body)
  | Switch (scrutinee, arms) -> merge_switch scrutinee arms
  | _ -> e
