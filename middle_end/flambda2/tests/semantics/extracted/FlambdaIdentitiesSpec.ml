open BinInt
open BinNums
open BinPos
open FlambdaKindModel
open FlambdaModel
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open FlambdaValueSpec

type outcome =
  | Exactly of coq_Z
  | The_other_side
  | Negation_of_the_other_side
  | Bitwise_not_of_the_other_side
  | Cannot_simplify

(** val symmetric_op_one_side_unknown : binary_int_arith_op -> coq_Z -> outcome
    **)

let symmetric_op_one_side_unknown op this_side =
  match op with
  | Add -> if Z.eqb this_side Z0 then The_other_side else Cannot_simplify
  | Mul ->
    if Z.eqb this_side Z0
    then Exactly Z0
    else if Z.eqb this_side (Zpos Coq_xH)
    then The_other_side
    else if Z.eqb this_side (Zneg Coq_xH)
    then Negation_of_the_other_side
    else Cannot_simplify
  | And ->
    if Z.eqb this_side (Zneg Coq_xH)
    then The_other_side
    else if Z.eqb this_side Z0
    then Exactly Z0
    else Cannot_simplify
  | Or ->
    if Z.eqb this_side (Zneg Coq_xH)
    then Exactly (Zneg Coq_xH)
    else if Z.eqb this_side Z0
    then The_other_side
    else Cannot_simplify
  | Xor ->
    if Z.eqb this_side Z0
    then The_other_side
    else if Z.eqb this_side (Zneg Coq_xH)
    then Bitwise_not_of_the_other_side
    else Cannot_simplify
  | _ -> Cannot_simplify

(** val is_signed : signedness -> bool **)

let is_signed = function Signed -> true | Unsigned -> false

(** val op_lhs_unknown : binary_int_arith_op -> coq_Z -> outcome **)

let op_lhs_unknown op rhs =
  match op with
  | Sub -> if Z.eqb rhs Z0 then The_other_side else Cannot_simplify
  | Div s ->
    if Z.eqb rhs (Zpos Coq_xH)
    then The_other_side
    else if Z.eqb rhs (Zneg Coq_xH) && is_signed s
    then Negation_of_the_other_side
    else Cannot_simplify
  | Mod s ->
    if Z.eqb rhs (Zpos Coq_xH)
    then Exactly Z0
    else if Z.eqb rhs (Zneg Coq_xH) && is_signed s
    then Exactly Z0
    else Cannot_simplify
  | _ -> symmetric_op_one_side_unknown op rhs

(** val op_rhs_unknown : binary_int_arith_op -> coq_Z -> outcome **)

let op_rhs_unknown op lhs =
  match op with
  | Sub -> if Z.eqb lhs Z0 then Negation_of_the_other_side else Cannot_simplify
  | Div _ -> Cannot_simplify
  | Mod _ -> Cannot_simplify
  | _ -> symmetric_op_one_side_unknown op lhs

(** val shift_lhs_unknown : int_shift_op -> coq_Z -> outcome **)

let shift_lhs_unknown _ rhs =
  if Z.eqb rhs Z0 then The_other_side else Cannot_simplify

(** val shift_rhs_unknown : int_shift_op -> coq_Z -> outcome **)

let shift_rhs_unknown op lhs =
  match op with
  | Asr ->
    if Z.eqb lhs Z0
    then Exactly Z0
    else if Z.eqb lhs (Zneg Coq_xH)
    then Exactly (Zneg Coq_xH)
    else Cannot_simplify
  | _ -> if Z.eqb lhs Z0 then Exactly Z0 else Cannot_simplify

(** val int_of_simple : standard_int -> simple -> coq_Z option **)

let int_of_simple kind = function
  | Const c -> int_of_value kind (Value_const c)
  | _ -> None

(** val is_const : simple -> bool **)

let is_const = function Const _ -> true | _ -> false

(** val named_of_outcome : standard_int -> outcome -> simple -> named option **)

let named_of_outcome kind o other =
  match o with
  | Exactly i -> Some (Simple (Const (const_of_int kind i)))
  | The_other_side -> Some (Simple other)
  | Negation_of_the_other_side ->
    Some
      (Prim
         (Binary (Int_arith (kind, Sub)), [Const (const_of_int kind Z0); other]))
  | Bitwise_not_of_the_other_side ->
    Some (Prim (Unary (Unary_int_arith (kind, Not)), other :: []))
  | Cannot_simplify -> None

(** val same_value_const : equality_comparison -> const **)

let same_value_const op =
  Naked_immediate (match op with Phys_eq -> Zpos Coq_xH | Phys_neq -> Z0)

(** val identity_of_binary : binary_primitive -> simple -> simple -> named
    option **)

let identity_of_binary p arg1 arg2 =
  match p with
  | Phys_equal op -> (
    match arg1 with
    | Var x -> (
      match arg2 with
      | Var y ->
        if Pos.eqb x y
        then Some (Simple (Const (same_value_const op)))
        else None
      | _ -> None)
    | _ -> None)
  | Int_arith (kind, op) -> (
    match int_of_simple kind arg1 with
    | Some lhs -> (
      match int_of_simple kind arg2 with
      | Some _ -> None
      | None ->
        if is_const arg2
        then None
        else named_of_outcome kind (op_rhs_unknown op lhs) arg2)
    | None -> (
      match int_of_simple kind arg2 with
      | Some rhs ->
        if is_const arg1
        then None
        else named_of_outcome kind (op_lhs_unknown op rhs) arg1
      | None -> None))
  | Int_shift (kind, op) -> (
    match int_of_simple kind arg1 with
    | Some lhs -> (
      match int_of_simple Standard_naked_immediate arg2 with
      | Some _ -> None
      | None ->
        if is_const arg2
        then None
        else named_of_outcome kind (shift_rhs_unknown op lhs) arg2)
    | None -> (
      match int_of_simple Standard_naked_immediate arg2 with
      | Some rhs ->
        if is_const arg1
        then None
        else named_of_outcome kind (shift_lhs_unknown op rhs) arg1
      | None -> None))
  | _ -> None

(** val binary_applied : prim -> simple list -> ((binary_primitive * simple) *
    simple) option **)

let binary_applied p args =
  match p with
  | Binary p0 -> (
    match args with
    | [] -> None
    | arg1 :: l -> (
      match l with
      | [] -> None
      | arg2 :: l0 -> (
        match l0 with [] -> Some ((p0, arg1), arg2) | _ :: _ -> None)))
  | _ -> None

(** val identity_named : named -> named **)

let identity_named d =
  match d with
  | Prim (p, args) -> (
    match binary_applied p args with
    | Some p0 -> (
      let p1, arg2 = p0 in
      let p2, arg1 = p1 in
      match identity_of_binary p2 arg1 arg2 with Some d' -> d' | None -> d)
    | None -> d)
  | _ -> d

(** val apply_identities : expr -> expr **)

let rec apply_identities e =
  match e with
  | Let (x, kind, d, body) ->
    Let (x, kind, identity_named d, apply_identities body)
  | Let_static (bindings, body) -> Let_static (bindings, apply_identities body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, apply_identities_in_handler h, apply_identities body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, apply_identities body)
  | _ -> e

(** val apply_identities_in_handler : continuation_handler ->
    continuation_handler **)

and apply_identities_in_handler = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, apply_identities handler)
