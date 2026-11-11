open FlambdaKindModel

type signedness =
  | Signed
  | Unsigned

type unary_primitive =
  | Is_int of bool
  | Is_null
  | Get_tag
  | Opaque_identity of flambda_kind
  | Untag_immediate
  | Tag_immediate

type binary_int_arith_op =
  | Add
  | Sub
  | Mul
  | Div of signedness
  | Mod of signedness
  | And
  | Or
  | Xor

type int_comparison =
  | Int_eq
  | Int_neq
  | Int_lt of signedness
  | Int_gt of signedness
  | Int_le of signedness
  | Int_ge of signedness

type int_comparison_behaviour =
  | Yielding_bool of int_comparison
  | Yielding_int_like_compare_functions of signedness

type binary_primitive =
  | Int_arith of standard_int * binary_int_arith_op
  | Int_comp of standard_int * int_comparison_behaviour

type prim =
  | Unary of unary_primitive
  | Binary of binary_primitive
