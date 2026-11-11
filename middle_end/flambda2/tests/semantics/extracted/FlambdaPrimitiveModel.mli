open BinNums
open FlambdaKindModel

type signedness =
  | Signed
  | Unsigned

type block_access_field_kind =
  | Any_value
  | Immediate

type block_access_kind =
  | Block_access_values of coq_Z option * coq_Z option * block_access_field_kind

type unary_primitive =
  | Block_load of block_access_kind * coq_Z
  | Is_int of bool
  | Is_null
  | Get_tag
  | Opaque_identity of flambda_kind
  | Unbox_number of boxable_number
  | Box_number of boxable_number
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

type block_kind = Block_kind_values of coq_Z

type variadic_primitive = Make_block of block_kind

type prim =
  | Unary of unary_primitive
  | Binary of binary_primitive
  | Variadic of variadic_primitive
