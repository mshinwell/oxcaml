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

type mutability =
  | Mutable
  | Immutable
  | Immutable_unique

type unary_int_arith_op = Not

type unary_primitive =
  | Block_load of block_access_kind * mutability * coq_Z
  | Is_int of bool
  | Is_null
  | Get_tag
  | String_length
  | Opaque_identity of flambda_kind
  | Unary_int_arith of standard_int * unary_int_arith_op
  | Num_conv of standard_int * standard_int
  | Boolean_not
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

type int_shift_op =
  | Lsl
  | Lsr
  | Asr

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

type string_accessor_width =
  | Eight
  | Eight_signed

type equality_comparison =
  | Phys_eq
  | Phys_neq

type binary_primitive =
  | String_or_bigstring_load of string_accessor_width
  | Phys_equal of equality_comparison
  | Int_arith of standard_int * binary_int_arith_op
  | Int_shift of standard_int * int_shift_op
  | Int_comp of standard_int * int_comparison_behaviour

type block_kind = Block_kind_values of coq_Z

type variadic_primitive = Make_block of block_kind

type prim =
  | Unary of unary_primitive
  | Binary of binary_primitive
  | Variadic of variadic_primitive
