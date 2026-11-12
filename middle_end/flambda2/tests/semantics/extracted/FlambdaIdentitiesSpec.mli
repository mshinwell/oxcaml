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

val symmetric_op_one_side_unknown : binary_int_arith_op -> coq_Z -> outcome

val is_signed : signedness -> bool

val op_lhs_unknown : binary_int_arith_op -> coq_Z -> outcome

val op_rhs_unknown : binary_int_arith_op -> coq_Z -> outcome

val shift_lhs_unknown : int_shift_op -> coq_Z -> outcome

val shift_rhs_unknown : int_shift_op -> coq_Z -> outcome

val int_of_simple : standard_int -> simple -> coq_Z option

val is_const : simple -> bool

val named_of_outcome : standard_int -> outcome -> simple -> named option

val same_value_const : equality_comparison -> const

val identity_of_binary : binary_primitive -> simple -> simple -> named option

val binary_applied :
  prim -> simple list -> ((binary_primitive * simple) * simple) option

val identity_named : named -> named

val apply_identities : expr -> expr

val apply_identities_in_handler : continuation_handler -> continuation_handler
