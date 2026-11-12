open BinInt
open BinNums
open BinPos
open FlambdaCseSpec
open FlambdaKindModel
open FlambdaModel
open FlambdaPrimitiveModel

val first_known :
  (variable * (prim * simple list) -> 'a1 option) -> computed -> 'a1 option

type comparison = (standard_int * signedness) * simple list

val comparison_held :
  variable -> variable * (prim * simple list) -> comparison option

val tagged_comparison_held :
  computed -> variable -> variable * (prim * simple list) -> comparison option

val compared : computed -> simple -> comparison option

val is_tagged_zero : simple -> bool

val tested : prim -> int_comparison option

val swap_comparison : int_comparison -> int_comparison

val against_zero : signedness -> int_comparison -> int_comparison option

val recover_one_way :
  computed -> simple -> simple -> int_comparison -> named option

val recover_comparison : computed -> named -> named

val recover_comparisons_knowing : computed -> expr -> expr

val recover_comparisons_in_handler :
  computed -> continuation_handler -> continuation_handler

val recover_known_comparisons : expr -> expr
