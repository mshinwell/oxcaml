open BinInt
open BinNums
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaPrimitiveModel
open FlambdaValueSpec
open OxCamlOption

val in_range : coq_Z -> coq_Z -> bool

val wrap : coq_Z -> coq_Z -> coq_Z

val unsigned : coq_Z -> coq_Z -> coq_Z

val reading : coq_Z -> signedness -> coq_Z -> coq_Z

val int_width : standard_int -> coq_Z

val const_of_int : standard_int -> coq_Z -> const

val int_of_value : standard_int -> value -> coq_Z option

val eval_int_arith :
  coq_Z -> binary_int_arith_op -> coq_Z -> coq_Z -> coq_Z option

val eval_int_comparison : coq_Z -> int_comparison -> coq_Z -> coq_Z -> bool

val eval_int_comp : coq_Z -> int_comparison_behaviour -> coq_Z -> coq_Z -> coq_Z

val naked_bool : bool -> value

val is_tagged_immediate : value -> bool

val eval_is_int : static_env -> bool -> value -> bool option

val eval_is_null : static_env -> value -> bool option

val eval_unary_primitive :
  static_env -> unary_primitive -> value -> value option

val eval_binary_primitive : binary_primitive -> value -> value -> value option

val eval_prim : static_env -> prim -> value list -> value option

val prim_eq_dec : prim -> prim -> bool

val prim_eqb : prim -> prim -> bool
