open BinNums
open FlambdaModel
open FlambdaSemanticsSpec
open FlambdaTypeGrammar
open FlambdaValueSpec

val number_of_const : const -> coq_Z option

val value_of_name : env -> name -> value option

val closures_index_contents :
  (set_of_closures_contents, unit) row_like_index -> set_of_closures_contents
