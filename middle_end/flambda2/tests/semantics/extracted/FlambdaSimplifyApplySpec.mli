open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaValueSpec
open List

val closure_of_set_type :
  function_slot ->
  (function_slot * code_id) list ->
  value_slot list ->
  flambda_type list ->
  flambda_type

val set_of_closures_type :
  code_id -> value_slot list -> flambda_type list -> flambda_type
