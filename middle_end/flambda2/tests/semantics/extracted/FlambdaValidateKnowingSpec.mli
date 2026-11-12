open Datatypes
open FlambdaEnvAliasesFollowSpec
open FlambdaLiftSpec
open FlambdaLoopifySpec
open FlambdaModel
open FlambdaUnusedStaticsSpec
open FlambdaValidateSpec
open ListDef

val knowing_round : (expr -> expr) -> expr -> expr

val normalise_knowing : (expr -> expr) -> nat -> expr -> expr

val validate_unit_knowing :
  nat ->
  dropped ->
  value_slot list ->
  loopified ->
  lifting list ->
  code_id list ->
  expr ->
  expr ->
  validation
