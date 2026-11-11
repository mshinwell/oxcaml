open Datatypes
open FlambdaAliasesSpec
open FlambdaBlockLoadSpec
open FlambdaCompareSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnboxSpec
open FlambdaUnusedContsSpec
open FlambdaUnusedStaticsSpec

val iterate : nat -> (expr -> expr) -> expr -> expr

val normalise_code_before : expr -> expr

val normalise_before_round : expr -> expr

val normalise_before : nat -> expr -> expr

val normalise_code_after : expr -> expr

val normalise_after_round : expr -> expr

val normalise_after : nat -> expr -> expr

val without_statics : dropped -> expr -> expr

type validation =
  | Same_up_to_bound_names
  | Same_once_normalised
  | Same_once_unused_statics_removed
  | Not_validated

val validate_unit : nat -> dropped -> expr -> expr -> validation
