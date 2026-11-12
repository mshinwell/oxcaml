open Datatypes
open FlambdaAliasesSpec
open FlambdaBlockLoadSpec
open FlambdaCompareSpec
open FlambdaCseSpec
open FlambdaFloatCodeSpec
open FlambdaForwardSpec
open FlambdaHoistCodeSpec
open FlambdaIdentitiesSpec
open FlambdaInlineSiblingsSpec
open FlambdaKnownClosuresSpec
open FlambdaKnownSymbolsSpec
open FlambdaLiftSpec
open FlambdaLoopAliasesSpec
open FlambdaLoopLetsSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaParamAliasesSpec
open FlambdaRecHandlersSpec
open FlambdaRenameApartSpec
open FlambdaShortcutSpec
open FlambdaSinkContsSpec
open FlambdaStaticsOrderSpec
open FlambdaUnboxSpec
open FlambdaUnusedContsSpec
open FlambdaUnusedParamsSpec
open FlambdaUnusedProjectionsSpec
open FlambdaUnusedSlotsSpec
open FlambdaUnusedStaticsSpec

val iterate : nat -> (expr -> expr) -> expr -> expr

val normalise_expr_before : expr -> expr

val normalise_code_before : expr -> expr

val normalise_before_inlined : expr -> expr

val normalise_before_round : code_id list -> expr -> expr

val normalise_expr_params : expr -> expr

val normalise_code_params : expr -> expr

val normalise_params_round : expr -> expr

val normalise_before : nat -> code_id list -> expr -> expr

val normalise_expr_after : expr -> expr

val normalise_code_after : expr -> expr

val normalise_after_round : code_id list -> expr -> expr

val normalise_after : nat -> code_id list -> expr -> expr

val without_statics : dropped -> expr -> expr

val with_lifting : lifting -> expr -> expr

val with_known : expr -> expr

val normalise_lifted_round : code_id list -> expr -> expr

val normalise_lifted : nat -> code_id list -> expr -> expr

val lifted_in_turn : nat -> lifting list -> code_id list -> expr -> expr

val without_slots : value_slot list -> expr -> expr

val with_code_first : expr -> expr

type validation =
  | Same_up_to_bound_names
  | Same_once_normalised
  | Same_once_unused_statics_removed
  | Same_once_lifted
  | Not_validated

val validate_unit :
  nat ->
  dropped ->
  value_slot list ->
  lifting list ->
  code_id list ->
  expr ->
  expr ->
  validation
