open Datatypes
open FlambdaAliasesSpec
open FlambdaBlockLoadSpec
open FlambdaCodeLetsSpec
open FlambdaCompareSpec
open FlambdaCseSpec
open FlambdaDeadParamsSpec
open FlambdaFloatCodeSpec
open FlambdaForwardSpec
open FlambdaHoistCodeSpec
open FlambdaIdentitiesSpec
open FlambdaInlineSiblingsSpec
open FlambdaInlineTailSpec
open FlambdaKnownClosuresSpec
open FlambdaKnownSymbolsSpec
open FlambdaLiftFromCodeSpec
open FlambdaLiftSpec
open FlambdaLoopAliasesSpec
open FlambdaLoopLetsSpec
open FlambdaLoopifySpec
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
open FlambdaWellFormedSpec
open List

val iterate : nat -> (expr -> expr) -> expr -> expr

val normalise_expr_before : expr -> expr

val normalise_code_before : expr -> expr

val normalise_before_inlined : expr -> expr

val normalise_before_round_avoiding :
  continuation list -> code_id list -> expr -> expr

val normalise_before_round : code_id list -> expr -> expr

val normalise_expr_params : expr -> expr

val normalise_code_params : expr -> expr

val normalise_params_round : expr -> expr

val normalise_before : nat -> code_id list -> expr -> expr

val inline_once_applied_after : expr -> expr

val normalise_expr_after : expr -> expr

val normalise_code_after : expr -> expr

val normalise_after_round : code_id list -> expr -> expr

val normalise_after : nat -> code_id list -> expr -> expr

val without_statics : dropped -> expr -> expr

val with_lifting : lifting -> expr -> expr

val with_known : expr -> expr

val normalise_lifted_round : continuation list -> code_id list -> expr -> expr

val normalise_lifted : nat -> continuation list -> code_id list -> expr -> expr

val unit_continuations : lifting list -> continuation list

val lifted_in_turn :
  nat -> continuation list -> lifting list -> code_id list -> expr -> expr

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
  loopified ->
  lifting list ->
  code_id list ->
  expr ->
  expr ->
  validation
