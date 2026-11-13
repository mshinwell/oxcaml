open BinPos
open Bool
open Datatypes
open FlambdaBindingTime
open FlambdaKindModel
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaSemanticsSpec
open FlambdaSimplifyApplySpec
open FlambdaSimplifyPassSpec
open FlambdaSimplifyPrimitivesSpec
open FlambdaSimplifyPruningSpec
open FlambdaSimplifyStaticsSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv
open FlambdaTypingEnvInvariantSpec
open FlambdaUnusedContsSpec
open List
open ListDef
open PeanoNat

val well_formed_or_known : bool -> Typing_env.t -> bool

val let_step_of : Typing_env.t -> variable -> named -> outcome -> let_step

val outcome_keeps_fit : Typing_env.t -> variable -> outcome -> bool

val simplify_let_carried :
  bool -> Typing_env.t -> variable -> named -> let_step * bool

val declare_variable_carried :
  bool -> Typing_env.t -> variable -> flambda_kind -> Typing_env.t option

val let_env_carried :
  bool ->
  Typing_env.t ->
  variable ->
  flambda_kind ->
  named ->
  (Typing_env.t * bool) option

val define_variables_carried :
  bool -> Typing_env.t -> (variable * flambda_kind) list -> Typing_env.t option

val code_env_in_carried :
  bool ->
  Typing_env.t ->
  variable list ->
  variable ->
  code_metadata ->
  Typing_env.t option

val handler_env_carried :
  bool ->
  Typing_env.t ->
  variable list ->
  handler_metadata ->
  Typing_env.t option

val bind_params_to_args_carried :
  bool ->
  (simple -> bool) ->
  Typing_env.t ->
  ((variable * flambda_kind) * simple) list ->
  (Typing_env.t * bool) option

val use_env_carried :
  bool ->
  Typing_env.t ->
  Typing_env.t ->
  variable list ->
  handler_metadata ->
  simple list ->
  (Typing_env.t * bool) option

val find_use_carried :
  bool ->
  Typing_env.t ->
  Typing_env.t ->
  continuation ->
  continuation_handler ->
  expr ->
  (((Typing_env.t * bool) * variable list) * continuation list) option

val simplify_expr_carried : bool -> Typing_env.t -> expr -> expr

val simplify_handler_carried :
  bool -> bool -> Typing_env.t -> continuation_handler -> continuation_handler

val simplify_static_binding_carried :
  bool -> Typing_env.t -> static_binding -> static_binding

val simplify_code_carried : bool -> Typing_env.t -> code -> code

val simplify_by_types_carried : expr -> expr
