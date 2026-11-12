open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaProvers
open FlambdaSimplifyPrimitivesSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv
open FlambdaValueSpec
open List
open ListDef

val with_call_kind : apply_expr -> call_kind -> apply_expr

val with_callee_and_args : apply_expr -> simple -> simple list -> apply_expr

val direct_call_kind : Typing_env.t -> apply_expr -> call_kind

val canonical_apply : Typing_env.t -> apply_expr -> apply_expr

val simplify_apply : Typing_env.t -> apply_expr -> expr

val closure_of_set_type :
  function_slot ->
  (function_slot * code_id) list ->
  value_slot list ->
  flambda_type list ->
  flambda_type

val set_of_closures_type :
  code_id -> value_slot list -> flambda_type list -> flambda_type
