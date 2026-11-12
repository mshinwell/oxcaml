open BinInt
open BinPos
open Datatypes
open FlambdaBindingTime
open FlambdaEnvAliases
open FlambdaEnvAliasesInvariantSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypeWellFormedSpec
open FlambdaTypingEnv
open List
open ListDef

val binding_time_of :
  flambda_type * Binding_time.With_name_mode.t -> Binding_time.t

val binding_times_bounded_b : Typing_env.t -> bool

val binding_times_in_range_b : Typing_env.t -> bool

val binding_times_distinct_b : Typing_env.t -> bool

val types_closed_b : Typing_env.t -> bool

val symbols_recorded_b : Typing_env.t -> bool

val symbols_defined_b : Typing_env.t -> bool

val all_levels : Typing_env.t -> Typing_env_level.t list

val all_scopes : Typing_env.t -> Scope.t list

val levels_disjoint_b : Typing_env_level.t -> Typing_env_level.t -> bool

val levels_pairwise_disjoint_b : Typing_env_level.t list -> bool

val defined_variables_bound_b : Typing_env.t -> bool

val indexed_at_b : Typing_env_level.t -> Binding_time.t -> variable -> bool

val level_indexed_b : Typing_env_level.t -> bool

val levels_indexed_b : Typing_env.t -> bool

val level_binding_times_recorded_b : Typing_env.t -> bool

val level_binding_times_in_range_b : Typing_env.t -> bool

val scopes_decreasing_b : Scope.t list -> bool

val variables_defined_b : Typing_env.t -> bool

val aliases_known_b : Typing_env.t -> bool

val canonical_names_concrete_b : Typing_env.t -> bool

val typing_env_well_formed : Typing_env.t -> bool

val types_well_formed_b : Typing_env.t -> bool
