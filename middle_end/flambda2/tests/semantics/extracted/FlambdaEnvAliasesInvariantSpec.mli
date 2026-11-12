open FlambdaBindingTime
open FlambdaCompareSpec
open FlambdaEnvAliases
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open List

val demoted_to_b : Aliases.t -> name -> simple -> bool

val is_canonical_b : Aliases.t -> simple -> bool

val canonical_elements_canonical_b : Aliases.t -> bool

val listed_aliases_demoted_b :
  Aliases.t -> simple -> Aliases.Aliases_of_canonical_element.t -> bool

val aliases_listed_b : Aliases.t -> bool

val aliases_consistent_b : Aliases.t -> bool

val name_modes_recorded_of_b :
  (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
  Aliases.Aliases_of_canonical_element.t ->
  bool

val name_modes_recorded_b :
  (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
  Aliases.t ->
  bool
