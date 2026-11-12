open Datatypes
open FlambdaBindingTime
open FlambdaEnvAliases
open FlambdaExpandHead
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaMeetGrammar
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv

type 'a meet_return_value =
  | Left_input
  | Right_input
  | Both_inputs
  | New_result of 'a

val extract_value : 'a1 meet_return_value -> 'a1 -> 'a1 -> 'a1

module Meet_env_type : sig
  type t =
    { typing_env : Typing_env.t;
      adding_equations_for_names : name list;
      names_to_avoid : variable list
    }
end

module Meet_result : sig
  type 'a t =
    | Bottom of unit meet_return_value
    | Ok of 'a meet_return_value * Meet_env_type.t
end

type meet_expanded_head =
  Meet_env_type.t ->
  Expanded_type.t ->
  Expanded_type.t ->
  Expanded_type.t Meet_result.t option

val map_result : ('a1 -> 'a2) -> 'a1 Meet_result.t -> 'a2 Meet_result.t

module Meet_env : sig
  type t = Meet_env_type.t =
    { typing_env : Typing_env.t;
      adding_equations_for_names : name list;
      names_to_avoid : variable list
    }

  val typing_env : t -> Typing_env.t

  val adding_equations_for_names : t -> name list

  val names_to_avoid : t -> variable list

  val create : Typing_env.t -> t

  val with_typing_env : t -> Typing_env.t -> t

  val map_typing_env : t -> (Typing_env.t -> Typing_env.t) -> t

  val with_names_to_avoid : t -> variable list -> t

  val current_typing_env : t -> Typing_env.t

  val make_bottom : t -> t

  val replace_concrete_equation :
    Typing_env.t -> name -> flambda_type -> Typing_env.t option

  val add_concrete_equation_on_canonical_name :
    bool ->
    t ->
    name ->
    Expanded_type.t ->
    meet_expanded_head ->
    t Or_bottom.t option

  val adding_equation_for_name :
    t -> name -> (t -> t Or_bottom.t option) -> t Or_bottom.t option

  val add_or_delay_concrete_equation_on_canonical_name :
    bool ->
    t ->
    name ->
    Expanded_type.t ->
    meet_expanded_head ->
    t Or_bottom.t option

  val add_concrete_equation_on_const :
    bool ->
    t ->
    const ->
    Expanded_type.t ->
    meet_expanded_head ->
    t Or_bottom.t option

  val add_or_delay_concrete_equation_on_canonical :
    bool ->
    t ->
    simple ->
    Expanded_type.t ->
    meet_expanded_head ->
    t Or_bottom.t option

  val add_concrete_equation_on_simple :
    bool ->
    t ->
    simple ->
    Expanded_type.t ->
    meet_expanded_head ->
    t Or_bottom.t option

  val record_demotion :
    bool ->
    t ->
    flambda_kind ->
    name ->
    simple ->
    meet_expanded_head ->
    t Or_bottom.t option

  val add_alias_between_canonicals :
    bool ->
    t ->
    flambda_kind ->
    simple ->
    simple ->
    meet_expanded_head ->
    t Or_bottom.t option

  val add_equation_on_simple0 :
    bool ->
    t ->
    simple ->
    flambda_type ->
    meet_expanded_head ->
    t Or_bottom.t option

  val add_equation0 :
    bool ->
    t ->
    name ->
    flambda_type ->
    meet_expanded_head ->
    t Or_bottom.t option

  val add_equations0 :
    bool ->
    t ->
    (name * flambda_type) list ->
    meet_expanded_head ->
    t Or_bottom.t option

  val add_env_extension0 :
    bool -> t -> env_extension -> meet_expanded_head -> t Or_bottom.t option

  val add_equation_strict :
    t -> name -> flambda_type -> meet_expanded_head -> t Or_bottom.t option

  val add_env_extension_strict :
    t -> env_extension -> meet_expanded_head -> t Or_bottom.t option

  val bottom_on_exception : t -> t Or_bottom.t option -> t option

  val add_equation : t -> name -> flambda_type -> meet_expanded_head -> t option

  val add_equation_on_simple :
    t -> simple -> flambda_type -> meet_expanded_head -> t option

  val add_env_extension : t -> env_extension -> meet_expanded_head -> t option

  val enter_scope : t -> (Scope.t * Typing_env.t) * t

  val add_definition : t -> name -> Name_mode.t -> flambda_kind -> t option

  val add_variable_definition :
    t -> variable -> flambda_kind -> Name_mode.t -> t

  val add_alias0 :
    bool -> t -> simple -> simple -> meet_expanded_head -> t Or_bottom.t option

  val add_alias :
    t -> simple -> simple -> meet_expanded_head -> t Or_bottom.t option

  val meet :
    t ->
    flambda_type ->
    flambda_type ->
    meet_expanded_head ->
    Expanded_type.t Meet_result.t option

  val meet_type :
    t ->
    flambda_type ->
    flambda_type ->
    meet_expanded_head ->
    flambda_type Meet_result.t option

  val final_typing_env : t -> Typing_env.t

  val final_typing_env_strict : t -> Typing_env.t Or_bottom.t

  val use_meet_env : Typing_env.t -> (t -> t option) -> Typing_env.t option
end
