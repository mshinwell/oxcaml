open BinInt
open BinNums
open Datatypes
open FlambdaBindingTime
open FlambdaEnvAliases
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open List

module Scope : sig
  type t = coq_Z

  val initial : t

  val next : t -> t
end

module Typing_env_level : sig
  type t =
    { defined_vars : flambda_kind finite_map;
      binding_times : (Binding_time.t, variable list) Keyed.finite_map;
      equations : (name, flambda_type) Keyed.finite_map
    }

  val defined_vars : t -> flambda_kind finite_map

  val binding_times : t -> (Binding_time.t, variable list) Keyed.finite_map

  val equations : t -> (name, flambda_type) Keyed.finite_map

  val defined_variables_with_kinds : t -> flambda_kind finite_map

  val find_kind : t -> variable -> flambda_kind option

  val empty : t

  val is_empty : t -> bool

  val add_definition : t -> variable -> flambda_kind -> Binding_time.t -> t

  val add_or_replace_equation : t -> name -> flambda_type -> t

  val concat : t -> t -> t option

  val insert_binding_time :
    Binding_time.t -> Binding_time.t list -> Binding_time.t list

  val sort_binding_times : Binding_time.t list -> Binding_time.t list

  val variables_in_order : t -> variable list

  val fold_on_defined_vars :
    (variable -> flambda_kind -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 option
end

module Cached_level : sig
  type t =
    { names_to_types :
        (name, flambda_type * Binding_time.With_name_mode.t) Keyed.finite_map;
      aliases : Aliases.t
    }

  val names_to_types :
    t -> (name, flambda_type * Binding_time.With_name_mode.t) Keyed.finite_map

  val aliases : t -> Aliases.t

  val empty : t

  val add_or_replace_binding :
    t -> name -> flambda_type -> Binding_time.t -> Name_mode.t -> t

  val replace_variable_binding : t -> variable -> flambda_type -> t

  val with_aliases : t -> Aliases.t -> t
end

module Typing_env : sig
  module One_level : sig
    type t =
      { scope : Scope.t;
        level : Typing_env_level.t
      }

    val scope : t -> Scope.t

    val level : t -> Typing_env_level.t

    val create_empty : Scope.t -> t
  end

  type t =
    { defined_symbols : symbol list;
      prev_levels : One_level.t list;
      current_level : One_level.t;
      just_after_level : Cached_level.t;
      next_binding_time : Binding_time.t;
      min_binding_time : Binding_time.t;
      is_bottom : bool
    }

  val defined_symbols : t -> symbol list

  val prev_levels : t -> One_level.t list

  val current_level : t -> One_level.t

  val just_after_level : t -> Cached_level.t

  val next_binding_time : t -> Binding_time.t

  val min_binding_time : t -> Binding_time.t

  val is_bottom : t -> bool

  val make_bottom : t -> t

  val aliases : t -> Aliases.t

  val names_to_types :
    t -> (name, flambda_type * Binding_time.With_name_mode.t) Keyed.finite_map

  val current_scope : t -> Scope.t

  val create : t

  val with_current_level : t -> One_level.t -> Cached_level.t -> t

  val with_current_level_and_next_binding_time :
    t -> One_level.t -> Cached_level.t -> Binding_time.t -> t

  val with_aliases : t -> Aliases.t -> t

  val cached : t -> Cached_level.t

  val increment_scope : t -> t

  val initial_symbol_type : flambda_type * Binding_time.With_name_mode.t

  val check_optional_kind_matches : flambda_type -> flambda_kind option -> bool

  val find_with_binding_time_and_mode' :
    t ->
    name ->
    flambda_kind option ->
    (flambda_type * Binding_time.With_name_mode.t) option

  val find : t -> name -> flambda_kind option -> flambda_type option

  val find_with_binding_time_and_mode :
    t ->
    name ->
    flambda_kind option ->
    (flambda_type * Binding_time.With_name_mode.t) option

  val binding_time_and_mode : t -> name -> Binding_time.With_name_mode.t option

  val binding_time_and_mode_of_simple :
    t -> simple -> Binding_time.With_name_mode.t option

  val mem : Name_mode.t option -> t -> name -> bool

  val mem_simple : Name_mode.t option -> t -> simple -> bool

  val binding_time_resolver : t -> name -> Binding_time.With_name_mode.t

  val add_variable_definition :
    t -> variable -> flambda_kind -> Name_mode.t -> t

  val add_symbol_definition : t -> symbol -> t

  val add_symbol_definitions : t -> symbol list -> t

  val add_definition : t -> name -> Name_mode.t -> flambda_kind -> t option

  val replace_equation : t -> name -> flambda_type -> t

  val aliases_add :
    t -> simple -> simple -> Aliases.add_result Or_bottom.t option

  type add_alias_result =
    { canonical_element : simple;
      demoted_name : name;
      add_alias_result_t : t
    }

  val canonical_element : add_alias_result -> simple

  val demoted_name : add_alias_result -> name

  val add_alias_result_t : add_alias_result -> t

  val add_alias :
    t -> simple -> simple -> add_alias_result or_unknown_or_bottom option

  val cut_loop :
    Scope.t ->
    Typing_env_level.t ->
    One_level.t list ->
    Typing_env_level.t option

  val cut : t -> Scope.t -> Typing_env_level.t option

  val type_simple_in_term_exn :
    t -> Name_mode.t option -> simple -> (flambda_type * simple) option option

  val get_canonical_simple_ignoring_name_mode : t -> simple -> simple

  val get_canonical_simple_exn :
    t ->
    Name_mode.t option ->
    Name_mode.t option ->
    simple ->
    simple option option

  val get_alias_then_canonical_simple_exn :
    t ->
    Name_mode.t option ->
    Name_mode.t option ->
    flambda_type ->
    simple option option

  val closure_env : t -> t
end
