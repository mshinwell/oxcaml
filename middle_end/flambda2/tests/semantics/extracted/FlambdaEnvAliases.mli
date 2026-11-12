open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBindingTime
open FlambdaCompareSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open List
open ListDef

val name_is_symbol : name -> bool

val name_of_simple : simple -> name option

val simple_equal : simple -> simple -> bool

module Aliases : sig
  module Aliases_of_canonical_element : sig
    type t = (name, Name_mode.t) Keyed.finite_map

    val empty : t

    val mem : t -> name -> bool

    val add : t -> name -> Name_mode.t -> t option

    val all : t -> name list

    val at_mode : t -> Name_mode.t -> name list

    val find_earliest_candidates :
      t ->
      (Name_mode.t -> name list -> name list) ->
      Name_mode.t ->
      name list option

    val union : t -> t -> t
  end

  type t =
    { canonical_elements : (name, simple) Keyed.finite_map;
      aliases_of_canonical_names :
        (name, Aliases_of_canonical_element.t) Keyed.finite_map;
      aliases_of_consts :
        (const, Aliases_of_canonical_element.t) Keyed.finite_map
    }

  val canonical_elements : t -> (name, simple) Keyed.finite_map

  val aliases_of_canonical_names :
    t -> (name, Aliases_of_canonical_element.t) Keyed.finite_map

  val aliases_of_consts :
    t -> (const, Aliases_of_canonical_element.t) Keyed.finite_map

  val name_defined_earlier :
    (name -> Binding_time.With_name_mode.t) ->
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    name ->
    name ->
    bool

  val defined_earlier :
    (name -> Binding_time.With_name_mode.t) ->
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    simple ->
    simple ->
    bool

  val binding_time_and_name_mode :
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    simple ->
    Binding_time.With_name_mode.t

  val compute_name_mode_unscoped :
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    simple ->
    Name_mode.t

  val compute_name_mode :
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    simple ->
    Binding_time.t ->
    Name_mode.t

  val empty : t

  type is_canonical_or_alias =
    | Is_canonical
    | Alias_of_canonical of simple

  val canonical : t -> simple -> is_canonical_or_alias

  val get_aliases_of_canonical_element :
    t -> simple -> Aliases_of_canonical_element.t

  val add_alias_between_canonical_elements :
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    t ->
    simple ->
    simple ->
    t Or_bottom.t option

  type to_be_demoted =
    | Demote_canonical_element1
    | Demote_canonical_element2

  val choose_canonical_element_to_be_demoted :
    (name -> Binding_time.With_name_mode.t) ->
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    simple ->
    simple ->
    to_be_demoted

  val add_alias :
    (name -> Binding_time.With_name_mode.t) ->
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    t ->
    simple ->
    simple ->
    (t * to_be_demoted) Or_bottom.t option

  val add0 :
    (name -> Binding_time.With_name_mode.t) ->
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    t ->
    simple ->
    simple ->
    (t * to_be_demoted) Or_bottom.t option

  type add_result =
    { add_result_t : t;
      demoted_name : name;
      canonical_element : simple
    }

  val add_result_t : add_result -> t

  val demoted_name : add_result -> name

  val canonical_element : add_result -> simple

  val add :
    (name -> Binding_time.With_name_mode.t) ->
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    t ->
    simple ->
    simple ->
    add_result Or_bottom.t option

  val find_earliest_alias :
    (name -> Binding_time.With_name_mode.t) ->
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    t ->
    simple ->
    Binding_time.t ->
    Name_mode.t ->
    simple option

  val get_canonical_element_exn :
    (name -> Binding_time.With_name_mode.t) ->
    (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map ->
    t ->
    simple ->
    Name_mode.t ->
    Name_mode.t ->
    Binding_time.t ->
    simple option

  val get_canonical_ignoring_name_mode : t -> name -> simple
end
