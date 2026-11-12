open BinPos
open Datatypes
open FlambdaBindingTime
open FlambdaEnvAliases
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypeProject
open FlambdaTypingEnv
open List
open ListDef
open OxCamlOption
open PeanoNat

module Index : sig
  type t = nat

  val equal : t -> t -> bool

  val number : 'a1 list -> (t * 'a1) list

  val insert : t * 'a1 -> (t * 'a1) list -> (t * 'a1) list

  val bindings : (t, 'a1) Keyed.finite_map -> (t * 'a1) list

  val choose : (t, 'a1) Keyed.finite_map -> (t * 'a1) option
end

module Simples_in_joined_envs : sig
  type t = (Index.t, simple) Keyed.finite_map

  val find : Index.t -> t -> simple option

  val equal : t -> t -> bool
end

module Source_env : sig
  type t = Typing_env.t

  val exists_in_source_env : t -> variable -> bool

  val latest_bound : t -> variable -> variable -> variable option

  type candidate =
    | No_simples_in_joined_envs
    | No_canonical_in_source_env
    | Canonical_in_all_joined_envs of simple
    | Latest_bound_source_var of variable

  val source_var_of : t -> simple -> variable option

  val candidate_step : t -> candidate -> simple -> candidate option

  val candidate_canonical_in_source_env :
    t -> Simples_in_joined_envs.t -> candidate option
end

module Bindings_in_target_env : sig
  type t =
    { source_env : Source_env.t;
      existential_for_these_simples_map :
        (Simples_in_joined_envs.t, variable) Keyed.finite_map;
      imported_variables : flambda_kind finite_map;
      existential_variables : flambda_kind finite_map;
      names_to_avoid : variable list
    }

  val source_env : t -> Source_env.t

  val existential_for_these_simples_map :
    t -> (Simples_in_joined_envs.t, variable) Keyed.finite_map

  val imported_variables : t -> flambda_kind finite_map

  val existential_variables : t -> flambda_kind finite_map

  val names_to_avoid : t -> variable list

  val from_source_env : variable list -> Source_env.t -> t

  val exists_in_target_env : t -> variable -> bool

  val has_existential_for_these_simples :
    t -> Simples_in_joined_envs.t -> variable option

  val existential_for_these_simples :
    (variable list -> variable) ->
    t ->
    Simples_in_joined_envs.t ->
    flambda_kind ->
    variable * t

  val import_from_all_envs : t -> variable -> flambda_kind -> t

  val imported_variables_in_order : t -> (variable * flambda_kind) list

  val existential_variables_in_order : t -> (variable * flambda_kind) list
end

module Joined_envs : sig
  type t =
    ( Index.t,
      Typing_env.t * (name, flambda_type) Keyed.finite_map )
    Keyed.finite_map

  val get_nth_joined_env : t -> Index.t -> Typing_env.t option

  val keys : t -> Index.t list

  val exists_in_all_joined_envs : t -> (Index.t, 'a1) Keyed.finite_map -> bool

  val equal_in_bindings : t -> simple -> (Index.t * simple) list -> bool option

  val equal_in_all_joined_envs :
    t -> simple -> Simples_in_joined_envs.t -> bool option

  val canonicals_of_alias_types :
    t -> (Index.t * flambda_type) list -> Simples_in_joined_envs.t option option

  val get_alias_then_canonical_simple_ignoring_name_mode_exn :
    t ->
    (Index.t, flambda_type) Keyed.finite_map ->
    Simples_in_joined_envs.t option option

  val types_of_simples :
    (const -> flambda_type) ->
    t ->
    flambda_kind ->
    (Index.t * simple) list ->
    (Index.t, flambda_type) Keyed.finite_map option

  val find_simples_in_joined_envs :
    (const -> flambda_type) ->
    t ->
    Simples_in_joined_envs.t ->
    flambda_kind ->
    (Index.t, flambda_type) Keyed.finite_map option

  val types_of_imported_var :
    (Index.t * (Typing_env.t * (name, flambda_type) Keyed.finite_map)) list ->
    variable ->
    flambda_kind ->
    (Index.t, flambda_type) Keyed.finite_map option

  val find_imported_var :
    t ->
    variable ->
    flambda_kind ->
    (Index.t, flambda_type) Keyed.finite_map option

  val kind_of_var_in :
    (Index.t * (Typing_env.t * (name, flambda_type) Keyed.finite_map)) list ->
    variable ->
    flambda_kind option

  val kind_of_imported_var : t -> variable -> flambda_kind option

  val get_canonical_simples_ignoring_name_mode :
    t -> (Index.t * simple) list -> Simples_in_joined_envs.t option
end

module Aliases_of_existentials : sig
  type t = variable list finite_map

  val empty : t

  val aliases_of_existential_var : t -> variable -> variable list

  val add : t -> variable -> variable -> t
end

module Join_env : sig
  type parameters =
    { fresh : variable list -> variable;
      type_eqb : flambda_type -> flambda_type -> bool;
      env_extension_eqb : env_extension -> env_extension -> bool;
      expand_const : const -> flambda_type;
      join_depth : nat
    }

  val fresh : parameters -> variable list -> variable

  val type_eqb : parameters -> flambda_type -> flambda_type -> bool

  val env_extension_eqb : parameters -> env_extension -> env_extension -> bool

  val expand_const : parameters -> const -> flambda_type

  val join_depth : parameters -> nat

  type t =
    { joined_envs : Joined_envs.t;
      types_in_target_env : flambda_type finite_map;
      types_in_joined_envs :
        (Index.t, flambda_type) Keyed.finite_map finite_map;
      aliases_of_existentials : Aliases_of_existentials.t;
      imported_vars : variable list;
      definitions_of_existentials :
        (Simples_in_joined_envs.t * flambda_kind) finite_map;
      bindings : Bindings_in_target_env.t
    }

  val joined_envs : t -> Joined_envs.t

  val types_in_target_env : t -> flambda_type finite_map

  val types_in_joined_envs :
    t -> (Index.t, flambda_type) Keyed.finite_map finite_map

  val aliases_of_existentials : t -> Aliases_of_existentials.t

  val imported_vars : t -> variable list

  val definitions_of_existentials :
    t -> (Simples_in_joined_envs.t * flambda_kind) finite_map

  val bindings : t -> Bindings_in_target_env.t

  val create : Joined_envs.t -> Bindings_in_target_env.t -> t

  val source_env : t -> Source_env.t

  val new_definitions_of_existentials :
    t -> t -> (Simples_in_joined_envs.t * flambda_kind) finite_map

  val new_equations_in_joined_envs :
    t -> t -> (Index.t, flambda_type) Keyed.finite_map finite_map

  val existential_for_these_canonicals :
    parameters -> t -> Simples_in_joined_envs.t -> flambda_kind -> variable * t

  val add_alias_of_existential :
    parameters -> t -> flambda_kind -> variable -> Simples_in_joined_envs.t -> t

  val add_equation_in_target_env : t -> variable -> flambda_type -> t option

  val add_equations_in_joined_envs :
    t -> variable -> (Index.t, flambda_type) Keyed.finite_map -> t

  type canonical_in_target_env =
    | Canonical_in_source_env of simple
    | Import_from_all_joined_envs of variable
    | Existential_for_these_canonicals of Simples_in_joined_envs.t

  val n_way_join_canonical_simples :
    t -> Simples_in_joined_envs.t -> canonical_in_target_env option

  val import_type_transitive_with :
    (t -> variable -> t option) -> t -> flambda_type -> t option

  val add_equals_in_joined_envs_with :
    parameters ->
    (t -> variable -> t option) ->
    t ->
    flambda_kind ->
    variable ->
    Simples_in_joined_envs.t ->
    t option

  val import_or_delay_n_way_join_of_concrete_type_with :
    parameters ->
    (t -> variable -> t option) ->
    t ->
    variable ->
    (Index.t, flambda_type) Keyed.finite_map ->
    t option

  val import_or_delay_n_way_join_type_with :
    parameters ->
    (t -> variable -> t option) ->
    t ->
    variable ->
    (Index.t, flambda_type) Keyed.finite_map ->
    t option

  val import_var_transitive_body :
    parameters -> (t -> variable -> t option) -> t -> variable -> t option

  val import_var_transitive : parameters -> nat -> t -> variable -> t option

  val import_type_transitive :
    parameters -> nat -> t -> flambda_type -> t option

  val import_or_delay_n_way_join_type :
    parameters ->
    nat ->
    t ->
    variable ->
    (Index.t, flambda_type) Keyed.finite_map ->
    t option

  val import_name_transitive : parameters -> nat -> t -> name -> t option

  val names_with_equations_everywhere : Joined_envs.t -> name list

  val types_of_name_in_levels :
    Joined_envs.t -> name -> (Index.t, flambda_type) Keyed.finite_map

  val join_aliases_into_bindings :
    parameters -> nat -> t -> Joined_envs.t -> t option

  type inverse_relations = (Relation.t * name) list finite_map

  val add_to_inverse_relations :
    inverse_relations -> variable -> Relation.t -> name -> inverse_relations

  val with_inverse_relation :
    head_of_kind_naked_immediate -> Relation.t -> name -> flambda_type

  val empty_naked_immediate_head : head_of_kind_naked_immediate

  val add_or_replace_equation :
    env_extension -> name -> flambda_type -> env_extension

  val equations_of : env_extension -> (name, flambda_type) Keyed.finite_map

  val add_inverse_relation_to_env_extension :
    nat ->
    name list ->
    env_extension ->
    name ->
    Relation.t ->
    name ->
    env_extension option

  val recover_inverse_relations :
    inverse_relations ->
    name ->
    flambda_type ->
    (flambda_type * inverse_relations) option

  type n_way_join_type =
    t -> (Index.t * flambda_type) list -> (flambda_type Or_unknown.t * t) option

  type choices =
    { recover_relations_on :
        t -> variable -> (Index.t, flambda_type) Keyed.finite_map -> bool
    }

  val recover_relations_on :
    choices -> t -> variable -> (Index.t, flambda_type) Keyed.finite_map -> bool

  val compiler_choices : choices

  val stands_for : t -> Index.t -> variable -> simple option

  val has_alias_in_terms : Typing_env.t -> simple -> bool

  val in_terms_in_all_joined_envs : t -> variable -> bool

  val repaired_choices : choices

  val n_way_join_round :
    choices ->
    n_way_join_type ->
    t ->
    (Index.t, flambda_type) Keyed.finite_map finite_map ->
    inverse_relations ->
    (inverse_relations * t) option

  val n_way_join_delayed_equations :
    nat ->
    choices ->
    n_way_join_type ->
    t ->
    inverse_relations ->
    (Index.t, flambda_type) Keyed.finite_map finite_map ->
    (inverse_relations * t) option

  val equations_of_existentials :
    parameters ->
    t ->
    (variable * (Simples_in_joined_envs.t * flambda_kind)) list ->
    (Index.t, flambda_type) Keyed.finite_map finite_map option

  val n_way_join_loop :
    nat ->
    parameters ->
    nat ->
    choices ->
    n_way_join_type ->
    t ->
    inverse_relations ->
    (Simples_in_joined_envs.t * flambda_kind) finite_map ->
    (inverse_relations * t) option

  val joined_env : t -> Index.t -> Typing_env.t option

  val import_type : parameters -> nat -> t -> flambda_type -> t option

  val n_way_join_simples :
    parameters ->
    nat ->
    t ->
    flambda_kind ->
    (Index.t * simple) list ->
    (simple Or_bottom.t * t) option

  val n_way_join_env_extension :
    parameters ->
    nat ->
    t ->
    (Index.t * env_extension) list ->
    (env_extension * t) Or_bottom.t option

  type ('meet_env, 'meet_expanded_head) meet_env_functions =
    { create_meet_env : Typing_env.t -> 'meet_env;
      current_typing_env : 'meet_env -> Typing_env.t;
      add_variable_definition :
        'meet_env -> variable -> flambda_kind -> Name_mode.t -> 'meet_env;
      add_env_extension :
        'meet_env -> env_extension -> 'meet_expanded_head -> 'meet_env option;
      make_bottom : 'meet_env -> 'meet_env;
      final_typing_env : 'meet_env -> Typing_env.t;
      names_to_avoid : 'meet_env -> variable list;
      with_names_to_avoid : 'meet_env -> variable list -> 'meet_env
    }

  val create_meet_env : ('a1, 'a2) meet_env_functions -> Typing_env.t -> 'a1

  val current_typing_env : ('a1, 'a2) meet_env_functions -> 'a1 -> Typing_env.t

  val add_variable_definition :
    ('a1, 'a2) meet_env_functions ->
    'a1 ->
    variable ->
    flambda_kind ->
    Name_mode.t ->
    'a1

  val add_env_extension :
    ('a1, 'a2) meet_env_functions -> 'a1 -> env_extension -> 'a2 -> 'a1 option

  val make_bottom : ('a1, 'a2) meet_env_functions -> 'a1 -> 'a1

  val final_typing_env : ('a1, 'a2) meet_env_functions -> 'a1 -> Typing_env.t

  val names_to_avoid : ('a1, 'a2) meet_env_functions -> 'a1 -> variable list

  val with_names_to_avoid :
    ('a1, 'a2) meet_env_functions -> 'a1 -> variable list -> 'a1

  val move_definition :
    (Simples_in_joined_envs.t * flambda_kind) finite_map ->
    variable ->
    variable ->
    (Simples_in_joined_envs.t * flambda_kind) finite_map

  val move_equation :
    flambda_type finite_map ->
    variable ->
    variable ->
    flambda_type finite_map option

  val move_inverse_relation :
    inverse_relations -> variable -> variable -> inverse_relations

  val in_inverse_relations : inverse_relations -> variable -> bool

  val count_occurrences : variable -> variable list -> nat

  val earliest_bound :
    Typing_env.t -> variable -> variable list -> variable option

  val choose_alias : Typing_env.t -> variable list -> variable option option

  val expand_variable :
    nat -> flambda_type finite_map -> variable -> flambda_type option

  val define_or_eliminate_variables_and_add_equations :
    ('a1, 'a2) meet_env_functions ->
    nat ->
    'a2 ->
    t ->
    'a1 ->
    inverse_relations ->
    ('a1 * (Simples_in_joined_envs.t * flambda_kind) finite_map) option

  val cut_for_joins :
    Scope.t -> (Index.t * Typing_env.t) list -> Joined_envs.t option

  val cut_and_n_way_join0 :
    ('a1, 'a2) meet_env_functions ->
    parameters ->
    nat ->
    choices ->
    n_way_join_type ->
    'a2 ->
    variable list ->
    'a1 ->
    Typing_env.t ->
    Joined_envs.t ->
    (('a1 * (Simples_in_joined_envs.t * flambda_kind) finite_map)
    * variable list)
    option

  val variables_of_env : Typing_env.t -> variable list

  val cut_and_n_way_join :
    ('a1, 'a2) meet_env_functions ->
    parameters ->
    nat ->
    choices ->
    n_way_join_type ->
    'a2 ->
    Scope.t ->
    'a1 ->
    Typing_env.t ->
    Typing_env.t list ->
    'a1 option
end

module Analysis : sig
  type 'a t =
    { definitions_in_joined_envs :
        (Simples_in_joined_envs.t * flambda_kind) finite_map;
      canonical_definitions_at_normal_mode :
        (Simples_in_joined_envs.t * flambda_kind) finite_map;
      external_ids : (Index.t, 'a) Keyed.finite_map
    }

  val definitions_in_joined_envs :
    'a1 t -> (Simples_in_joined_envs.t * flambda_kind) finite_map

  val canonical_definitions_at_normal_mode :
    'a1 t -> (Simples_in_joined_envs.t * flambda_kind) finite_map

  val value_at_use : simple -> const Or_unknown.t

  val values_of_bindings :
    (Index.t, 'a1) Keyed.finite_map ->
    (Index.t * simple) list ->
    ('a1 * const Or_unknown.t) list option

  val values_at_uses :
    (Index.t, 'a1) Keyed.finite_map ->
    Simples_in_joined_envs.t ->
    ('a1 * const Or_unknown.t) list option

  type simple_refined_at_join =
    | Not_refined_at_join
    | Invariant_in_all_uses of simple
    | Variable_refined_at_these_uses of Simples_in_joined_envs.t * flambda_kind

  val simple_refined_at_join_of :
    'a1 t -> Typing_env.t -> simple -> simple_refined_at_join

  val definitions_of_bindings :
    (Index.t, 'a1) Keyed.finite_map ->
    (Index.t * simple) list ->
    ('a1 * simple) list option

  val definitions_at_uses :
    (Index.t, 'a1) Keyed.finite_map ->
    Simples_in_joined_envs.t ->
    ('a1 * simple) list option

  val variables_created_at_join :
    'a1 t -> ((variable * Simples_in_joined_envs.t) * flambda_kind) list

  val simples_at_normal_mode :
    Joined_envs.t ->
    (Index.t * simple) list ->
    Simples_in_joined_envs.t option option

  val definitions_at_normal_mode :
    Joined_envs.t ->
    (variable * (Simples_in_joined_envs.t * flambda_kind)) list ->
    (Simples_in_joined_envs.t * flambda_kind) finite_map option

  val create :
    (Index.t, 'a1) Keyed.finite_map ->
    Joined_envs.t ->
    (Simples_in_joined_envs.t * flambda_kind) finite_map ->
    'a1 t option
end

val cut_and_n_way_join_with_analysis :
  ('a2, 'a3) Join_env.meet_env_functions ->
  Join_env.parameters ->
  nat ->
  Join_env.choices ->
  Join_env.n_way_join_type ->
  'a3 ->
  variable list ->
  Scope.t ->
  Typing_env.t ->
  ('a1 * Typing_env.t) list ->
  (Typing_env.t * 'a1 Analysis.t) option
