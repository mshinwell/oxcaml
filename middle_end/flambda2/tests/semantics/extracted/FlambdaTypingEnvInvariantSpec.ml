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

(** val binding_time_of : (flambda_type * Binding_time.With_name_mode.t) ->
    Binding_time.t **)

let binding_time_of entry = (snd entry).Binding_time.With_name_mode.binding_time

(** val binding_times_bounded_b : Typing_env.t -> bool **)

let binding_times_bounded_b tenv =
  Z.leb Binding_time.earliest_var tenv.Typing_env.min_binding_time
  && Z.leb tenv.Typing_env.min_binding_time tenv.Typing_env.next_binding_time

(** val binding_times_in_range_b : Typing_env.t -> bool **)

let binding_times_in_range_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun n entry ->
      match n with
      | Name_var _ ->
        Z.leb Binding_time.earliest_var (binding_time_of entry)
        && Z.ltb (binding_time_of entry) tenv.Typing_env.next_binding_time
      | Name_symbol _ -> true)
    (Typing_env.names_to_types tenv)

(** val binding_times_distinct_b : Typing_env.t -> bool **)

let binding_times_distinct_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun n entry ->
      Keyed.for_all_bindings_b name_eqb
        (fun n' entry' ->
          match n with
          | Name_var x -> (
            match n' with
            | Name_var y ->
              Pos.eqb x y
              || negb (Z.eqb (binding_time_of entry) (binding_time_of entry'))
            | Name_symbol _ -> true)
          | Name_symbol _ -> true)
        (Typing_env.names_to_types tenv))
    (Typing_env.names_to_types tenv)

(** val types_closed_b : Typing_env.t -> bool **)

let types_closed_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun _ entry ->
      forallb
        (fun x ->
          Keyed.is_bound name_eqb (Name_var x) (Typing_env.names_to_types tenv))
        (free_variables (fst entry)))
    (Typing_env.names_to_types tenv)

(** val symbols_recorded_b : Typing_env.t -> bool **)

let symbols_recorded_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun n entry ->
      match n with
      | Name_var _ -> true
      | Name_symbol _ ->
        Binding_time.With_name_mode.equal (snd entry)
          Binding_time.With_name_mode.symbols)
    (Typing_env.names_to_types tenv)

(** val symbols_defined_b : Typing_env.t -> bool **)

let symbols_defined_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun n _ ->
      match n with
      | Name_var _ -> true
      | Name_symbol s -> among s tenv.Typing_env.defined_symbols)
    (Typing_env.names_to_types tenv)

(** val all_levels : Typing_env.t -> Typing_env_level.t list **)

let all_levels tenv =
  map
    (fun t0 -> t0.Typing_env.One_level.level)
    (tenv.Typing_env.current_level :: tenv.Typing_env.prev_levels)

(** val all_scopes : Typing_env.t -> Scope.t list **)

let all_scopes tenv =
  map
    (fun t0 -> t0.Typing_env.One_level.scope)
    (tenv.Typing_env.current_level :: tenv.Typing_env.prev_levels)

(** val levels_disjoint_b : Typing_env_level.t -> Typing_env_level.t -> bool **)

let levels_disjoint_b earlier later =
  Keyed.is_empty
    (inter
       (domain earlier.Typing_env_level.defined_vars)
       (domain later.Typing_env_level.defined_vars))
  && Keyed.is_empty
       (Keyed.inter Z.eqb
          (Keyed.domain Z.eqb earlier.Typing_env_level.binding_times)
          (Keyed.domain Z.eqb later.Typing_env_level.binding_times))

(** val levels_pairwise_disjoint_b : Typing_env_level.t list -> bool **)

let rec levels_pairwise_disjoint_b = function
  | [] -> true
  | later :: levels0 ->
    forallb (fun earlier -> levels_disjoint_b earlier later) levels0
    && levels_pairwise_disjoint_b levels0

(** val defined_variables_bound_b : Typing_env.t -> bool **)

let defined_variables_bound_b tenv =
  forallb
    (fun level0 ->
      Keyed.for_all_bindings_b Pos.eqb
        (fun x k ->
          match
            Keyed.lookup name_eqb (Name_var x) (Typing_env.names_to_types tenv)
          with
          | Some p ->
            let ty, _ = p in
            kind_eqb (kind ty) k
          | None -> false)
        level0.Typing_env_level.defined_vars)
    (all_levels tenv)

(** val indexed_at_b : Typing_env_level.t -> Binding_time.t -> variable -> bool
    **)

let indexed_at_b level0 binding_time0 x =
  match
    Keyed.lookup Z.eqb binding_time0 level0.Typing_env_level.binding_times
  with
  | Some vars -> among x vars
  | None -> false

(** val level_indexed_b : Typing_env_level.t -> bool **)

let level_indexed_b level0 =
  Keyed.for_all_bindings_b Z.eqb
    (fun _ vars -> all_among vars (domain level0.Typing_env_level.defined_vars))
    level0.Typing_env_level.binding_times
  && forallb
       (fun x ->
         existsb
           (fun binding_time0 -> indexed_at_b level0 binding_time0 x)
           (Keyed.domain Z.eqb level0.Typing_env_level.binding_times))
       (domain level0.Typing_env_level.defined_vars)

(** val levels_indexed_b : Typing_env.t -> bool **)

let levels_indexed_b tenv = forallb level_indexed_b (all_levels tenv)

(** val level_binding_times_recorded_b : Typing_env.t -> bool **)

let level_binding_times_recorded_b tenv =
  forallb
    (fun level0 ->
      Keyed.for_all_bindings_b Z.eqb
        (fun binding_time0 vars ->
          forallb
            (fun x ->
              match
                Keyed.lookup name_eqb (Name_var x)
                  (Typing_env.names_to_types tenv)
              with
              | Some entry -> Z.eqb (binding_time_of entry) binding_time0
              | None -> false)
            vars)
        level0.Typing_env_level.binding_times)
    (all_levels tenv)

(** val level_binding_times_in_range_b : Typing_env.t -> bool **)

let level_binding_times_in_range_b tenv =
  forallb
    (fun level0 ->
      forallb
        (fun binding_time0 ->
          Z.ltb binding_time0 tenv.Typing_env.next_binding_time)
        (Keyed.domain Z.eqb level0.Typing_env_level.binding_times))
    (all_levels tenv)

(** val scopes_decreasing_b : Scope.t list -> bool **)

let rec scopes_decreasing_b = function
  | [] -> true
  | later :: scopes0 ->
    (match scopes0 with [] -> true | earlier :: _ -> Z.ltb earlier later)
    && scopes_decreasing_b scopes0

(** val variables_defined_b : Typing_env.t -> bool **)

let variables_defined_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun n _ ->
      match n with
      | Name_var x ->
        existsb
          (fun level0 -> is_bound x level0.Typing_env_level.defined_vars)
          (all_levels tenv)
      | Name_symbol _ -> true)
    (Typing_env.names_to_types tenv)

(** val aliases_known_b : Typing_env.t -> bool **)

let aliases_known_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun n canonical_element ->
      Typing_env.mem None tenv n
      && Typing_env.mem_simple None tenv canonical_element)
    (Typing_env.aliases tenv).Aliases.canonical_elements

(** val canonical_names_concrete_b : Typing_env.t -> bool **)

let canonical_names_concrete_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun n entry ->
      match get_alias_opt (fst entry) with
      | Some _ ->
        negb (is_canonical_b (Typing_env.aliases tenv) (simple_of_name n))
      | None -> true)
    (Typing_env.names_to_types tenv)

(** val typing_env_well_formed : Typing_env.t -> bool **)

let typing_env_well_formed tenv =
  ((((((binding_times_bounded_b tenv && binding_times_in_range_b tenv)
      && binding_times_distinct_b tenv)
     && types_closed_b tenv)
    && symbols_defined_b tenv)
   && symbols_recorded_b tenv)
  && (((((levels_pairwise_disjoint_b (all_levels tenv)
         && defined_variables_bound_b tenv)
        && levels_indexed_b tenv)
       && level_binding_times_recorded_b tenv)
      && level_binding_times_in_range_b tenv)
     && scopes_decreasing_b (all_scopes tenv))
  && variables_defined_b tenv)
  && ((aliases_consistent_b (Typing_env.aliases tenv)
      && name_modes_recorded_b
           (Typing_env.names_to_types tenv)
           (Typing_env.aliases tenv))
     && aliases_known_b tenv)
  && canonical_names_concrete_b tenv

(** val types_well_formed_b : Typing_env.t -> bool **)

let types_well_formed_b tenv =
  Keyed.for_all_bindings_b name_eqb
    (fun _ entry -> type_well_formed (fst entry))
    (Typing_env.names_to_types tenv)
