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

module Scope = struct
  type t = coq_Z

  (** val initial : t **)

  let initial = Z0

  (** val next : t -> t **)

  let next scope0 = Z.add scope0 (Zpos Coq_xH)
end

module Typing_env_level = struct
  type t =
    { defined_vars : flambda_kind finite_map;
      binding_times : (Binding_time.t, variable list) Keyed.finite_map;
      equations : (name, flambda_type) Keyed.finite_map
    }

  (** val defined_vars : t -> flambda_kind finite_map **)

  let defined_vars t0 = t0.defined_vars

  (** val binding_times : t -> (Binding_time.t, variable list) Keyed.finite_map
      **)

  let binding_times t0 = t0.binding_times

  (** val equations : t -> (name, flambda_type) Keyed.finite_map **)

  let equations t0 = t0.equations

  (** val defined_variables_with_kinds : t -> flambda_kind finite_map **)

  let defined_variables_with_kinds level0 = level0.defined_vars

  (** val find_kind : t -> variable -> flambda_kind option **)

  let find_kind level0 var = lookup var level0.defined_vars

  (** val empty : t **)

  let empty = { defined_vars = []; binding_times = []; equations = [] }

  (** val is_empty : t -> bool **)

  let is_empty level0 =
    (Keyed.is_empty level0.defined_vars && Keyed.is_empty level0.binding_times)
    && Keyed.is_empty level0.equations

  (** val add_definition : t -> variable -> flambda_kind -> Binding_time.t -> t
      **)

  let add_definition level0 var kind0 binding_time0 =
    let vars =
      match Keyed.lookup Z.eqb binding_time0 level0.binding_times with
      | Some prev_vars -> var :: prev_vars
      | None -> var :: []
    in
    { defined_vars = (var, kind0) :: level0.defined_vars;
      binding_times = (binding_time0, vars) :: level0.binding_times;
      equations = level0.equations
    }

  (** val add_or_replace_equation : t -> name -> flambda_type -> t **)

  let add_or_replace_equation level0 name0 ty =
    if is_obviously_unknown ty
    then
      { defined_vars = level0.defined_vars;
        binding_times = level0.binding_times;
        equations = Keyed.unbind name_eqb name0 level0.equations
      }
    else
      { defined_vars = level0.defined_vars;
        binding_times = level0.binding_times;
        equations = (name0, ty) :: level0.equations
      }

  (** val concat : t -> t -> t option **)

  let concat earlier later =
    if
      Keyed.is_empty
        (inter (domain earlier.defined_vars) (domain later.defined_vars))
      && Keyed.is_empty
           (Keyed.inter Z.eqb
              (Keyed.domain Z.eqb earlier.binding_times)
              (Keyed.domain Z.eqb later.binding_times))
    then
      Some
        { defined_vars = app later.defined_vars earlier.defined_vars;
          binding_times = app later.binding_times earlier.binding_times;
          equations = app later.equations earlier.equations
        }
    else None

  (** val insert_binding_time : Binding_time.t -> Binding_time.t list ->
      Binding_time.t list **)

  let rec insert_binding_time binding_time0 sorted =
    match sorted with
    | [] -> binding_time0 :: []
    | first :: rest ->
      if Z.leb binding_time0 first
      then binding_time0 :: sorted
      else first :: insert_binding_time binding_time0 rest

  (** val sort_binding_times : Binding_time.t list -> Binding_time.t list **)

  let sort_binding_times binding_times0 =
    fold_right insert_binding_time [] binding_times0

  (** val variables_in_order : t -> variable list **)

  let variables_in_order level0 =
    flat_map
      (fun binding_time0 ->
        match Keyed.lookup Z.eqb binding_time0 level0.binding_times with
        | Some vars -> dedup vars
        | None -> [])
      (sort_binding_times (Keyed.domain Z.eqb level0.binding_times))

  (** val fold_on_defined_vars : (variable -> flambda_kind -> 'a1 -> 'a1) -> t
      -> 'a1 -> 'a1 option **)

  let fold_on_defined_vars f level0 init =
    fold_left
      (fun acc var ->
        match acc with
        | Some acc0 -> (
          match find_kind level0 var with
          | Some kind0 -> Some (f var kind0 acc0)
          | None -> None)
        | None -> None)
      (variables_in_order level0)
      (Some init)
end

module Cached_level = struct
  type t =
    { names_to_types :
        (name, flambda_type * Binding_time.With_name_mode.t) Keyed.finite_map;
      aliases : Aliases.t
    }

  (** val names_to_types : t -> (name, flambda_type *
      Binding_time.With_name_mode.t) Keyed.finite_map **)

  let names_to_types t0 = t0.names_to_types

  (** val aliases : t -> Aliases.t **)

  let aliases t0 = t0.aliases

  (** val empty : t **)

  let empty = { names_to_types = []; aliases = Aliases.empty }

  (** val add_or_replace_binding : t -> name -> flambda_type -> Binding_time.t
      -> Name_mode.t -> t **)

  let add_or_replace_binding cached0 name0 ty binding_time0 name_mode0 =
    let binding_time_and_mode0 =
      { Binding_time.With_name_mode.binding_time = binding_time0;
        Binding_time.With_name_mode.name_mode = name_mode0
      }
    in
    { names_to_types =
        (name0, (ty, binding_time_and_mode0)) :: cached0.names_to_types;
      aliases = cached0.aliases
    }

  (** val replace_variable_binding : t -> variable -> flambda_type -> t **)

  let replace_variable_binding cached0 var ty =
    match Keyed.lookup name_eqb (Name_var var) cached0.names_to_types with
    | Some p ->
      let _, binding_time_and_mode0 = p in
      { names_to_types =
          (Name_var var, (ty, binding_time_and_mode0)) :: cached0.names_to_types;
        aliases = cached0.aliases
      }
    | None -> cached0

  (** val with_aliases : t -> Aliases.t -> t **)

  let with_aliases cached0 aliases0 =
    { names_to_types = cached0.names_to_types; aliases = aliases0 }
end

module Typing_env = struct
  module One_level = struct
    type t =
      { scope : Scope.t;
        level : Typing_env_level.t
      }

    (** val scope : t -> Scope.t **)

    let scope t0 = t0.scope

    (** val level : t -> Typing_env_level.t **)

    let level t0 = t0.level

    (** val create_empty : Scope.t -> t **)

    let create_empty scope0 = { scope = scope0; level = Typing_env_level.empty }
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

  (** val defined_symbols : t -> symbol list **)

  let defined_symbols t0 = t0.defined_symbols

  (** val prev_levels : t -> One_level.t list **)

  let prev_levels t0 = t0.prev_levels

  (** val current_level : t -> One_level.t **)

  let current_level t0 = t0.current_level

  (** val just_after_level : t -> Cached_level.t **)

  let just_after_level t0 = t0.just_after_level

  (** val next_binding_time : t -> Binding_time.t **)

  let next_binding_time t0 = t0.next_binding_time

  (** val min_binding_time : t -> Binding_time.t **)

  let min_binding_time t0 = t0.min_binding_time

  (** val is_bottom : t -> bool **)

  let is_bottom t0 = t0.is_bottom

  (** val make_bottom : t -> t **)

  let make_bottom tenv =
    { defined_symbols = tenv.defined_symbols;
      prev_levels = tenv.prev_levels;
      current_level = tenv.current_level;
      just_after_level = tenv.just_after_level;
      next_binding_time = tenv.next_binding_time;
      min_binding_time = tenv.min_binding_time;
      is_bottom = true
    }

  (** val aliases : t -> Aliases.t **)

  let aliases tenv = tenv.just_after_level.Cached_level.aliases

  (** val names_to_types : t -> (name, flambda_type *
      Binding_time.With_name_mode.t) Keyed.finite_map **)

  let names_to_types tenv = tenv.just_after_level.Cached_level.names_to_types

  (** val current_scope : t -> Scope.t **)

  let current_scope tenv = tenv.current_level.One_level.scope

  (** val create : t **)

  let create =
    { defined_symbols = [];
      prev_levels = [];
      current_level = One_level.create_empty (Scope.next Scope.initial);
      just_after_level = Cached_level.empty;
      next_binding_time = Binding_time.earliest_var;
      min_binding_time = Binding_time.earliest_var;
      is_bottom = false
    }

  (** val with_current_level : t -> One_level.t -> Cached_level.t -> t **)

  let with_current_level tenv current_level0 just_after_level0 =
    { defined_symbols = tenv.defined_symbols;
      prev_levels = tenv.prev_levels;
      current_level = current_level0;
      just_after_level = just_after_level0;
      next_binding_time = tenv.next_binding_time;
      min_binding_time = tenv.min_binding_time;
      is_bottom = tenv.is_bottom
    }

  (** val with_current_level_and_next_binding_time : t -> One_level.t ->
      Cached_level.t -> Binding_time.t -> t **)

  let with_current_level_and_next_binding_time tenv current_level0
      just_after_level0 next_binding_time0 =
    { defined_symbols = tenv.defined_symbols;
      prev_levels = tenv.prev_levels;
      current_level = current_level0;
      just_after_level = just_after_level0;
      next_binding_time = next_binding_time0;
      min_binding_time = tenv.min_binding_time;
      is_bottom = tenv.is_bottom
    }

  (** val with_aliases : t -> Aliases.t -> t **)

  let with_aliases tenv aliases0 =
    with_current_level tenv tenv.current_level
      (Cached_level.with_aliases tenv.just_after_level aliases0)

  (** val cached : t -> Cached_level.t **)

  let cached tenv = tenv.just_after_level

  (** val increment_scope : t -> t **)

  let increment_scope tenv =
    { defined_symbols = tenv.defined_symbols;
      prev_levels = tenv.current_level :: tenv.prev_levels;
      current_level =
        { One_level.scope = Scope.next (current_scope tenv);
          One_level.level = Typing_env_level.empty
        };
      just_after_level = tenv.just_after_level;
      next_binding_time = tenv.next_binding_time;
      min_binding_time = tenv.min_binding_time;
      is_bottom = tenv.is_bottom
    }

  (** val initial_symbol_type : flambda_type * Binding_time.With_name_mode.t **)

  let initial_symbol_type =
    any_non_null_value, Binding_time.With_name_mode.symbols

  (** val check_optional_kind_matches : flambda_type -> flambda_kind option ->
      bool **)

  let check_optional_kind_matches ty = function
    | Some kind0 -> kind_eqb kind0 (kind ty)
    | None -> true

  (** val find_with_binding_time_and_mode' : t -> name -> flambda_kind option ->
      (flambda_type * Binding_time.With_name_mode.t) option **)

  let find_with_binding_time_and_mode' tenv name0 kind0 =
    match Keyed.lookup name_eqb name0 (names_to_types tenv) with
    | Some p ->
      let ty, binding_time_and_mode0 = p in
      if check_optional_kind_matches ty kind0
      then
        if tenv.is_bottom
        then Some (bottom (kind ty), binding_time_and_mode0)
        else Some (ty, binding_time_and_mode0)
      else None
    | None -> (
      match name0 with
      | Name_var _ -> None
      | Name_symbol sym ->
        if
          among sym tenv.defined_symbols
          && check_optional_kind_matches (fst initial_symbol_type) kind0
        then Some initial_symbol_type
        else None)

  (** val find : t -> name -> flambda_kind option -> flambda_type option **)

  let find tenv name0 kind0 =
    option_map fst (find_with_binding_time_and_mode' tenv name0 kind0)

  (** val find_with_binding_time_and_mode : t -> name -> flambda_kind option ->
      (flambda_type * Binding_time.With_name_mode.t) option **)

  let find_with_binding_time_and_mode tenv name0 kind0 =
    match find_with_binding_time_and_mode' tenv name0 kind0 with
    | Some p ->
      let ty, binding_time_and_mode0 = p in
      let scoped_mode =
        Binding_time.With_name_mode.scoped_name_mode binding_time_and_mode0
          tenv.min_binding_time
      in
      Some
        ( ty,
          { Binding_time.With_name_mode.binding_time =
              binding_time_and_mode0.Binding_time.With_name_mode.binding_time;
            Binding_time.With_name_mode.name_mode = scoped_mode
          } )
    | None -> None

  (** val binding_time_and_mode : t -> name -> Binding_time.With_name_mode.t
      option **)

  let binding_time_and_mode tenv name0 =
    match name0 with
    | Name_var _ ->
      option_map snd (find_with_binding_time_and_mode tenv name0 None)
    | Name_symbol _ -> Some Binding_time.With_name_mode.symbols

  (** val binding_time_and_mode_of_simple : t -> simple ->
      Binding_time.With_name_mode.t option **)

  let binding_time_and_mode_of_simple tenv = function
    | Var x -> binding_time_and_mode tenv (Name_var x)
    | Symbol s -> binding_time_and_mode tenv (Name_symbol s)
    | Const _ -> Some Binding_time.With_name_mode.consts

  (** val mem : Name_mode.t option -> t -> name -> bool **)

  let mem min_name_mode tenv name0 =
    match name0 with
    | Name_var _ -> (
      match Keyed.lookup name_eqb name0 (names_to_types tenv) with
      | Some p -> (
        let _, binding_time_and_mode0 = p in
        let name_mode0 =
          Binding_time.With_name_mode.scoped_name_mode binding_time_and_mode0
            tenv.min_binding_time
        in
        match min_name_mode with
        | Some min_name_mode0 -> (
          match Name_mode.compare_partial_order min_name_mode0 name_mode0 with
          | Some c -> Z.leb c Z0
          | None -> false)
        | None -> true)
      | None -> false)
    | Name_symbol sym -> among sym tenv.defined_symbols

  (** val mem_simple : Name_mode.t option -> t -> simple -> bool **)

  let mem_simple min_name_mode tenv = function
    | Var x -> mem min_name_mode tenv (Name_var x)
    | Symbol s -> mem min_name_mode tenv (Name_symbol s)
    | Const _ -> true

  (** val binding_time_resolver : t -> name -> Binding_time.With_name_mode.t **)

  let binding_time_resolver tenv name0 =
    match Keyed.lookup name_eqb name0 (names_to_types tenv) with
    | Some p ->
      let _, binding_time_and_mode0 = p in
      binding_time_and_mode0
    | None -> (
      match name0 with
      | Name_var _ -> Binding_time.With_name_mode.imported_variables
      | Name_symbol _ -> Binding_time.With_name_mode.symbols)

  (** val add_variable_definition : t -> variable -> flambda_kind -> Name_mode.t
      -> t **)

  let add_variable_definition tenv var kind0 name_mode0 =
    let level0 =
      Typing_env_level.add_definition tenv.current_level.One_level.level var
        kind0 tenv.next_binding_time
    in
    let just_after_level0 =
      Cached_level.add_or_replace_binding (cached tenv) (Name_var var)
        (unknown kind0) tenv.next_binding_time name_mode0
    in
    let current_level0 =
      { One_level.scope = current_scope tenv; One_level.level = level0 }
    in
    with_current_level_and_next_binding_time tenv current_level0
      just_after_level0
      (Binding_time.succ tenv.next_binding_time)

  (** val add_symbol_definition : t -> symbol -> t **)

  let add_symbol_definition tenv sym =
    { defined_symbols = sym :: tenv.defined_symbols;
      prev_levels = tenv.prev_levels;
      current_level = tenv.current_level;
      just_after_level = tenv.just_after_level;
      next_binding_time = tenv.next_binding_time;
      min_binding_time = tenv.min_binding_time;
      is_bottom = tenv.is_bottom
    }

  (** val add_definition : t -> name -> Name_mode.t -> flambda_kind -> t option
      **)

  let add_definition tenv name0 name_mode0 kind0 =
    match name0 with
    | Name_var var -> Some (add_variable_definition tenv var kind0 name_mode0)
    | Name_symbol sym ->
      if Name_mode.equal name_mode0 Name_mode.normal
      then Some (add_symbol_definition tenv sym)
      else None

  (** val replace_equation : t -> name -> flambda_type -> t **)

  let replace_equation tenv name0 ty =
    let level0 =
      Typing_env_level.add_or_replace_equation
        tenv.current_level.One_level.level name0 ty
    in
    let just_after_level0 =
      match name0 with
      | Name_var var ->
        Cached_level.replace_variable_binding tenv.just_after_level var ty
      | Name_symbol _ ->
        Cached_level.add_or_replace_binding tenv.just_after_level name0 ty
          Binding_time.symbols Name_mode.normal
    in
    with_current_level tenv
      { One_level.scope = current_scope tenv; One_level.level = level0 }
      just_after_level0

  (** val aliases_add : t -> simple -> simple -> Aliases.add_result Or_bottom.t
      option **)

  let aliases_add tenv canonical_element1 canonical_element2 =
    Aliases.add
      (binding_time_resolver tenv)
      (names_to_types tenv) (aliases tenv) canonical_element1 canonical_element2

  type add_alias_result =
    { canonical_element : simple;
      demoted_name : name;
      add_alias_result_t : t
    }

  (** val canonical_element : add_alias_result -> simple **)

  let canonical_element a = a.canonical_element

  (** val demoted_name : add_alias_result -> name **)

  let demoted_name a = a.demoted_name

  (** val add_alias_result_t : add_alias_result -> t **)

  let add_alias_result_t a = a.add_alias_result_t

  (** val add_alias : t -> simple -> simple -> add_alias_result
      or_unknown_or_bottom option **)

  let add_alias tenv canonical_element1 canonical_element2 =
    match aliases_add tenv canonical_element1 canonical_element2 with
    | Some t0 -> (
      match t0 with
      | Or_bottom.Ok result ->
        Some
          (Ok
             { canonical_element = result.Aliases.canonical_element;
               demoted_name = result.Aliases.demoted_name;
               add_alias_result_t =
                 with_aliases tenv result.Aliases.add_result_t
             })
      | Or_bottom.Bottom -> Some Bottom)
    | None -> None

  (** val cut_loop : Scope.t -> Typing_env_level.t -> One_level.t list ->
      Typing_env_level.t option **)

  let rec cut_loop cut_after result = function
    | [] -> Some result
    | one_level :: levels0 ->
      if Z.ltb cut_after one_level.One_level.scope
      then
        match Typing_env_level.concat one_level.One_level.level result with
        | Some result0 -> cut_loop cut_after result0 levels0
        | None -> None
      else Some result

  (** val cut : t -> Scope.t -> Typing_env_level.t option **)

  let cut tenv cut_after =
    if Z.leb (current_scope tenv) cut_after
    then Some Typing_env_level.empty
    else cut_loop cut_after tenv.current_level.One_level.level tenv.prev_levels

  (** val get_canonical_simple_ignoring_name_mode : t -> simple -> simple **)

  let get_canonical_simple_ignoring_name_mode tenv simple0 =
    match simple0 with
    | Var x ->
      Aliases.get_canonical_ignoring_name_mode (aliases tenv) (Name_var x)
    | Symbol s ->
      Aliases.get_canonical_ignoring_name_mode (aliases tenv) (Name_symbol s)
    | Const _ -> simple0

  (** val get_canonical_simple_exn : t -> Name_mode.t option -> Name_mode.t
      option -> simple -> simple option option **)

  let get_canonical_simple_exn tenv min_name_mode name_mode_of_existing_simple
      simple0 =
    match
      match name_mode_of_existing_simple with
      | Some name_mode0 -> Some name_mode0
      | None ->
        option_map
          (fun t0 -> t0.Binding_time.With_name_mode.name_mode)
          (binding_time_and_mode_of_simple tenv simple0)
    with
    | Some name_mode_simple ->
      let min_name_mode0 =
        match min_name_mode with
        | Some name_mode0 -> name_mode0
        | None -> name_mode_simple
      in
      Some
        (Aliases.get_canonical_element_exn
           (binding_time_resolver tenv)
           (names_to_types tenv) (aliases tenv) simple0 name_mode_simple
           min_name_mode0 tenv.min_binding_time)
    | None -> None

  (** val get_alias_then_canonical_simple_exn : t -> Name_mode.t option ->
      Name_mode.t option -> flambda_type -> simple option option **)

  let get_alias_then_canonical_simple_exn tenv min_name_mode
      name_mode_of_existing_simple typ =
    match get_alias_opt typ with
    | Some simple0 ->
      get_canonical_simple_exn tenv min_name_mode name_mode_of_existing_simple
        simple0
    | None -> Some None
end
