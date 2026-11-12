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

module Index = struct
  type t = nat

  (** val equal : t -> t -> bool **)

  let equal = Nat.eqb

  (** val number : 'a1 list -> (t * 'a1) list **)

  let number xs = combine (seq O (length xs)) xs

  (** val insert : (t * 'a1) -> (t * 'a1) list -> (t * 'a1) list **)

  let rec insert binding sorted =
    match sorted with
    | [] -> binding :: []
    | binding' :: rest ->
      if Nat.leb (fst binding) (fst binding')
      then binding :: sorted
      else binding' :: insert binding rest

  (** val bindings : (t, 'a1) Keyed.finite_map -> (t * 'a1) list **)

  let bindings map0 = fold_right insert [] (Keyed.compact equal map0)

  (** val choose : (t, 'a1) Keyed.finite_map -> (t * 'a1) option **)

  let choose map0 =
    match bindings map0 with [] -> None | binding :: _ -> Some binding
end

module Simples_in_joined_envs = struct
  type t = (Index.t, simple) Keyed.finite_map

  (** val find : Index.t -> t -> simple option **)

  let find index simples = Keyed.lookup Index.equal index simples

  (** val equal : t -> t -> bool **)

  let equal simples simples' =
    Keyed.for_all_bindings_b Index.equal
      (fun index simple0 ->
        match find index simples' with
        | Some simple' -> simple_equal simple0 simple'
        | None -> false)
      simples
    && Keyed.for_all_bindings_b Index.equal
         (fun index _ -> Keyed.is_bound Index.equal index simples)
         simples'
end

module Source_env = struct
  type t = Typing_env.t

  (** val exists_in_source_env : t -> variable -> bool **)

  let exists_in_source_env source_env0 var =
    Typing_env.mem None source_env0 (Name_var var)

  (** val latest_bound : t -> variable -> variable -> variable option **)

  let latest_bound source_env0 var var0 =
    if Pos.eqb var var0
    then Some var
    else
      match Typing_env.binding_time_and_mode source_env0 (Name_var var) with
      | Some time -> (
        match Typing_env.binding_time_and_mode source_env0 (Name_var var0) with
        | Some time0 ->
          let binding_time0 = time.Binding_time.With_name_mode.binding_time in
          let binding_time1 = time0.Binding_time.With_name_mode.binding_time in
          if Binding_time.strictly_earlier binding_time0 binding_time1
          then Some var0
          else if Binding_time.strictly_earlier binding_time1 binding_time0
          then Some var
          else None
        | None -> None)
      | None -> None

  type candidate =
    | No_simples_in_joined_envs
    | No_canonical_in_source_env
    | Canonical_in_all_joined_envs of simple
    | Latest_bound_source_var of variable

  (** val source_var_of : t -> simple -> variable option **)

  let source_var_of source_env0 = function
    | Var var -> if exists_in_source_env source_env0 var then Some var else None
    | _ -> None

  (** val candidate_step : t -> candidate -> simple -> candidate option **)

  let candidate_step source_env0 possible canonical =
    let maybe_this_source_var =
      match source_var_of source_env0 canonical with
      | Some var -> Latest_bound_source_var var
      | None -> No_canonical_in_source_env
    in
    let latest_source_var_with =
     fun var ->
      match source_var_of source_env0 canonical with
      | Some var0 ->
        option_map
          (fun x -> Latest_bound_source_var x)
          (latest_bound source_env0 var var0)
      | None -> Some (Latest_bound_source_var var)
    in
    match possible with
    | No_simples_in_joined_envs -> Some (Canonical_in_all_joined_envs canonical)
    | No_canonical_in_source_env -> Some maybe_this_source_var
    | Canonical_in_all_joined_envs shared_simple -> (
      if simple_equal canonical shared_simple
      then Some possible
      else
        match source_var_of source_env0 shared_simple with
        | Some var -> latest_source_var_with var
        | None -> Some maybe_this_source_var)
    | Latest_bound_source_var var -> latest_source_var_with var

  (** val candidate_canonical_in_source_env : t -> Simples_in_joined_envs.t ->
      candidate option **)

  let candidate_canonical_in_source_env source_env0 canonicals_in_joined_envs =
    fold_left
      (fun possible binding ->
        match possible with
        | Some possible0 -> candidate_step source_env0 possible0 (snd binding)
        | None -> None)
      (Keyed.compact Index.equal canonicals_in_joined_envs)
      (Some No_simples_in_joined_envs)
end

module Bindings_in_target_env = struct
  type t =
    { source_env : Source_env.t;
      existential_for_these_simples_map :
        (Simples_in_joined_envs.t, variable) Keyed.finite_map;
      imported_variables : flambda_kind finite_map;
      existential_variables : flambda_kind finite_map;
      names_to_avoid : variable list
    }

  (** val source_env : t -> Source_env.t **)

  let source_env t0 = t0.source_env

  (** val existential_for_these_simples_map : t -> (Simples_in_joined_envs.t,
      variable) Keyed.finite_map **)

  let existential_for_these_simples_map t0 =
    t0.existential_for_these_simples_map

  (** val imported_variables : t -> flambda_kind finite_map **)

  let imported_variables t0 = t0.imported_variables

  (** val existential_variables : t -> flambda_kind finite_map **)

  let existential_variables t0 = t0.existential_variables

  (** val names_to_avoid : t -> variable list **)

  let names_to_avoid t0 = t0.names_to_avoid

  (** val from_source_env : variable list -> Source_env.t -> t **)

  let from_source_env names_to_avoid0 source_env0 =
    { source_env = source_env0;
      existential_for_these_simples_map = [];
      imported_variables = [];
      existential_variables = [];
      names_to_avoid = names_to_avoid0
    }

  (** val exists_in_target_env : t -> variable -> bool **)

  let exists_in_target_env bindings0 var =
    (Source_env.exists_in_source_env bindings0.source_env var
    || is_bound var bindings0.existential_variables)
    || is_bound var bindings0.imported_variables

  (** val has_existential_for_these_simples : t -> Simples_in_joined_envs.t ->
      variable option **)

  let has_existential_for_these_simples bindings0 simples =
    Keyed.lookup Simples_in_joined_envs.equal simples
      bindings0.existential_for_these_simples_map

  (** val existential_for_these_simples : (variable list -> variable) -> t ->
      Simples_in_joined_envs.t -> flambda_kind -> variable * t **)

  let existential_for_these_simples fresh0 bindings0 simples kind0 =
    match has_existential_for_these_simples bindings0 simples with
    | Some existing_canonical -> existing_canonical, bindings0
    | None ->
      let var = fresh0 bindings0.names_to_avoid in
      ( var,
        { source_env = bindings0.source_env;
          existential_for_these_simples_map =
            (simples, var) :: bindings0.existential_for_these_simples_map;
          imported_variables = bindings0.imported_variables;
          existential_variables =
            (var, kind0) :: bindings0.existential_variables;
          names_to_avoid = var :: bindings0.names_to_avoid
        } )

  (** val import_from_all_envs : t -> variable -> flambda_kind -> t **)

  let import_from_all_envs bindings0 imported_var kind0 =
    if is_bound imported_var bindings0.imported_variables
    then bindings0
    else
      { source_env = bindings0.source_env;
        existential_for_these_simples_map =
          bindings0.existential_for_these_simples_map;
        imported_variables =
          (imported_var, kind0) :: bindings0.imported_variables;
        existential_variables = bindings0.existential_variables;
        names_to_avoid = bindings0.names_to_avoid
      }

  (** val imported_variables_in_order : t -> (variable * flambda_kind) list **)

  let imported_variables_in_order bindings0 =
    rev (compact bindings0.imported_variables)

  (** val existential_variables_in_order : t -> (variable * flambda_kind) list **)

  let existential_variables_in_order bindings0 =
    rev (compact bindings0.existential_variables)
end

module Joined_envs = struct
  type t =
    ( Index.t,
      Typing_env.t * (name, flambda_type) Keyed.finite_map )
    Keyed.finite_map

  (** val get_nth_joined_env : t -> Index.t -> Typing_env.t option **)

  let get_nth_joined_env envs index =
    option_map fst (Keyed.lookup Index.equal index envs)

  (** val keys : t -> Index.t list **)

  let keys envs = Keyed.domain Index.equal envs

  (** val exists_in_all_joined_envs : t -> (Index.t, 'a1) Keyed.finite_map ->
      bool **)

  let exists_in_all_joined_envs envs map0 =
    forallb (fun index -> Keyed.is_bound Index.equal index map0) (keys envs)

  (** val equal_in_bindings : t -> simple -> (Index.t * simple) list -> bool
      option **)

  let rec equal_in_bindings envs simple0 = function
    | [] -> Some true
    | p :: bindings1 -> (
      let index, canonical = p in
      if simple_equal canonical simple0
      then equal_in_bindings envs simple0 bindings1
      else
        match get_nth_joined_env envs index with
        | Some env ->
          if
            simple_equal canonical
              (Typing_env.get_canonical_simple_ignoring_name_mode env simple0)
          then equal_in_bindings envs simple0 bindings1
          else Some false
        | None -> None)

  (** val equal_in_all_joined_envs : t -> simple -> Simples_in_joined_envs.t ->
      bool option **)

  let equal_in_all_joined_envs envs simple0 simples_in_joined_envs =
    equal_in_bindings envs simple0
      (Keyed.compact Index.equal simples_in_joined_envs)

  (** val canonicals_of_alias_types : t -> (Index.t * flambda_type) list ->
      Simples_in_joined_envs.t option option **)

  let rec canonicals_of_alias_types envs = function
    | [] -> Some (Some [])
    | p :: types0 -> (
      let index, ty = p in
      match get_nth_joined_env envs index with
      | Some env -> (
        match canonicals_of_alias_types envs types0 with
        | Some canonicals ->
          Some
            (match get_alias_opt ty with
            | Some alias -> (
              match canonicals with
              | Some canonicals0 ->
                Some
                  (( index,
                     Typing_env.get_canonical_simple_ignoring_name_mode env
                       alias )
                  :: canonicals0)
              | None -> None)
            | None -> None)
        | None -> None)
      | None -> None)

  (** val get_alias_then_canonical_simple_ignoring_name_mode_exn : t ->
      (Index.t, flambda_type) Keyed.finite_map -> Simples_in_joined_envs.t
      option option **)

  let get_alias_then_canonical_simple_ignoring_name_mode_exn envs types =
    canonicals_of_alias_types envs (Keyed.compact Index.equal types)

  (** val types_of_simples : (const -> flambda_type) -> t -> flambda_kind ->
      (Index.t * simple) list -> (Index.t, flambda_type) Keyed.finite_map option
      **)

  let rec types_of_simples expand_const0 envs kind0 = function
    | [] -> Some []
    | p :: simples0 -> (
      let index, simple0 = p in
      match
        match simple0 with
        | Var var -> (
          match get_nth_joined_env envs index with
          | Some env -> Typing_env.find env (Name_var var) (Some kind0)
          | None -> None)
        | Symbol symbol -> (
          match get_nth_joined_env envs index with
          | Some env -> Typing_env.find env (Name_symbol symbol) (Some kind0)
          | None -> None)
        | Const const0 -> Some (expand_const0 const0)
      with
      | Some ty -> (
        match types_of_simples expand_const0 envs kind0 simples0 with
        | Some types -> Some ((index, ty) :: types)
        | None -> None)
      | None -> None)

  (** val find_simples_in_joined_envs : (const -> flambda_type) -> t ->
      Simples_in_joined_envs.t -> flambda_kind -> (Index.t, flambda_type)
      Keyed.finite_map option **)

  let find_simples_in_joined_envs expand_const0 envs simples kind0 =
    types_of_simples expand_const0 envs kind0
      (Keyed.compact Index.equal simples)

  (** val types_of_imported_var : (Index.t * (Typing_env.t * (name,
      flambda_type) Keyed.finite_map)) list -> variable -> flambda_kind ->
      (Index.t, flambda_type) Keyed.finite_map option **)

  let rec types_of_imported_var envs var kind0 =
    match envs with
    | [] -> Some []
    | p :: envs0 -> (
      let index, p0 = p in
      let env, _ = p0 in
      match types_of_imported_var envs0 var kind0 with
      | Some types ->
        if Typing_env.mem None env (Name_var var)
        then
          match Typing_env.find env (Name_var var) (Some kind0) with
          | Some ty -> Some ((index, ty) :: types)
          | None -> None
        else Some types
      | None -> None)

  (** val find_imported_var : t -> variable -> flambda_kind -> (Index.t,
      flambda_type) Keyed.finite_map option **)

  let find_imported_var envs var kind0 =
    types_of_imported_var (Keyed.compact Index.equal envs) var kind0

  (** val kind_of_var_in : (Index.t * (Typing_env.t * (name, flambda_type)
      Keyed.finite_map)) list -> variable -> flambda_kind option **)

  let rec kind_of_var_in envs var =
    match envs with
    | [] -> None
    | p :: envs0 -> (
      let _, p0 = p in
      let env, _ = p0 in
      match Typing_env.find env (Name_var var) None with
      | Some ty ->
        if Typing_env.mem None env (Name_var var)
        then Some (kind ty)
        else kind_of_var_in envs0 var
      | None -> kind_of_var_in envs0 var)

  (** val kind_of_imported_var : t -> variable -> flambda_kind option **)

  let kind_of_imported_var envs var =
    kind_of_var_in (Keyed.compact Index.equal envs) var

  (** val get_canonical_simples_ignoring_name_mode : t -> (Index.t * simple)
      list -> Simples_in_joined_envs.t option **)

  let get_canonical_simples_ignoring_name_mode envs simples =
    fold_left
      (fun acc binding ->
        match acc with
        | Some acc0 -> (
          match get_nth_joined_env envs (fst binding) with
          | Some env ->
            Some
              (( fst binding,
                 Typing_env.get_canonical_simple_ignoring_name_mode env
                   (snd binding) )
              :: acc0)
          | None -> None)
        | None -> None)
      simples (Some [])
end

module Aliases_of_existentials = struct
  type t = variable list finite_map

  (** val empty : t **)

  let empty = []

  (** val aliases_of_existential_var : t -> variable -> variable list **)

  let aliases_of_existential_var aliases var =
    match lookup var aliases with Some vars -> vars | None -> []

  (** val add : t -> variable -> variable -> t **)

  let add aliases demoted_var existential_var =
    let aliases_of_canonical_element =
      aliases_of_existential_var aliases existential_var
    in
    if among demoted_var aliases_of_canonical_element
    then aliases
    else
      (existential_var, demoted_var :: aliases_of_canonical_element) :: aliases
end

module Join_env = struct
  type parameters =
    { fresh : variable list -> variable;
      type_eqb : flambda_type -> flambda_type -> bool;
      env_extension_eqb : env_extension -> env_extension -> bool;
      expand_const : const -> flambda_type;
      join_depth : nat
    }

  (** val fresh : parameters -> variable list -> variable **)

  let fresh p = p.fresh

  (** val type_eqb : parameters -> flambda_type -> flambda_type -> bool **)

  let type_eqb p = p.type_eqb

  (** val env_extension_eqb : parameters -> env_extension -> env_extension ->
      bool **)

  let env_extension_eqb p = p.env_extension_eqb

  (** val expand_const : parameters -> const -> flambda_type **)

  let expand_const p = p.expand_const

  (** val join_depth : parameters -> nat **)

  let join_depth p = p.join_depth

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

  (** val joined_envs : t -> Joined_envs.t **)

  let joined_envs t0 = t0.joined_envs

  (** val types_in_target_env : t -> flambda_type finite_map **)

  let types_in_target_env t0 = t0.types_in_target_env

  (** val types_in_joined_envs : t -> (Index.t, flambda_type) Keyed.finite_map
      finite_map **)

  let types_in_joined_envs t0 = t0.types_in_joined_envs

  (** val aliases_of_existentials : t -> Aliases_of_existentials.t **)

  let aliases_of_existentials t0 = t0.aliases_of_existentials

  (** val imported_vars : t -> variable list **)

  let imported_vars t0 = t0.imported_vars

  (** val definitions_of_existentials : t -> (Simples_in_joined_envs.t *
      flambda_kind) finite_map **)

  let definitions_of_existentials t0 = t0.definitions_of_existentials

  (** val bindings : t -> Bindings_in_target_env.t **)

  let bindings t0 = t0.bindings

  (** val create : Joined_envs.t -> Bindings_in_target_env.t -> t **)

  let create joined_envs0 bindings0 =
    { joined_envs = joined_envs0;
      types_in_target_env = [];
      types_in_joined_envs = [];
      aliases_of_existentials = Aliases_of_existentials.empty;
      imported_vars = [];
      definitions_of_existentials = [];
      bindings = bindings0
    }

  (** val source_env : t -> Source_env.t **)

  let source_env env = env.bindings.Bindings_in_target_env.source_env

  (** val new_definitions_of_existentials : t -> t -> (Simples_in_joined_envs.t
      * flambda_kind) finite_map **)

  let new_definitions_of_existentials env since =
    filter_bindings
      (fun var _ -> negb (is_bound var since.definitions_of_existentials))
      env.definitions_of_existentials

  (** val new_equations_in_joined_envs : t -> t -> (Index.t, flambda_type)
      Keyed.finite_map finite_map **)

  let new_equations_in_joined_envs env since =
    filter_bindings
      (fun var _ -> negb (is_bound var since.types_in_joined_envs))
      env.types_in_joined_envs

  (** val existential_for_these_canonicals : parameters -> t ->
      Simples_in_joined_envs.t -> flambda_kind -> variable * t **)

  let existential_for_these_canonicals p env canonicals kind0 =
    let existential_var, bindings0 =
      Bindings_in_target_env.existential_for_these_simples p.fresh env.bindings
        canonicals kind0
    in
    let definitions_of_existentials0 =
      if is_bound existential_var env.definitions_of_existentials
      then env.definitions_of_existentials
      else
        (existential_var, (canonicals, kind0))
        :: env.definitions_of_existentials
    in
    ( existential_var,
      { joined_envs = env.joined_envs;
        types_in_target_env = env.types_in_target_env;
        types_in_joined_envs = env.types_in_joined_envs;
        aliases_of_existentials = env.aliases_of_existentials;
        imported_vars = env.imported_vars;
        definitions_of_existentials = definitions_of_existentials0;
        bindings = bindings0
      } )

  (** val add_alias_of_existential : parameters -> t -> flambda_kind -> variable
      -> Simples_in_joined_envs.t -> t **)

  let add_alias_of_existential p env kind0 var canonicals =
    let existential_var, env0 =
      existential_for_these_canonicals p env canonicals kind0
    in
    { joined_envs = env0.joined_envs;
      types_in_target_env = env0.types_in_target_env;
      types_in_joined_envs = env0.types_in_joined_envs;
      aliases_of_existentials =
        Aliases_of_existentials.add env0.aliases_of_existentials var
          existential_var;
      imported_vars = env0.imported_vars;
      definitions_of_existentials = env0.definitions_of_existentials;
      bindings = env0.bindings
    }

  (** val add_equation_in_target_env : t -> variable -> flambda_type -> t option
      **)

  let add_equation_in_target_env env var ty =
    if is_bound var env.types_in_target_env
    then None
    else
      Some
        { joined_envs = env.joined_envs;
          types_in_target_env = (var, ty) :: env.types_in_target_env;
          types_in_joined_envs = env.types_in_joined_envs;
          aliases_of_existentials = env.aliases_of_existentials;
          imported_vars = env.imported_vars;
          definitions_of_existentials = env.definitions_of_existentials;
          bindings = env.bindings
        }

  (** val add_equations_in_joined_envs : t -> variable -> (Index.t,
      flambda_type) Keyed.finite_map -> t **)

  let add_equations_in_joined_envs env var types =
    { joined_envs = env.joined_envs;
      types_in_target_env = env.types_in_target_env;
      types_in_joined_envs = (var, types) :: env.types_in_joined_envs;
      aliases_of_existentials = env.aliases_of_existentials;
      imported_vars = env.imported_vars;
      definitions_of_existentials = env.definitions_of_existentials;
      bindings = env.bindings
    }

  type canonical_in_target_env =
    | Canonical_in_source_env of simple
    | Import_from_all_joined_envs of variable
    | Existential_for_these_canonicals of Simples_in_joined_envs.t

  (** val n_way_join_canonical_simples : t -> Simples_in_joined_envs.t ->
      canonical_in_target_env option **)

  let n_way_join_canonical_simples env canonicals =
    match
      Source_env.candidate_canonical_in_source_env (source_env env) canonicals
    with
    | Some candidate0 -> (
      match candidate0 with
      | Source_env.Canonical_in_all_joined_envs simple0 -> (
        match simple0 with
        | Var var ->
          if Source_env.exists_in_source_env (source_env env) var
          then Some (Canonical_in_source_env simple0)
          else Some (Import_from_all_joined_envs var)
        | _ -> Some (Canonical_in_source_env simple0))
      | Source_env.Latest_bound_source_var var -> (
        match
          Joined_envs.equal_in_all_joined_envs env.joined_envs (Var var)
            canonicals
        with
        | Some equal0 ->
          Some
            (if equal0
             then Canonical_in_source_env (Var var)
             else Existential_for_these_canonicals canonicals)
        | None -> None)
      | _ -> Some (Existential_for_these_canonicals canonicals))
    | None -> None

  (** val import_type_transitive_with : (t -> variable -> t option) -> t ->
      flambda_type -> t option **)

  let import_type_transitive_with import_var env ty =
    fold_left
      (fun env0 var ->
        match env0 with Some env1 -> import_var env1 var | None -> None)
      (free_variables ty) (Some env)

  (** val add_equals_in_joined_envs_with : parameters -> (t -> variable -> t
      option) -> t -> flambda_kind -> variable -> Simples_in_joined_envs.t -> t
      option **)

  let add_equals_in_joined_envs_with p import_var env kind0 var simples =
    match n_way_join_canonical_simples env simples with
    | Some canonical -> (
      match canonical with
      | Canonical_in_source_env canonical0 ->
        add_equation_in_target_env env var (alias_type_of kind0 canonical0)
      | Import_from_all_joined_envs imported -> (
        match import_var env imported with
        | Some env0 ->
          add_equation_in_target_env env0 var
            (alias_type_of kind0 (Var imported))
        | None -> None)
      | Existential_for_these_canonicals canonicals ->
        Some (add_alias_of_existential p env kind0 var canonicals))
    | None -> None

  (** val import_or_delay_n_way_join_of_concrete_type_with : parameters -> (t ->
      variable -> t option) -> t -> variable -> (Index.t, flambda_type)
      Keyed.finite_map -> t option **)

  let import_or_delay_n_way_join_of_concrete_type_with p import_var env var
      types =
    match Index.choose types with
    | Some p0 ->
      let index, any_ty = p0 in
      if
        forallb
          (fun binding ->
            Index.equal (fst binding) index || p.type_eqb any_ty (snd binding))
          (Keyed.compact Index.equal types)
      then
        match add_equation_in_target_env env var any_ty with
        | Some env0 -> import_type_transitive_with import_var env0 any_ty
        | None -> None
      else Some (add_equations_in_joined_envs env var types)
    | None -> None

  (** val import_or_delay_n_way_join_type_with : parameters -> (t -> variable ->
      t option) -> t -> variable -> (Index.t, flambda_type) Keyed.finite_map ->
      t option **)

  let import_or_delay_n_way_join_type_with p import_var env var types =
    match Index.choose types with
    | Some p0 -> (
      let _, any_ty = p0 in
      match
        Joined_envs.get_alias_then_canonical_simple_ignoring_name_mode_exn
          env.joined_envs types
      with
      | Some canonical_simples -> (
        match canonical_simples with
        | Some canonical_simples0 ->
          add_equals_in_joined_envs_with p import_var env (kind any_ty) var
            canonical_simples0
        | None ->
          import_or_delay_n_way_join_of_concrete_type_with p import_var env var
            types)
      | None -> None)
    | None -> None

  (** val import_var_transitive_body : parameters -> (t -> variable -> t option)
      -> t -> variable -> t option **)

  let import_var_transitive_body p import_var env var =
    if Source_env.exists_in_source_env (source_env env) var
    then Some env
    else if among var env.imported_vars
    then Some env
    else
      match Joined_envs.kind_of_imported_var env.joined_envs var with
      | Some kind0 -> (
        let env0 =
          { joined_envs = env.joined_envs;
            types_in_target_env = env.types_in_target_env;
            types_in_joined_envs = env.types_in_joined_envs;
            aliases_of_existentials = env.aliases_of_existentials;
            imported_vars = var :: env.imported_vars;
            definitions_of_existentials = env.definitions_of_existentials;
            bindings =
              Bindings_in_target_env.import_from_all_envs env.bindings var kind0
          }
        in
        match Joined_envs.find_imported_var env0.joined_envs var kind0 with
        | Some types ->
          let has_alias_type =
            existsb
              (fun binding -> is_some (get_alias_opt (snd binding)))
              (Keyed.compact Index.equal types)
          in
          if has_alias_type
          then
            let alias_types =
              Keyed.map_values
                (fun ty ->
                  match get_alias_opt ty with
                  | Some _ -> ty
                  | None -> alias_type_of kind0 (Var var))
                types
            in
            match
              Joined_envs.get_alias_then_canonical_simple_ignoring_name_mode_exn
                env0.joined_envs alias_types
            with
            | Some canonical_simples -> (
              match canonical_simples with
              | Some canonical_simples0 ->
                add_equals_in_joined_envs_with p import_var env0 kind0 var
                  canonical_simples0
              | None -> None)
            | None -> None
          else
            import_or_delay_n_way_join_of_concrete_type_with p import_var env0
              var types
        | None -> None)
      | None -> None

  (** val import_var_transitive : parameters -> nat -> t -> variable -> t option
      **)

  let rec import_var_transitive p fuel env var =
    match fuel with
    | O -> None
    | S fuel0 ->
      import_var_transitive_body p (import_var_transitive p fuel0) env var

  (** val import_type_transitive : parameters -> nat -> t -> flambda_type -> t
      option **)

  let import_type_transitive p fuel env ty =
    import_type_transitive_with (import_var_transitive p fuel) env ty

  (** val import_or_delay_n_way_join_type : parameters -> nat -> t -> variable
      -> (Index.t, flambda_type) Keyed.finite_map -> t option **)

  let import_or_delay_n_way_join_type p fuel env var types =
    import_or_delay_n_way_join_type_with p
      (import_var_transitive p fuel)
      env var types

  (** val import_name_transitive : parameters -> nat -> t -> name -> t option **)

  let import_name_transitive p fuel env = function
    | Name_var var -> import_var_transitive p fuel env var
    | Name_symbol _ -> Some env

  (** val names_with_equations_everywhere : Joined_envs.t -> name list **)

  let names_with_equations_everywhere equations_to_join =
    match Keyed.compact Index.equal equations_to_join with
    | [] -> []
    | p :: others ->
      let _, p0 = p in
      let _, equations0 = p0 in
      filter
        (fun name0 ->
          forallb
            (fun other -> Keyed.is_bound name_eqb name0 (snd (snd other)))
            others)
        (Keyed.domain name_eqb equations0)

  (** val types_of_name_in_levels : Joined_envs.t -> name -> (Index.t,
      flambda_type) Keyed.finite_map **)

  let types_of_name_in_levels equations_to_join name0 =
    flat_map
      (fun binding ->
        match Keyed.lookup name_eqb name0 (snd (snd binding)) with
        | Some ty -> (fst binding, ty) :: []
        | None -> [])
      (Keyed.compact Index.equal equations_to_join)

  (** val join_aliases_into_bindings : parameters -> nat -> t -> Joined_envs.t
      -> t option **)

  let join_aliases_into_bindings p fuel env equations_to_join =
    let exists_in_target_env0 =
      Bindings_in_target_env.exists_in_target_env env.bindings
    in
    fold_left
      (fun env0 name0 ->
        match env0 with
        | Some env1 -> (
          match name0 with
          | Name_var var ->
            if exists_in_target_env0 var
            then
              import_or_delay_n_way_join_type p fuel env1 var
                (types_of_name_in_levels equations_to_join name0)
            else Some env1
          | Name_symbol _ -> Some env1)
        | None -> None)
      (names_with_equations_everywhere equations_to_join)
      (Some env)

  type inverse_relations = (Relation.t * name) list finite_map

  (** val add_to_inverse_relations : inverse_relations -> variable -> Relation.t
      -> name -> inverse_relations **)

  let add_to_inverse_relations relations var relation scrutinee =
    ( var,
      (relation, scrutinee)
      ::
      (match lookup var relations with
      | Some existing -> existing
      | None -> []) )
    :: relations

  (** val with_inverse_relation : head_of_kind_naked_immediate -> Relation.t ->
      name -> flambda_type **)

  let with_inverse_relation head relation scrutinee =
    Type_naked_immediate
      (Ok
         (No_alias
            { naked_immediates = head.naked_immediates;
              inverse_relations =
                (relation, scrutinee) :: head.inverse_relations
            }))

  (** val empty_naked_immediate_head : head_of_kind_naked_immediate **)

  let empty_naked_immediate_head =
    { naked_immediates = Or_unknown.Unknown; inverse_relations = [] }

  (** val add_or_replace_equation : env_extension -> name -> flambda_type ->
      env_extension **)

  let add_or_replace_equation extension name0 ty =
    let (Env_extension equations0) = extension in
    Env_extension ((name0, ty) :: Keyed.unbind name_eqb name0 equations0)

  (** val equations_of : env_extension -> (name, flambda_type) Keyed.finite_map
      **)

  let equations_of = function Env_extension equations0 -> equations0

  (** val add_inverse_relation_to_env_extension : nat -> name list ->
      env_extension -> name -> Relation.t -> name -> env_extension option **)

  let rec add_inverse_relation_to_env_extension fuel seen extension name0
      relation scrutinee =
    match Keyed.lookup name_eqb name0 (equations_of extension) with
    | Some existing_ty -> (
      match existing_ty with
      | Type_naked_immediate ty -> (
        match ty with
        | Unknown ->
          Some
            (add_or_replace_equation extension name0
               (with_inverse_relation empty_naked_immediate_head relation
                  scrutinee))
        | Ok a -> (
          match a with
          | No_alias head -> (
            match head.naked_immediates with
            | Or_unknown.Known a0 -> (
              match a0 with
              | [] -> None
              | _ :: _ ->
                Some
                  (add_or_replace_equation extension name0
                     (with_inverse_relation head relation scrutinee)))
            | Or_unknown.Unknown ->
              Some
                (add_or_replace_equation extension name0
                   (with_inverse_relation head relation scrutinee)))
          | Equals simple0 -> (
            match name_of_simple simple0 with
            | Some name' -> (
              match fuel with
              | O ->
                Some
                  (add_or_replace_equation extension name0
                     (with_inverse_relation empty_naked_immediate_head relation
                        scrutinee))
              | S fuel0 ->
                if Keyed.among name_eqb name' seen
                then
                  Some
                    (add_or_replace_equation extension name0
                       (with_inverse_relation empty_naked_immediate_head
                          relation scrutinee))
                else
                  add_inverse_relation_to_env_extension fuel0 (name0 :: seen)
                    extension name' relation scrutinee)
            | None -> Some extension))
        | Bottom -> Some extension)
      | _ -> None)
    | None ->
      Some
        (add_or_replace_equation extension name0
           (with_inverse_relation empty_naked_immediate_head relation scrutinee))

  (** val recover_inverse_relations : inverse_relations -> name -> flambda_type
      -> (flambda_type * inverse_relations) option **)

  let recover_inverse_relations relations name0 ty =
    match ty with
    | Type_value ty0 -> (
      match ty0 with
      | Ok a -> (
        match a with
        | No_alias h -> (
          let (Head_of_kind_value (non_null, is_null0)) = h in
          match non_null with
          | Ok head -> (
            match is_null0 with
            | Not_null -> (
              match head with
              | Variant
                  (is_int, immediates, get_tag, blocks, extensions, is_unique)
                -> (
                let no_immediates =
                  match immediates with
                  | Or_unknown.Known imm_ty -> is_obviously_bottom imm_ty
                  | Or_unknown.Unknown -> false
                in
                if no_immediates
                then
                  match get_tag with
                  | Some get_tag_var ->
                    Some
                      ( ty,
                        add_to_inverse_relations relations get_tag_var
                          Relation.Get_tag name0 )
                  | None -> (
                    let relations0 =
                      match is_int with
                      | Some is_int_var ->
                        add_to_inverse_relations relations is_int_var
                          Relation.Is_int name0
                      | None -> relations
                    in
                    match get_tag with
                    | Some get_tag_var -> (
                      match extensions with
                      | No_extensions -> (
                        match
                          add_inverse_relation_to_env_extension
                            (length (equations_of empty_env_extension))
                            [] empty_env_extension (Name_var get_tag_var)
                            Relation.Get_tag name0
                        with
                        | Some when_block ->
                          Some
                            ( Type_value
                                (Ok
                                   (No_alias
                                      (Head_of_kind_value
                                         ( Ok
                                             (Variant
                                                ( is_int,
                                                  immediates,
                                                  get_tag,
                                                  blocks,
                                                  Ext
                                                    ( empty_env_extension,
                                                      when_block ),
                                                  is_unique )),
                                           Not_null )))),
                              relations0 )
                        | None -> None)
                      | Ext (when_immediate, when_block) -> (
                        match
                          add_inverse_relation_to_env_extension
                            (length (equations_of when_block))
                            [] when_block (Name_var get_tag_var)
                            Relation.Get_tag name0
                        with
                        | Some when_block0 ->
                          Some
                            ( Type_value
                                (Ok
                                   (No_alias
                                      (Head_of_kind_value
                                         ( Ok
                                             (Variant
                                                ( is_int,
                                                  immediates,
                                                  get_tag,
                                                  blocks,
                                                  Ext
                                                    (when_immediate, when_block0),
                                                  is_unique )),
                                           Not_null )))),
                              relations0 )
                        | None -> None))
                    | None -> Some (ty, relations0))
                else
                  let relations0 =
                    match is_int with
                    | Some is_int_var ->
                      add_to_inverse_relations relations is_int_var
                        Relation.Is_int name0
                    | None -> relations
                  in
                  match get_tag with
                  | Some get_tag_var -> (
                    match extensions with
                    | No_extensions -> (
                      match
                        add_inverse_relation_to_env_extension
                          (length (equations_of empty_env_extension))
                          [] empty_env_extension (Name_var get_tag_var)
                          Relation.Get_tag name0
                      with
                      | Some when_block ->
                        Some
                          ( Type_value
                              (Ok
                                 (No_alias
                                    (Head_of_kind_value
                                       ( Ok
                                           (Variant
                                              ( is_int,
                                                immediates,
                                                get_tag,
                                                blocks,
                                                Ext
                                                  ( empty_env_extension,
                                                    when_block ),
                                                is_unique )),
                                         Not_null )))),
                            relations0 )
                      | None -> None)
                    | Ext (when_immediate, when_block) -> (
                      match
                        add_inverse_relation_to_env_extension
                          (length (equations_of when_block))
                          [] when_block (Name_var get_tag_var) Relation.Get_tag
                          name0
                      with
                      | Some when_block0 ->
                        Some
                          ( Type_value
                              (Ok
                                 (No_alias
                                    (Head_of_kind_value
                                       ( Ok
                                           (Variant
                                              ( is_int,
                                                immediates,
                                                get_tag,
                                                blocks,
                                                Ext (when_immediate, when_block0),
                                                is_unique )),
                                         Not_null )))),
                            relations0 )
                      | None -> None))
                  | None -> Some (ty, relations0))
              | _ -> Some (ty, relations))
            | Maybe_null is_null ->
              Some
                ( ty,
                  match is_null with
                  | Some is_null_var ->
                    add_to_inverse_relations relations is_null_var
                      Relation.Is_null name0
                  | None -> relations ))
          | _ -> (
            match is_null0 with
            | Not_null -> Some (ty, relations)
            | Maybe_null is_null ->
              Some
                ( ty,
                  match is_null with
                  | Some is_null_var ->
                    add_to_inverse_relations relations is_null_var
                      Relation.Is_null name0
                  | None -> relations )))
        | Equals _ -> Some (ty, relations))
      | _ -> Some (ty, relations))
    | _ -> Some (ty, relations)

  type n_way_join_type =
    t -> (Index.t * flambda_type) list -> (flambda_type Or_unknown.t * t) option

  type choices =
    { recover_relations_on :
        t -> variable -> (Index.t, flambda_type) Keyed.finite_map -> bool
    }

  (** val recover_relations_on : choices -> t -> variable -> (Index.t,
      flambda_type) Keyed.finite_map -> bool **)

  let recover_relations_on c = c.recover_relations_on

  (** val compiler_choices : choices **)

  let compiler_choices =
    { recover_relations_on =
        (fun env _ types ->
          Joined_envs.exists_in_all_joined_envs env.joined_envs types)
    }

  (** val stands_for : t -> Index.t -> variable -> simple option **)

  let stands_for env index var =
    match lookup var env.definitions_of_existentials with
    | Some p ->
      let simples, _ = p in
      Simples_in_joined_envs.find index simples
    | None -> Some (Var var)

  (** val has_alias_in_terms : Typing_env.t -> simple -> bool **)

  let has_alias_in_terms tenv simple0 =
    match
      Typing_env.get_canonical_simple_exn tenv (Some Name_mode.normal) None
        simple0
    with
    | Some o -> (
      match o with
      | Some canonical ->
        Typing_env.mem_simple (Some Name_mode.normal) tenv canonical
      | None -> false)
    | None -> false

  (** val in_terms_in_all_joined_envs : t -> variable -> bool **)

  let in_terms_in_all_joined_envs env var =
    forallb
      (fun index ->
        match Joined_envs.get_nth_joined_env env.joined_envs index with
        | Some tenv -> (
          match stands_for env index var with
          | Some simple0 -> has_alias_in_terms tenv simple0
          | None -> false)
        | None -> false)
      (Joined_envs.keys env.joined_envs)

  (** val repaired_choices : choices **)

  let repaired_choices =
    { recover_relations_on =
        (fun env var types ->
          Joined_envs.exists_in_all_joined_envs env.joined_envs types
          && in_terms_in_all_joined_envs env var)
    }

  (** val n_way_join_round : choices -> n_way_join_type -> t -> (Index.t,
      flambda_type) Keyed.finite_map finite_map -> inverse_relations ->
      (inverse_relations * t) option **)

  let n_way_join_round choices0 n_way_join_type0 env equations_to_join relations
      =
    fold_left
      (fun acc binding ->
        match acc with
        | Some y -> (
          let relations0, env0 = y in
          let var = fst binding in
          let types = snd binding in
          match n_way_join_type0 env0 (Index.bindings types) with
          | Some p -> (
            let joined, env1 = p in
            match joined with
            | Or_unknown.Known ty -> (
              match
                if choices0.recover_relations_on env1 var types
                then recover_inverse_relations relations0 (Name_var var) ty
                else Some (ty, relations0)
              with
              | Some p0 -> (
                let ty0, relations1 = p0 in
                match add_equation_in_target_env env1 var ty0 with
                | Some env2 -> Some (relations1, env2)
                | None -> None)
              | None -> None)
            | Or_unknown.Unknown -> Some (relations0, env1))
          | None -> None)
        | None -> None)
      (compact equations_to_join)
      (Some (relations, env))

  (** val n_way_join_delayed_equations : nat -> choices -> n_way_join_type -> t
      -> inverse_relations -> (Index.t, flambda_type) Keyed.finite_map
      finite_map -> (inverse_relations * t) option **)

  let rec n_way_join_delayed_equations fuel choices0 n_way_join_type0
      env_this_round relations equations_this_round =
    match fuel with
    | O -> None
    | S fuel0 -> (
      if Keyed.is_empty equations_this_round
      then Some (relations, env_this_round)
      else
        match
          n_way_join_round choices0 n_way_join_type0 env_this_round
            equations_this_round relations
        with
        | Some p ->
          let relations0, env_next_round = p in
          n_way_join_delayed_equations fuel0 choices0 n_way_join_type0
            env_next_round relations0
            (new_equations_in_joined_envs env_next_round env_this_round)
        | None -> None)

  (** val equations_of_existentials : parameters -> t -> (variable *
      (Simples_in_joined_envs.t * flambda_kind)) list -> (Index.t, flambda_type)
      Keyed.finite_map finite_map option **)

  let rec equations_of_existentials p env = function
    | [] -> Some []
    | p0 :: existentials0 -> (
      let var, p1 = p0 in
      let simples, kind0 = p1 in
      match
        Joined_envs.find_simples_in_joined_envs p.expand_const env.joined_envs
          simples kind0
      with
      | Some types -> (
        match equations_of_existentials p env existentials0 with
        | Some equations0 -> Some ((var, types) :: equations0)
        | None -> None)
      | None -> None)

  (** val n_way_join_loop : nat -> parameters -> nat -> choices ->
      n_way_join_type -> t -> inverse_relations -> (Simples_in_joined_envs.t *
      flambda_kind) finite_map -> (inverse_relations * t) option **)

  let rec n_way_join_loop depth_left p fuel choices0 n_way_join_type0
      env_this_round relations existentials_this_round =
    match depth_left with
    | O -> Some (relations, env_this_round)
    | S depth_left0 -> (
      if Keyed.is_empty existentials_this_round
      then Some (relations, env_this_round)
      else
        match
          equations_of_existentials p env_this_round
            (compact existentials_this_round)
        with
        | Some equations_in_joined_envs -> (
          match
            n_way_join_delayed_equations fuel choices0 n_way_join_type0
              env_this_round relations equations_in_joined_envs
          with
          | Some p0 ->
            let relations0, env_next_round = p0 in
            n_way_join_loop depth_left0 p fuel choices0 n_way_join_type0
              env_next_round relations0
              (new_definitions_of_existentials env_next_round env_this_round)
          | None -> None)
        | None -> None)

  (** val joined_env : t -> Index.t -> Typing_env.t option **)

  let joined_env env index =
    Joined_envs.get_nth_joined_env env.joined_envs index

  (** val import_type : parameters -> nat -> t -> flambda_type -> t option **)

  let import_type = import_type_transitive

  (** val n_way_join_simples : parameters -> nat -> t -> flambda_kind ->
      (Index.t * simple) list -> (simple Or_bottom.t * t) option **)

  let n_way_join_simples p fuel env kind0 simples =
    match simples with
    | [] -> Some (Or_bottom.Bottom, env)
    | _ :: _ -> (
      match
        Joined_envs.get_canonical_simples_ignoring_name_mode env.joined_envs
          simples
      with
      | Some canonicals -> (
        match n_way_join_canonical_simples env canonicals with
        | Some canonical -> (
          match canonical with
          | Canonical_in_source_env simple0 -> Some (Or_bottom.Ok simple0, env)
          | Import_from_all_joined_envs var -> (
            match import_var_transitive p fuel env var with
            | Some env0 -> Some (Or_bottom.Ok (Var var), env0)
            | None -> None)
          | Existential_for_these_canonicals canonicals0 ->
            let var, env0 =
              existential_for_these_canonicals p env canonicals0 kind0
            in
            Some (Or_bottom.Ok (Var var), env0))
        | None -> None)
      | None -> None)

  (** val n_way_join_env_extension : parameters -> nat -> t -> (Index.t *
      env_extension) list -> (env_extension * t) Or_bottom.t option **)

  let n_way_join_env_extension p fuel env = function
    | [] -> Some Or_bottom.Bottom
    | p0 :: other_extensions ->
      let _, first_extension = p0 in
      if
        forallb
          (fun binding -> p.env_extension_eqb (snd binding) first_extension)
          other_extensions
      then
        match
          fold_left
            (fun env0 equation ->
              match env0 with
              | Some env1 -> (
                match import_name_transitive p fuel env1 (fst equation) with
                | Some env2 -> import_type_transitive p fuel env2 (snd equation)
                | None -> None)
              | None -> None)
            (equations_of first_extension)
            (Some env)
        with
        | Some env0 -> Some (Or_bottom.Ok (first_extension, env0))
        | None -> None
      else Some (Or_bottom.Ok (empty_env_extension, env))

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

  (** val create_meet_env : ('a1, 'a2) meet_env_functions -> Typing_env.t -> 'a1
      **)

  let create_meet_env m = m.create_meet_env

  (** val current_typing_env : ('a1, 'a2) meet_env_functions -> 'a1 ->
      Typing_env.t **)

  let current_typing_env m = m.current_typing_env

  (** val add_variable_definition : ('a1, 'a2) meet_env_functions -> 'a1 ->
      variable -> flambda_kind -> Name_mode.t -> 'a1 **)

  let add_variable_definition m = m.add_variable_definition

  (** val add_env_extension : ('a1, 'a2) meet_env_functions -> 'a1 ->
      env_extension -> 'a2 -> 'a1 option **)

  let add_env_extension m = m.add_env_extension

  (** val make_bottom : ('a1, 'a2) meet_env_functions -> 'a1 -> 'a1 **)

  let make_bottom m = m.make_bottom

  (** val final_typing_env : ('a1, 'a2) meet_env_functions -> 'a1 ->
      Typing_env.t **)

  let final_typing_env m = m.final_typing_env

  (** val names_to_avoid : ('a1, 'a2) meet_env_functions -> 'a1 -> variable list
      **)

  let names_to_avoid m = m.names_to_avoid

  (** val with_names_to_avoid : ('a1, 'a2) meet_env_functions -> 'a1 -> variable
      list -> 'a1 **)

  let with_names_to_avoid m = m.with_names_to_avoid

  (** val move_definition : (Simples_in_joined_envs.t * flambda_kind) finite_map
      -> variable -> variable -> (Simples_in_joined_envs.t * flambda_kind)
      finite_map **)

  let move_definition definitions from to_ =
    match lookup from definitions with
    | Some defn -> (to_, defn) :: unbind from definitions
    | None -> definitions

  (** val move_equation : flambda_type finite_map -> variable -> variable ->
      flambda_type finite_map option **)

  let move_equation equations0 from to_ =
    if is_bound to_ equations0
    then None
    else
      match lookup from equations0 with
      | Some ty -> Some ((to_, ty) :: unbind from equations0)
      | None -> Some equations0

  (** val move_inverse_relation : inverse_relations -> variable -> variable ->
      inverse_relations **)

  let move_inverse_relation relations from to_ =
    match lookup from relations with
    | Some names ->
      let relations0 = unbind from relations in
      ( to_,
        app names
          (match lookup to_ relations0 with
          | Some existing -> existing
          | None -> []) )
      :: relations0
    | None -> relations

  (** val in_inverse_relations : inverse_relations -> variable -> bool **)

  let in_inverse_relations relations var =
    is_bound var relations
    || existsb
         (fun binding ->
           existsb
             (fun pair -> name_eqb (snd pair) (Name_var var))
             (snd binding))
         (compact relations)

  (** val count_occurrences : variable -> variable list -> nat **)

  let count_occurrences var vars = length (filter (Pos.eqb var) vars)

  (** val earliest_bound : Typing_env.t -> variable -> variable list -> variable
      option **)

  let rec earliest_bound tenv best = function
    | [] -> Some best
    | var :: candidates0 -> (
      match Typing_env.binding_time_and_mode tenv (Name_var var) with
      | Some time -> (
        match Typing_env.binding_time_and_mode tenv (Name_var best) with
        | Some best_time ->
          earliest_bound tenv
            (if
               Binding_time.strictly_earlier
                 time.Binding_time.With_name_mode.binding_time
                 best_time.Binding_time.With_name_mode.binding_time
             then var
             else best)
            candidates0
        | None -> None)
      | None -> None)

  (** val choose_alias : Typing_env.t -> variable list -> variable option option
      **)

  let choose_alias tenv = function
    | [] -> Some None
    | var :: aliases0 ->
      option_map (fun x -> Some x) (earliest_bound tenv var aliases0)

  (** val expand_variable : nat -> flambda_type finite_map -> variable ->
      flambda_type option **)

  let rec expand_variable fuel to_expand var =
    match fuel with
    | O -> None
    | S fuel0 -> (
      match lookup var to_expand with
      | Some ty -> (
        match get_alias_opt ty with
        | Some s -> (
          match s with
          | Var var' ->
            if among var' (domain to_expand)
            then expand_variable fuel0 to_expand var'
            else Some ty
          | _ -> Some ty)
        | None ->
          project_variables_out (domain to_expand)
            (expand_variable fuel0 to_expand)
            ty)
      | None -> None)

  (** val define_or_eliminate_variables_and_add_equations : ('a1, 'a2)
      meet_env_functions -> nat -> 'a2 -> t -> 'a1 -> inverse_relations -> ('a1
      * (Simples_in_joined_envs.t * flambda_kind) finite_map) option **)

  let define_or_eliminate_variables_and_add_equations ops fuel
      meet_expanded_head_fn env source_env0 relations =
    let target_env =
      fold_left
        (fun target_env binding ->
          ops.add_variable_definition target_env (fst binding) (snd binding)
            Name_mode.in_types)
        (Bindings_in_target_env.imported_variables_in_order env.bindings)
        source_env0
    in
    let equations0 = env.types_in_target_env in
    let free_vars_in_equations =
      flat_map
        (fun binding -> free_variables (snd binding))
        (compact equations0)
    in
    let unique_occurrence_is_in_equations =
     fun var ->
      negb (in_inverse_relations relations var)
      && Nat.leb (count_occurrences var free_vars_in_equations) (S O)
    in
    let tenv_of_aliases = ops.current_typing_env target_env in
    match
      fold_left
        (fun acc binding ->
          match acc with
          | Some y -> (
            let y0, definitions = y in
            let y1, relations0 = y0 in
            let y2, equations1 = y1 in
            let target_env0, to_expand = y2 in
            let var = fst binding in
            let var_kind = snd binding in
            let aliases_of_var =
              Aliases_of_existentials.aliases_of_existential_var
                env.aliases_of_existentials var
            in
            match choose_alias tenv_of_aliases aliases_of_var with
            | Some canon -> (
              match canon with
              | Some canon_var -> (
                let demoted_aliases =
                  filter
                    (fun alias -> negb (Pos.eqb alias canon_var))
                    aliases_of_var
                in
                let definitions0 = move_definition definitions var canon_var in
                match move_equation equations1 var canon_var with
                | Some equations2 ->
                  let relations1 =
                    move_inverse_relation relations0 var canon_var
                  in
                  let ty = alias_type_of var_kind (Var canon_var) in
                  let equations3 =
                    fold_left
                      (fun equations3 alias -> (alias, ty) :: equations3)
                      demoted_aliases equations2
                  in
                  Some
                    ( ( ((target_env0, (var, ty) :: to_expand), equations3),
                        relations1 ),
                      definitions0 )
                | None -> None)
              | None ->
                if unique_occurrence_is_in_equations var
                then
                  let ty =
                    match lookup var equations1 with
                    | Some ty -> ty
                    | None -> unknown var_kind
                  in
                  Some
                    ( ( ( (target_env0, (var, ty) :: to_expand),
                          unbind var equations1 ),
                        relations0 ),
                      unbind var definitions )
                else
                  Some
                    ( ( ( ( ops.add_variable_definition target_env0 var var_kind
                              Name_mode.in_types,
                            to_expand ),
                          equations1 ),
                        relations0 ),
                      definitions ))
            | None -> None)
          | None -> None)
        (Bindings_in_target_env.existential_variables_in_order env.bindings)
        (Some
           ( (((target_env, []), equations0), relations),
             env.definitions_of_existentials ))
    with
    | Some p -> (
      let p0, definitions = p in
      let p1, relations0 = p0 in
      let p2, equations1 = p1 in
      let target_env0, to_expand = p2 in
      let to_project = domain to_expand in
      let expand = expand_variable fuel to_expand in
      match
        traverse
          (fun binding ->
            match project_variables_out to_project expand (snd binding) with
            | Some ty -> Some (Name_var (fst binding), ty)
            | None -> None)
          (compact equations1)
      with
      | Some equations2 -> (
        match
          traverse
            (fun binding ->
              match
                project_variables_out to_project expand
                  (Type_naked_immediate
                     (Ok
                        (No_alias
                           { naked_immediates = Or_unknown.Unknown;
                             inverse_relations = snd binding
                           })))
              with
              | Some ty -> Some (Name_var (fst binding), ty)
              | None -> None)
            (compact relations0)
        with
        | Some equations_for_inverse_relations -> (
          match
            ops.add_env_extension target_env0 (Env_extension equations2)
              meet_expanded_head_fn
          with
          | Some target_env1 -> (
            match
              ops.add_env_extension target_env1
                (Env_extension equations_for_inverse_relations)
                meet_expanded_head_fn
            with
            | Some target_env2 -> Some (target_env2, definitions)
            | None -> None)
          | None -> None)
        | None -> None)
      | None -> None)
    | None -> None

  (** val cut_for_joins : Scope.t -> (Index.t * Typing_env.t) list ->
      Joined_envs.t option **)

  let rec cut_for_joins cut_after = function
    | [] -> Some []
    | p :: envs0 -> (
      let index, tenv = p in
      match cut_for_joins cut_after envs0 with
      | Some rest -> (
        if tenv.Typing_env.is_bottom
        then Some rest
        else
          match Typing_env.cut tenv cut_after with
          | Some level ->
            Some ((index, (tenv, level.Typing_env_level.equations)) :: rest)
          | None -> None)
      | None -> None)

  (** val cut_and_n_way_join0 : ('a1, 'a2) meet_env_functions -> parameters ->
      nat -> choices -> n_way_join_type -> 'a2 -> variable list -> 'a1 ->
      Typing_env.t -> Joined_envs.t -> (('a1 * (Simples_in_joined_envs.t *
      flambda_kind) finite_map) * variable list) option **)

  let cut_and_n_way_join0 ops p fuel choices0 n_way_join_type0
      meet_expanded_head_fn avoid source_env0 source_tenv equations_to_join =
    if Keyed.is_empty equations_to_join
    then Some ((ops.make_bottom source_env0, []), avoid)
    else
      let empty_bindings =
        Bindings_in_target_env.from_source_env avoid source_tenv
      in
      let empty_env = create equations_to_join empty_bindings in
      match join_aliases_into_bindings p fuel empty_env equations_to_join with
      | Some env -> (
        match
          n_way_join_delayed_equations fuel choices0 n_way_join_type0 env []
            (new_equations_in_joined_envs env empty_env)
        with
        | Some p0 -> (
          let relations, env0 = p0 in
          match
            n_way_join_loop p.join_depth p fuel choices0 n_way_join_type0 env0
              relations
              (new_definitions_of_existentials env0 empty_env)
          with
          | Some p1 -> (
            let relations0, env1 = p1 in
            let names = env1.bindings.Bindings_in_target_env.names_to_avoid in
            match
              define_or_eliminate_variables_and_add_equations ops fuel
                meet_expanded_head_fn env1
                (ops.with_names_to_avoid source_env0 names)
                relations0
            with
            | Some p2 -> Some (p2, names)
            | None -> None)
          | None -> None)
        | None -> None)
      | None -> None

  (** val variables_of_env : Typing_env.t -> variable list **)

  let variables_of_env tenv =
    flat_map
      (fun binding ->
        match fst binding with Name_var var -> var :: [] | Name_symbol _ -> [])
      (Typing_env.names_to_types tenv)

  (** val cut_and_n_way_join : ('a1, 'a2) meet_env_functions -> parameters ->
      nat -> choices -> n_way_join_type -> 'a2 -> Scope.t -> 'a1 -> Typing_env.t
      -> Typing_env.t list -> 'a1 option **)

  let cut_and_n_way_join ops p fuel choices0 n_way_join_type0
      meet_expanded_head_fn cut_after source_env0 source_tenv joined_envs0 =
    match cut_for_joins cut_after (Index.number joined_envs0) with
    | Some equations_to_join -> (
      let avoid =
        app
          (ops.names_to_avoid source_env0)
          (app
             (variables_of_env source_tenv)
             (flat_map variables_of_env joined_envs0))
      in
      match
        cut_and_n_way_join0 ops p fuel choices0 n_way_join_type0
          meet_expanded_head_fn avoid source_env0 source_tenv equations_to_join
      with
      | Some p0 ->
        let p1, _ = p0 in
        let target_env, _ = p1 in
        Some target_env
      | None -> None)
    | None -> None
end

module Analysis = struct
  type 'a t =
    { definitions_in_joined_envs :
        (Simples_in_joined_envs.t * flambda_kind) finite_map;
      canonical_definitions_at_normal_mode :
        (Simples_in_joined_envs.t * flambda_kind) finite_map;
      external_ids : (Index.t, 'a) Keyed.finite_map
    }

  (** val definitions_in_joined_envs : 'a1 t -> (Simples_in_joined_envs.t *
      flambda_kind) finite_map **)

  let definitions_in_joined_envs t0 = t0.definitions_in_joined_envs

  (** val canonical_definitions_at_normal_mode : 'a1 t ->
      (Simples_in_joined_envs.t * flambda_kind) finite_map **)

  let canonical_definitions_at_normal_mode t0 =
    t0.canonical_definitions_at_normal_mode

  (** val value_at_use : simple -> const Or_unknown.t **)

  let value_at_use = function
    | Const const0 -> Or_unknown.Known const0
    | _ -> Or_unknown.Unknown

  (** val values_of_bindings : (Index.t, 'a1) Keyed.finite_map -> (Index.t *
      simple) list -> ('a1 * const Or_unknown.t) list option **)

  let rec values_of_bindings external_ids0 = function
    | [] -> Some []
    | p :: canonicals_in_joined_envs0 -> (
      let index, simple0 = p in
      match Keyed.lookup Index.equal index external_ids0 with
      | Some external_id -> (
        match values_of_bindings external_ids0 canonicals_in_joined_envs0 with
        | Some values -> Some ((external_id, value_at_use simple0) :: values)
        | None -> None)
      | None -> None)

  (** val values_at_uses : (Index.t, 'a1) Keyed.finite_map ->
      Simples_in_joined_envs.t -> ('a1 * const Or_unknown.t) list option **)

  let values_at_uses external_ids0 canonicals_in_joined_envs =
    values_of_bindings external_ids0
      (Keyed.compact Index.equal canonicals_in_joined_envs)

  type simple_refined_at_join =
    | Not_refined_at_join
    | Invariant_in_all_uses of simple
    | Variable_refined_at_these_uses of Simples_in_joined_envs.t * flambda_kind

  (** val simple_refined_at_join_of : 'a1 t -> Typing_env.t -> simple ->
      simple_refined_at_join **)

  let simple_refined_at_join_of analysis env simple0 =
    match Typing_env.get_canonical_simple_ignoring_name_mode env simple0 with
    | Var var -> (
      match lookup var analysis.definitions_in_joined_envs with
      | Some p ->
        let canonicals_in_joined_envs, kind0 = p in
        Variable_refined_at_these_uses (canonicals_in_joined_envs, kind0)
      | None -> Not_refined_at_join)
    | x -> Invariant_in_all_uses x

  (** val definitions_of_bindings : (Index.t, 'a1) Keyed.finite_map -> (Index.t
      * simple) list -> ('a1 * simple) list option **)

  let rec definitions_of_bindings external_ids0 = function
    | [] -> Some []
    | p :: canonicals_in_joined_envs0 -> (
      let index, simple0 = p in
      match Keyed.lookup Index.equal index external_ids0 with
      | Some external_id -> (
        match
          definitions_of_bindings external_ids0 canonicals_in_joined_envs0
        with
        | Some definitions -> Some ((external_id, simple0) :: definitions)
        | None -> None)
      | None -> None)

  (** val definitions_at_uses : (Index.t, 'a1) Keyed.finite_map ->
      Simples_in_joined_envs.t -> ('a1 * simple) list option **)

  let definitions_at_uses external_ids0 canonicals_in_joined_envs =
    definitions_of_bindings external_ids0
      (Keyed.compact Index.equal canonicals_in_joined_envs)

  (** val variables_created_at_join : 'a1 t -> ((variable *
      Simples_in_joined_envs.t) * flambda_kind) list **)

  let variables_created_at_join analysis =
    map
      (fun binding -> (fst binding, fst (snd binding)), snd (snd binding))
      (compact analysis.canonical_definitions_at_normal_mode)

  (** val simples_at_normal_mode : Joined_envs.t -> (Index.t * simple) list ->
      Simples_in_joined_envs.t option option **)

  let rec simples_at_normal_mode joined_envs0 = function
    | [] -> Some (Some [])
    | p :: simples0 -> (
      let index, simple0 = p in
      match Joined_envs.get_nth_joined_env joined_envs0 index with
      | Some typing_env -> (
        match
          Typing_env.get_canonical_simple_exn typing_env (Some Name_mode.normal)
            None simple0
        with
        | Some canonical -> (
          match simples_at_normal_mode joined_envs0 simples0 with
          | Some rest ->
            Some
              (match canonical with
              | Some canonical0 -> (
                match rest with
                | Some rest0 -> Some ((index, canonical0) :: rest0)
                | None -> None)
              | None -> None)
          | None -> None)
        | None -> None)
      | None -> None)

  (** val definitions_at_normal_mode : Joined_envs.t -> (variable *
      (Simples_in_joined_envs.t * flambda_kind)) list ->
      (Simples_in_joined_envs.t * flambda_kind) finite_map option **)

  let rec definitions_at_normal_mode joined_envs0 = function
    | [] -> Some []
    | p :: definitions0 -> (
      let var, p0 = p in
      let simples, kind0 = p0 in
      match
        simples_at_normal_mode joined_envs0 (Keyed.compact Index.equal simples)
      with
      | Some at_normal_mode -> (
        match definitions_at_normal_mode joined_envs0 definitions0 with
        | Some rest ->
          Some
            (match at_normal_mode with
            | Some simples0 -> (var, (simples0, kind0)) :: rest
            | None -> rest)
        | None -> None)
      | None -> None)

  (** val create : (Index.t, 'a1) Keyed.finite_map -> Joined_envs.t ->
      (Simples_in_joined_envs.t * flambda_kind) finite_map -> 'a1 t option **)

  let create external_ids0 joined_envs0 definitions_in_joined_envs0 =
    match
      definitions_at_normal_mode joined_envs0
        (compact definitions_in_joined_envs0)
    with
    | Some canonical_definitions_at_normal_mode0 ->
      Some
        { definitions_in_joined_envs = definitions_in_joined_envs0;
          canonical_definitions_at_normal_mode =
            canonical_definitions_at_normal_mode0;
          external_ids = external_ids0
        }
    | None -> None
end

(** val cut_and_n_way_join_with_analysis : ('a2, 'a3)
    Join_env.meet_env_functions -> Join_env.parameters -> nat ->
    Join_env.choices -> Join_env.n_way_join_type -> 'a3 -> variable list ->
    Scope.t -> Typing_env.t -> ('a1 * Typing_env.t) list -> (Typing_env.t * 'a1
    Analysis.t) option **)

let cut_and_n_way_join_with_analysis ops p fuel choices0 n_way_join_type0
    meet_expanded_head_fn avoid cut_after source_tenv joined_envs0 =
  let numbered = Index.number joined_envs0 in
  let external_ids0 =
    flat_map
      (fun binding ->
        if (snd (snd binding)).Typing_env.is_bottom
        then []
        else (fst binding, fst (snd binding)) :: [])
      numbered
  in
  match
    Join_env.cut_for_joins cut_after
      (map (fun binding -> fst binding, snd (snd binding)) numbered)
  with
  | Some equations_to_join -> (
    let source_env0 = ops.Join_env.create_meet_env source_tenv in
    match
      Join_env.cut_and_n_way_join0 ops p fuel choices0 n_way_join_type0
        meet_expanded_head_fn avoid source_env0 source_tenv equations_to_join
    with
    | Some p0 -> (
      let p1, _ = p0 in
      let target_env, definitions = p1 in
      let target_env0 = ops.Join_env.final_typing_env target_env in
      match Analysis.create external_ids0 equations_to_join definitions with
      | Some join_analysis -> Some (target_env0, join_analysis)
      | None -> None)
    | None -> None)
  | None -> None
