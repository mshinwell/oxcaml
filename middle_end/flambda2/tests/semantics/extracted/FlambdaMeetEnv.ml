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

(** val extract_value : 'a1 meet_return_value -> 'a1 -> 'a1 -> 'a1 **)

let extract_value res left right =
  match res with Right_input -> right | New_result value -> value | _ -> left

module Meet_env_type = struct
  type t =
    { typing_env : Typing_env.t;
      adding_equations_for_names : name list;
      names_to_avoid : variable list
    }
end

module Meet_result = struct
  type 'a t =
    | Bottom of unit meet_return_value
    | Ok of 'a meet_return_value * Meet_env_type.t
end

type meet_expanded_head =
  Meet_env_type.t ->
  Expanded_type.t ->
  Expanded_type.t ->
  Expanded_type.t Meet_result.t option

(** val map_result : ('a1 -> 'a2) -> 'a1 Meet_result.t -> 'a2 Meet_result.t **)

let map_result f = function
  | Meet_result.Bottom r -> Meet_result.Bottom r
  | Meet_result.Ok (r, env) -> (
    match r with
    | Left_input -> Meet_result.Ok (Left_input, env)
    | Right_input -> Meet_result.Ok (Right_input, env)
    | Both_inputs -> Meet_result.Ok (Both_inputs, env)
    | New_result x -> Meet_result.Ok (New_result (f x), env))

module Meet_env = struct
  type t = Meet_env_type.t =
    { typing_env : Typing_env.t;
      adding_equations_for_names : name list;
      names_to_avoid : variable list
    }

  (** val typing_env : t -> Typing_env.t **)

  let typing_env t0 = t0.typing_env

  (** val adding_equations_for_names : t -> name list **)

  let adding_equations_for_names t0 = t0.adding_equations_for_names

  (** val names_to_avoid : t -> variable list **)

  let names_to_avoid t0 = t0.names_to_avoid

  (** val create : Typing_env.t -> t **)

  let create typing_env0 =
    { typing_env = typing_env0;
      adding_equations_for_names = [];
      names_to_avoid = []
    }

  (** val with_typing_env : t -> Typing_env.t -> t **)

  let with_typing_env env typing_env0 =
    { typing_env = typing_env0;
      adding_equations_for_names = env.adding_equations_for_names;
      names_to_avoid = env.names_to_avoid
    }

  (** val map_typing_env : t -> (Typing_env.t -> Typing_env.t) -> t **)

  let map_typing_env env f = with_typing_env env (f env.typing_env)

  (** val with_names_to_avoid : t -> variable list -> t **)

  let with_names_to_avoid env names =
    { typing_env = env.typing_env;
      adding_equations_for_names = env.adding_equations_for_names;
      names_to_avoid = names
    }

  (** val current_typing_env : t -> Typing_env.t **)

  let current_typing_env env = env.typing_env

  (** val make_bottom : t -> t **)

  let make_bottom env = map_typing_env env Typing_env.make_bottom

  (** val replace_concrete_equation : Typing_env.t -> name -> flambda_type ->
      Typing_env.t option **)

  let replace_concrete_equation tenv name0 ty =
    match must_be_singleton ty with
    | Some singleton -> (
      match singleton with
      | Some const0 -> (
        match
          Aliases.canonical (Typing_env.aliases tenv) (simple_of_name name0)
        with
        | Aliases.Is_canonical -> (
          match
            Typing_env.add_alias tenv (simple_of_name name0) (Const const0)
          with
          | Some result -> (
            match result with
            | Ok result0 ->
              if
                name_eqb result0.Typing_env.demoted_name name0
                && simple_equal result0.Typing_env.canonical_element
                     (Const const0)
              then
                Some
                  (Typing_env.replace_equation
                     result0.Typing_env.add_alias_result_t
                     result0.Typing_env.demoted_name
                     (alias_type_of (kind_of_const const0)
                        result0.Typing_env.canonical_element))
              else None
            | _ -> None)
          | None -> None)
        | Aliases.Alias_of_canonical _ -> None)
      | None -> (
        match get_alias_opt ty with
        | Some _ -> None
        | None -> Some (Typing_env.replace_equation tenv name0 ty)))
    | None -> None

  (** val add_concrete_equation_on_canonical_name : bool -> t -> name ->
      Expanded_type.t -> meet_expanded_head -> t Or_bottom.t option **)

  let add_concrete_equation_on_canonical_name raise_on_bottom env name0 ty
      meet_expanded_head0 =
    let kind0 = ty.Expanded_type.kind in
    match Typing_env.find env.typing_env name0 (Some kind0) with
    | Some existing_ty_of_name -> (
      match Expanded_type.of_non_alias_type existing_ty_of_name with
      | Some existing_ty -> (
        match meet_expanded_head0 env ty existing_ty with
        | Some result -> (
          match result with
          | Meet_result.Bottom _ ->
            if raise_on_bottom
            then Some Or_bottom.Bottom
            else
              Some
                (Or_bottom.Ok
                   (map_typing_env env (fun tenv ->
                        Typing_env.replace_equation tenv name0 (bottom kind0))))
          | Meet_result.Ok (r, env0) -> (
            match r with
            | Left_input -> (
              match
                replace_concrete_equation env0.typing_env name0
                  (Expanded_type.to_type ty)
              with
              | Some tenv -> Some (Or_bottom.Ok (with_typing_env env0 tenv))
              | None -> None)
            | New_result ty' -> (
              match
                replace_concrete_equation env0.typing_env name0
                  (Expanded_type.to_type ty')
              with
              | Some tenv -> Some (Or_bottom.Ok (with_typing_env env0 tenv))
              | None -> None)
            | _ -> Some (Or_bottom.Ok env0)))
        | None -> None)
      | None -> None)
    | None -> None

  (** val adding_equation_for_name : t -> name -> (t -> t Or_bottom.t option) ->
      t Or_bottom.t option **)

  let adding_equation_for_name env name0 f =
    let adding_equations_for_names0 = env.adding_equations_for_names in
    let env0 =
      { typing_env = env.typing_env;
        adding_equations_for_names = name0 :: adding_equations_for_names0;
        names_to_avoid = env.names_to_avoid
      }
    in
    match f env0 with
    | Some result -> (
      match result with
      | Or_bottom.Ok env1 ->
        Some
          (Or_bottom.Ok
             { typing_env = env1.typing_env;
               adding_equations_for_names = adding_equations_for_names0;
               names_to_avoid = env1.names_to_avoid
             })
      | Or_bottom.Bottom -> Some Or_bottom.Bottom)
    | None -> None

  (** val add_or_delay_concrete_equation_on_canonical_name : bool -> t -> name
      -> Expanded_type.t -> meet_expanded_head -> t Or_bottom.t option **)

  let add_or_delay_concrete_equation_on_canonical_name raise_on_bottom env name0
      ty meet_expanded_head0 =
    if Keyed.among name_eqb name0 env.adding_equations_for_names
    then Some (Or_bottom.Ok env)
    else
      adding_equation_for_name env name0 (fun env0 ->
          add_concrete_equation_on_canonical_name raise_on_bottom env0 name0 ty
            meet_expanded_head0)

  (** val add_concrete_equation_on_const : bool -> t -> const -> Expanded_type.t
      -> meet_expanded_head -> t Or_bottom.t option **)

  let add_concrete_equation_on_const raise_on_bottom env const0 ty
      meet_expanded_head0 =
    match meet_expanded_head0 env ty (Expanded_type.create_const const0) with
    | Some result -> (
      match result with
      | Meet_result.Bottom _ ->
        if raise_on_bottom
        then Some Or_bottom.Bottom
        else Some (Or_bottom.Ok env)
      | Meet_result.Ok (_, env0) -> Some (Or_bottom.Ok env0))
    | None -> None

  (** val add_or_delay_concrete_equation_on_canonical : bool -> t -> simple ->
      Expanded_type.t -> meet_expanded_head -> t Or_bottom.t option **)

  let add_or_delay_concrete_equation_on_canonical raise_on_bottom env simple0 ty
      meet_expanded_head0 =
    match simple0 with
    | Var x ->
      add_or_delay_concrete_equation_on_canonical_name raise_on_bottom env
        (Name_var x) ty meet_expanded_head0
    | Symbol s ->
      add_or_delay_concrete_equation_on_canonical_name raise_on_bottom env
        (Name_symbol s) ty meet_expanded_head0
    | Const const0 ->
      add_concrete_equation_on_const raise_on_bottom env const0 ty
        meet_expanded_head0

  (** val add_concrete_equation_on_simple : bool -> t -> simple ->
      Expanded_type.t -> meet_expanded_head -> t Or_bottom.t option **)

  let add_concrete_equation_on_simple raise_on_bottom env simple0 ty
      meet_expanded_head0 =
    let canonical0 =
      Typing_env.get_canonical_simple_ignoring_name_mode env.typing_env simple0
    in
    add_or_delay_concrete_equation_on_canonical raise_on_bottom env canonical0
      ty meet_expanded_head0

  (** val record_demotion : bool -> t -> flambda_kind -> name -> simple ->
      meet_expanded_head -> t Or_bottom.t option **)

  let record_demotion raise_on_bottom env kind0 demoted canonical0
      meet_expanded_head0 =
    match Typing_env.find env.typing_env demoted (Some kind0) with
    | Some ty_of_demoted -> (
      let env0 =
        map_typing_env env (fun tenv ->
            Typing_env.replace_equation tenv demoted
              (alias_type_of kind0 canonical0))
      in
      match
        expand_head0 env0.typing_env ty_of_demoted
          (Some (simple_of_name demoted))
      with
      | Some ty_of_demoted0 ->
        add_or_delay_concrete_equation_on_canonical raise_on_bottom env0
          canonical0 ty_of_demoted0 meet_expanded_head0
      | None -> None)
    | None -> None

  (** val add_alias_between_canonicals : bool -> t -> flambda_kind -> simple ->
      simple -> meet_expanded_head -> t Or_bottom.t option **)

  let add_alias_between_canonicals raise_on_bottom env kind0 canonical_element1
      canonical_element2 meet_expanded_head0 =
    if simple_equal canonical_element1 canonical_element2
    then Some (Or_bottom.Ok env)
    else
      match
        Typing_env.add_alias env.typing_env canonical_element1
          canonical_element2
      with
      | Some result -> (
        match result with
        | Unknown -> Some (Or_bottom.Ok env)
        | Ok result0 ->
          record_demotion raise_on_bottom
            (with_typing_env env result0.Typing_env.add_alias_result_t)
            kind0 result0.Typing_env.demoted_name
            result0.Typing_env.canonical_element meet_expanded_head0
        | Bottom ->
          if raise_on_bottom
          then Some Or_bottom.Bottom
          else Some (Or_bottom.Ok env))
      | None -> None

  (** val add_equation_on_simple0 : bool -> t -> simple -> flambda_type ->
      meet_expanded_head -> t Or_bottom.t option **)

  let add_equation_on_simple0 raise_on_bottom env simple0 ty meet_expanded_head0
      =
    match get_alias_opt ty with
    | Some alias ->
      let canonical_element1 =
        Typing_env.get_canonical_simple_ignoring_name_mode env.typing_env
          simple0
      in
      let canonical_element2 =
        Typing_env.get_canonical_simple_ignoring_name_mode env.typing_env alias
      in
      add_alias_between_canonicals raise_on_bottom env (kind ty)
        canonical_element1 canonical_element2 meet_expanded_head0
    | None -> (
      match Expanded_type.of_non_alias_type ty with
      | Some ty0 ->
        add_concrete_equation_on_simple raise_on_bottom env simple0 ty0
          meet_expanded_head0
      | None -> None)

  (** val add_equation0 : bool -> t -> name -> flambda_type ->
      meet_expanded_head -> t Or_bottom.t option **)

  let add_equation0 raise_on_bottom env name0 ty meet_expanded_head0 =
    add_equation_on_simple0 raise_on_bottom env (simple_of_name name0) ty
      meet_expanded_head0

  (** val add_equations0 : bool -> t -> (name * flambda_type) list ->
      meet_expanded_head -> t Or_bottom.t option **)

  let rec add_equations0 raise_on_bottom env equations meet_expanded_head0 =
    match equations with
    | [] -> Some (Or_bottom.Ok env)
    | p :: equations0 -> (
      let name0, ty = p in
      match add_equation0 raise_on_bottom env name0 ty meet_expanded_head0 with
      | Some result -> (
        match result with
        | Or_bottom.Ok env0 ->
          add_equations0 raise_on_bottom env0 equations0 meet_expanded_head0
        | Or_bottom.Bottom -> Some Or_bottom.Bottom)
      | None -> None)

  (** val add_env_extension0 : bool -> t -> env_extension -> meet_expanded_head
      -> t Or_bottom.t option **)

  let add_env_extension0 raise_on_bottom env env_extension0 meet_expanded_head0
      =
    let (Env_extension equations) = env_extension0 in
    add_equations0 raise_on_bottom env
      (Keyed.compact name_eqb equations)
      meet_expanded_head0

  (** val add_equation_strict : t -> name -> flambda_type -> meet_expanded_head
      -> t Or_bottom.t option **)

  let add_equation_strict env name0 ty meet_expanded_head0 =
    if env.typing_env.Typing_env.is_bottom
    then Some Or_bottom.Bottom
    else add_equation0 true env name0 ty meet_expanded_head0

  (** val add_env_extension_strict : t -> env_extension -> meet_expanded_head ->
      t Or_bottom.t option **)

  let add_env_extension_strict env env_extension0 meet_expanded_head0 =
    if env.typing_env.Typing_env.is_bottom
    then Some Or_bottom.Bottom
    else add_env_extension0 true env env_extension0 meet_expanded_head0

  (** val bottom_on_exception : t -> t Or_bottom.t option -> t option **)

  let bottom_on_exception env = function
    | Some result0 -> (
      match result0 with
      | Or_bottom.Ok env0 -> Some env0
      | Or_bottom.Bottom -> Some (make_bottom env))
    | None -> None

  (** val add_equation : t -> name -> flambda_type -> meet_expanded_head -> t
      option **)

  let add_equation env name0 ty meet_expanded_head0 =
    bottom_on_exception env
      (add_equation0 true env name0 ty meet_expanded_head0)

  (** val add_equation_on_simple : t -> simple -> flambda_type ->
      meet_expanded_head -> t option **)

  let add_equation_on_simple env simple0 ty meet_expanded_head0 =
    bottom_on_exception env
      (add_equation_on_simple0 true env simple0 ty meet_expanded_head0)

  (** val add_env_extension : t -> env_extension -> meet_expanded_head -> t
      option **)

  let add_env_extension env env_extension0 meet_expanded_head0 =
    bottom_on_exception env
      (add_env_extension0 true env env_extension0 meet_expanded_head0)

  (** val enter_scope : t -> (Scope.t * Typing_env.t) * t **)

  let enter_scope env =
    let tenv = env.typing_env in
    let current_scope0 = Typing_env.current_scope tenv in
    let env0 =
      { typing_env = Typing_env.increment_scope tenv;
        adding_equations_for_names = env.adding_equations_for_names;
        names_to_avoid = env.names_to_avoid
      }
    in
    (current_scope0, tenv), env0

  (** val add_definition : t -> name -> Name_mode.t -> flambda_kind -> t option
      **)

  let add_definition env name0 name_mode kind0 =
    match Typing_env.add_definition env.typing_env name0 name_mode kind0 with
    | Some tenv -> Some (with_typing_env env tenv)
    | None -> None

  (** val add_variable_definition : t -> variable -> flambda_kind -> Name_mode.t
      -> t **)

  let add_variable_definition env var kind0 name_mode =
    map_typing_env env (fun tenv ->
        Typing_env.add_variable_definition tenv var kind0 name_mode)

  (** val add_alias0 : bool -> t -> simple -> simple -> meet_expanded_head -> t
      Or_bottom.t option **)

  let add_alias0 raise_on_bottom env simple1 simple2 meet_expanded_head0 =
    let canonical1 =
      Typing_env.get_canonical_simple_ignoring_name_mode env.typing_env simple1
    in
    let canonical2 =
      Typing_env.get_canonical_simple_ignoring_name_mode env.typing_env simple2
    in
    match kind_of_simple env.typing_env canonical1 with
    | Some kind0 ->
      add_alias_between_canonicals raise_on_bottom env kind0 canonical1
        canonical2 meet_expanded_head0
    | None -> None

  (** val add_alias : t -> simple -> simple -> meet_expanded_head -> t
      Or_bottom.t option **)

  let add_alias env simple1 simple2 meet_expanded_head0 =
    add_alias0 true env simple1 simple2 meet_expanded_head0

  (** val meet : t -> flambda_type -> flambda_type -> meet_expanded_head ->
      Expanded_type.t Meet_result.t option **)

  let meet env t1 t2 meet_expanded_head0 =
    if negb (kind_eqb (kind t1) (kind t2))
    then None
    else
      let kind0 = kind t1 in
      let tenv = env.typing_env in
      match
        Typing_env.get_alias_then_canonical_simple_exn tenv
          (Some Name_mode.in_types) None t1
      with
      | Some simple1 -> (
        match
          Typing_env.get_alias_then_canonical_simple_exn tenv
            (Some Name_mode.in_types) None t2
        with
        | Some simple2 -> (
          let of_exception =
           fun result return_value ->
            match result with
            | Or_bottom.Ok env0 -> Meet_result.Ok (return_value, env0)
            | Or_bottom.Bottom -> Meet_result.Bottom (New_result ())
          in
          match simple1 with
          | Some simple3 -> (
            match simple2 with
            | Some simple4 -> (
              match
                add_alias_between_canonicals true env kind0 simple3 simple4
                  meet_expanded_head0
              with
              | Some result -> Some (of_exception result Both_inputs)
              | None -> None)
            | None -> (
              match expand_head0 tenv t2 simple2 with
              | Some expanded2 -> (
                match
                  add_or_delay_concrete_equation_on_canonical true env simple3
                    expanded2 meet_expanded_head0
                with
                | Some result -> Some (of_exception result Left_input)
                | None -> None)
              | None -> None))
          | None -> (
            match expand_head0 tenv t1 simple1 with
            | Some expanded1 -> (
              match simple2 with
              | Some simple3 -> (
                match
                  add_or_delay_concrete_equation_on_canonical true env simple3
                    expanded1 meet_expanded_head0
                with
                | Some result -> Some (of_exception result Right_input)
                | None -> None)
              | None -> (
                match expand_head0 tenv t2 simple2 with
                | Some expanded2 -> meet_expanded_head0 env expanded1 expanded2
                | None -> None))
            | None -> None))
        | None -> None)
      | None -> None

  (** val meet_type : t -> flambda_type -> flambda_type -> meet_expanded_head ->
      flambda_type Meet_result.t option **)

  let meet_type env t1 t2 meet_expanded_head0 =
    option_map
      (map_result Expanded_type.to_type)
      (meet env t1 t2 meet_expanded_head0)

  (** val final_typing_env : t -> Typing_env.t **)

  let final_typing_env env = env.typing_env

  (** val final_typing_env_strict : t -> Typing_env.t Or_bottom.t **)

  let final_typing_env_strict env = Or_bottom.Ok env.typing_env

  (** val use_meet_env : Typing_env.t -> (t -> t option) -> Typing_env.t option
      **)

  let use_meet_env tenv f = option_map final_typing_env (f (create tenv))
end
