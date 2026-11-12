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

(** val name_is_symbol : name -> bool **)

let name_is_symbol = function Name_var _ -> false | Name_symbol _ -> true

(** val name_of_simple : simple -> name option **)

let name_of_simple = function
  | Var x -> Some (Name_var x)
  | Symbol sym -> Some (Name_symbol sym)
  | Const _ -> None

(** val simple_equal : simple -> simple -> bool **)

let simple_equal s s' =
  match s with
  | Var x -> ( match s' with Var x' -> Pos.eqb x x' | _ -> false)
  | Symbol sym -> (
    match s' with Symbol sym' -> Pos.eqb sym sym' | _ -> false)
  | Const c -> ( match s' with Const c' -> const_eqb c c' | _ -> false)

module Aliases = struct
  module Aliases_of_canonical_element = struct
    type t = (name, Name_mode.t) Keyed.finite_map

    (** val empty : t **)

    let empty = []

    (** val mem : t -> name -> bool **)

    let mem t0 elt = Keyed.is_bound name_eqb elt t0

    (** val add : t -> name -> Name_mode.t -> t option **)

    let add t0 elt name_mode0 =
      if mem t0 elt then None else Some ((elt, name_mode0) :: t0)

    (** val all : t -> name list **)

    let all t0 = Keyed.domain name_eqb t0

    (** val at_mode : t -> Name_mode.t -> name list **)

    let at_mode t0 order =
      map fst
        (Keyed.filter_bindings name_eqb
           (fun _ name_mode0 -> Name_mode.equal name_mode0 order)
           t0)

    (** val find_earliest_candidates : t -> (Name_mode.t -> name list -> name
        list) -> Name_mode.t -> name list option **)

    let find_earliest_candidates t0 filter_by_scope min_name_mode =
      fold_left
        (fun res_opt order ->
          match res_opt with
          | Some _ -> res_opt
          | None -> (
            match Name_mode.compare_partial_order order min_name_mode with
            | Some result ->
              if Z.leb Z0 result
              then
                let aliases = filter_by_scope order (at_mode t0 order) in
                if Keyed.is_empty aliases then None else Some aliases
              else None
            | None -> None))
        [Name_mode.In_types; Name_mode.Phantom; Name_mode.Normal]
        None

    (** val union : t -> t -> t **)

    let union = app
  end

  type t =
    { canonical_elements : (name, simple) Keyed.finite_map;
      aliases_of_canonical_names :
        (name, Aliases_of_canonical_element.t) Keyed.finite_map;
      aliases_of_consts :
        (const, Aliases_of_canonical_element.t) Keyed.finite_map
    }

  (** val canonical_elements : t -> (name, simple) Keyed.finite_map **)

  let canonical_elements t0 = t0.canonical_elements

  (** val aliases_of_canonical_names : t -> (name,
      Aliases_of_canonical_element.t) Keyed.finite_map **)

  let aliases_of_canonical_names t0 = t0.aliases_of_canonical_names

  (** val aliases_of_consts : t -> (const, Aliases_of_canonical_element.t)
      Keyed.finite_map **)

  let aliases_of_consts t0 = t0.aliases_of_consts

  (** val name_defined_earlier : (name -> Binding_time.With_name_mode.t) ->
      (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map -> name ->
      name -> bool **)

  let name_defined_earlier binding_time_resolver binding_times_and_modes alias
      than =
    if name_eqb alias than || (name_is_symbol alias && name_is_symbol than)
    then false
    else if name_is_symbol alias && negb (name_is_symbol than)
    then true
    else if name_is_symbol than && negb (name_is_symbol alias)
    then false
    else
      let alias_binding_time =
        match Keyed.lookup name_eqb alias binding_times_and_modes with
        | Some p ->
          let _, binding_time_and_mode = p in
          binding_time_and_mode.Binding_time.With_name_mode.binding_time
        | None -> Binding_time.imported_variables
      in
      let than_binding_time =
        match Keyed.lookup name_eqb than binding_times_and_modes with
        | Some p ->
          let _, binding_time_and_mode = p in
          binding_time_and_mode.Binding_time.With_name_mode.binding_time
        | None -> Binding_time.imported_variables
      in
      if Binding_time.strictly_earlier alias_binding_time than_binding_time
      then true
      else if negb (Binding_time.equal alias_binding_time than_binding_time)
      then false
      else
        let alias_binding_time0 =
          (binding_time_resolver alias).Binding_time.With_name_mode.binding_time
        in
        let than_binding_time0 =
          (binding_time_resolver than).Binding_time.With_name_mode.binding_time
        in
        Binding_time.strictly_earlier alias_binding_time0 than_binding_time0

  (** val defined_earlier : (name -> Binding_time.With_name_mode.t) -> (name,
      'a1 * Binding_time.With_name_mode.t) Keyed.finite_map -> simple -> simple
      -> bool **)

  let defined_earlier binding_time_resolver binding_times_and_modes alias than =
    match name_of_simple than with
    | Some than0 -> (
      match name_of_simple alias with
      | Some alias0 ->
        name_defined_earlier binding_time_resolver binding_times_and_modes
          alias0 than0
      | None -> true)
    | None -> false

  (** val binding_time_and_name_mode : (name, 'a1 *
      Binding_time.With_name_mode.t) Keyed.finite_map -> simple ->
      Binding_time.With_name_mode.t **)

  let binding_time_and_name_mode binding_times_and_modes = function
    | Var var -> (
      match Keyed.lookup name_eqb (Name_var var) binding_times_and_modes with
      | Some p ->
        let _, binding_time_and_mode = p in
        binding_time_and_mode
      | None -> Binding_time.With_name_mode.imported_variables)
    | Symbol _ -> Binding_time.With_name_mode.symbols
    | Const _ -> Binding_time.With_name_mode.consts

  (** val compute_name_mode_unscoped : (name, 'a1 *
      Binding_time.With_name_mode.t) Keyed.finite_map -> simple -> Name_mode.t **)

  let compute_name_mode_unscoped binding_times_and_modes elt =
    (binding_time_and_name_mode binding_times_and_modes elt)
      .Binding_time.With_name_mode.name_mode

  (** val compute_name_mode : (name, 'a1 * Binding_time.With_name_mode.t)
      Keyed.finite_map -> simple -> Binding_time.t -> Name_mode.t **)

  let compute_name_mode binding_times_and_modes elt min_binding_time =
    Binding_time.With_name_mode.scoped_name_mode
      (binding_time_and_name_mode binding_times_and_modes elt)
      min_binding_time

  (** val empty : t **)

  let empty =
    { canonical_elements = [];
      aliases_of_canonical_names = [];
      aliases_of_consts = []
    }

  type is_canonical_or_alias =
    | Is_canonical
    | Alias_of_canonical of simple

  (** val canonical : t -> simple -> is_canonical_or_alias **)

  let canonical t0 element =
    match name_of_simple element with
    | Some name0 -> (
      match Keyed.lookup name_eqb name0 t0.canonical_elements with
      | Some canonical_element0 -> Alias_of_canonical canonical_element0
      | None -> Is_canonical)
    | None -> Is_canonical

  (** val get_aliases_of_canonical_element : t -> simple ->
      Aliases_of_canonical_element.t **)

  let get_aliases_of_canonical_element t0 canonical_element0 =
    let aliases =
      match canonical_element0 with
      | Var var ->
        Keyed.lookup name_eqb (Name_var var) t0.aliases_of_canonical_names
      | Symbol symbol ->
        Keyed.lookup name_eqb (Name_symbol symbol) t0.aliases_of_canonical_names
      | Const const0 -> Keyed.lookup const_eqb const0 t0.aliases_of_consts
    in
    match aliases with
    | Some aliases0 -> aliases0
    | None -> Aliases_of_canonical_element.empty

  (** val add_alias_between_canonical_elements : (name, 'a1 *
      Binding_time.With_name_mode.t) Keyed.finite_map -> t -> simple -> simple
      -> t Or_bottom.t option **)

  let add_alias_between_canonical_elements binding_times_and_modes t0
      canonical_element0 to_be_demoted0 =
    if simple_equal canonical_element0 to_be_demoted0
    then Some (Or_bottom.Ok t0)
    else
      match name_of_simple to_be_demoted0 with
      | Some name_to_be_demoted -> (
        let aliases_of_to_be_demoted =
          get_aliases_of_canonical_element t0 to_be_demoted0
        in
        let canonical_elements0 =
          (name_to_be_demoted, canonical_element0)
          :: app
               (map
                  (fun alias -> alias, canonical_element0)
                  (Aliases_of_canonical_element.all aliases_of_to_be_demoted))
               t0.canonical_elements
        in
        let aliases_of_canonical_element =
          get_aliases_of_canonical_element t0 canonical_element0
        in
        match
          Aliases_of_canonical_element.add
            (Aliases_of_canonical_element.union aliases_of_to_be_demoted
               aliases_of_canonical_element)
            name_to_be_demoted
            (compute_name_mode_unscoped binding_times_and_modes to_be_demoted0)
        with
        | Some aliases -> (
          let aliases_of_canonical_names0 =
            Keyed.unbind name_eqb name_to_be_demoted
              t0.aliases_of_canonical_names
          in
          match canonical_element0 with
          | Var var ->
            let aliases_of_canonical_names1 =
              (Name_var var, aliases) :: aliases_of_canonical_names0
            in
            let aliases_of_consts0 = t0.aliases_of_consts in
            Some
              (Or_bottom.Ok
                 { canonical_elements = canonical_elements0;
                   aliases_of_canonical_names = aliases_of_canonical_names1;
                   aliases_of_consts = aliases_of_consts0
                 })
          | Symbol symbol ->
            let aliases_of_canonical_names1 =
              (Name_symbol symbol, aliases) :: aliases_of_canonical_names0
            in
            let aliases_of_consts0 = t0.aliases_of_consts in
            Some
              (Or_bottom.Ok
                 { canonical_elements = canonical_elements0;
                   aliases_of_canonical_names = aliases_of_canonical_names1;
                   aliases_of_consts = aliases_of_consts0
                 })
          | Const const0 ->
            let aliases_of_consts0 =
              (const0, aliases) :: t0.aliases_of_consts
            in
            Some
              (Or_bottom.Ok
                 { canonical_elements = canonical_elements0;
                   aliases_of_canonical_names = aliases_of_canonical_names0;
                   aliases_of_consts = aliases_of_consts0
                 }))
        | None -> None)
      | None -> Some Or_bottom.Bottom

  type to_be_demoted =
    | Demote_canonical_element1
    | Demote_canonical_element2

  (** val choose_canonical_element_to_be_demoted : (name ->
      Binding_time.With_name_mode.t) -> (name, 'a1 *
      Binding_time.With_name_mode.t) Keyed.finite_map -> simple -> simple ->
      to_be_demoted **)

  let choose_canonical_element_to_be_demoted binding_time_resolver
      binding_times_and_modes canonical_element1 canonical_element2 =
    if
      defined_earlier binding_time_resolver binding_times_and_modes
        canonical_element1 canonical_element2
    then Demote_canonical_element2
    else Demote_canonical_element1

  (** val add_alias : (name -> Binding_time.With_name_mode.t) -> (name, 'a1 *
      Binding_time.With_name_mode.t) Keyed.finite_map -> t -> simple -> simple
      -> (t * to_be_demoted) Or_bottom.t option **)

  let add_alias binding_time_resolver binding_times_and_modes t0
      canonical_element1 canonical_element2 =
    let which_element =
      choose_canonical_element_to_be_demoted binding_time_resolver
        binding_times_and_modes canonical_element1 canonical_element2
    in
    match which_element with
    | Demote_canonical_element1 -> (
      match
        add_alias_between_canonical_elements binding_times_and_modes t0
          canonical_element2 canonical_element1
      with
      | Some t1 -> (
        match t1 with
        | Or_bottom.Ok t2 -> Some (Or_bottom.Ok (t2, which_element))
        | Or_bottom.Bottom -> Some Or_bottom.Bottom)
      | None -> None)
    | Demote_canonical_element2 -> (
      match
        add_alias_between_canonical_elements binding_times_and_modes t0
          canonical_element1 canonical_element2
      with
      | Some t1 -> (
        match t1 with
        | Or_bottom.Ok t2 -> Some (Or_bottom.Ok (t2, which_element))
        | Or_bottom.Bottom -> Some Or_bottom.Bottom)
      | None -> None)

  (** val add0 : (name -> Binding_time.With_name_mode.t) -> (name, 'a1 *
      Binding_time.With_name_mode.t) Keyed.finite_map -> t -> simple -> simple
      -> (t * to_be_demoted) Or_bottom.t option **)

  let add0 = add_alias

  type add_result =
    { add_result_t : t;
      demoted_name : name;
      canonical_element : simple
    }

  (** val add_result_t : add_result -> t **)

  let add_result_t a = a.add_result_t

  (** val demoted_name : add_result -> name **)

  let demoted_name a = a.demoted_name

  (** val canonical_element : add_result -> simple **)

  let canonical_element a = a.canonical_element

  (** val add : (name -> Binding_time.With_name_mode.t) -> (name, 'a1 *
      Binding_time.With_name_mode.t) Keyed.finite_map -> t -> simple -> simple
      -> add_result Or_bottom.t option **)

  let add binding_time_resolver binding_times_and_modes t0 canonical_element1
      canonical_element2 =
    match
      add0 binding_time_resolver binding_times_and_modes t0 canonical_element1
        canonical_element2
    with
    | Some result -> (
      match result with
      | Or_bottom.Ok a -> (
        let t1, which_element = a in
        match which_element with
        | Demote_canonical_element1 -> (
          match name_of_simple canonical_element1 with
          | Some name0 ->
            Some
              (Or_bottom.Ok
                 { add_result_t = t1;
                   demoted_name = name0;
                   canonical_element = canonical_element2
                 })
          | None -> None)
        | Demote_canonical_element2 -> (
          match name_of_simple canonical_element2 with
          | Some name0 ->
            Some
              (Or_bottom.Ok
                 { add_result_t = t1;
                   demoted_name = name0;
                   canonical_element = canonical_element1
                 })
          | None -> None))
      | Or_bottom.Bottom -> Some Or_bottom.Bottom)
    | None -> None

  (** val find_earliest_alias : (name -> Binding_time.With_name_mode.t) ->
      (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map -> t ->
      simple -> Binding_time.t -> Name_mode.t -> simple option **)

  let find_earliest_alias binding_time_resolver binding_times_and_modes t0
      canonical_element0 min_binding_time min_name_mode =
    let aliases = get_aliases_of_canonical_element t0 canonical_element0 in
    let filter_by_scope =
     fun name_mode0 names ->
      if Name_mode.equal name_mode0 Name_mode.in_types
      then names
      else
        filter
          (fun name0 ->
            let scoped_name_mode0 =
              compute_name_mode binding_times_and_modes (simple_of_name name0)
                min_binding_time
            in
            Name_mode.equal name_mode0 scoped_name_mode0)
          names
    in
    match
      Aliases_of_canonical_element.find_earliest_candidates aliases
        filter_by_scope min_name_mode
    with
    | Some at_earliest_mode -> (
      match at_earliest_mode with
      | [] -> None
      | first :: _ ->
        let earliest =
          fold_left
            (fun min_elt elt ->
              if
                name_defined_earlier binding_time_resolver
                  binding_times_and_modes elt min_elt
              then elt
              else min_elt)
            at_earliest_mode first
        in
        Some (simple_of_name earliest))
    | None -> None

  (** val get_canonical_element_exn : (name -> Binding_time.With_name_mode.t) ->
      (name, 'a1 * Binding_time.With_name_mode.t) Keyed.finite_map -> t ->
      simple -> Name_mode.t -> Name_mode.t -> Binding_time.t -> simple option **)

  let get_canonical_element_exn binding_time_resolver binding_times_and_modes t0
      element elt_name_mode min_name_mode min_binding_time =
    let at_least_min_name_mode =
     fun name_mode0 ->
      match Name_mode.compare_partial_order name_mode0 min_name_mode with
      | Some c -> Z.leb Z0 c
      | None -> false
    in
    let canonical0 = canonical t0 element in
    match canonical0 with
    | Is_canonical -> (
      if at_least_min_name_mode elt_name_mode
      then Some element
      else
        match canonical0 with
        | Is_canonical ->
          if at_least_min_name_mode elt_name_mode
          then Some element
          else
            find_earliest_alias binding_time_resolver binding_times_and_modes t0
              element min_binding_time min_name_mode
        | Alias_of_canonical canonical_element0 ->
          let name_mode0 =
            compute_name_mode binding_times_and_modes canonical_element0
              min_binding_time
          in
          if at_least_min_name_mode name_mode0
          then Some canonical_element0
          else
            find_earliest_alias binding_time_resolver binding_times_and_modes t0
              canonical_element0 min_binding_time min_name_mode)
    | Alias_of_canonical _ -> (
      match canonical0 with
      | Is_canonical ->
        if at_least_min_name_mode elt_name_mode
        then Some element
        else
          find_earliest_alias binding_time_resolver binding_times_and_modes t0
            element min_binding_time min_name_mode
      | Alias_of_canonical canonical_element0 ->
        let name_mode0 =
          compute_name_mode binding_times_and_modes canonical_element0
            min_binding_time
        in
        if at_least_min_name_mode name_mode0
        then Some canonical_element0
        else
          find_earliest_alias binding_time_resolver binding_times_and_modes t0
            canonical_element0 min_binding_time min_name_mode)

  (** val get_canonical_ignoring_name_mode : t -> name -> simple **)

  let get_canonical_ignoring_name_mode t0 name0 =
    let elt = simple_of_name name0 in
    match canonical t0 elt with
    | Is_canonical -> elt
    | Alias_of_canonical canonical_element0 -> canonical_element0
end
