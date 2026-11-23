open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar

module Code_age_relation = struct
  type t = (code_id * code_id) list

  (** val empty : t **)

  let empty = []

  (** val get_older_version_of : t -> code_id -> code_id option **)

  let get_older_version_of rel id = lookup id rel

  (** val add : t -> code_id -> code_id -> t **)

  let add rel newer older = (newer, older) :: rel

  (** val has_older_version_in : (code_id -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> bool)
      -> nat -> t -> ('a1 -> t option) -> code_id -> code_id list -> bool
      Or_unknown.t option **)

  let rec has_older_version_in get_compilation_unit current_unit
      compilation_unit_equal steps rel resolver id candidates =
    match steps with
    | O -> None
    | S steps0 -> (
      if among id candidates
      then Some (Or_unknown.Known true)
      else
        match lookup id rel with
        | Some older ->
          has_older_version_in get_compilation_unit current_unit
            compilation_unit_equal steps0 rel resolver older candidates
        | None -> (
          let comp_unit = get_compilation_unit id in
          if compilation_unit_equal comp_unit current_unit
          then Some (Or_unknown.Known false)
          else
            match resolver comp_unit with
            | Some rel0 -> (
              match lookup id rel0 with
              | Some older ->
                has_older_version_in get_compilation_unit current_unit
                  compilation_unit_equal steps0 rel0 resolver older candidates
              | None -> Some (Or_unknown.Known false))
            | None -> Some Or_unknown.Unknown))

  (** val should_keep_id : (code_id -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> bool) ->
      nat -> t -> ('a1 -> t option) -> code_id list -> code_id -> bool option **)

  let should_keep_id get_compilation_unit current_unit compilation_unit_equal
      steps rel resolver other_ids id =
    match
      has_older_version_in get_compilation_unit current_unit
        compilation_unit_equal steps rel resolver id other_ids
    with
    | Some t0 -> (
      match t0 with
      | Or_unknown.Known has_older_version_in_other_ids ->
        Some has_older_version_in_other_ids
      | Or_unknown.Unknown -> Some true)
    | None -> None

  (** val filter_ids : (code_id -> bool option) -> code_id list -> code_id list
      option **)

  let rec filter_ids keep = function
    | [] -> Some []
    | id :: ids0 -> (
      match keep id with
      | Some kept -> (
        match filter_ids keep ids0 with
        | Some ids1 -> Some (if kept then id :: ids1 else ids1)
        | None -> None)
      | None -> None)

  (** val meet_set : (code_id -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> bool) -> nat -> t
      -> ('a1 -> t option) -> code_id list -> code_id list -> code_id list
      Or_bottom.t option **)

  let meet_set get_compilation_unit current_unit compilation_unit_equal steps
      rel resolver ids1 ids2 =
    if all_among ids1 ids2 && all_among ids2 ids1
    then Some (Or_bottom.Ok ids1)
    else
      match
        filter_ids
          (should_keep_id get_compilation_unit current_unit
             compilation_unit_equal steps rel resolver ids1)
          ids2
      with
      | Some kept2 -> (
        match
          filter_ids
            (should_keep_id get_compilation_unit current_unit
               compilation_unit_equal steps rel resolver ids2)
            ids1
        with
        | Some kept1 -> (
          match app kept2 kept1 with
          | [] -> Some Or_bottom.Bottom
          | c :: l -> Some (Or_bottom.Ok (c :: l)))
        | None -> None)
      | None -> None

  (** val meet : (code_id -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> bool) -> nat -> t ->
      ('a1 -> t option) -> code_id -> code_id -> code_id or_unknown_or_bottom
      option **)

  let meet get_compilation_unit current_unit compilation_unit_equal steps rel
      resolver id1 id2 =
    if Pos.eqb id1 id2
    then Some (Ok id1)
    else
      match
        has_older_version_in get_compilation_unit current_unit
          compilation_unit_equal steps rel resolver id2 (id1 :: [])
      with
      | Some older1 -> (
        match
          has_older_version_in get_compilation_unit current_unit
            compilation_unit_equal steps rel resolver id1 (id2 :: [])
        with
        | Some older2 ->
          Some
            (match older1 with
            | Or_unknown.Known a -> (
              if a
              then Ok id2
              else
                match older2 with
                | Or_unknown.Known a0 -> if a0 then Ok id1 else Bottom
                | Or_unknown.Unknown -> Unknown)
            | Or_unknown.Unknown -> (
              match older2 with
              | Or_unknown.Known a -> if a then Ok id1 else Unknown
              | Or_unknown.Unknown -> Unknown))
        | None -> None)
      | None -> None
end
