open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar

module Code_age_relation = struct
  type t = (code_id * code_id) list

  (** val empty : t **)

  let empty = []

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
