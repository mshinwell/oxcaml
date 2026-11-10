open BinNums
open BinPos
open PosDef

module Z = struct
  (** val eqb : coq_Z -> coq_Z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> ( match y with Z0 -> true | _ -> false)
    | Zpos p -> ( match y with Zpos q -> Pos.eqb p q | _ -> false)
    | Zneg p -> ( match y with Zneg q -> Pos.eqb p q | _ -> false)

  (** val eq_dec : coq_Z -> coq_Z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> ( match y with Z0 -> true | _ -> false)
    | Zpos p -> ( match y with Zpos p0 -> BinPos.Pos.eq_dec p p0 | _ -> false)
    | Zneg p -> ( match y with Zneg p0 -> BinPos.Pos.eq_dec p p0 | _ -> false)
end
