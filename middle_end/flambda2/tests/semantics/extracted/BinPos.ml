open BinNums

module Pos = struct
  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | Coq_xI p0 -> ( match q with Coq_xI q0 -> eqb p0 q0 | _ -> false)
    | Coq_xO p0 -> ( match q with Coq_xO q0 -> eqb p0 q0 | _ -> false)
    | Coq_xH -> ( match q with Coq_xH -> true | _ -> false)

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | Coq_xI p0 -> ( match x0 with Coq_xI p1 -> eq_dec p0 p1 | _ -> false)
    | Coq_xO p0 -> ( match x0 with Coq_xO p1 -> eq_dec p0 p1 | _ -> false)
    | Coq_xH -> ( match x0 with Coq_xH -> true | _ -> false)
end
