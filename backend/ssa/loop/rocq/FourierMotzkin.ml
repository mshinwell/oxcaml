open IntArith
open OxCamlList

module Affine = struct
  type t =
    { const : int;
      terms : (int * int) list
    }

  (** val const : t -> int **)

  let const t0 = t0.const

  (** val terms : t -> (int * int) list **)

  let terms t0 = t0.terms

  (** val constant : int -> t **)

  let constant c = { const = c; terms = [] }

  (** val var : int -> t **)

  let var id = { const = 0; terms = (id, 1) :: [] }

  (** val coeff : int -> t -> int **)

  let coeff id f = assoc_default 0 id f.terms

  (** val terms_equal : (int * int) list -> (int * int) list -> bool **)

  let rec terms_equal l1 l2 =
    match l1 with
    | [] -> ( match l2 with [] -> true | _ :: _ -> false)
    | p :: l3 -> (
      let i1, c1 = p in
      match l2 with
      | [] -> false
      | p0 :: l4 ->
        let i2, c2 = p0 in
        (Int.equal i1 i2 && Int.equal c1 c2) && terms_equal l3 l4)

  (** val equal : t -> t -> bool **)

  let equal a b = Int.equal a.const b.const && terms_equal a.terms b.terms

  (** val add_const : t -> int -> t **)

  let add_const f c = { const = f.const + c; terms = f.terms }

  (** val add : t -> t -> t **)

  let add a b =
    let ids = sort_uniq (List.map fst a.terms @ List.map fst b.terms) in
    let ts =
      List.filter_map
        (fun id ->
          let c = coeff id a + coeff id b in
          if Int.equal c 0 then None else Some (id, c))
        ids
    in
    { const = a.const + b.const; terms = ts }

  (** val scale : int -> t -> t **)

  let scale k f =
    if Int.equal k 0
    then constant 0
    else
      { const = f.const * k;
        terms =
          List.map
            (fun pat ->
              let id, c = pat in
              id, c * k)
            f.terms
      }

  (** val neg : t -> t **)

  let neg f = scale (-1) f

  (** val sub : t -> t -> t **)

  let sub a b = add a (neg b)

  (** val scale_checked : int -> t -> t option **)

  let scale_checked k f =
    if Int.equal k 0
    then Some (constant 0)
    else
      match mul_ovf f.const k with
      | Some c -> (
        match
          map_opt
            (fun pat ->
              let id, c0 = pat in
              match mul_ovf c0 k with Some c1 -> Some (id, c1) | None -> None)
            f.terms
        with
        | Some ts -> Some { const = c; terms = ts }
        | None -> None)
      | None -> None

  (** val add_checked : t -> t -> t option **)

  let add_checked a b =
    let ids = sort_uniq (List.map fst a.terms @ List.map fst b.terms) in
    match
      filter_map_opt
        (fun id ->
          match add_ovf (coeff id a) (coeff id b) with
          | Some c -> Some (if Int.equal c 0 then None else Some (id, c))
          | None -> None)
        ids
    with
    | Some ts -> (
      match add_ovf a.const b.const with
      | Some c -> Some { const = c; terms = ts }
      | None -> None)
    | None -> None

  (** val add_const_checked : t -> int -> t option **)

  let add_const_checked f c =
    match add_ovf f.const c with
    | Some k -> Some { const = k; terms = f.terms }
    | None -> None

  (** val sub_checked : t -> t -> t option **)

  let sub_checked a b =
    match scale_checked (-1) b with Some nb -> add_checked a nb | None -> None
end

(** val coeff64 : int -> (int * int64) list -> int64 **)

let coeff64 = assoc_default 0L

(** val scaled : int64 -> Affine.t -> (int64 * (int * int64) list) option **)

let scaled k f =
  match mul_ovf64 k (Int64.of_int f.Affine.const) with
  | Some c -> (
    match
      map_opt
        (fun pat ->
          let id, c0 = pat in
          match mul_ovf64 k (Int64.of_int c0) with
          | Some c1 -> Some (id, c1)
          | None -> None)
        f.Affine.terms
    with
    | Some ts -> Some (c, ts)
    | None -> None)
  | None -> None

(** val resolvent : int -> int -> Affine.t -> Affine.t -> Affine.t option **)

let resolvent cp cn p n =
  let cp64 = Int64.of_int cp in
  let cn64 = Int64.of_int cn in
  match scaled cn64 p with
  | Some p0 -> (
    let pc, pterms = p0 in
    match scaled cp64 n with
    | Some p1 -> (
      let nc, nterms = p1 in
      let ids = sort_uniq (List.map fst pterms @ List.map fst nterms) in
      match
        filter_map_opt
          (fun id ->
            match add_ovf64 (coeff64 id pterms) (coeff64 id nterms) with
            | Some c -> Some (if Int64.equal c 0L then None else Some (id, c))
            | None -> None)
          ids
      with
      | Some ts -> (
        match add_ovf64 pc nc with
        | Some c -> (
          match ts with
          | [] ->
            Some
              { Affine.const = (if 0 <= Int64.compare c 0L then 0 else -1);
                Affine.terms = []
              }
          | _ :: _ -> (
            let g =
              List.fold_left
                (fun g pat ->
                  let _, c0 = pat in
                  gcd64 g (Int64.abs c0))
                0L ts
            in
            let g0 = if 0 < Int64.compare g 1L then g else 1L in
            match to_int_ovf (fdiv64 c g0) with
            | Some k -> (
              match
                map_opt
                  (fun pat ->
                    let id, c0 = pat in
                    match to_int_ovf (Int64.div c0 g0) with
                    | Some c1 -> Some (id, c1)
                    | None -> None)
                  ts
              with
              | Some ts0 -> Some { Affine.const = k; Affine.terms = ts0 }
              | None -> None)
            | None -> None))
        | None -> None)
      | None -> None)
    | None -> None)
  | None -> None

(** val elim : int -> Affine.t list -> Affine.t list option **)

let elim atom ineqs =
  if 0 < List.compare_length_with ineqs 500
  then None
  else
    let cf = fun f -> Affine.coeff atom f in
    let pos = List.filter (fun f -> 0 < cf f) ineqs in
    let neg0 = List.filter (fun f -> cf f < 0) ineqs in
    let zero_coeff = List.filter (fun f -> Int.equal (cf f) 0) ineqs in
    let resolvents =
      List.concat_map
        (fun p ->
          List.filter_map
            (fun n ->
              match neg_ovf (cf n) with
              | Some cn -> resolvent (cf p) cn p n
              | None -> None)
            neg0)
        pos
    in
    Some (List.rev_append zero_coeff resolvents)

(** val elim_all : int list -> Affine.t list -> Affine.t list option **)

let rec elim_all atoms ineqs =
  match atoms with
  | [] -> Some ineqs
  | atom :: atoms0 -> (
    match elim atom ineqs with
    | Some ineqs0 -> elim_all atoms0 ineqs0
    | None -> None)

(** val feasible : Affine.t list -> bool **)

let feasible ineqs =
  let atoms =
    sort_uniq (List.concat_map (fun f -> List.map fst f.Affine.terms) ineqs)
  in
  if 0 < List.compare_length_with atoms 64
  then true
  else
    match elim_all atoms ineqs with
    | Some reduced -> List.for_all (fun f -> 0 <= f.Affine.const) reduced
    | None -> true

(** val entails : Affine.t list -> Affine.t -> bool **)

let entails facts goal =
  let negated =
    match Affine.scale_checked (-1) goal with
    | Some ng -> Affine.add_const_checked ng (-1)
    | None -> None
  in
  match negated with Some ng -> not (feasible (ng :: facts)) | None -> false
