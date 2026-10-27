open AffineExpr
open FourierMotzkin
open IntArith
open LoopComparisons
open SsaDominance
open SsaModel

type ctx =
  { atoms : (int * value) list;
    next : int
  }

(** val new_ctx : ctx **)

let new_ctx = { atoms = []; next = 0 }

(** val intern : ctx -> value -> int * ctx **)

let intern c v =
  match
    List.find_opt
      (fun pat ->
        let _, w = pat in
        Ssa.Value.equal v w)
      c.atoms
  with
  | Some p ->
    let id, _ = p in
    id, c
  | None ->
    let id = c.next in
    id, { atoms = (id, v) :: c.atoms; next = id + 1 }

(** val atomize : ctx -> value -> (t * Range.t option) * ctx **)

let atomize c v =
  let id, c0 = intern c v in
  (Atom id, Some Range.full), c0

(** val keep : ctx -> value -> t -> Range.t option -> (t * Range.t option) * ctx
    **)

let keep c v node range =
  match range with Some _ -> (node, range), c | None -> atomize c v

(** val radd : Range.t option -> Range.t option -> Range.t option **)

let radd a b =
  match a with
  | Some a0 -> ( match b with Some b0 -> Range.add a0 b0 | None -> None)
  | None -> None

(** val rsub : Range.t option -> Range.t option -> Range.t option **)

let rsub a b =
  match a with
  | Some a0 -> ( match b with Some b0 -> Range.sub a0 b0 | None -> None)
  | None -> None

(** val rscale : int -> Range.t option -> Range.t option **)

let rscale k = function Some r0 -> Range.scale k r0 | None -> None

(** val expr_of_value : ctx -> tree -> (t * Range.t option) * ctx **)

let rec expr_of_value c = function
  | Const_int (v, n) ->
    if int64_is_int n
    then
      let k = Int64.to_int n in
      (Const k, Some (Range.const k)), c
    else atomize c v
  | Iadd (v, a, b) ->
    let p, c0 = expr_of_value c a in
    let ea, ra = p in
    let p0, c1 = expr_of_value c0 b in
    let eb, rb = p0 in
    keep c1 v (Add (ea, eb)) (radd ra rb)
  | Isub (v, a, b) ->
    let p, c0 = expr_of_value c a in
    let ea, ra = p in
    let p0, c1 = expr_of_value c0 b in
    let eb, rb = p0 in
    keep c1 v (Sub (ea, eb)) (rsub ra rb)
  | Iadd_imm (v, a, k) ->
    let p, c0 = expr_of_value c a in
    let ea, ra = p in
    keep c0 v (Add (ea, Const k)) (radd ra (Some (Range.const k)))
  | Isub_imm (v, a, k) ->
    let p, c0 = expr_of_value c a in
    let ea, ra = p in
    keep c0 v (Sub (ea, Const k)) (rsub ra (Some (Range.const k)))
  | Ilsl (v, a, k) ->
    if 0 <= k && k < 16
    then
      let p, c0 = expr_of_value c a in
      let ea, ra = p in
      keep c0 v (Scale (1 lsl k, ea)) (rscale (1 lsl k) ra)
    else atomize c v
  | Iasr (v, a, k) ->
    if 0 <= k && k < 16
    then
      let p, c0 = expr_of_value c a in
      let ea, o = p in
      match o with
      | Some _ ->
        let id, c1 = intern c0 v in
        (Shr_atom (id, ea, k), Some (Range.shr_signed k)), c1
      | None -> atomize c0 v
    else atomize c v
  | Ilsr (v, k) ->
    if 1 <= k && k < 64
    then
      let id, c0 = intern c v in
      (Lsr_atom (id, k), Some (Range.shr_logical k)), c0
    else atomize c v
  | Ior (v, a, m) ->
    if 0 <= m
    then
      let p, c0 = expr_of_value c a in
      let ea, o = p in
      match o with
      | Some r ->
        let id, c1 = intern c0 v in
        (Or_atom (id, ea, m), Range.or_mask m r), c1
      | None -> atomize c0 v
    else atomize c v
  | Icomp (v, _, _, _) -> atomize c v
  | Icomp_imm (v, _, _, _) -> atomize c v
  | Other v -> atomize c v

(** val push_sides : Affine.t list -> Affine.t list -> Affine.t list **)

let push_sides side sides =
  List.fold_left
    (fun side0 f ->
      if List.exists (Affine.equal f) side0 then side0 else f :: side0)
    side sides

(** val linearize : ctx -> Affine.t list -> tree -> (Affine.t * Affine.t list) *
    ctx **)

let linearize c side t0 =
  let p, c0 = expr_of_value c t0 in
  let e, _ = p in
  match to_affine e with
  | Some p0 ->
    let form, sides = p0 in
    (form, push_sides side sides), c0
  | None ->
    let id, c1 = intern c0 (root t0) in
    (Affine.var id, side), c1

(** val cond_facts : ctx -> Affine.t list -> bool -> tree -> (Affine.t list *
    Affine.t list) * ctx **)

let cond_facts c side negate = function
  | Icomp (_, cmp, a, b) ->
    let p, c0 = linearize c side a in
    let la, side0 = p in
    let p0, c1 = linearize c0 side0 b in
    let lb, side1 = p0 in
    (facts negate cmp la lb, side1), c1
  | Icomp_imm (_, cmp, a, k) ->
    let p, c0 = linearize c side a in
    let la, side0 = p in
    (facts negate cmp la (Affine.constant k), side0), c0
  | _ -> ([], side), c

(** val guard_test : block -> block -> (value * bool) option **)

let guard_test target idom =
  match Ssa_view.terminator idom with
  | Terminator.Switch (index, targets) -> (
    match targets with
    | [] -> None
    | ifnot :: l -> (
      match l with
      | [] -> None
      | ifso :: l0 -> (
        match l0 with
        | [] ->
          if edge_dominates idom ifso target
          then Some (index, false)
          else if edge_dominates idom ifnot target
          then Some (index, true)
          else None
        | _ :: _ -> None)))
  | _ -> None

(** val guard_facts : block -> ((Affine.t list * Affine.t list) * ctx) -> block
    -> (Affine.t list * Affine.t list) * ctx **)

let guard_facts target st idom =
  let p, c = st in
  let acc, side = p in
  match guard_test target idom with
  | Some p0 ->
    let index, negate = p0 in
    let p1, c0 = cond_facts c side negate (Ssa_view.tree_of_value index) in
    let fs, side0 = p1 in
    (fs @ acc, side0), c0
  | None -> (acc, side), c

(** val guards_at : ctx -> Affine.t list -> block -> (Affine.t list * Affine.t
    list) * ctx **)

let guards_at c side target =
  List.fold_left (guard_facts target)
    (([], side), c)
    (Ssa_view.strict_dominators target)
