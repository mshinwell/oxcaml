open SsaModel

(** val strictly_dominates : block -> block -> bool **)

let strictly_dominates dominator block0 =
  Ssa.Block.dominates dominator block0 && not (Ssa.Block.equal dominator block0)

(** val edge_dominates : block -> block -> block -> bool **)

let edge_dominates pred succ target =
  (Ssa.Block.dominates succ target && not (Ssa.Block.dominates succ pred))
  &&
  match Ssa.Block.predecessors succ with
  | [] -> false
  | only_pred :: l -> (
    match l with [] -> Ssa.Block.equal only_pred pred | _ :: _ -> false)
