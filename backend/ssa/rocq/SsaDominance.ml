open SsaModel

(** val strictly_dominates : block -> block -> bool **)

let strictly_dominates d b =
  Ssa.Block.dominates d b && not (Ssa.Block.equal d b)

(** val edge_dominates : block -> block -> block -> bool **)

let edge_dominates src succ target =
  (Ssa.Block.dominates succ target && not (Ssa.Block.dominates succ src))
  &&
  match Ssa.Block.predecessors succ with
  | [] -> false
  | p :: l -> ( match l with [] -> Ssa.Block.equal p src | _ :: _ -> false)
