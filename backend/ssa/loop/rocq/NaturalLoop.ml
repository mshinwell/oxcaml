open SsaModel

type natural_loop =
  { header : block;
    body : blockset;
    back_edges : block list
  }

(** val add_new : (blockset * block list) -> block -> blockset * block list **)

let add_new acc p =
  let body0, added = acc in
  if Ssa.Block.Set.mem p body0
  then body0, added
  else Ssa.Block.Set.add p body0, p :: added

(** val walk : block list -> blockset -> block list -> blockset **)

let rec walk fuel body0 worklist =
  match fuel with
  | [] -> body0
  | _ :: fuel0 -> (
    match worklist with
    | [] -> body0
    | bl :: rest ->
      let body1, added =
        List.fold_left add_new (body0, rest) (Ssa.Block.predecessors bl)
      in
      walk fuel0 body1 added)

(** val natural_loop_body : block list -> block -> block list -> blockset **)

let natural_loop_body fuel header0 back_preds =
  let body0, seeds =
    List.fold_left add_new (Ssa.Block.Set.singleton header0, []) back_preds
  in
  walk fuel body0 seeds

(** val add_back_edge : block -> block -> (block * block list) list -> (block *
    block list) list **)

let rec add_back_edge header0 src = function
  | [] -> (header0, src :: []) :: []
  | p :: tbl0 ->
    let h, srcs = p in
    if Ssa.Block.equal h header0
    then (h, src :: srcs) :: tbl0
    else (h, srcs) :: add_back_edge header0 src tbl0

(** val record_back_edge : block -> (block * block list) list -> block -> (block
    * block list) list **)

let record_back_edge bl tbl succ =
  if Ssa.Block.dominates succ bl then add_back_edge succ bl tbl else tbl

(** val record_back_edges : (block * block list) list -> block -> (block * block
    list) list **)

let record_back_edges tbl bl =
  List.fold_left (record_back_edge bl) tbl (Ssa.Block.all_successors bl)

(** val find_loops : block list -> natural_loop list **)

let find_loops blocks =
  let header_tbl = List.fold_left record_back_edges [] blocks in
  List.map
    (fun pat ->
      let header0, back_preds = pat in
      { header = header0;
        body = natural_loop_body blocks header0 back_preds;
        back_edges = back_preds
      })
    header_tbl

(** val edge_dominates : block -> block -> block -> bool **)

let edge_dominates src succ target =
  Ssa.Block.dominates succ target
  &&
  match Ssa.Block.predecessors succ with
  | [] -> false
  | p :: l -> ( match l with [] -> Ssa.Block.equal p src | _ :: _ -> false)
