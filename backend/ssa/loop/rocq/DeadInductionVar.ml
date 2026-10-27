open InductionVar
open NaturalLoop
open OxCamlList
open SsaGraph
open SsaModel

type biv_result =
  { biv : biv;
    dead : bool
  }

type loop_result =
  { loop : natural_loop;
    bivs : biv_result list;
    useless : bool
  }

(** val param_uses_ok : block list -> block -> int -> Ssa.finished Ssa.Value.t
    -> Ssa.finished Ssa.Value.t list -> bool **)

let param_uses_ok blocks header0 k cond updates =
  all_uses_ok blocks (is_param header0 k)
    (fun i ->
      instr_defines_value i cond || List.exists (instr_defines_value i) updates)
    (fun _ _ -> false)

(** val cond_uses_ok : block list -> block -> Ssa.finished Ssa.Value.t -> bool **)

let cond_uses_ok blocks header0 cond =
  all_uses_ok blocks (Ssa.Value.equal cond)
    (fun _ -> false)
    (fun bl _ -> Ssa.Block.equal bl header0)

(** val update_uses_ok : block list -> block -> blockset -> int -> Ssa.finished
    Ssa.Value.t -> Ssa.finished Ssa.Value.t -> bool **)

let update_uses_ok blocks header0 back_preds k cond u =
  all_uses_ok blocks (Ssa.Value.equal u)
    (fun i -> instr_defines_value i cond)
    (fun bl _ -> Ssa.Block.Set.mem bl back_preds && goto_passes header0 k u bl)

(** val is_dead : block list -> biv -> bool **)

let is_dead blocks biv0 =
  match find_exit_branch biv0.InductionVar.loop with
  | Some exit_info ->
    let cond = exit_info.condition in
    let header0 = biv0.InductionVar.loop.header in
    let k = biv0.param_index in
    let back_preds = back_edge_set biv0.InductionVar.loop in
    (param_uses_ok blocks header0 k cond biv0.update
    && cond_uses_ok blocks header0 cond)
    && List.for_all
         (update_uses_ok blocks header0 back_preds k cond)
         biv0.update
  | None -> false

(** val loop_is_useless : natural_loop -> biv_result list -> bool **)

let loop_is_useless loop0 bivs0 =
  same_length (params loop0.header) bivs0
  && List.for_all (fun b -> b.dead) bivs0

(** val analyze : block list -> (natural_loop * biv list) list -> loop_result
    list **)

let analyze blocks loops =
  List.map
    (fun pat ->
      let loop0, bivs0 = pat in
      let bivs1 =
        List.map (fun biv0 -> { biv = biv0; dead = is_dead blocks biv0 }) bivs0
      in
      { loop = loop0; bivs = bivs1; useless = loop_is_useless loop0 bivs1 })
    loops
