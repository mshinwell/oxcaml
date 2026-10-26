open InductionVar
open LoopTermination
open NaturalLoop
open OcamlList
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

(** val instr_defines_value : instr -> value -> bool **)

let instr_defines_value i v =
  match Ssa_view.instr i with
  | Op (id, _) -> (
    match Ssa_view.value v with
    | Res (id', _) -> Ssa.Instruction.Id.equal id id'
    | Block_param (_, _) -> false)
  | _ -> false

(** val args_of_instr : instr -> value list **)

let args_of_instr i =
  match Ssa_view.instr i with Op (_, args) -> args | _ -> []

(** val terminator_args : Terminator.t -> value list list **)

let terminator_args = function
  | Terminator.Continue (_, args) ->
    List.filter_map
      (fun arg ->
        match arg with
        | Ssa.Terminator.Arg v -> Some v
        | Ssa.Terminator.Omitted_since_unused -> None)
      args
    :: []
  | Terminator.Switch (index, _) -> (index :: []) :: []
  | Terminator.Call args -> args :: []
  | Terminator.Invalid args -> args :: []

(** val count_occurrences : ('a1 -> bool) -> 'a1 list -> int **)

let count_occurrences same l =
  List.fold_left (fun n x -> if same x then n + 1 else n) 0 l

(** val all_uses_ok : block list -> (value -> bool) -> (instr -> bool) -> (block
    -> value list -> bool) -> bool **)

let all_uses_ok blocks same approve_instr approve_term =
  List.for_all
    (fun bl ->
      List.for_all
        (fun i -> (not (List.exists same (args_of_instr i))) || approve_instr i)
        (Ssa_view.body bl)
      && List.for_all
           (fun arr -> (not (List.exists same arr)) || approve_term bl arr)
           (terminator_args (Ssa_view.terminator bl)))
    blocks

(** val is_dead : block list -> biv -> bool **)

let is_dead blocks biv0 =
  match find_exit_branch biv0.InductionVar.loop with
  | Some exit_info ->
    let cond = exit_info.condition in
    let header0 = biv0.InductionVar.loop.header in
    let k = biv0.param_index in
    let is_self = is_header_param header0 k in
    let back_preds = back_edge_set biv0.InductionVar.loop in
    let self_ok =
      all_uses_ok blocks is_self
        (fun i ->
          instr_defines_value i cond
          || List.exists (instr_defines_value i) biv0.update)
        (fun _ _ -> false)
    in
    let cond_ok =
      all_uses_ok blocks (Ssa.Value.equal cond)
        (fun _ -> false)
        (fun bl _ -> Ssa.Block.equal bl header0)
    in
    if not (self_ok && cond_ok)
    then false
    else
      List.for_all
        (fun v ->
          all_uses_ok blocks (Ssa.Value.equal v)
            (fun i -> instr_defines_value i cond)
            (fun bl _ ->
              Ssa.Block.Set.mem bl back_preds
              &&
              match Ssa_view.terminator bl with
              | Terminator.Continue (continuation, args) -> (
                match continuation with
                | Ssa.Goto goto ->
                  (Ssa.Block.equal goto header0
                  &&
                  match arg_value args k with
                  | Some a -> Ssa.Value.equal a v
                  | None -> false)
                  && Int.equal
                       (count_occurrences
                          (fun arg ->
                            match arg with
                            | Ssa.Terminator.Arg a -> Ssa.Value.equal a v
                            | Ssa.Terminator.Omitted_since_unused -> false)
                          args)
                       1
                | _ -> false)
              | _ -> false))
        biv0.update
  | None -> false

(** val loop_is_useless : natural_loop -> biv_result list -> bool **)

let loop_is_useless loop0 bivs0 =
  same_length (Ssa_view.params loop0.header) bivs0
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
