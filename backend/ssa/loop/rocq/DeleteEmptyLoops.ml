open DeadInductionVar
open InductionVar
open LoopTermination
open NaturalLoop
open SsaModel

(** val terminator_pure_control : Terminator.t -> bool **)

let terminator_pure_control = function
  | Terminator.Continue (continuation, _) -> (
    match continuation with Ssa.Goto _ -> true | _ -> false)
  | Terminator.Switch (_, _) -> true
  | _ -> false

(** val body_effect_free : natural_loop -> bool **)

let body_effect_free loop0 =
  Ssa.Block.Set.for_all
    (fun bl ->
      List.for_all
        (fun i -> not (Ssa.Instruction.has_side_effect i))
        (Ssa_view.body bl)
      && terminator_pure_control (Ssa_view.terminator bl))
    loop0.body

(** val find_deletions : op_def -> block list -> (block * block) list **)

let find_deletions op_def0 blocks =
  let loops = InductionVar.analyze op_def0 blocks in
  let dead = DeadInductionVar.analyze blocks loops in
  List.filter_map
    (fun dr ->
      let loop0 = dr.DeadInductionVar.loop in
      let bivs0 = List.map (fun br -> br.biv) dr.bivs in
      let terminates =
        match analyze op_def0 loop0 bivs0 with
        | Terminates -> true
        | Unknown -> false
      in
      if (dr.useless && terminates) && body_effect_free loop0
      then
        match find_exit_branch loop0 with
        | Some exit_info -> (
          match Ssa_view.params exit_info.exit_target with
          | [] -> Some (loop0.header, exit_info.exit_target)
          | _ :: _ -> None)
        | None -> None
      else None)
    dead
