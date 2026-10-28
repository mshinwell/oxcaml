open SsaGraph
open SsaModel

(** val supported_operation : Operation.t -> 'a1 list -> bool **)

let supported_operation op args =
  match op with
  | Operation.Const_int _ -> ( match args with [] -> true | _ :: _ -> false)
  | Operation.Intop op0 -> (
    match op0 with
    | Operation.Iadd -> (
      match args with
      | [] -> false
      | _ :: l -> (
        match l with
        | [] -> false
        | _ :: l0 -> ( match l0 with [] -> true | _ :: _ -> false)))
    | Operation.Isub -> (
      match args with
      | [] -> false
      | _ :: l -> (
        match l with
        | [] -> false
        | _ :: l0 -> ( match l0 with [] -> true | _ :: _ -> false)))
    | Operation.Icomp _ -> (
      match args with
      | [] -> false
      | _ :: l -> (
        match l with
        | [] -> false
        | _ :: l0 -> ( match l0 with [] -> true | _ :: _ -> false)))
    | _ -> false)
  | Operation.Intop_imm (op0, _) -> (
    match op0 with
    | Operation.Iadd -> (
      match args with
      | [] -> false
      | _ :: l -> ( match l with [] -> true | _ :: _ -> false))
    | Operation.Isub -> (
      match args with
      | [] -> false
      | _ :: l -> ( match l with [] -> true | _ :: _ -> false))
    | Operation.Icomp _ -> (
      match args with
      | [] -> false
      | _ :: l -> ( match l with [] -> true | _ :: _ -> false))
    | _ -> false)
  | _ -> false

(** val supported_instruction : Ssa.finished Ssa.Instruction.t -> bool **)

let supported_instruction instruction =
  (fun f_op f_push_trap f_pop_trap (i : Ssa.finished Ssa.Instruction.t) ->
    match i with
    | Ssa.Instruction.Op { Ssa.Instruction.id; op; args; typ; _ } ->
      f_op id op (Array.to_list args) (Array.length typ)
    | Ssa.Instruction.Push_trap _ -> f_push_trap ()
    | Ssa.Instruction.Pop_trap _ -> f_pop_trap ())
    (fun _ op args results ->
      Int.equal results 1 && supported_operation op args)
    (fun _ -> false)
    (fun _ -> false)
    instruction

(** val supported_block : block -> bool **)

let supported_block b =
  List.for_all supported_instruction (block_body b)
  && terminator_pure_control (Ssa.Block.terminator b)
