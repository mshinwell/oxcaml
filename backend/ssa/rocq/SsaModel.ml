type block = Ssa.finished Ssa.Block.t

type value = Ssa.finished Ssa.Value.t

type instr = Ssa.finished Ssa.Instruction.t

type instr_id = Ssa.finished Ssa.Instruction.Id.t

type blockset = Ssa.Block.Set.t

type raise_kind = Lambda.raise_kind

module Terminator = struct
  type t =
    | Continue of
        Ssa.finished Ssa.continuation * Ssa.finished Ssa.Terminator.arg list
    | Switch of value * block list
    | Call of value list
    | Invalid of value list
end

type value_view =
  | Res of instr_id * Operation.t * value list
  | Block_param of block * int

type instr_view =
  | Op of instr_id * value list
  | Push_trap
  | Pop_trap

type tree =
  | Const_int of value * int64
  | Iadd of value * tree * tree
  | Isub of value * tree * tree
  | Iadd_imm of value * tree * int
  | Isub_imm of value * tree * int
  | Ilsl of value * tree * int
  | Iasr of value * tree * int
  | Ilsr of value * int
  | Ior of value * tree * int
  | Icomp of value * Cmm.integer_comparison * tree * tree
  | Icomp_imm of value * Cmm.integer_comparison * tree * int
  | Other of value

(** val root : tree -> value **)

let root = function
  | Const_int (v, _) -> v
  | Iadd (v, _, _) -> v
  | Isub (v, _, _) -> v
  | Iadd_imm (v, _, _) -> v
  | Isub_imm (v, _, _) -> v
  | Ilsl (v, _, _) -> v
  | Iasr (v, _, _) -> v
  | Ilsr (v, _) -> v
  | Ior (v, _, _) -> v
  | Icomp (v, _, _, _) -> v
  | Icomp_imm (v, _, _, _) -> v
  | Other v -> v

type op_def = (Ssa.finished, Ssa.finished Ssa.Block.t) Ssa.Instruction.Id.Tbl.t
