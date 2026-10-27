(* The SSA graph as the loop models see it.

   The models of backend/ssa/loop/ run on a finished SSA graph
   ([Ssa.finished Ssa.graph]), but its blocks, values and instructions are
   OxCaml data the models cannot look inside. This file declares them as
   abstract types ([Parameter]), with the few observations the passes make
   of them: what a value is defined by, what a block's terminator is, and
   so on. Each observation is realized at extraction (SsaModelExtract.v) by
   a function of the compiler: some directly by [Ssa] ([Block.predecessors],
   [Block.dominates], ...), the others by the small functions of
   backend/ssa/ssa_view.ml, each of which turns a [match] on that data into one
   of the [Inductive] views below.

   Nothing here is proved. What the proofs rely on about these observations
   is stated where it is used, as hypotheses of the theorems (what an
   operation computes, what dominance means, how a run of a loop goes). The
   axioms below say only how the equalities and the block sets behave,
   which is what [Ssa.Block.equal] (identity of blocks), [Ssa.Value.equal]
   (identity of values) and [Ssa.Block.Set] (sets ordered by block id)
   provide. *)

From Stdlib Require Import ZArith Bool List.
From OxCamlStdlib Require Import OxCamlInt OxCamlInt64.
From OxCamlBackend Require Import IntegerComparison.
Import ListNotations.

(* ======================================================================== *)
(* The abstract types and their equalities                                  *)
(* ======================================================================== *)

(* [Ssa.finished Ssa.Block.t], [Ssa.finished Ssa.Value.t],
   [Ssa.finished Ssa.Instruction.t] and [Ssa.finished Ssa.Instruction.Id.t]. *)
Parameter block : Type.
Parameter value : Type.
Parameter instr : Type.
Parameter instr_id : Type.

(* [Ssa.Block.equal], [Ssa.Value.equal] and [Ssa.Instruction.Id.equal]:
   the identity of the OxCaml data, which the models take as equality. *)
Parameter block_eqb : block -> block -> bool.
Parameter value_eqb : value -> value -> bool.
Parameter instr_id_eqb : instr_id -> instr_id -> bool.
Axiom block_eqb_spec : forall a b, block_eqb a b = true <-> a = b.
Axiom value_eqb_spec : forall a b, value_eqb a b = true <-> a = b.
Axiom instr_id_eqb_spec : forall a b, instr_id_eqb a b = true <-> a = b.

(* ======================================================================== *)
(* Sets of blocks: [Ssa.Block.Set]                                          *)
(* ======================================================================== *)

Parameter blockset : Type.
Parameter set_empty : blockset.
Parameter set_singleton : block -> blockset.
Parameter set_add : block -> blockset -> blockset.
Parameter set_mem : block -> blockset -> bool.
Parameter set_for_all : (block -> bool) -> blockset -> bool.
(* Membership: nothing is in the empty set; a singleton holds its element;
   adding a block puts it in and keeps the others; [set_for_all f] holds
   exactly when [f] holds of every member. *)
Axiom set_mem_empty : forall b, set_mem b set_empty = false.
Axiom set_mem_singleton : forall b x,
  set_mem b (set_singleton x) = block_eqb b x.
Axiom set_mem_add : forall b x s,
  set_mem b (set_add x s) = block_eqb b x || set_mem b s.
Axiom set_for_all_spec : forall f s,
  set_for_all f s = true <-> (forall b, set_mem b s = true -> f b = true).

(* ======================================================================== *)
(* Blocks                                                                   *)
(* ======================================================================== *)

(* [Block.predecessors], [Block.all_successors] (the structural successors
   and the exception successor) and [Block.dominates]: [dominates a b] says
   that [a] dominates [b], [a = b] included. *)
Parameter predecessors : block -> list block.
Parameter all_successors : block -> list block.
Parameter dominates : block -> block -> bool.

(* The blocks that strictly dominate a block, nearest first, ending with
   the graph's entry: the chain [AffineSsa.guards_at] walks, built by
   [Ssa_view.strict_dominators] with [Block.immediate_dominator]. *)
Parameter strict_dominators : block -> list block.

(* [Block.params] as a list, [Block.param], and [Block.body] as a list
   ([block_body], as the loop record of NaturalLoop.v has a [body]). *)
Parameter params : block -> list value.
Parameter param : block -> int -> value.
Parameter block_body : block -> list instr.

(* --- Terminators --- *)

(* [Ssa.continuation]; the payload of [Raise] is not inspected. *)
Parameter raise_kind : Type.
Inductive continuation : Type :=
  | Goto (b : block)
  | Return
  | Raise (k : raise_kind)
  | Unreachable.

(* [Ssa.Terminator]: [arg] is [Terminator.arg], and [t] is [Terminator.t]
   with its arrays as lists and only the fields the loop passes read. *)
Module Terminator.
  Inductive arg : Type :=
    | Arg (v : value)
    | Omitted_since_unused.

  Inductive t : Type :=
    | Continue (continuation : continuation) (args : list arg)
    | Switch (index : value) (targets : list block)
    | Call (args : list value)
    | Invalid (args : list value).
End Terminator.

(* [Block.terminator]. *)
Parameter terminator : block -> Terminator.t.

(* ======================================================================== *)
(* Values and instructions                                                  *)
(* ======================================================================== *)

(* The shapes of a [Value.t] the loop passes match on. [Res id op] is
   [Res ({ id; op; args; _ }, _)] with [op] and [args] summarized as an
   [op_view]: [Op_add x y] is [op = Intop Iadd] with [args = [| x; y |]],
   [Op_add_imm x c] is [op = Intop_imm (Iadd, c)] with [args = [| x |]],
   and so on; [Op_const] is any of the [Const_*] operations; [Op_other] is
   everything else, including the above with an unexpected number of
   arguments. [Block_param b i] is [Block_param (b, i)]. *)
Inductive op_view : Type :=
  | Op_const
  | Op_add (x y : value)
  | Op_sub (x y : value)
  | Op_add_imm (x : value) (c : int)
  | Op_sub_imm (x : value) (c : int)
  | Op_comp (cmp : integer_comparison) (x y : value)
  | Op_comp_imm (cmp : integer_comparison) (x : value) (k : int)
  | Op_other.

Inductive value_view : Type :=
  | Res (id : instr_id) (op : op_view)
  | Block_param (b : block) (i : int).

Parameter view_value : value -> value_view.

(* The shape of an [Instruction.t]: [Op id args] is [Op { id; args; _ }]
   with the arguments as a list. *)
Inductive instr_view : Type :=
  | Op (id : instr_id) (args : list value)
  | Push_trap
  | Pop_trap.

Parameter view_instr : instr -> instr_view.

(* [Instruction.has_side_effect]. *)
Parameter has_side_effect : instr -> bool.

(* --- The tree view of a value graph, for AffineSsa.v --- *)

(* What [AffineSsa.expr_of_value] matches on, as a tree built by
   [Ssa_view.tree_of_value]: each node holds its SSA value [v], and, when
   [v] is defined by an operation the recogniser knows, that operation with
   the trees of the arguments it looks at. The constructors follow the
   patterns of [Ssa_view.tree_of_value]: [Iadd v a b] is [Res ({ op = Intop
   Iadd; args = [| a; b |] }, _)], [Iadd_imm v a k] is [Intop_imm (Iadd,
   k)] with argument [a], and so on. [Const_int]'s [nativeint] is an
   [Int64] here (the same integers on a 64-bit machine; [Ssa_view]
   converts). The argument of a logical shift is not inspected and is not
   kept. [Other] is every other value, which is atomized. *)
Inductive tree : Type :=
  | Const_int (v : value) (n : Int64.t)
  | Iadd (v : value) (a b : tree)
  | Isub (v : value) (a b : tree)
  | Iadd_imm (v : value) (a : tree) (k : int)
  | Isub_imm (v : value) (a : tree) (k : int)
  | Ilsl (v : value) (a : tree) (k : int)
  | Iasr (v : value) (a : tree) (k : int)
  | Ilsr (v : value) (k : int)
  | Ior (v : value) (a : tree) (m : int)
  | Icomp (v : value) (cmp : integer_comparison) (a b : tree)
  | Icomp_imm (v : value) (cmp : integer_comparison) (a : tree) (k : int)
  | Other (v : value).

(* The SSA value a tree stands for. *)
Definition root (t : tree) : value :=
  match t with
  | Const_int v _ | Iadd v _ _ | Isub v _ _ | Iadd_imm v _ _ | Isub_imm v _ _
  | Ilsl v _ _ | Iasr v _ _ | Ilsr v _ | Ior v _ _ | Icomp v _ _ _
  | Icomp_imm v _ _ _ | Other v => v
  end.

(* [Ssa_view.tree_of_value], and the one thing assumed of its shape: the
   tree built for a value has that value at its root (every branch of the
   it builds a node for [v] itself). What the nodes assert about the
   machine values is [tree_sound] in AffineSsa.v, assumed where used. *)
Parameter tree_of_value : value -> tree.
Axiom tree_of_value_root : forall v, root (tree_of_value v) = v.

(* ======================================================================== *)
(* The table of defining blocks                                             *)
(* ======================================================================== *)

(* The table from the id of each [Op] to the block defining it, built by
   [Ssa_view.compute_op_def]; [op_def_find] is
   [Instruction.Id.Tbl.find_opt]. *)
Parameter op_def : Type.
Parameter op_def_find : op_def -> instr_id -> option block.
