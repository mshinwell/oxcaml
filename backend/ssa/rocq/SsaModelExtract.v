(* Extraction directives for SsaModel.v: which type and function of the
   compiler stand for each abstract type and observation of the model. As
   in OxCamlExtract.v (rocq/), nothing here is proved; the mapping is
   trusted by inspection. The observations that are not functions of [Ssa]
   itself are the functions of backend/ssa/ssa_view.ml, which turn the
   compiler's data into the model's views. *)

From Stdlib Require Import Extraction.
From OxCamlSsa Require Import SsaModel.

(* The abstract types and their equalities. *)
Extract Constant block => "Ssa.finished Ssa.Block.t".
Extract Constant value => "Ssa.finished Ssa.Value.t".
Extract Constant instr => "Ssa.finished Ssa.Instruction.t".
Extract Constant instr_id => "Ssa.finished Ssa.Instruction.Id.t".
Extract Inlined Constant block_eqb => "Ssa.Block.equal".
Extract Inlined Constant value_eqb => "Ssa.Value.equal".
Extract Inlined Constant instr_id_eqb => "Ssa.Instruction.Id.equal".

(* Sets of blocks. *)
Extract Constant blockset => "Ssa.Block.Set.t".
Extract Inlined Constant set_empty => "Ssa.Block.Set.empty".
Extract Inlined Constant set_singleton => "Ssa.Block.Set.singleton".
Extract Inlined Constant set_add => "Ssa.Block.Set.add".
Extract Inlined Constant set_mem => "Ssa.Block.Set.mem".
Extract Inlined Constant set_for_all => "Ssa.Block.Set.for_all".

(* Blocks. *)
Extract Inlined Constant predecessors => "Ssa.Block.predecessors".
Extract Inlined Constant all_successors => "Ssa.Block.all_successors".
Extract Inlined Constant dominates => "Ssa.Block.dominates".
Extract Inlined Constant strict_dominators => "Ssa_view.strict_dominators".
Extract Inlined Constant params => "Ssa_view.params".
Extract Inlined Constant param => "Ssa.Block.param".
Extract Inlined Constant block_body => "Ssa_view.body".

(* Terminators: [continuation] and [Terminator.arg] are the compiler's own
   types, whose constructors must be listed in the same order as in
   backend/ssa/ssa.mli; [Terminator.t] is the model's view. *)
Extract Constant raise_kind => "Lambda.raise_kind".
Extract Inductive continuation => "Ssa.finished Ssa.continuation"
  [ "Ssa.Goto" "Ssa.Return" "Ssa.Raise" "Ssa.Unreachable" ].
Extract Inductive Terminator.arg => "Ssa.finished Ssa.Terminator.arg"
  [ "Ssa.Terminator.Arg" "Ssa.Terminator.Omitted_since_unused" ].
Extract Inlined Constant terminator => "Ssa_view.terminator".

(* Values and instructions. *)
Extract Inlined Constant view_value => "Ssa_view.value".
Extract Inlined Constant view_instr => "Ssa_view.instr".
Extract Inlined Constant has_side_effect => "Ssa.Instruction.has_side_effect".
Extract Inlined Constant tree_of_value => "Ssa_view.tree_of_value".

(* The table [Ssa_view.compute_op_def] builds. The type is spelt out, as
   Ssa_view depends on the extraction of SsaModel.v. *)
Extract Constant op_def =>
  "(Ssa.finished, Ssa.finished Ssa.Block.t) Ssa.Instruction.Id.Tbl.t".
Extract Inlined Constant op_def_find => "Ssa.Instruction.Id.Tbl.find_opt".
