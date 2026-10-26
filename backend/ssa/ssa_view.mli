(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

[@@@ocaml.warning "+a-40-41-42"]

(** The observations of a finished SSA graph made by the Rocq models of the SSA
    passes (rocq/SsaModel.v), as the OCaml functions the models' abstract
    observations are extracted to. Each function turns a [match] on the
    compiler's data into one of the model's views; rocq/SsaModelExtract.v says
    which observation each one realizes.

    These functions are trusted, not proved: the proofs assume of each view what
    the model says it means (for instance, that the tree built by
    {!tree_of_value} is truthful in the sense of [tree_sound] in
    backend/ssa/loop/rocq/AffineSsa.v). *)

open Ssa.Export

(** [SsaModel.view_value]: the shape of the operation defining a value. *)
val value : finished Value.t -> SsaModel.value_view

(** [SsaModel.view_instr]: the shape of an instruction. *)
val instr : finished Instruction.t -> SsaModel.instr_view

(** [SsaModel.terminator]: a block's terminator, with its arrays as lists. *)
val terminator : finished Block.t -> SsaModel.Terminator.t

(** [SsaModel.params]: [Block.params] as a list. *)
val params : finished Block.t -> finished Value.t list

(** [SsaModel.block_body]: [Block.body] as a list. *)
val body : finished Block.t -> finished Instruction.t list

(** [SsaModel.strict_dominators]: the blocks strictly dominating a block,
    nearest first, ending with the graph's entry; the chain
    [Block.immediate_dominator] walks. *)
val strict_dominators : finished Block.t -> finished Block.t list

(** [SsaModel.tree_of_value]: the operations defining a value and, recursively,
    its arguments, in the shapes the affine linearization
    (backend/ssa/loop/rocq/AffineSsa.v) matches on. *)
val tree_of_value : finished Value.t -> SsaModel.tree
