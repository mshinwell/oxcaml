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

open! Int_replace_polymorphic_compare

[@@@ocaml.warning "+a-40-41-42"]

(* See [induction_var.mli] for the interface.

   The implementation is [InductionVar], generated from the Rocq model in
   [rocq/InductionVar.v] by [rocq/Extract.v] (see [rocq/Makefile]), except
   [compute_op_def], which fills a hash table and is not modelled. This file
   adds the labelled arguments of the interface. *)

open Ssa.Export
module E = InductionVar

type loop = Natural_loop.loop =
  { header : finished Block.t;
    body : Block.Set.t;
    back_edges : finished Block.t list
  }

type op_def = (finished, finished Block.t) Instruction.Id.Tbl.t

let compute_op_def (ssa : finished Ssa.graph) : op_def =
  let tbl : op_def = Instruction.Id.Tbl.create 64 in
  List.iter
    (fun (bl : finished Block.t) ->
      Array.iter
        (fun (i : finished Instruction.t) ->
          match i with
          | Op { id; _ } -> Instruction.Id.Tbl.replace tbl id bl
          | Push_trap _ | Pop_trap _ -> ())
        (Block.body bl))
    (Ssa.blocks ssa);
  tbl

type step = E.biv_step =
  | Step_const of int
  | Step_var of finished Value.t

type biv = E.biv =
  { loop : loop;
    param_index : int;
    update : finished Value.t list;
    step : step;
    sign : [`Add | `Sub]
  }

let analyze ~op_def (ssa : finished Ssa.graph) : (loop * biv list) list =
  E.analyze op_def (Ssa.blocks ssa)

let is_header_param = E.is_header_param

let signed_step = E.signed_step

let back_edge_set = E.back_edge_set

let is_loop_invariant ~op_def ~header v = E.is_loop_invariant op_def header v
