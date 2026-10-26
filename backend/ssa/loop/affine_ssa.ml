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

(* See [affine_ssa.mli] for the interface.

   The linearization of values and the facts of a branch are [AffineSsa],
   generated from the Rocq model in [rocq/AffineSsa.v] by [rocq/Extract.v] (see
   [rocq/Makefile]). The model cannot look inside SSA values, so it works on a
   copy of the part of the value graph it inspects, built by [tree_of_value]
   below; and it passes its atom interner and its list of side facts along as
   values, which this file keeps in the mutable [ctx] and the [side] reference
   of the interface. [guards_at], which walks the dominator tree, is not
   modelled and is as it was. *)

open Ssa.Export
module Affine = Fourier_motzkin.Affine
module E = AffineSsa

type ctx = { mutable c : E.ctx }

let new_ctx () = { c = E.new_ctx }

(* The operations defining [v] and, recursively, its arguments, in the shapes
   the model matches on. This is the one place that looks inside SSA values;
   [tree_sound] in rocq/AffineSsa.v says what each node asserts about the
   machine values, which is what the proofs assume of this function. *)
let rec tree_of_value (v : finished Value.t) : E.tree =
  match[@warning "-fragile-match"] v with
  | Res ({ op = Const_int n; _ }, _) -> E.Const_int (v, Int64.of_nativeint n)
  | Res ({ op = Intop Iadd; args = [| a; b |]; _ }, _) ->
    E.Iadd (v, tree_of_value a, tree_of_value b)
  | Res ({ op = Intop Isub; args = [| a; b |]; _ }, _) ->
    E.Isub (v, tree_of_value a, tree_of_value b)
  | Res ({ op = Intop_imm (Iadd, k); args = [| a |]; _ }, _) ->
    E.Iadd_imm (v, tree_of_value a, k)
  | Res ({ op = Intop_imm (Isub, k); args = [| a |]; _ }, _) ->
    E.Isub_imm (v, tree_of_value a, k)
  | Res ({ op = Intop_imm (Ilsl, k); args = [| a |]; _ }, _) ->
    E.Ilsl (v, tree_of_value a, k)
  | Res ({ op = Intop_imm (Iasr, k); args = [| a |]; _ }, _) ->
    E.Iasr (v, tree_of_value a, k)
  | Res ({ op = Intop_imm (Ilsr, k); args = [| _ |]; _ }, _) -> E.Ilsr (v, k)
  | Res ({ op = Intop_imm (Ior, m); args = [| a |]; _ }, _) ->
    E.Ior (v, tree_of_value a, m)
  | Res ({ op = Intop (Icomp cmp); args = [| a; b |]; _ }, _) ->
    E.Icomp (v, cmp, tree_of_value a, tree_of_value b)
  | Res ({ op = Intop_imm (Icomp cmp, k); args = [| a |]; _ }, _) ->
    E.Icomp_imm (v, cmp, tree_of_value a, k)
  | _ -> E.Other v

let linearize ctx side (v : finished Value.t) : Affine.t =
  let (form, side'), c = E.linearize ctx.c !side (tree_of_value v) in
  side := side';
  ctx.c <- c;
  form

let cond_facts ctx side ~negate (cond : finished Value.t) : Affine.t list =
  let (facts, side'), c =
    E.cond_facts ctx.c !side negate (tree_of_value cond)
  in
  side := side';
  ctx.c <- c;
  facts

(* Facts that hold at entry to [target], gathered from the two-target branches
   on its immediate-dominator chain. In a two-target [Switch], [targets.(0)] is
   the false edge and [targets.(1)] the true edge. *)
let guards_at ctx side (target : finished Block.t) : Affine.t list =
  let acc = ref [] in
  let rec walk (block : finished Block.t) =
    let idom = Block.immediate_dominator block in
    if not (Block.equal idom block)
    then begin
      (match[@warning "-fragile-match"] Block.terminator idom with
      | Switch { index; targets = [| ifnot; ifso |] } ->
        (* [index] (or its negation) is a fact at [target] only if the taken
           edge [idom -> ifso] (resp. [idom -> ifnot]) *dominates* [target] —
           i.e. every path from entry to [target] traverses that specific edge;
           see {!Natural_loop.edge_dominates}. *)
        let edge_dominates (succ : finished Block.t) =
          Natural_loop.edge_dominates ~src:idom ~succ ~target
        in
        if edge_dominates ifso
        then acc := cond_facts ctx side ~negate:false index @ !acc
        else if edge_dominates ifnot
        then acc := cond_facts ctx side ~negate:true index @ !acc
      | _ -> ());
      walk idom
    end
  in
  walk target;
  !acc
