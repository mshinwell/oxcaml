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

   The implementation is [AffineSsa], generated from the Rocq model in
   [rocq/AffineSsa.v] by [rocq/Extract.v] (see [rocq/Makefile]). The model
   cannot look inside SSA values, so it works on the copy of the part of the
   value graph it inspects built by [Ssa_view.tree_of_value]; and it passes its
   atom interner and its list of side facts along as values, which this file
   keeps in the mutable [ctx] and the [side] reference of the interface. *)

open Ssa.Export
module Affine = Fourier_motzkin.Affine
module E = AffineSsa

type ctx = { mutable c : E.ctx }

let new_ctx () = { c = E.new_ctx }

let linearize ctx side (v : finished Value.t) : Affine.t =
  let (form, side'), c = E.linearize ctx.c !side (Ssa_view.tree_of_value v) in
  side := side';
  ctx.c <- c;
  form

let guards_at ctx side (target : finished Block.t) : Affine.t list =
  let (facts, side'), c = E.guards_at ctx.c !side target in
  side := side';
  ctx.c <- c;
  facts
