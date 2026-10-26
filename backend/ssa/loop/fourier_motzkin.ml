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

(* See [fourier_motzkin.mli] for the interface.

   The implementation is [FourierMotzkin], generated from the Rocq model in
   [rocq/FourierMotzkin.v] by [rocq/Extract.v] (see [rocq/Makefile]). The model
   returns [None] where the interface raises [Overflow]; this file raises it. *)

module E = FourierMotzkin

exception Overflow

module Affine = struct
  type t = E.Affine.t =
    { const : int;
      terms : (int * int) list
    }

  let const = E.Affine.constant

  let var = E.Affine.var

  let equal = E.Affine.equal

  let coeff = E.Affine.coeff

  let add_const = E.Affine.add_const

  let add = E.Affine.add

  let scale = E.Affine.scale

  let neg = E.Affine.neg

  let sub = E.Affine.sub

  let checked = function Some f -> f | None -> raise Overflow

  let add_checked a b = checked (E.Affine.add_checked a b)

  let scale_checked k f = checked (E.Affine.scale_checked k f)

  let add_const_checked f c = checked (E.Affine.add_const_checked f c)

  let sub_checked a b = checked (E.Affine.sub_checked a b)
end

let feasible = E.feasible

let entails = E.entails
