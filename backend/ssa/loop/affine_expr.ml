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

(* See [affine_expr.mli] for the interface.

   The implementation is [AffineExpr], generated from the Rocq model in
   [rocq/AffineExpr.v] by [rocq/Extract.v] (see [rocq/Makefile]). The model's
   expressions have positional constructor arguments where the interface has
   inline records, so [to_affine] converts first; and the model returns [None]
   where the interface raises [Overflow]. *)

module E = AffineExpr
module Affine = Fourier_motzkin.Affine

type t =
  | Const of int
  | Atom of int
  | Add of t * t
  | Sub of t * t
  | Scale of int * t
  | Shr_atom of
      { atom : int;
        arg : t;
        bits : int
      }
  | Lsr_atom of
      { atom : int;
        bits : int
      }
  | Or_atom of
      { atom : int;
        arg : t;
        mask : int
      }

module Range = struct
  type t = E.Range.t =
    { lo : int64;
      hi : int64
    }

  let full = E.Range.full

  let const = E.Range.const

  let shr_signed = E.Range.shr_signed

  let shr_logical = E.Range.shr_logical

  let or_mask = E.Range.or_mask

  let add = E.Range.add

  let sub = E.Range.sub

  let scale = E.Range.scale
end

let rec to_model (e : t) : E.t =
  match e with
  | Const c -> E.Const c
  | Atom id -> E.Atom id
  | Add (a, b) -> E.Add (to_model a, to_model b)
  | Sub (a, b) -> E.Sub (to_model a, to_model b)
  | Scale (k, a) -> E.Scale (k, to_model a)
  | Shr_atom { atom; arg; bits } -> E.Shr_atom (atom, to_model arg, bits)
  | Lsr_atom { atom; bits } -> E.Lsr_atom (atom, bits)
  | Or_atom { atom; arg; mask } -> E.Or_atom (atom, to_model arg, mask)

let to_affine e =
  match E.to_affine (to_model e) with
  | Some result -> result
  | None -> raise Fourier_motzkin.Overflow
