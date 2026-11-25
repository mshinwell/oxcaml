(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*            Mark Shinwell and Xavier Clerc, Jane Street Europe          *)
(*                       Guillaume Bury, OCamlPro SAS                     *)
(*                                                                        *)
(*   Copyright 2017--2023 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Empty_array_kind], after its interface
   middle_end/flambda2/term_basics/empty_array_kind.mli
   (Git blob b498799a865133d47ed5a7e62f458e5dd90592d7). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* empty_array_kind.mli:16  type t = | Values_or_immediates_or_naked_floats ( ** Traditional OCaml arrays. * ) | Unboxed_products | Naked_float32s | Naked_ints | Naked_int8s | Naked_int16s | Naked_int32s | Naked_int64s | Naked_nativeints | Naked_vec128s | Naked_vec256s | Naked_vec512s | Naked_masks *)
Parameter t : Type.
Extract Inlined Constant t => "Empty_array_kind.t".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Empty_array_kind. End Empty_array_kind.
