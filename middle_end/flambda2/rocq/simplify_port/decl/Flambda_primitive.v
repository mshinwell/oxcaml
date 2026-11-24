(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*            Mark Shinwell and Xavier Clerc, Jane Street Europe          *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   Copyright 2017--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flambda_primitive], after its interface
   middle_end/flambda2/terms/flambda_primitive.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Array_kind.
  (* flambda_primitive.mli:54  type t = | Immediates ( ** An array consisting only of immediate values. * ) | Gc_ignorable_values ( ** An array consisting of [value]-kind elements that the GC may ignore. * ) | Values ( ** An array consisting of elements of kind [value]. With the float array optimisation enabled, such elements must never be [float]s. * ) | Naked_floats ( ** An array consisting of naked floats, represented usi... *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Array_kind.t".
End Array_kind.
(* flambda_primitive.mli:273  type 'signed_or_unsigned comparison = | Eq | Neq | Lt of 'signed_or_unsigned | Gt of 'signed_or_unsigned | Le of 'signed_or_unsigned | Ge of 'signed_or_unsigned *)
Parameter comparison : Type -> Type.
Extract Constant comparison "'a1" => "('a1) Flambda_primitive.comparison".
(* flambda_primitive.mli:353  type signed_or_unsigned = | Signed | Unsigned *)
Parameter signed_or_unsigned : Type.
Extract Inlined Constant signed_or_unsigned => "Flambda_primitive.signed_or_unsigned".
(* flambda_primitive.mli:667  type t = | Nullary of nullary_primitive | Unary of unary_primitive * Simple.t | Binary of binary_primitive * Simple.t * Simple.t | Ternary of ternary_primitive * Simple.t * Simple.t * Simple.t | Quaternary of quaternary_primitive * Simple.t * Simple.t * Simple.t * Simple.t | Variadic of variadic_primitive * Simple.t list *)
Parameter t : Type.
Extract Inlined Constant t => "Flambda_primitive.t".
Module Eligible_for_cse.
  (* flambda_primitive.mli:788  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Eligible_for_cse.t".
End Eligible_for_cse.
