(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Vincent Laviron, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023 OCamlPro SAS                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Comparison_result], after its interface
   middle_end/flambda2/simplify/comparison_result.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_primitive Format Variable_.

(* comparison_result.mli:15  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Comparison_result.t".
(* comparison_result.mli:17  val create : prim:Flambda_primitive.t -> comparison_results:t Variable.Map.t -> t option *)
Parameter create : Flambda_primitive.t -> Variable_.Map.t t -> M (option t).
Extract Inlined Constant create => "Comparison_result.create".
(* comparison_result.mli:20  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Comparison_result.print".
(* comparison_result.mli:22  val convert_result_compared_to_tagged_zero : t -> Flambda_primitive.signed_or_unsigned Flambda_primitive.comparison -> Flambda_primitive.t option *)
Parameter convert_result_compared_to_tagged_zero : t -> Flambda_primitive.comparison Flambda_primitive.signed_or_unsigned -> M (option Flambda_primitive.t).
Extract Inlined Constant convert_result_compared_to_tagged_zero => "Comparison_result.convert_result_compared_to_tagged_zero".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Comparison_result. End Comparison_result.
