(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                        Nicolas Ojeda Bar, LexiFi                       *)
(*                    Mark Shinwell, Jane Street Europe                   *)
(*                                                                        *)
(*   Copyright 2016 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*   Copyright 2017--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Targetint_32_64], after its interface
   middle_end/flambda2/numbers/targetint_32_64.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Stdlib_ Target_system.

(* targetint_32_64.mli:32  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Targetint_32_64.t".
(* targetint_32_64.mli:140  val of_int : Target_system.Machine_width.t -> int -> t *)
Parameter of_int : Target_system.Machine_width.t -> int -> M t.
Extract Inlined Constant of_int => "Targetint_32_64.of_int".
(* targetint_32_64.mli:148  val to_int : t -> int *)
Parameter to_int : t -> M int.
Extract Inlined Constant to_int => "Targetint_32_64.to_int".
(* targetint_32_64.mli:159  val of_float : Target_system.Machine_width.t -> float -> t *)
Parameter of_float : Target_system.Machine_width.t -> Stdlib_.float_ -> M t.
Extract Inlined Constant of_float => "Targetint_32_64.of_float".
(* targetint_32_64.mli:162  val to_float : t -> float *)
Parameter to_float : t -> M Stdlib_.float_.
Extract Inlined Constant to_float => "Targetint_32_64.to_float".
(* targetint_32_64.mli:165  val of_int32 : Target_system.Machine_width.t -> int32 -> t *)
Parameter of_int32 : Target_system.Machine_width.t -> Stdlib_.int32 -> M t.
Extract Inlined Constant of_int32 => "Targetint_32_64.of_int32".
(* targetint_32_64.mli:171  val to_int32 : t -> int32 *)
Parameter to_int32 : t -> M Stdlib_.int32.
Extract Inlined Constant to_int32 => "Targetint_32_64.to_int32".
(* targetint_32_64.mli:175  val of_int64 : Target_system.Machine_width.t -> int64 -> t *)
Parameter of_int64 : Target_system.Machine_width.t -> Stdlib_.int64 -> M t.
Extract Inlined Constant of_int64 => "Targetint_32_64.of_int64".
(* targetint_32_64.mli:178  val to_int64 : t -> int64 *)
Parameter to_int64 : t -> M Stdlib_.int64.
Extract Inlined Constant to_int64 => "Targetint_32_64.to_int64".
Module Set_.
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Targetint_32_64.Set.t".
End Set_.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Targetint_32_64. End Targetint_32_64.
