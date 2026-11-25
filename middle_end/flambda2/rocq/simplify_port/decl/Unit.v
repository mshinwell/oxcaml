(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018 OCamlPro SAS                                          *)
(*   Copyright 2018 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Unit], after its interface
   middle_end/flambda2/term_basics/unit.mli
   (Git blob 7409f02595aad464f2c2ea74e7c650e3c851c6a7). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* unit.mli:17  type t = unit *)
Definition t : Type := unit.
Extract Inlined Constant t => "Unit.t".
Module T.
  (* unit.mli:19  include Container_types.S with type t := t *)
  Definition t : Type := Unit.t.
  Extract Inlined Constant t => "Unit.T.t".
End T.
(* unit.mli:19  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Unit.T.t -> M unit.
Extract Inlined Constant print => "Unit.print".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Unit. End Unit.
