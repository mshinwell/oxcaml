(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2019--2019 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Slot_offsets], after its interface
   middle_end/flambda2/simplify_shared/slot_offsets.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Set_of_closures.

(* slot_offsets.mli:20  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Slot_offsets.t".
(* slot_offsets.mli:52  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Slot_offsets.print".
(* slot_offsets.mli:55  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Slot_offsets.empty".
(* slot_offsets.mli:58  val add_set_of_closures : t -> is_phantom:bool -> Set_of_closures.t -> t *)
Parameter add_set_of_closures : t -> bool -> Set_of_closures.t -> M t.
Extract Inlined Constant add_set_of_closures => "Slot_offsets.add_set_of_closures".
(* slot_offsets.mli:70  val add_offsets_from_function : t -> from_function:t -> t *)
Parameter add_offsets_from_function : t -> t -> M t.
Extract Inlined Constant add_offsets_from_function => "Slot_offsets.add_offsets_from_function".
