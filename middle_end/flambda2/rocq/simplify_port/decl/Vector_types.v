(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017--2019 OCamlPro SAS                                    *)
(*   Copyright 2017--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Vector_types], after its interface
   middle_end/flambda2/numbers/vector_types.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Vec128.
  Module Bit_pattern.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Vector_types.Vec128.Bit_pattern.t".
  End Bit_pattern.
End Vec128.
Module Vec256.
  Module Bit_pattern.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Vector_types.Vec256.Bit_pattern.t".
  End Bit_pattern.
End Vec256.
Module Vec512.
  Module Bit_pattern.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Vector_types.Vec512.Bit_pattern.t".
  End Bit_pattern.
End Vec512.
Module Mask.
  Module Bit_pattern.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Vector_types.Mask.Bit_pattern.t".
  End Bit_pattern.
End Mask.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Vector_types. End Vector_types.
