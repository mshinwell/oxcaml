(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Numeric_types], after its interface
   middle_end/flambda2/numbers/numeric_types.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Int8.
  (* numeric_types.mli:32  type t = private int *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Int8.t".
End Int8.
Module Int16.
  (* numeric_types.mli:56  type t = private int *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Int16.t".
End Int16.
Module Float_by_bit_pattern.
  (* container_types_intf.ml:297  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.t".
End Float_by_bit_pattern.
Module Float32_by_bit_pattern.
  (* container_types_intf.ml:297  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.t".
End Float32_by_bit_pattern.
