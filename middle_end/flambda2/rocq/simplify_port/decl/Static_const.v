(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Static_const], after its interface
   middle_end/flambda2/terms/static_const.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* static_const.mli:25  type t = private | Set_of_closures of Set_of_closures.t | Block of Tag.Scannable.t * Mutability.t * Flambda_kind.Scannable_block_shape.t * Simple.With_debuginfo.t list | Boxed_float32 of Numeric_types.Float32_by_bit_pattern.t Or_variable.t | Boxed_float of Numeric_types.Float_by_bit_pattern.t Or_variable.t | Boxed_int32 of Int32.t Or_variable.t | Boxed_int64 of Int64.t Or_variable.t | Boxed_nat... *)
Parameter t : Type.
Extract Inlined Constant t => "Static_const.t".
Module Map.
  (* static_const.mli:71  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Static_const.Map.t".
End Map.
