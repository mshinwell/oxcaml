(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Removed_operations], after its interface
   middle_end/flambda2/terms/removed_operations.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* removed_operations.mli:17  type t = private { call : int; alloc : int; prim : int; branch : int; direct_call_of_indirect : int; updated_direct_call : int; ( ** Updated direct calls is the count of direct call changed from one code_id to another. It does not count in evaluate, but it matters for equal. * ) ( * CR pchambart: it should track in some way the difference between the called codes * ) specialized_poly_compare : ... *)
Parameter t : Type.
Extract Inlined Constant t => "Removed_operations.t".
