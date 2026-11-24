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
From SimplifyPort.decl Require Flambda_primitive.

(* removed_operations.mli:17  type t = private { call : int; alloc : int; prim : int; branch : int; direct_call_of_indirect : int; updated_direct_call : int; ( ** Updated direct calls is the count of direct call changed from one code_id to another. It does not count in evaluate, but it matters for equal. * ) ( * CR pchambart: it should track in some way the difference between the called codes * ) specialized_poly_compare : ... *)
Parameter t : Type.
Extract Inlined Constant t => "Removed_operations.t".
(* removed_operations.mli:33  val zero : t *)
Parameter zero : t.
Extract Inlined Constant zero => "Removed_operations.zero".
(* removed_operations.mli:35  val call : t *)
Parameter call : t.
Extract Inlined Constant call => "Removed_operations.call".
(* removed_operations.mli:37  val branch : t *)
Parameter branch : t.
Extract Inlined Constant branch => "Removed_operations.branch".
(* removed_operations.mli:39  val prim : Flambda_primitive.t -> t *)
Parameter prim : Flambda_primitive.t -> M t.
Extract Inlined Constant prim => "Removed_operations.prim".
(* removed_operations.mli:41  val alloc : t *)
Parameter alloc : t.
Extract Inlined Constant alloc => "Removed_operations.alloc".
(* removed_operations.mli:43  val direct_call_of_indirect : t *)
Parameter direct_call_of_indirect : t.
Extract Inlined Constant direct_call_of_indirect => "Removed_operations.direct_call_of_indirect".
(* removed_operations.mli:45  val updated_direct_call : t *)
Parameter updated_direct_call : t.
Extract Inlined Constant updated_direct_call => "Removed_operations.updated_direct_call".
(* removed_operations.mli:47  val specialized_poly_compare : t *)
Parameter specialized_poly_compare : t.
Extract Inlined Constant specialized_poly_compare => "Removed_operations.specialized_poly_compare".
(* removed_operations.mli:49  val ( + ) : t -> t -> t *)
Parameter op_plus : t -> t -> M t.
Extract Inlined Constant op_plus => "Removed_operations.( + )".
(* removed_operations.mli:55  val equal : t -> t -> bool *)
Parameter equal : t -> t -> M bool.
Extract Inlined Constant equal => "Removed_operations.equal".
