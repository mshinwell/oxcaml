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
   Simplify uses of the compiler's module [Flambda_unit], after its interface
   middle_end/flambda2/terms/flambda_unit.mli
   (Git blob 99fc462104d16536022805b95c81a627cc8a19ec). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Flambda Symbol Variable_.

(* flambda_unit.mli:31  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Flambda_unit.t".
(* flambda_unit.mli:35  val create : return_continuation:Continuation.t -> exn_continuation:Continuation.t -> toplevel_my_alloc_region:Variable.t -> body:Flambda.Expr.t -> module_symbol:Symbol.t -> t *)
Parameter create : Continuation.t -> Continuation.t -> Variable_.t -> Flambda.Expr.t -> Symbol.t -> M t.
Extract Inlined Constant create => "Flambda_unit.create".
(* flambda_unit.mli:47  val return_continuation : t -> Continuation.t *)
Parameter return_continuation : t -> M Continuation.t.
Extract Inlined Constant return_continuation => "Flambda_unit.return_continuation".
(* flambda_unit.mli:49  val exn_continuation : t -> Continuation.t *)
Parameter exn_continuation : t -> M Continuation.t.
Extract Inlined Constant exn_continuation => "Flambda_unit.exn_continuation".
(* flambda_unit.mli:51  val toplevel_my_alloc_region : t -> Variable.t *)
Parameter toplevel_my_alloc_region : t -> M Variable_.t.
Extract Inlined Constant toplevel_my_alloc_region => "Flambda_unit.toplevel_my_alloc_region".
(* flambda_unit.mli:53  val module_symbol : t -> Symbol.t *)
Parameter module_symbol : t -> M Symbol.t.
Extract Inlined Constant module_symbol => "Flambda_unit.module_symbol".
(* flambda_unit.mli:55  val body : t -> Flambda.Expr.t *)
Parameter body : t -> M Flambda.Expr.t.
Extract Inlined Constant body => "Flambda_unit.body".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flambda_unit. End Flambda_unit.
