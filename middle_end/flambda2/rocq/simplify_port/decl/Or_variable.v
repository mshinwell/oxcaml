(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Or_variable], after its interface
   middle_end/flambda2/term_basics/or_variable.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Debuginfo Name_occurrences Variable_.

(* or_variable.mli:19  type 'a t = | Const of 'a | Var of Variable.t * Debuginfo.t *)
Inductive t (A : Type) : Type :=
| Const : A -> t A
| Var : Variable_.t -> Debuginfo.t -> t A.
Arguments Const {A}.
Arguments Var {A}.
Extract Inductive t => "Or_variable.t" [ "Or_variable.Const" "Or_variable.Var" ].
(* or_variable.mli:33  val free_names : _ t -> Name_occurrences.t *)
Parameter free_names : forall {A : Type}, t A -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Or_variable.free_names".
