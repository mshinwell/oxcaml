(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017--2018 OCamlPro SAS                                    *)
(*   Copyright 2017--2018 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Scope], after its interface
   middle_end/flambda2/term_basics/scope.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* scope.mli:19  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Scope.t".
Module T.
  (* scope.mli:21  include Container_types.S with type t := t *)
  Definition t : Type := Scope.t.
  Extract Inlined Constant t => "Scope.T.t".
End T.
(* scope.mli:21  include Container_types.S with type t := t *)
Parameter equal : Scope.T.t -> Scope.T.t -> M bool.
Extract Inlined Constant equal => "Scope.equal".
(* scope.mli:21  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Scope.T.t -> M unit.
Extract Inlined Constant print => "Scope.print".
Module Map.
  (* scope.mli:21  include Container_types.S with type t := t *)
  Definition key : Type := Scope.t.
  Extract Inlined Constant key => "Scope.Map.key".
  (* scope.mli:21  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Scope.Map.t".
  (* scope.mli:21  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Scope.Map.empty".
  (* scope.mli:21  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Scope.Map.add".
  (* scope.mli:21  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Scope.Map.fold".
  (* scope.mli:21  include Container_types.S with type t := t *)
  Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
  Extract Inlined Constant split => "Scope.Map.split".
  (* scope.mli:21  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Scope.Map.find".
  (* scope.mli:21  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Scope.Map.print".
End Map.
(* scope.mli:25  val prev : t -> t *)
Parameter prev : t -> M t.
Extract Inlined Constant prev => "Scope.prev".
(* scope.mli:27  val next : t -> t *)
Parameter next : t -> M t.
Extract Inlined Constant next => "Scope.next".
