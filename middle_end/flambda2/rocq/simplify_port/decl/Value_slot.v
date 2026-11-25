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
   Simplify uses of the compiler's module [Value_slot], after its interface
   middle_end/flambda2/identifiers/value_slot.mli
   (Git blob f4bd65fc47813c288fc4e813ec3984a25d4a9aa2). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Compilation_unit Flambda_kind Format.

(* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
Parameter t : Type.
Extract Inlined Constant t => "Value_slot.t".
Module Map.
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Definition key : Type := Value_slot.t.
  Extract Inlined Constant key => "Value_slot.Map.key".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Value_slot.Map.t".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Value_slot.Map.empty".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Value_slot.Map.add".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Value_slot.Map.update".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Value_slot.Map.fold".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant for_all => "Value_slot.Map.for_all".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
  Extract Inlined Constant filter => "Value_slot.Map.filter".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Value_slot.Map.map".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Value_slot.Map.mapi".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  Extract Inlined Constant of_list => "Value_slot.Map.of_list".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter data : forall {A : Type}, t A -> M (list A).
  Extract Inlined Constant data => "Value_slot.Map.data".
  (* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Value_slot.Map.print".
End Map.
(* value_slot.mli:22  include Slot.S with type payload := Flambda_kind.t * is_always_immediate:bool *)
Parameter to_string : t -> M string.
Extract Inlined Constant to_string => "Value_slot.to_string".
(* value_slot.mli:24  val create : Compilation_unit.t -> name:string -> is_always_immediate:bool -> Flambda_kind.t -> t *)
Parameter create : Compilation_unit.t -> string -> bool -> Flambda_kind.t -> M t.
Extract Inlined Constant create => "Value_slot.create".
(* value_slot.mli:31  val kind : t -> Flambda_kind.t *)
Parameter kind : t -> M Flambda_kind.t.
Extract Inlined Constant kind => "Value_slot.kind".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Value_slot. End Value_slot.
