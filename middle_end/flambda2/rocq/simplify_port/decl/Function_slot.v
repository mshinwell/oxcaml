(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Function_slot], after its interface
   middle_end/flambda2/identifiers/function_slot.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Compilation_unit Format.

(* function_slot.mli:26  include Slot.S with type payload := int *)
Parameter t : Type.
Extract Inlined Constant t => "Function_slot.t".
Module T.
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Definition t : Type := Function_slot.t.
  Extract Inlined Constant t => "Function_slot.T.t".
End T.
(* function_slot.mli:26  include Slot.S with type payload := int *)
Parameter print : Format.formatter -> Function_slot.T.t -> M unit.
Extract Inlined Constant print => "Function_slot.print".
Module Map.
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Definition key : Type := Function_slot.t.
  Extract Inlined Constant key => "Function_slot.Map.key".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Function_slot.Map.t".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Function_slot.Map.empty".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Function_slot.Map.add".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Function_slot.Map.fold".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter cardinal : forall {A : Type}, t A -> M int.
  Extract Inlined Constant cardinal => "Function_slot.Map.cardinal".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Function_slot.Map.find".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Function_slot.Map.map".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Function_slot.Map.mapi".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  Extract Inlined Constant of_list => "Function_slot.Map.of_list".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Function_slot.Map.print".
End Map.
Module Lmap.
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Definition key : Type := Function_slot.t.
  Extract Inlined Constant key => "Function_slot.Lmap.key".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Function_slot.Lmap.t".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Function_slot.Lmap.singleton".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Function_slot.Lmap.fold".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter fold_left_map : forall {A B C : Type}, (A -> key -> B -> M (A * C)) -> A -> t B -> M (A * t C).
  Extract Inlined Constant fold_left_map => "Function_slot.Lmap.fold_left_map".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter keys : forall {A : Type}, t A -> M (list key).
  Extract Inlined Constant keys => "Function_slot.Lmap.keys".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter data : forall {A : Type}, t A -> M (list A).
  Extract Inlined Constant data => "Function_slot.Lmap.data".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
  Extract Inlined Constant bindings => "Function_slot.Lmap.bindings".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter is_singleton : forall {A : Type}, t A -> M bool.
  Extract Inlined Constant is_singleton => "Function_slot.Lmap.is_singleton".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Function_slot.Lmap.map".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Function_slot.Lmap.mapi".
  (* function_slot.mli:26  include Slot.S with type payload := int *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Function_slot.Lmap.exists".
End Lmap.
(* function_slot.mli:26  include Slot.S with type payload := int *)
Parameter to_string : t -> M string.
Extract Inlined Constant to_string => "Function_slot.to_string".
(* function_slot.mli:26  include Slot.S with type payload := int *)
Parameter name : t -> M string.
Extract Inlined Constant name => "Function_slot.name".
(* function_slot.mli:26  include Slot.S with type payload := int *)
Parameter canonical_name : t -> M string.
Extract Inlined Constant canonical_name => "Function_slot.canonical_name".
(* function_slot.mli:28  val create : Compilation_unit.t -> name:string -> size:int -> t *)
Parameter create : Compilation_unit.t -> string -> int -> M t.
Extract Inlined Constant create => "Function_slot.create".
(* function_slot.mli:32  val size_from_arity : num_complex_params:int -> is_tupled:bool -> int *)
Parameter size_from_arity : int -> bool -> M int.
Extract Inlined Constant size_from_arity => "Function_slot.size_from_arity".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Function_slot. End Function_slot.
