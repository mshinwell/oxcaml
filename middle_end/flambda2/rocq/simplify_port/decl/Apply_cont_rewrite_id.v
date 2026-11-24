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
   Simplify uses of the compiler's module [Apply_cont_rewrite_id], after its interface
   middle_end/flambda2/identifiers/apply_cont_rewrite_id.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Or_null.

(* apply_cont_rewrite_id.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Apply_cont_rewrite_id.t".
Module T.
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Definition t : Type := Apply_cont_rewrite_id.t.
  Extract Inlined Constant t => "Apply_cont_rewrite_id.T.t".
End T.
(* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Apply_cont_rewrite_id.T.t -> M unit.
Extract Inlined Constant print => "Apply_cont_rewrite_id.print".
Module Set_.
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Definition elt : Type := Apply_cont_rewrite_id.t.
  Extract Inlined Constant elt => "Apply_cont_rewrite_id.Set.elt".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Apply_cont_rewrite_id.Set.t".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Apply_cont_rewrite_id.Set.empty".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter is_empty : t -> M bool.
  Extract Inlined Constant is_empty => "Apply_cont_rewrite_id.Set.is_empty".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Apply_cont_rewrite_id.Set.mem".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Apply_cont_rewrite_id.Set.add".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Apply_cont_rewrite_id.Set.fold".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter cardinal : t -> M int.
  Extract Inlined Constant cardinal => "Apply_cont_rewrite_id.Set.cardinal".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Apply_cont_rewrite_id.Set.print".
End Set_.
Module Map.
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Definition key : Type := Apply_cont_rewrite_id.t.
  Extract Inlined Constant key => "Apply_cont_rewrite_id.Map.key".
  Module Set_.
    (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
    Definition t : Type := Apply_cont_rewrite_id.Set_.t.
    Extract Inlined Constant t => "Apply_cont_rewrite_id.Map.Set.t".
  End Set_.
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Apply_cont_rewrite_id.Map.t".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Apply_cont_rewrite_id.Map.empty".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter is_empty : forall {A : Type}, t A -> M bool.
  Extract Inlined Constant is_empty => "Apply_cont_rewrite_id.Map.is_empty".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  Extract Inlined Constant mem => "Apply_cont_rewrite_id.Map.mem".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Apply_cont_rewrite_id.Map.add".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Apply_cont_rewrite_id.Map.update".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Apply_cont_rewrite_id.Map.singleton".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
  Extract Inlined Constant merge => "Apply_cont_rewrite_id.Map.merge".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Apply_cont_rewrite_id.Map.fold".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant for_all => "Apply_cont_rewrite_id.Map.for_all".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Apply_cont_rewrite_id.Map.exists".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
  Extract Inlined Constant filter_map => "Apply_cont_rewrite_id.Map.filter_map".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Apply_cont_rewrite_id.Map.find".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Apply_cont_rewrite_id.Map.find_or_null".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Apply_cont_rewrite_id.Map.map".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter data : forall {A : Type}, t A -> M (list A).
  Extract Inlined Constant data => "Apply_cont_rewrite_id.Map.data".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter of_set : forall {A : Type}, (key -> M A) -> Apply_cont_rewrite_id.Map.Set_.t -> M (t A).
  Extract Inlined Constant of_set => "Apply_cont_rewrite_id.Map.of_set".
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Apply_cont_rewrite_id.Map.print".
End Map.
(* apply_cont_rewrite_id.mli:21  val create : unit -> t *)
Parameter create : unit -> M t.
Extract Inlined Constant create => "Apply_cont_rewrite_id.create".
