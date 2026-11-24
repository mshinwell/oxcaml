(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2019 OCamlPro SAS                                          *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Name_mode], after its interface
   middle_end/flambda2/nominal/name_mode.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* name_mode.mli:20  type t = private | Normal | Phantom | In_types *)
Inductive t : Type :=
| Normal : t
| Phantom : t
| In_types : t.
Extract Inductive t => "Name_mode.t" [ "Name_mode.Normal" "Name_mode.Phantom" "Name_mode.In_types" ].
(* name_mode.mli:25  type name_mode = t *)
Definition name_mode : Type := t.
Extract Inlined Constant name_mode => "Name_mode.name_mode".
(* name_mode.mli:28  val normal : t *)
Parameter normal : t.
Extract Inlined Constant normal => "Name_mode.normal".
(* name_mode.mli:33  val in_types : t *)
Parameter in_types : t.
Extract Inlined Constant in_types => "Name_mode.in_types".
(* name_mode.mli:38  val phantom : t *)
Parameter phantom : t.
Extract Inlined Constant phantom => "Name_mode.phantom".
(* name_mode.mli:40  val is_normal : t -> bool *)
Parameter is_normal : t -> M bool.
Extract Inlined Constant is_normal => "Name_mode.is_normal".
(* name_mode.mli:42  val is_phantom : t -> bool *)
Parameter is_phantom : t -> M bool.
Extract Inlined Constant is_phantom => "Name_mode.is_phantom".
(* name_mode.mli:46  val can_be_in_terms : t -> bool *)
Parameter can_be_in_terms : t -> M bool.
Extract Inlined Constant can_be_in_terms => "Name_mode.can_be_in_terms".
Module T.
  (* name_mode.mli:51  include Container_types.S with type t := t *)
  Definition t : Type := Name_mode.t.
  Extract Inlined Constant t => "Name_mode.T.t".
End T.
(* name_mode.mli:51  include Container_types.S with type t := t *)
Parameter equal : Name_mode.T.t -> Name_mode.T.t -> M bool.
Extract Inlined Constant equal => "Name_mode.equal".
(* name_mode.mli:51  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Name_mode.T.t -> M unit.
Extract Inlined Constant print => "Name_mode.print".
Module Or_absent.
  (* name_mode.mli:61  type t = private | Absent | Present of name_mode *)
  Inductive t : Type :=
  | Absent : t
  | Present : Name_mode.name_mode -> t.
  Extract Inductive t => "Name_mode.Or_absent.t" [ "Name_mode.Or_absent.Absent" "Name_mode.Or_absent.Present" ].
  (* name_mode.mli:65  val absent : t *)
  Parameter absent : t.
  Extract Inlined Constant absent => "Name_mode.Or_absent.absent".
  (* name_mode.mli:67  val present : name_mode -> t *)
  Parameter present : Name_mode.name_mode -> M t.
  Extract Inlined Constant present => "Name_mode.Or_absent.present".
  (* name_mode.mli:69  val is_present : t -> bool *)
  Parameter is_present : t -> M bool.
  Extract Inlined Constant is_present => "Name_mode.Or_absent.is_present".
  Module T.
    (* name_mode.mli:73  include Container_types.S with type t := t *)
    Definition t : Type := Name_mode.Or_absent.t.
    Extract Inlined Constant t => "Name_mode.Or_absent.T.t".
  End T.
  (* name_mode.mli:73  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> Name_mode.Or_absent.T.t -> M unit.
  Extract Inlined Constant print => "Name_mode.Or_absent.print".
  (* name_mode.mli:75  val compare_partial_order : t -> t -> int option *)
  Parameter compare_partial_order : t -> t -> M (option int).
  Extract Inlined Constant compare_partial_order => "Name_mode.Or_absent.compare_partial_order".
  (* name_mode.mli:80  val join_in_terms : t -> t -> t *)
  Parameter join_in_terms : t -> t -> M t.
  Extract Inlined Constant join_in_terms => "Name_mode.Or_absent.join_in_terms".
End Or_absent.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Name_mode. End Name_mode.
