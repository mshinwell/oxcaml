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

(* GENERATED, not written by hand: the declarations of the modules that
   middle_end/flambda2/simplify/common_subexpression_elimination.ml
   (Git blob 2d097a00e62af6c65f516baa0932149da53d2d65) makes for itself by
   applying a functor of another part of the compiler, and of what the
   file uses of them. The port keeps the definitions of these modules as
   they are in the file, and the realisations name them as the file does.
   Made by tools/declgen (see decl/README.md): a change is made there,
   not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Simple.

(* module Rhs_kind, lines 78-122 of the file *)
Module Rhs_kind.
  (* common_subexpression_elimination.ml:79  type t = | Needs_extra_binding of { bound_to : Simple.t } | Rhs_in_scope of { bound_to : Simple.t } *)
  Inductive t : Type :=
  | Needs_extra_binding : Simple.t -> t
  | Rhs_in_scope : Simple.t -> t.
  Extract Inductive t => "Rhs_kind.t" [ "(fun x__1 -> (Rhs_kind.Needs_extra_binding { bound_to = x__1 } : Rhs_kind.t))" "(fun x__1 -> (Rhs_kind.Rhs_in_scope { bound_to = x__1 } : Rhs_kind.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Rhs_kind.t) with Rhs_kind.Needs_extra_binding { bound_to = x__1 } -> f__1 x__1 | Rhs_kind.Rhs_in_scope { bound_to = x__1 } -> f__2 x__1)".
  (* common_subexpression_elimination.ml:83  val bound_to : t -> Simple.t *)
  Parameter bound_to : t -> M Simple.t.
  Extract Inlined Constant bound_to => "Rhs_kind.bound_to".
  Module Set_.
    (* common_subexpression_elimination.ml:85  include Container_types.S with type t := t *)
    Definition elt : Type := Common_subexpression_elimination__local.Rhs_kind.t.
    Extract Inlined Constant elt => "Rhs_kind.Set.elt".
    (* common_subexpression_elimination.ml:85  include Container_types.S with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Rhs_kind.Set.t".
    (* common_subexpression_elimination.ml:85  include Container_types.S with type t := t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Rhs_kind.Set.of_list".
    (* common_subexpression_elimination.ml:85  include Container_types.S with type t := t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Rhs_kind.Set.get_singleton".
  End Set_.
End Rhs_kind.

(* Not in the file of Simplify: an empty module with the name of this file.
   With it Rocq's extraction writes no [open] of this file, which is not a
   module of OCaml, and prints each of its names in full. *)
Module Common_subexpression_elimination__local. End Common_subexpression_elimination__local.
