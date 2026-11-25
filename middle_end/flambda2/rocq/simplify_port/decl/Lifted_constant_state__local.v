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
   middle_end/flambda2/simplify/lifting/lifted_constant_state.ml
   (Git blob 1ad8d0fcb1f011a3668fb9aaee542637baabc863) makes for itself by
   applying a functor of another part of the compiler, and of what the
   file uses of them. The port keeps the definitions of these modules as
   they are in the file, and the realisations name them as the file does.
   Made by tools/declgen (see decl/README.md): a change is made there,
   not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id_or_symbol.

(* module SCC_lifted_constants, lines 82-82 of the file *)
Module SCC_lifted_constants.
  (* strongly_connected_components.mli:91  module Make (Id : Id) : S with module Id := Id *)
  Inductive component : Type :=
  | Has_loop : list Code_id_or_symbol.t -> component
  | No_loop : Code_id_or_symbol.t -> component.
  Extract Inductive component => "SCC_lifted_constants.component" [ "SCC_lifted_constants.Has_loop" "SCC_lifted_constants.No_loop" ].
  (* strongly_connected_components.mli:91  module Make (Id : Id) : S with module Id := Id *)
  Parameter stable_connected_components_sorted_from_roots_to_leaf : list (Code_id_or_symbol.t * Code_id_or_symbol.Set_.t) -> M (array component).
  Extract Inlined Constant stable_connected_components_sorted_from_roots_to_leaf => "SCC_lifted_constants.stable_connected_components_sorted_from_roots_to_leaf".
End SCC_lifted_constants.

(* Not in the file of Simplify: an empty module with the name of this file.
   With it Rocq's extraction writes no [open] of this file, which is not a
   module of OCaml, and prints each of its names in full. *)
Module Lifted_constant_state__local. End Lifted_constant_state__local.
