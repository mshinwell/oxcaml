(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2021 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of the modules that
   middle_end/flambda2/simplify/rebuilt_expr.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9 makes for itself by applying a functor of another
   part of the compiler, and of what the file uses of them. The port keeps
   the definitions of these modules as they are in the file, and the
   realisations name them as the file does. Made by tools/declgen (see
   decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Variable_.

Module Matching_for_unique_handler.
  Module Match_permutable_parameters.
    (* module HV, lines 390-390 of the file *)
    Module HV.
      (* stdlib/hashtbl.mli  type key *)
      Definition key : Type := Variable_.t.
      Extract Inlined Constant key => "HV.key".
      (* stdlib/hashtbl.mli  type t *)
      (* abstract here: it is the type Stdlib__Hashtbl.Make(Flambda2_identifiers__Variable).t is not a global name. *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) HV.t".
      (* stdlib/hashtbl.mli  val create : int -> 'a HV.t *)
      Parameter create : forall {A : Type}, int -> M (t A).
      Extract Inlined Constant create => "HV.create".
      (* stdlib/hashtbl.mli  val find : 'a HV.t -> HV.key -> 'a *)
      Parameter find : forall {A : Type}, t A -> key -> M A.
      Extract Inlined Constant find => "HV.find".
      (* stdlib/hashtbl.mli  val replace : 'a HV.t -> HV.key -> 'a -> unit *)
      Parameter replace : forall {A : Type}, t A -> key -> A -> M unit.
      Extract Inlined Constant replace => "HV.replace".
    End HV.
  End Match_permutable_parameters.
End Matching_for_unique_handler.

(* Not in the file of Simplify: an empty module with the name of this file.
   With it Rocq's extraction writes no [open] of this file, which is not a
   module of OCaml, and prints each of its names in full. *)
Module Rebuilt_expr__local. End Rebuilt_expr__local.
