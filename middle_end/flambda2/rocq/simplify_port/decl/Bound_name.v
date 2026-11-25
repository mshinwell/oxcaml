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
   Simplify uses of the compiler's module [Bound_name], after its interface
   middle_end/flambda2/bound_identifiers/bound_name.mli
   (Git blob 55e6a871a43ccea4fa2ff5eb33caedf9e240b968). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var Format Name Name_mode Symbol.

(* bound_name.mli:20  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Bound_name.t".
(* bound_name.mli:22  val create : Name.t -> Name_mode.t -> t *)
Parameter create : Name.t -> Name_mode.t -> M t.
Extract Inlined Constant create => "Bound_name.create".
(* bound_name.mli:24  val create_var : Bound_var.t -> t *)
Parameter create_var : Bound_var.t -> M t.
Extract Inlined Constant create_var => "Bound_name.create_var".
(* bound_name.mli:26  val create_symbol : Symbol.t -> t *)
Parameter create_symbol : Symbol.t -> M t.
Extract Inlined Constant create_symbol => "Bound_name.create_symbol".
(* bound_name.mli:28  val name : t -> Name.t *)
Parameter name : t -> M Name.t.
Extract Inlined Constant name => "Bound_name.name".
(* bound_name.mli:30  val name_mode : t -> Name_mode.t *)
Parameter name_mode : t -> M Name_mode.t.
Extract Inlined Constant name_mode => "Bound_name.name_mode".
(* bound_name.mli:32  val is_symbol : t -> bool *)
Parameter is_symbol : t -> M bool.
Extract Inlined Constant is_symbol => "Bound_name.is_symbol".
(* bound_name.mli:34  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Bound_name.print".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Bound_name. End Bound_name.
