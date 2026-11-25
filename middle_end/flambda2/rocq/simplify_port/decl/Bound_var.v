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
   Simplify uses of the compiler's module [Bound_var], after its interface
   middle_end/flambda2/bound_identifiers/bound_var.mli
   (Git blob f4e683073c7ff0504e81309566fb8377f01bda35). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_debug_uid Format Name_mode Variable_.

(* bound_var.mli:20  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Bound_var.t".
(* bound_var.mli:22  val create : Variable.t -> Flambda_debug_uid.t -> Name_mode.t -> t *)
Parameter create : Variable_.t -> Flambda_debug_uid.t -> Name_mode.t -> M t.
Extract Inlined Constant create => "Bound_var.create".
(* bound_var.mli:24  val var : t -> Variable.t *)
Parameter var : t -> M Variable_.t.
Extract Inlined Constant var => "Bound_var.var".
(* bound_var.mli:28  val debug_uid : t -> Flambda_debug_uid.t *)
Parameter debug_uid : t -> M Flambda_debug_uid.t.
Extract Inlined Constant debug_uid => "Bound_var.debug_uid".
(* bound_var.mli:30  val name_mode : t -> Name_mode.t *)
Parameter name_mode : t -> M Name_mode.t.
Extract Inlined Constant name_mode => "Bound_var.name_mode".
(* bound_var.mli:34  include Bindable.S with type t := t *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Bound_var.print".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Bound_var. End Bound_var.
