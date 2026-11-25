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
   Simplify uses of the compiler's module [Inlining_state], after its interface
   middle_end/flambda2/terms/inlining_state.mli
   (Git blob 9736e01507f71b022c5bcaa5e305f8189833175f). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Inlining_arguments.

(* inlining_state.mli:19  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Inlining_state.t".
(* inlining_state.mli:21  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Inlining_state.print".
(* inlining_state.mli:25  val default : round:int -> t *)
Parameter default : int -> M t.
Extract Inlined Constant default => "Inlining_state.default".
(* inlining_state.mli:31  val stub_depth : t -> int *)
Parameter stub_depth : t -> M int.
Extract Inlined Constant stub_depth => "Inlining_state.stub_depth".
(* inlining_state.mli:33  val increment_depth : t -> is_stub:bool -> by:int -> t *)
Parameter increment_depth : t -> bool -> int -> M t.
Extract Inlined Constant increment_depth => "Inlining_state.increment_depth".
(* inlining_state.mli:35  val is_depth_exceeded : t -> bool *)
Parameter is_depth_exceeded : t -> M bool.
Extract Inlined Constant is_depth_exceeded => "Inlining_state.is_depth_exceeded".
(* inlining_state.mli:40  val combine : from_env:t -> from_metadata:t -> t *)
Parameter combine : t -> t -> M t.
Extract Inlined Constant combine => "Inlining_state.combine".
(* inlining_state.mli:42  val with_arguments : Inlining_arguments.t -> t -> t *)
Parameter with_arguments : Inlining_arguments.t -> t -> M t.
Extract Inlined Constant with_arguments => "Inlining_state.with_arguments".
(* inlining_state.mli:44  val arguments : t -> Inlining_arguments.t *)
Parameter arguments : t -> M Inlining_arguments.t.
Extract Inlined Constant arguments => "Inlining_state.arguments".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Inlining_state. End Inlining_state.
