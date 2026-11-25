(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Lambda], after its interface
   lambda/lambda.mli
   (Git blob 5d8b6a63e7c95c3d422511f4e7826a5a55c41d83). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Clflags Location.

(* lambda.mli:49  type return_mode = private | Maybe_alloc_stack | Not_alloc_stack *)
Inductive return_mode : Type :=
| Maybe_alloc_stack : return_mode
| Not_alloc_stack : return_mode.
Extract Inductive return_mode => "Lambda.return_mode" [ "Lambda.Maybe_alloc_stack" "Lambda.Not_alloc_stack" ].
(* lambda.mli:144  type lazy_block_tag = | Lazy_tag | Forward_tag *)
Parameter lazy_block_tag : Type.
Extract Inlined Constant lazy_block_tag => "Lambda.lazy_block_tag".
(* lambda.mli:860  type zero_alloc_attribute = | Default_zero_alloc | Check of { strict: bool; ( * [strict=true] property holds on all paths. [strict=false] if the function returns normally, then the property holds (but property violations on exceptional returns or divering loops are ignored). This definition may not be applicable to new properties. * ) loc: Location.t; custom_error_msg: string option; partial: b... *)
Inductive zero_alloc_attribute : Type :=
| Default_zero_alloc : zero_alloc_attribute
| Check : bool -> Location.t -> option string -> bool -> zero_alloc_attribute
| Assume : bool -> bool -> bool -> Location.t -> zero_alloc_attribute.
Extract Inductive zero_alloc_attribute => "Lambda.zero_alloc_attribute" [ "Lambda.Default_zero_alloc" "(fun (x__1, x__2, x__3, x__4) -> (Lambda.Check { strict = x__1; loc = x__2; custom_error_msg = x__3; partial = x__4 } : Lambda.zero_alloc_attribute))" "(fun (x__1, x__2, x__3, x__4) -> (Lambda.Assume { strict = x__1; never_returns_normally = x__2; never_raises = x__3; loc = x__4 } : Lambda.zero_alloc_attribute))" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : Lambda.zero_alloc_attribute) with Lambda.Default_zero_alloc -> f__1 () | Lambda.Check { strict = x__1; loc = x__2; custom_error_msg = x__3; partial = x__4 } -> f__2 x__1 x__2 x__3 x__4 | Lambda.Assume { strict = x__1; never_returns_normally = x__2; never_raises = x__3; loc = x__4 } -> f__3 x__1 x__2 x__3 x__4)".
(* lambda.mli:883  type regalloc_attribute = | Default_regalloc | Regalloc of Clflags.Register_allocator.t *)
Inductive regalloc_attribute : Type :=
| Default_regalloc : regalloc_attribute
| Regalloc : Clflags.Register_allocator.t -> regalloc_attribute.
Extract Inductive regalloc_attribute => "Lambda.regalloc_attribute" [ "Lambda.Default_regalloc" "Lambda.Regalloc" ].
(* lambda.mli:886  type regalloc_param_attribute = | Default_regalloc_params | Regalloc_params of string list *)
Inductive regalloc_param_attribute : Type :=
| Default_regalloc_params : regalloc_param_attribute
| Regalloc_params : list string -> regalloc_param_attribute.
Extract Inductive regalloc_param_attribute => "Lambda.regalloc_param_attribute" [ "Lambda.Default_regalloc_params" "Lambda.Regalloc_params" ].

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Lambda. End Lambda.
