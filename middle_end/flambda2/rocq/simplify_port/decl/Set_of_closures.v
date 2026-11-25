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
   Simplify uses of the compiler's module [Set_of_closures], after its interface
   middle_end/flambda2/terms/set_of_closures.mli
   (Git blob deeaec8800d27b41fce1cf009cb94f3204d8cfa1). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Function_declarations Simple Value_slot.

(* set_of_closures.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Set_of_closures.t".
(* set_of_closures.mli:36  val function_decls : t -> Function_declarations.t *)
Parameter function_decls : t -> M Function_declarations.t.
Extract Inlined Constant function_decls => "Set_of_closures.function_decls".
(* set_of_closures.mli:39  val value_slots : t -> Simple.t Value_slot.Map.t *)
Parameter value_slots : t -> M (Value_slot.Map.t Simple.t).
Extract Inlined Constant value_slots => "Set_of_closures.value_slots".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Set_of_closures. End Set_of_closures.
