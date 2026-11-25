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
   Simplify uses of the compiler's module [Code_size], after its interface
   middle_end/flambda2/terms/code_size.mli
   (Git blob 193927d6e81c9246a81e79a4742d6962c81d187d). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Apply_expr Flambda_kind Flambda_primitive Simple Switch_expr Target_system.

(* code_size.mli:22  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Code_size.t".
(* code_size.mli:25  val of_int : int -> t *)
Parameter of_int : int -> M t.
Extract Inlined Constant of_int => "Code_size.of_int".
(* code_size.mli:29  val zero : t *)
Parameter zero : t.
Extract Inlined Constant zero => "Code_size.zero".
(* code_size.mli:31  val ( + ) : t -> t -> t *)
Parameter op_plus : t -> t -> M t.
Extract Inlined Constant op_plus => "Code_size.( + )".
(* code_size.mli:33  val ( - ) : t -> t -> t *)
Parameter op_minus : t -> t -> M t.
Extract Inlined Constant op_minus => "Code_size.( - )".
(* code_size.mli:35  val ( <= ) : t -> t -> bool *)
Parameter op_lt_eq : t -> t -> M bool.
Extract Inlined Constant op_lt_eq => "Code_size.( <= )".
(* code_size.mli:41  val box_number : machine_width:Target_system.Machine_width.t -> Flambda_kind.Boxable_number.t -> t *)
Parameter box_number : Target_system.Machine_width.t -> Flambda_kind.Boxable_number.t -> M t.
Extract Inlined Constant box_number => "Code_size.box_number".
(* code_size.mli:46  val block : int -> t *)
Parameter block : int -> M t.
Extract Inlined Constant block => "Code_size.block".
(* code_size.mli:48  val array : int -> t *)
Parameter array : int -> M t.
Extract Inlined Constant array => "Code_size.array".
(* code_size.mli:50  val prim : machine_width:Target_system.Machine_width.t -> Flambda_primitive.t -> t *)
Parameter prim : Target_system.Machine_width.t -> Flambda_primitive.t -> M t.
Extract Inlined Constant prim => "Code_size.prim".
(* code_size.mli:53  val simple : Simple.t -> t *)
Parameter simple : Simple.t -> M t.
Extract Inlined Constant simple => "Code_size.simple".
(* code_size.mli:57  val apply : Apply_expr.t -> t *)
Parameter apply : Apply_expr.t -> M t.
Extract Inlined Constant apply => "Code_size.apply".
(* code_size.mli:59  val apply_cont : Apply_cont_expr.t -> t *)
Parameter apply_cont : Apply_cont_expr.t -> M t.
Extract Inlined Constant apply_cont => "Code_size.apply_cont".
(* code_size.mli:61  val switch : Switch_expr.t -> t *)
Parameter switch : Switch_expr.t -> M t.
Extract Inlined Constant switch => "Code_size.switch".
(* code_size.mli:63  val invalid : t *)
Parameter invalid : t.
Extract Inlined Constant invalid => "Code_size.invalid".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Code_size. End Code_size.
