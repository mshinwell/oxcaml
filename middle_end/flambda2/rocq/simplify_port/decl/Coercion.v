(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Coercion], after its interface
   middle_end/flambda2/term_basics/coercion.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Int_ids Name_occurrences.

(* int_ids.mli:197  and type rec_info_expr = Rec_info_expr.t *)
Definition rec_info_expr : Type := Int_ids.Rec_info_expr.t.
Extract Inlined Constant rec_info_expr => "Coercion.rec_info_expr".
(* coercion0.mli:37  type t = private | Id | Change_depth of { from : rec_info_expr; to_ : rec_info_expr } *)
Definition t : Type := Int_ids.Coercion.t.
Extract Inlined Constant t => "Coercion.t".
(* coercion0.mli:44  val change_depth : from:rec_info_expr -> to_:rec_info_expr -> t *)
Parameter change_depth : rec_info_expr -> rec_info_expr -> M t.
Extract Inlined Constant change_depth => "Coercion.change_depth".
(* coercion0.mli:46  val id : t *)
Parameter id : t.
Extract Inlined Constant id => "Coercion.id".
(* coercion0.mli:51  val is_id : t -> bool *)
Parameter is_id : t -> M bool.
Extract Inlined Constant is_id => "Coercion.is_id".
(* coercion.mli:19  include Contains_names.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Coercion.free_names".
(* coercion.mli:27  val compose_exn : t -> then_:t -> t *)
Parameter compose_exn : t -> t -> M t.
Extract Inlined Constant compose_exn => "Coercion.compose_exn".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Coercion. End Coercion.
