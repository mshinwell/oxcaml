(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*   Copyright 2021--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Closure_info], after its interface
   middle_end/flambda2/simplify/env/closure_info.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Continuation Format Variable_.

(* closure_info.mli:16  type t = private | Not_in_a_closure | In_a_set_of_closures_but_not_yet_in_a_specific_closure | Closure of { code_id : Code_id.t; return_continuation : Continuation.t; exn_continuation : Continuation.t; my_closure : Variable.t; my_alloc_region : Variable.t } *)
Record closure_payload_ : Type := { code_id : Code_id.t; return_continuation : Continuation.t; exn_continuation : Continuation.t; my_closure : Variable_.t; my_alloc_region : Variable_.t }.
Inductive t : Type :=
| Not_in_a_closure : t
| In_a_set_of_closures_but_not_yet_in_a_specific_closure : t
| Closure : closure_payload_ -> t.
(* closure_info.mli:27  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Closure_info.print".
(* closure_info.mli:29  val not_in_a_closure : t *)
Parameter not_in_a_closure : t.
Extract Inlined Constant not_in_a_closure => "Closure_info.not_in_a_closure".
(* closure_info.mli:31  val in_a_set_of_closures : t *)
Parameter in_a_set_of_closures : t.
Extract Inlined Constant in_a_set_of_closures => "Closure_info.in_a_set_of_closures".
(* closure_info.mli:33  val in_a_closure : Code_id.t -> return_continuation:Continuation.t -> exn_continuation:Continuation.t -> my_closure:Variable.t -> my_alloc_region:Variable.t -> t *)
Parameter in_a_closure : Code_id.t -> Continuation.t -> Continuation.t -> Variable_.t -> Variable_.t -> M t.
Extract Inlined Constant in_a_closure => "Closure_info.in_a_closure".
(* closure_info.mli:41  type in_or_out_of_closure = | In_a_closure | Not_in_a_closure *)
Inductive in_or_out_of_closure_ : Type :=
| In_a_closure : in_or_out_of_closure_
| Not_in_a_closure_ : in_or_out_of_closure_.
Extract Inductive in_or_out_of_closure_ => "Closure_info.in_or_out_of_closure" [ "Closure_info.In_a_closure" "Closure_info.Not_in_a_closure" ].
(* closure_info.mli:45  val in_or_out_of_closure : t -> in_or_out_of_closure *)
Parameter in_or_out_of_closure : t -> M in_or_out_of_closure_.
Extract Inlined Constant in_or_out_of_closure => "Closure_info.in_or_out_of_closure".
