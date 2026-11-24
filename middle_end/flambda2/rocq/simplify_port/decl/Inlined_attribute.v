(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018 OCamlPro SAS                                          *)
(*   Copyright 2018 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Inlined_attribute], after its interface
   middle_end/flambda2/terms/inlined_attribute.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

Module Use_info.
  (* inlined_attribute.mli:20  type t = | Expected_to_be_used | Unused_because_of_call_site_decision | Unused_because_function_unknown | Jsir_inlining_disabled *)
  Inductive t : Type :=
  | Expected_to_be_used : t
  | Unused_because_of_call_site_decision : t
  | Unused_because_function_unknown : t
  | Jsir_inlining_disabled : t.
End Use_info.
(* inlined_attribute.mli:29  type t = | Always_inlined of Use_info.t | Hint_inlined | Forward_inlined | Never_inlined | Unroll of int * Use_info.t | Default_inlined *)
Inductive t : Type :=
| Always_inlined : Inlined_attribute.Use_info.t -> t
| Hint_inlined : t
| Forward_inlined : t
| Never_inlined : t
| Unroll : int -> Inlined_attribute.Use_info.t -> t
| Default_inlined : t.
(* inlined_attribute.mli:37  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Inlined_attribute.print".
(* inlined_attribute.mli:47  val with_use_info : t -> Use_info.t -> t *)
Parameter with_use_info : t -> Inlined_attribute.Use_info.t -> M t.
Extract Inlined Constant with_use_info => "Inlined_attribute.with_use_info".
(* inlined_attribute.mli:51  val forward_inlined : unit -> t *)
Parameter forward_inlined : unit -> M t.
Extract Inlined Constant forward_inlined => "Inlined_attribute.forward_inlined".
