(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Function_decl_inlining_decision_type], after its interface
   middle_end/flambda2/terms/function_decl_inlining_decision_type.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_size.

(* function_decl_inlining_decision_type.mli:17  type t = | Not_yet_decided | Never_inline_attribute | Function_body_too_large of Code_size.t | Functor_body_too_large of Code_size.t | Stub | Attribute_inline ( * CR mshinwell/bclement: we could consider combining Small_function and Small_functor in the future, with a flag for functors * ) | Small_function of { size : Code_size.t; small_function_size : Code_size.t } | Small_functor of { size : ... *)
(* PORT-GAP(type): the name of the field [size] is taken in Rocq: abstract, with a maker for each constructor and one eliminator. *)
Parameter t : Type.
Extract Inlined Constant t => "Function_decl_inlining_decision_type.t".
Parameter mk_Not_yet_decided : t.
Extract Inlined Constant mk_Not_yet_decided => "Function_decl_inlining_decision_type.Not_yet_decided".
Parameter mk_Never_inline_attribute : t.
Extract Inlined Constant mk_Never_inline_attribute => "Function_decl_inlining_decision_type.Never_inline_attribute".
Parameter mk_Function_body_too_large : Code_size.t -> t.
Extract Inlined Constant mk_Function_body_too_large => "(fun x__1 -> Function_decl_inlining_decision_type.Function_body_too_large x__1)".
Parameter mk_Functor_body_too_large : Code_size.t -> t.
Extract Inlined Constant mk_Functor_body_too_large => "(fun x__1 -> Function_decl_inlining_decision_type.Functor_body_too_large x__1)".
Parameter mk_Stub : t.
Extract Inlined Constant mk_Stub => "Function_decl_inlining_decision_type.Stub".
Parameter mk_Attribute_inline : t.
Extract Inlined Constant mk_Attribute_inline => "Function_decl_inlining_decision_type.Attribute_inline".
Parameter mk_Small_function : Code_size.t -> Code_size.t -> t.
Extract Inlined Constant mk_Small_function => "(fun x__1 x__2 -> Function_decl_inlining_decision_type.Small_function { size = x__1; small_function_size = x__2 })".
Parameter mk_Small_functor : Code_size.t -> Code_size.t -> t.
Extract Inlined Constant mk_Small_functor => "(fun x__1 x__2 -> Function_decl_inlining_decision_type.Small_functor { size = x__1; small_functor_size = x__2 })".
Parameter mk_Speculatively_inlinable : Code_size.t -> Code_size.t -> Code_size.t -> t.
Extract Inlined Constant mk_Speculatively_inlinable => "(fun x__1 x__2 x__3 -> Function_decl_inlining_decision_type.Speculatively_inlinable { size = x__1; small_function_size = x__2; large_function_size = x__3 })".
Parameter mk_Speculatively_inlinable_functor : Code_size.t -> Code_size.t -> Code_size.t -> t.
Extract Inlined Constant mk_Speculatively_inlinable_functor => "(fun x__1 x__2 x__3 -> Function_decl_inlining_decision_type.Speculatively_inlinable_functor { size = x__1; small_functor_size = x__2; large_functor_size = x__3 })".
Parameter mk_Recursive : t.
Extract Inlined Constant mk_Recursive => "Function_decl_inlining_decision_type.Recursive".
Parameter mk_Jsir_inlining_disabled : t.
Extract Inlined Constant mk_Jsir_inlining_disabled => "Function_decl_inlining_decision_type.Jsir_inlining_disabled".
Parameter match_t : forall {Res : Type}, t -> (unit -> M Res) -> (unit -> M Res) -> (Code_size.t -> M Res) -> (Code_size.t -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (Code_size.t -> Code_size.t -> M Res) -> (Code_size.t -> Code_size.t -> M Res) -> (Code_size.t -> Code_size.t -> Code_size.t -> M Res) -> (Code_size.t -> Code_size.t -> Code_size.t -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> M Res.
Extract Inlined Constant match_t => "(fun x__0 f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 f__9 f__10 f__11 f__12 -> match x__0 with Function_decl_inlining_decision_type.Not_yet_decided -> f__1 () | Function_decl_inlining_decision_type.Never_inline_attribute -> f__2 () | Function_decl_inlining_decision_type.Function_body_too_large x__1 -> f__3 x__1 | Function_decl_inlining_decision_type.Functor_body_too_large x__1 -> f__4 x__1 | Function_decl_inlining_decision_type.Stub -> f__5 () | Function_decl_inlining_decision_type.Attribute_inline -> f__6 () | Function_decl_inlining_decision_type.Small_function { size = x__1; small_function_size = x__2 } -> f__7 x__1 x__2 | Function_decl_inlining_decision_type.Small_functor { size = x__1; small_functor_size = x__2 } -> f__8 x__1 x__2 | Function_decl_inlining_decision_type.Speculatively_inlinable { size = x__1; small_function_size = x__2; large_function_size = x__3 } -> f__9 x__1 x__2 x__3 | Function_decl_inlining_decision_type.Speculatively_inlinable_functor { size = x__1; small_functor_size = x__2; large_functor_size = x__3 } -> f__10 x__1 x__2 x__3 | Function_decl_inlining_decision_type.Recursive -> f__11 () | Function_decl_inlining_decision_type.Jsir_inlining_disabled -> f__12 ())".
(* function_decl_inlining_decision_type.mli:51  val must_be_inlined : t -> bool *)
Parameter must_be_inlined : t -> M bool.
Extract Inlined Constant must_be_inlined => "Function_decl_inlining_decision_type.must_be_inlined".
(* function_decl_inlining_decision_type.mli:53  val has_attribute_inline : t -> bool *)
Parameter has_attribute_inline : t -> M bool.
Extract Inlined Constant has_attribute_inline => "Function_decl_inlining_decision_type.has_attribute_inline".
(* function_decl_inlining_decision_type.mli:55  val cannot_be_inlined : t -> bool *)
Parameter cannot_be_inlined : t -> M bool.
Extract Inlined Constant cannot_be_inlined => "Function_decl_inlining_decision_type.cannot_be_inlined".
