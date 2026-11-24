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
   Simplify uses of the compiler's module [Call_kind], after its interface
   middle_end/flambda2/terms/call_kind.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Coeffects Effects Or_unknown Simple.

Module Function_call.
  (* call_kind.mli:20  type t = private | Direct of Code_id.t ( ** The [code_id] uniquely determines the function symbol that must be called. * ) | Indirect_unknown_arity | Indirect_known_arity of Code_id.Set.t Or_unknown.t *)
  Inductive t : Type :=
  | Direct : Code_id.t -> t
  | Indirect_unknown_arity : t
  | Indirect_known_arity : Or_unknown.t Code_id.Set_.t -> t.
  (* call_kind.mli:30  val indirect_known_arity : code_ids:Code_id.Set.t Or_unknown.t -> t *)
  Parameter indirect_known_arity : Or_unknown.t Code_id.Set_.t -> M t.
  Extract Inlined Constant indirect_known_arity => "Call_kind.Function_call.indirect_known_arity".
End Function_call.
Module Method_kind.
  (* call_kind.mli:34  type t = | Self | Public | Cached *)
  Parameter t : Type.
  Extract Inlined Constant t => "Call_kind.Method_kind.t".
End Method_kind.
Module Effect.
  (* call_kind.mli:51  type t = private | Perform of { eff : Simple.t } | Reperform of { eff : Simple.t; cont : Simple.t; last_fiber : Simple.t } | With_stack of { valuec : Simple.t; exnc : Simple.t; effc : Simple.t; f : Simple.t; arg : Simple.t } | With_stack_preemptible of { valuec : Simple.t; exnc : Simple.t; effc : Simple.t; handle_tick : Simple.t; f : Simple.t; arg : Simple.t } | Continue of { cont : Simple.t; v... *)
  (* PORT-GAP(type): the name of the field [eff] is taken in Rocq: abstract, with a maker for each constructor and one eliminator. *)
  Parameter t : Type.
  Extract Inlined Constant t => "Call_kind.Effect.t".
  Parameter mk_Perform : Simple.t -> t.
  Extract Inlined Constant mk_Perform => "(fun x__1 -> Call_kind.Effect.Perform { eff = x__1 })".
  Parameter mk_Reperform : Simple.t -> Simple.t -> Simple.t -> t.
  Extract Inlined Constant mk_Reperform => "(fun x__1 x__2 x__3 -> Call_kind.Effect.Reperform { eff = x__1; cont = x__2; last_fiber = x__3 })".
  Parameter mk_With_stack : Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> t.
  Extract Inlined Constant mk_With_stack => "(fun x__1 x__2 x__3 x__4 x__5 -> Call_kind.Effect.With_stack { valuec = x__1; exnc = x__2; effc = x__3; f = x__4; arg = x__5 })".
  Parameter mk_With_stack_preemptible : Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> t.
  Extract Inlined Constant mk_With_stack_preemptible => "(fun x__1 x__2 x__3 x__4 x__5 x__6 -> Call_kind.Effect.With_stack_preemptible { valuec = x__1; exnc = x__2; effc = x__3; handle_tick = x__4; f = x__5; arg = x__6 })".
  Parameter mk_Continue : Simple.t -> Simple.t -> t.
  Extract Inlined Constant mk_Continue => "(fun x__1 x__2 -> Call_kind.Effect.Continue { cont = x__1; value = x__2 })".
  Parameter mk_Discontinue : Simple.t -> Simple.t -> t.
  Extract Inlined Constant mk_Discontinue => "(fun x__1 x__2 -> Call_kind.Effect.Discontinue { cont = x__1; exn = x__2 })".
  Parameter mk_Discontinue_with_backtrace : Simple.t -> Simple.t -> Simple.t -> t.
  Extract Inlined Constant mk_Discontinue_with_backtrace => "(fun x__1 x__2 x__3 -> Call_kind.Effect.Discontinue_with_backtrace { cont = x__1; exn = x__2; bt = x__3 })".
  Parameter match_t : forall {Res : Type}, t -> (Simple.t -> M Res) -> (Simple.t -> Simple.t -> Simple.t -> M Res) -> (Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> M Res) -> (Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> M Res) -> (Simple.t -> Simple.t -> M Res) -> (Simple.t -> Simple.t -> M Res) -> (Simple.t -> Simple.t -> Simple.t -> M Res) -> M Res.
  Extract Inlined Constant match_t => "(fun x__0 f__1 f__2 f__3 f__4 f__5 f__6 f__7 -> match x__0 with Call_kind.Effect.Perform { eff = x__1 } -> f__1 x__1 | Call_kind.Effect.Reperform { eff = x__1; cont = x__2; last_fiber = x__3 } -> f__2 x__1 x__2 x__3 | Call_kind.Effect.With_stack { valuec = x__1; exnc = x__2; effc = x__3; f = x__4; arg = x__5 } -> f__3 x__1 x__2 x__3 x__4 x__5 | Call_kind.Effect.With_stack_preemptible { valuec = x__1; exnc = x__2; effc = x__3; handle_tick = x__4; f = x__5; arg = x__6 } -> f__4 x__1 x__2 x__3 x__4 x__5 x__6 | Call_kind.Effect.Continue { cont = x__1; value = x__2 } -> f__5 x__1 x__2 | Call_kind.Effect.Discontinue { cont = x__1; exn = x__2 } -> f__6 x__1 x__2 | Call_kind.Effect.Discontinue_with_backtrace { cont = x__1; exn = x__2; bt = x__3 } -> f__7 x__1 x__2 x__3)".
  (* call_kind.mli:89  val perform : eff:Simple.t -> t *)
  Parameter perform : Simple.t -> M t.
  Extract Inlined Constant perform => "Call_kind.Effect.perform".
  (* call_kind.mli:91  val reperform : eff:Simple.t -> cont:Simple.t -> last_fiber:Simple.t -> t *)
  Parameter reperform : Simple.t -> Simple.t -> Simple.t -> M t.
  Extract Inlined Constant reperform => "Call_kind.Effect.reperform".
  (* call_kind.mli:93  val with_stack : valuec:Simple.t -> exnc:Simple.t -> effc:Simple.t -> f:Simple.t -> arg:Simple.t -> t *)
  Parameter with_stack : Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> M t.
  Extract Inlined Constant with_stack => "Call_kind.Effect.with_stack".
  (* call_kind.mli:101  val with_stack_preemptible : valuec:Simple.t -> exnc:Simple.t -> effc:Simple.t -> handle_tick:Simple.t -> f:Simple.t -> arg:Simple.t -> t *)
  Parameter with_stack_preemptible : Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> M t.
  Extract Inlined Constant with_stack_preemptible => "Call_kind.Effect.with_stack_preemptible".
  (* call_kind.mli:110  val continue : cont:Simple.t -> value:Simple.t -> t *)
  Parameter continue : Simple.t -> Simple.t -> M t.
  Extract Inlined Constant continue => "Call_kind.Effect.continue".
  (* call_kind.mli:112  val discontinue : cont:Simple.t -> exn:Simple.t -> t *)
  Parameter discontinue : Simple.t -> Simple.t -> M t.
  Extract Inlined Constant discontinue => "Call_kind.Effect.discontinue".
  (* call_kind.mli:114  val discontinue_with_backtrace : cont:Simple.t -> exn:Simple.t -> bt:Simple.t -> t *)
  Parameter discontinue_with_backtrace : Simple.t -> Simple.t -> Simple.t -> M t.
  Extract Inlined Constant discontinue_with_backtrace => "Call_kind.Effect.discontinue_with_backtrace".
End Effect.
(* call_kind.mli:128  type t = private | Function of { function_call : Function_call.t } | Method of { kind : Method_kind.t; obj : Simple.t } | C_call of { needs_caml_c_call : bool; is_c_builtin : bool; effects : Effects.t; coeffects : Coeffects.t } | Effect of Effect.t *)
Record function_payload_ : Type := { function_call : Call_kind.Function_call.t }.
Record method_payload_ : Type := { kind : Call_kind.Method_kind.t; obj : Simple.t }.
Record c_call_payload_ : Type := { needs_caml_c_call : bool; is_c_builtin : bool; effects : Effects.t; coeffects : Coeffects.t }.
Inductive t : Type :=
| Function : function_payload_ -> t
| Method : method_payload_ -> t
| C_call : c_call_payload_ -> t
| Effect : Call_kind.Effect.t -> t.
(* call_kind.mli:146  val direct_function_call : Code_id.t -> t *)
Parameter direct_function_call : Code_id.t -> M t.
Extract Inlined Constant direct_function_call => "Call_kind.direct_function_call".
(* call_kind.mli:148  val indirect_function_call_unknown_arity : t *)
Parameter indirect_function_call_unknown_arity : t.
Extract Inlined Constant indirect_function_call_unknown_arity => "Call_kind.indirect_function_call_unknown_arity".
(* call_kind.mli:150  val indirect_function_call_known_arity : code_ids:Code_id.Set.t Or_unknown.t -> t *)
Parameter indirect_function_call_known_arity : Or_unknown.t Code_id.Set_.t -> M t.
Extract Inlined Constant indirect_function_call_known_arity => "Call_kind.indirect_function_call_known_arity".
(* call_kind.mli:162  val effect_ : Effect.t -> t *)
Parameter effect_ : Call_kind.Effect.t -> M t.
Extract Inlined Constant effect_ => "Call_kind.effect_".
