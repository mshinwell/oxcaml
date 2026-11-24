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
   Simplify uses of the compiler's module [Simplify_import], after its interface
   middle_end/flambda2/simplify/simplify_import.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter Bound_pattern Bound_var Code Code_id_or_symbol Continuation_extra_params_and_args Continuation_uses_env Downwards_acc Downwards_env Expr_builder Flambda Flambda2_types Flambda_kind Flambda_primitive Flambda_unit Lifted_constant Lifted_constant_state Name_mode Name_occurrences Rebuilt_expr Rebuilt_static_const Reg_width_const Simplified_expr Simplify_primitive_result Simplify_simple Static_const Upwards_acc Upwards_env.

(* simplify_import.mli:17  val debug : unit -> bool *)
Parameter debug : unit -> M bool.
Extract Inlined Constant debug => "Simplify_import.debug".
(* module Apply = Flambda.Apply *)
Module Apply := Flambda.Apply.
(* module Apply_cont = Flambda.Apply_cont *)
Module Apply_cont := Flambda.Apply_cont.
(* module Code = Code *)
Module Code := decl.Code.
(* module Const = Reg_width_const *)
Module Const := Reg_width_const.
(* module Continuation_handler = Flambda.Continuation_handler *)
Module Continuation_handler := Flambda.Continuation_handler.
(* module Continuation_handlers = Flambda.Continuation_handlers *)
Module Continuation_handlers := Flambda.Continuation_handlers.
(* module Expr = Flambda.Expr *)
Module Expr := Flambda.Expr.
(* module Function_declarations = Flambda.Function_declarations *)
Module Function_declarations := Flambda.Function_declarations.
(* module Function_params_and_body = Flambda.Function_params_and_body *)
Module Function_params_and_body := Flambda.Function_params_and_body.
(* module Let_cont = Flambda.Let_cont *)
Module Let_cont := Flambda.Let_cont.
(* module Let = Flambda.Let *)
Module Let := Flambda.Let.
(* module Named = Flambda.Named *)
Module Named := Flambda.Named.
(* module Non_recursive_let_cont_handler = Flambda.Non_recursive_let_cont_handler *)
Module Non_recursive_let_cont_handler := Flambda.Non_recursive_let_cont_handler.
(* module Recursive_let_cont_handlers = Flambda.Recursive_let_cont_handlers *)
Module Recursive_let_cont_handlers := Flambda.Recursive_let_cont_handlers.
(* module Set_of_closures = Flambda.Set_of_closures *)
Module Set_of_closures := Flambda.Set_of_closures.
(* module Switch = Flambda.Switch *)
Module Switch := Flambda.Switch.
(* module AC = Flambda.Apply_cont *)
Module AC := Flambda.Apply_cont.
(* module BP = Bound_parameter *)
Module BP := Bound_parameter.
(* module BPt = Bound_pattern *)
Module BPt := Bound_pattern.
(* module BV = Bound_var *)
Module BV := Bound_var.
(* module CH = Flambda.Continuation_handler *)
Module CH := Flambda.Continuation_handler.
(* module CIS = Code_id_or_symbol *)
Module CIS := Code_id_or_symbol.
(* module CUE = Continuation_uses_env *)
Module CUE := Continuation_uses_env.
(* module DA = Downwards_acc *)
Module DA := Downwards_acc.
(* module DE = Downwards_env *)
Module DE := Downwards_env.
(* module EA = Continuation_extra_params_and_args.Extra_arg *)
Module EA := Continuation_extra_params_and_args.Extra_arg.
(* module EB = Expr_builder *)
Module EB := Expr_builder.
(* module EPA = Continuation_extra_params_and_args *)
Module EPA := Continuation_extra_params_and_args.
(* module FU = Flambda_unit *)
Module FU := Flambda_unit.
(* module K = Flambda_kind *)
Module K := Flambda_kind.
(* module KS = Flambda_kind.With_subkind *)
Module KS := Flambda_kind.With_subkind.
(* module LC = Lifted_constant *)
Module LC := Lifted_constant.
(* module LCS = Lifted_constant_state *)
Module LCS := Lifted_constant_state.
(* module NM = Name_mode *)
Module NM := Name_mode.
(* module NO = Name_occurrences *)
Module NO := Name_occurrences.
(* module P = Flambda_primitive *)
Module P := Flambda_primitive.
(* module RE = Rebuilt_expr *)
Module RE := Rebuilt_expr.
(* module RSC = Rebuilt_static_const *)
Module RSC := Rebuilt_static_const.
(* module RI = Apply_cont_rewrite_id *)
Module RI := Apply_cont_rewrite_id.
(* module S = Simplify_simple *)
Module S := Simplify_simple.
(* module SC = Static_const *)
Module SC := Static_const.
(* module SE = Simplified_expr *)
Module SE := Simplified_expr.
(* module SPR = Simplify_primitive_result *)
Module SPR := Simplify_primitive_result.
(* module T = Flambda2_types *)
Module T := Flambda2_types.
(* module TE = Flambda2_types.Typing_env *)
Module TE := Flambda2_types.Typing_env.
(* module TEE = Flambda2_types.Typing_env_extension *)
Module TEE := Flambda2_types.Typing_env_extension.
(* module UA = Upwards_acc *)
Module UA := Upwards_acc.
(* module UE = Upwards_env *)
Module UE := Upwards_env.
(* module VB = Bound_var *)
Module VB := Bound_var.
