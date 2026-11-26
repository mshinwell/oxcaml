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

(* This file follows middle_end/flambda2/simplify/simplify_import.ml
   (Git blob d521d4294f3c059a862aab45133b1c300c170002), line by line: the short
   names that the files of Simplify give to the compiler's modules. The
   numbers in the comments are the lines of that file. Every ported file
   imports it, as every file of Simplify opens the compiler's. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter
  Bound_pattern Bound_var Code Code_id_or_symbol
  Continuation_extra_params_and_args Continuation_uses_env Downwards_acc
  Downwards_env Expr_builder Flambda Flambda2_types Flambda_features
  Flambda_kind Flambda_primitive Flambda_unit Lifted_constant
  Lifted_constant_state Name_mode Name_occurrences Rebuilt_expr
  Rebuilt_static_const Reg_width_const Simplified_expr
  Simplify_primitive_result Simplify_simple Static_const Upwards_acc
  Upwards_env.

(* 17 *)
Definition debug := Flambda_features.debug_flambda2.

(* 19-34 *)
Module Apply := Flambda.Apply.
Module Apply_cont := Flambda.Apply_cont.
Module Code := Code.
Module Const := Reg_width_const.
Module Continuation_handler := Flambda.Continuation_handler.
Module Continuation_handlers := Flambda.Continuation_handlers.
Module Expr := Flambda.Expr.
Module Function_declarations := Flambda.Function_declarations.
Module Function_params_and_body := Flambda.Function_params_and_body.
Module Let_cont := Flambda.Let_cont.
Module Let := Flambda.Let.
Module Named := Flambda.Named.
Module Non_recursive_let_cont_handler := Flambda.Non_recursive_let_cont_handler.
Module Recursive_let_cont_handlers := Flambda.Recursive_let_cont_handlers.
Module Set_of_closures := Flambda.Set_of_closures.
Module Switch := Flambda.Switch.
(* 35-67 *)
Module AC := Apply_cont.
Module BP := Bound_parameter.
Module BPt := Bound_pattern.
Module BV := Bound_var.
Module CH := Continuation_handler.
Module CIS := Code_id_or_symbol.
Module CUE := Continuation_uses_env.
Module DA := Downwards_acc.
Module DE := Downwards_env.
Module EA := Continuation_extra_params_and_args.Extra_arg.
Module EB := Expr_builder.
Module EPA := Continuation_extra_params_and_args.
Module FU := Flambda_unit.
Module K := Flambda_kind.
Module KS := Flambda_kind.With_subkind.
Module LC := Lifted_constant.
Module LCS := Lifted_constant_state.
Module NM := Name_mode.
Module NO := Name_occurrences.
Module P := Flambda_primitive.
Module RE := Rebuilt_expr.
Module RSC := Rebuilt_static_const.
Module RI := Apply_cont_rewrite_id.
Module S := Simplify_simple.
Module SC := Static_const.
Module SE := Simplified_expr.
Module SPR := Simplify_primitive_result.
Module T := Flambda2_types.
Module TE := Flambda2_types.Typing_env.
Module TEE := Flambda2_types.Typing_env_extension.
Module UA := Upwards_acc.
Module UE := Upwards_env.
Module VB := Bound_var.
