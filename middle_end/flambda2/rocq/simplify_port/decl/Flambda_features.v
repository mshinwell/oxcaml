(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2020 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flambda_features], after its interface
   middle_end/flambda2/ui/flambda_features.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Oxcaml_flags Stdlib_.

(* flambda_features.mli:17  val debug_flambda2 : unit -> bool *)
Parameter debug_flambda2 : unit -> M bool.
Extract Inlined Constant debug_flambda2 => "Flambda_features.debug_flambda2".
(* flambda_features.mli:31  val join_points : unit -> bool *)
Parameter join_points : unit -> M bool.
Extract Inlined Constant join_points => "Flambda_features.join_points".
(* flambda_features.mli:37  val cse_depth : unit -> int *)
Parameter cse_depth : unit -> M int.
Extract Inlined Constant cse_depth => "Flambda_features.cse_depth".
(* flambda_features.mli:80  val simplify_stubs : unit -> bool *)
Parameter simplify_stubs : unit -> M bool.
Extract Inlined Constant simplify_stubs => "Flambda_features.simplify_stubs".
(* flambda_features.mli:82  val kind_checks : unit -> bool *)
Parameter kind_checks : unit -> M bool.
Extract Inlined Constant kind_checks => "Flambda_features.kind_checks".
(* flambda_features.mli:84  val match_in_match : unit -> bool *)
Parameter match_in_match : unit -> M bool.
Extract Inlined Constant match_in_match => "Flambda_features.match_in_match".
(* flambda_features.mli:86  val flat_float_array : unit -> bool *)
Parameter flat_float_array : unit -> M bool.
Extract Inlined Constant flat_float_array => "Flambda_features.flat_float_array".
(* flambda_features.mli:88  val function_result_types : is_a_functor:bool -> bool *)
Parameter function_result_types : bool -> M bool.
Extract Inlined Constant function_result_types => "Flambda_features.function_result_types".
(* flambda_features.mli:90  val debug : unit -> bool *)
Parameter debug : unit -> M bool.
Extract Inlined Constant debug => "Flambda_features.debug".
(* flambda_features.mli:94  val float_const_prop : unit -> bool *)
Parameter float_const_prop : unit -> M bool.
Extract Inlined Constant float_const_prop => "Flambda_features.float_const_prop".
(* flambda_features.mli:107  val check_invariants : unit -> bool *)
Parameter check_invariants : unit -> M bool.
Extract Inlined Constant check_invariants => "Flambda_features.check_invariants".
(* flambda_features.mli:109  val check_light_invariants : unit -> bool *)
Parameter check_light_invariants : unit -> M bool.
Extract Inlined Constant check_light_invariants => "Flambda_features.check_light_invariants".
(* flambda_features.mli:118  val dump_flambda : unit -> bool *)
Parameter dump_flambda : unit -> M bool.
Extract Inlined Constant dump_flambda => "Flambda_features.dump_flambda".
(* flambda_features.mli:134  val dump_flow : unit -> bool *)
Parameter dump_flow : unit -> M bool.
Extract Inlined Constant dump_flow => "Flambda_features.dump_flow".
(* flambda_features.mli:142  val erase_in_types_depth_variables : unit -> bool *)
Parameter erase_in_types_depth_variables : unit -> M bool.
Extract Inlined Constant erase_in_types_depth_variables => "Flambda_features.erase_in_types_depth_variables".
Module Inlining.
  (* flambda_features.mli:145  type round_or_default = | Round of int | Default of Oxcaml_flags.opt_level *)
  Inductive round_or_default : Type :=
  | Round : int -> round_or_default
  | Default : Oxcaml_flags.opt_level_ -> round_or_default.
  Extract Inductive round_or_default => "Flambda_features.Inlining.round_or_default" [ "Flambda_features.Inlining.Round" "Flambda_features.Inlining.Default" ].
  (* flambda_features.mli:149  val depth_scaling_factor : int *)
  Parameter depth_scaling_factor : int.
  Extract Inlined Constant depth_scaling_factor => "Flambda_features.Inlining.depth_scaling_factor".
  (* flambda_features.mli:155  val max_rec_depth : round_or_default -> int *)
  Parameter max_rec_depth : round_or_default -> M int.
  Extract Inlined Constant max_rec_depth => "Flambda_features.Inlining.max_rec_depth".
  (* flambda_features.mli:179  val speculative_inlining_only_if_arguments_useful : unit -> bool *)
  Parameter speculative_inlining_only_if_arguments_useful : unit -> M bool.
  Extract Inlined Constant speculative_inlining_only_if_arguments_useful => "Flambda_features.Inlining.speculative_inlining_only_if_arguments_useful".
  (* flambda_features.mli:181  val speculative_inlining_track_lifted_constants : unit -> bool *)
  Parameter speculative_inlining_track_lifted_constants : unit -> M bool.
  Extract Inlined Constant speculative_inlining_track_lifted_constants => "Flambda_features.Inlining.speculative_inlining_track_lifted_constants".
End Inlining.
Module Debug.
  (* flambda_features.mli:187  val keep_invalid_handlers : unit -> bool *)
  Parameter keep_invalid_handlers : unit -> M bool.
  Extract Inlined Constant keep_invalid_handlers => "Flambda_features.Debug.keep_invalid_handlers".
End Debug.
Module Expert.
  (* flambda_features.mli:199  val phantom_lets : unit -> bool *)
  Parameter phantom_lets : unit -> M bool.
  Extract Inlined Constant phantom_lets => "Flambda_features.Expert.phantom_lets".
  (* flambda_features.mli:201  val max_unboxing_depth : unit -> int *)
  Parameter max_unboxing_depth : unit -> M int.
  Extract Inlined Constant max_unboxing_depth => "Flambda_features.Expert.max_unboxing_depth".
  (* flambda_features.mli:205  val max_function_simplify_run : unit -> int *)
  Parameter max_function_simplify_run : unit -> M int.
  Extract Inlined Constant max_function_simplify_run => "Flambda_features.Expert.max_function_simplify_run".
  (* flambda_features.mli:209  val cont_lifting_budget : unit -> int *)
  Parameter cont_lifting_budget : unit -> M int.
  Extract Inlined Constant cont_lifting_budget => "Flambda_features.Expert.cont_lifting_budget".
  (* flambda_features.mli:211  val cont_spec_threshold : unit -> float *)
  Parameter cont_spec_threshold : unit -> M Stdlib_.float_.
  Extract Inlined Constant cont_spec_threshold => "Flambda_features.Expert.cont_spec_threshold".
End Expert.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flambda_features. End Flambda_features.
