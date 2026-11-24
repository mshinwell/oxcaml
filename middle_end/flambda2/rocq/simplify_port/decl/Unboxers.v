(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Unboxers], after its interface
   middle_end/flambda2/simplify/unboxing/unboxers.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda2_types Flambda_kind Flambda_primitive Function_slot Name_mode Reg_width_const Simple Target_ocaml_int Value_slot.

(* unboxers.mli:19  type number_decider = { param_name : string; kind : K.Naked_number_kind.t; prove_is_a_boxed_number : TE.t -> T.t -> unit T.proof_of_property } *)
Record number_decider : Type := { param_name : string; kind : Flambda_kind.Naked_number_kind.t; prove_is_a_boxed_number : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.proof_of_property unit) }.
(* unboxers.mli:25  type unboxer = { var_name : string; var_kind : Flambda_kind.t; poison_const : Const.t; unboxing_prim : Simple.t -> P.t; prove_simple : TE.t -> min_name_mode:Name_mode.t -> T.t -> Simple.t T.meet_shortcut } *)
Record unboxer : Type := { var_name : string; var_kind : Flambda_kind.t; poison_const : Reg_width_const.t; unboxing_prim : Simple.t -> M Flambda_primitive.t; prove_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Simple.t) }.
Module Field.
  (* unboxers.mli:35  val unboxing_prim : P.Block_access_kind.t -> block:Simple.t -> index:Target_ocaml_int.t -> P.t *)
  Parameter unboxing_prim : Flambda_primitive.Block_access_kind.t -> Simple.t -> Target_ocaml_int.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Field.unboxing_prim".
  (* unboxers.mli:38  val unboxer : poison_const:Const.t -> P.Block_access_kind.t -> index:Target_ocaml_int.t -> unboxer *)
  Parameter unboxer : Reg_width_const.t -> Flambda_primitive.Block_access_kind.t -> Target_ocaml_int.t -> M Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Field.unboxer".
End Field.
Module Closure_field.
  (* unboxers.mli:46  val unboxing_prim : Function_slot.t -> closure:Simple.t -> Value_slot.t -> P.t *)
  Parameter unboxing_prim : Function_slot.t -> Simple.t -> Value_slot.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Closure_field.unboxing_prim".
  (* unboxers.mli:48  val unboxer : Function_slot.t -> Value_slot.t -> unboxer *)
  Parameter unboxer : Function_slot.t -> Value_slot.t -> M Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Closure_field.unboxer".
End Closure_field.
(* NOT DECLARED: Unboxers.Number_S: a module type that no file of Simplify names from outside the file that defines it. *)
Module Immediate.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Immediate.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Immediate.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Immediate.unboxer".
End Immediate.
Module Float32.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Float32.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Float32.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Float32.unboxer".
End Float32.
Module Float.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Float.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Float.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Float.unboxer".
End Float.
Module Int32.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Int32.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Int32.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Int32.unboxer".
End Int32.
Module Int64.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Int64.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Int64.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Int64.unboxer".
End Int64.
Module Nativeint.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Nativeint.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Nativeint.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Nativeint.unboxer".
End Nativeint.
Module Vec128.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Vec128.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Vec128.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Vec128.unboxer".
End Vec128.
Module Vec256.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Vec256.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Vec256.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Vec256.unboxer".
End Vec256.
Module Vec512.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Vec512.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Vec512.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Vec512.unboxer".
End Vec512.
Module Mask.
  (* unboxers.mli:57  val decider : number_decider *)
  Parameter decider : Unboxers.number_decider.
  Extract Inlined Constant decider => "Unboxers.Mask.decider".
  (* unboxers.mli:59  val unboxing_prim : Simple.t -> P.t *)
  Parameter unboxing_prim : Simple.t -> M Flambda_primitive.t.
  Extract Inlined Constant unboxing_prim => "Unboxers.Mask.unboxing_prim".
  (* unboxers.mli:61  val unboxer : unboxer *)
  Parameter unboxer : Unboxers.unboxer.
  Extract Inlined Constant unboxer => "Unboxers.Mask.unboxer".
End Mask.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Unboxers. End Unboxers.
