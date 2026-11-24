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
   Simplify uses of the compiler's module [Simplify], after its interface
   middle_end/flambda2/simplify/simplify.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Flambda_cmx Flambda_unit Slot_offsets Target_system.

(* simplify.mli:23  type simplify_result = private { free_names : Name_occurrences.t; final_typing_env : Typing_env.t; all_code : Exported_code.t; slot_offsets : Slot_offsets.t; unit : Flambda_unit.t } *)
Parameter simplify_result : Type.
Extract Inlined Constant simplify_result => "Simplify.simplify_result".
(* simplify.mli:31  val run : cmx_loader:Flambda_cmx.loader -> machine_width:Target_system.Machine_width.t -> round:int -> code_slot_offsets:Slot_offsets.t Code_id.Map.t -> Flambda_unit.t -> simplify_result *)
Parameter run : Flambda_cmx.loader -> Target_system.Machine_width.t -> int -> Code_id.Map.t Slot_offsets.t -> Flambda_unit.t -> M simplify_result.
Extract Inlined Constant run => "Simplify.run".
