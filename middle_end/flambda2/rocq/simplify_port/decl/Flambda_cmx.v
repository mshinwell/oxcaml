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
   Simplify uses of the compiler's module [Flambda_cmx], after its interface
   middle_end/flambda2/cmx/flambda_cmx.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Compilation_unit Exported_code Flambda2_types.

(* flambda_cmx.mli:20  type loader *)
Parameter loader : Type.
Extract Inlined Constant loader => "Flambda_cmx.loader".
(* flambda_cmx.mli:25  val get_imported_code : loader -> unit -> Exported_code.t *)
Parameter get_imported_code : loader -> unit -> M Exported_code.t.
Extract Inlined Constant get_imported_code => "Flambda_cmx.get_imported_code".
(* flambda_cmx.mli:27  val load_cmx_file_contents : loader -> Compilation_unit.t -> Flambda2_types.Typing_env.Serializable.t option *)
Parameter load_cmx_file_contents : loader -> Compilation_unit.t -> M (option Flambda2_types.Typing_env.Serializable.t).
Extract Inlined Constant load_cmx_file_contents => "Flambda_cmx.load_cmx_file_contents".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flambda_cmx. End Flambda_cmx.
