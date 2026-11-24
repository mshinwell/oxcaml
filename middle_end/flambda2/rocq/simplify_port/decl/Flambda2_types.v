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
   Simplify uses of the compiler's module [Flambda2_types], after its interface
   middle_end/flambda2/types/flambda2_types.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* flambda2_types.mli:20  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Flambda2_types.t".
(* flambda2_types.mli:22  type flambda_type = t *)
Definition flambda_type : Type := t.
Extract Inlined Constant flambda_type => "Flambda2_types.flambda_type".
(* flambda2_types.mli:38  type typing_env *)
Parameter typing_env : Type.
Extract Inlined Constant typing_env => "Flambda2_types.typing_env".
Module Code_age_relation.
  (* flambda2_types.mli:43  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda2_types.Code_age_relation.t".
  (* flambda2_types.mli:47  val empty : t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Flambda2_types.Code_age_relation.empty".
End Code_age_relation.
Module Typing_env_extension.
  Module With_extra_variables.
    (* flambda2_types.mli:99  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Flambda2_types.Typing_env_extension.With_extra_variables.t".
  End With_extra_variables.
End Typing_env_extension.
Module Typing_env.
  (* flambda2_types.mli:120  type t = typing_env *)
  Definition t : Type := Flambda2_types.typing_env.
  Extract Inlined Constant t => "Flambda2_types.Typing_env.t".
  Module Serializable.
    (* flambda2_types.mli:140  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Flambda2_types.Typing_env.Serializable.t".
  End Serializable.
End Typing_env.
Module Join_analysis.
  (* flambda2_types.mli:303  type 'a t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Flambda2_types.Join_analysis.t".
End Join_analysis.
