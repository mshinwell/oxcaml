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
   Simplify uses of the compiler's module [Apply_cont_rewrite_id], after its interface
   middle_end/flambda2/identifiers/apply_cont_rewrite_id.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* apply_cont_rewrite_id.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Apply_cont_rewrite_id.t".
Module Set_.
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Apply_cont_rewrite_id.Set.t".
End Set_.
Module Map.
  (* apply_cont_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Apply_cont_rewrite_id.Map.t".
End Map.
