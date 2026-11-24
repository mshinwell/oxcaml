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
   Simplify uses of the compiler's module [Bound_parameters], after its interface
   middle_end/flambda2/bound_identifiers/bound_parameters.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameter Format Int_ids.

(* bound_parameters.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Bound_parameters.t".
(* bound_parameters.mli:19  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Bound_parameters.empty".
(* bound_parameters.mli:25  val append : t -> t -> t *)
Parameter append : t -> t -> M t.
Extract Inlined Constant append => "Bound_parameters.append".
(* bound_parameters.mli:27  val to_list : t -> Bound_parameter.t list *)
Parameter to_list : t -> M (list Bound_parameter.t).
Extract Inlined Constant to_list => "Bound_parameters.to_list".
(* bound_parameters.mli:41  val simples : t -> Int_ids.Simple.t list *)
Parameter simples : t -> M (list Int_ids.Simple.t).
Extract Inlined Constant simples => "Bound_parameters.simples".
(* bound_parameters.mli:57  include Bindable.S with type t := t *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Bound_parameters.print".
