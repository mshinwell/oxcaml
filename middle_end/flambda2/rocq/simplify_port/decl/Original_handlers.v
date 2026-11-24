(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Original_handlers], after its interface
   middle_end/flambda2/simplify/original_handlers.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Continuation Format Lifted_cont_params Non_recursive_handler One_recursive_handler.

(* original_handlers.mli:16  type t = private | Recursive of { invariant_params : Bound_parameters.t; lifted_params : Lifted_cont_params.t; continuation_handlers : One_recursive_handler.t Continuation.Lmap.t; can_be_lifted : bool } | Non_recursive of Non_recursive_handler.t *)
Record recursive_payload_ : Type := { invariant_params : Bound_parameters.t; lifted_params : Lifted_cont_params.t; continuation_handlers : Continuation.Lmap.t One_recursive_handler.t; can_be_lifted : bool }.
Inductive t : Type :=
| Recursive : recursive_payload_ -> t
| Non_recursive : Non_recursive_handler.t -> t.
(* original_handlers.mli:25  val create_recursive : invariant_params:Bound_parameters.t -> lifted_params:Lifted_cont_params.t -> continuation_handlers:One_recursive_handler.t Continuation.Lmap.t -> can_be_lifted:bool -> t *)
Parameter create_recursive : Bound_parameters.t -> Lifted_cont_params.t -> Continuation.Lmap.t One_recursive_handler.t -> bool -> M t.
Extract Inlined Constant create_recursive => "Original_handlers.create_recursive".
(* original_handlers.mli:32  val create_non_recursive : Non_recursive_handler.t -> t *)
Parameter create_non_recursive : Non_recursive_handler.t -> M t.
Extract Inlined Constant create_non_recursive => "Original_handlers.create_non_recursive".
(* original_handlers.mli:34  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Original_handlers.print".
(* original_handlers.mli:36  val bound_continuations : t -> Continuation.t list *)
Parameter bound_continuations : t -> M (list Continuation.t).
Extract Inlined Constant bound_continuations => "Original_handlers.bound_continuations".
(* original_handlers.mli:38  val can_be_lifted : t -> bool *)
Parameter can_be_lifted_ : t -> M bool.
Extract Inlined Constant can_be_lifted_ => "Original_handlers.can_be_lifted".
(* original_handlers.mli:40  val add_params_to_lift : t -> Lifted_cont_params.t -> t *)
Parameter add_params_to_lift : t -> Lifted_cont_params.t -> M t.
Extract Inlined Constant add_params_to_lift => "Original_handlers.add_params_to_lift".
