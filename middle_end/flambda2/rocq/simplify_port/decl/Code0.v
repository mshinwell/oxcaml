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
   Simplify uses of the compiler's module [Code0], after its interface
   middle_end/flambda2/terms/code0.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_metadata Format Name_occurrences Renaming.

(* code0.mli:17  type 'function_params_and_body t *)
Parameter t : Type -> Type.
Extract Constant t "'a1" => "('a1) Code0.t".
(* code0.mli:19  val code_metadata : _ t -> Code_metadata.t *)
Parameter code_metadata : forall {A : Type}, t A -> M Code_metadata.t.
Extract Inlined Constant code_metadata => "Code0.code_metadata".
(* code0.mli:27  val create_with_metadata : print_function_params_and_body: (Format.formatter -> 'function_params_and_body -> unit) -> params_and_body:'function_params_and_body -> free_names_of_params_and_body:Name_occurrences.t -> code_metadata:Code_metadata.t -> 'function_params_and_body t *)
Parameter create_with_metadata : forall {Function_params_and_body : Type}, (Format.formatter -> Function_params_and_body -> M unit) -> Function_params_and_body -> Name_occurrences.t -> Code_metadata.t -> M (t Function_params_and_body).
Extract Inlined Constant create_with_metadata => "Code0.create_with_metadata".
(* code0.mli:35  val create : print_function_params_and_body: (Format.formatter -> 'function_params_and_body -> unit) -> params_and_body:'function_params_and_body -> free_names_of_params_and_body:Name_occurrences.t -> 'function_params_and_body t Code_metadata.create_type *)
Parameter create : forall {Function_params_and_body : Type}, (Format.formatter -> Function_params_and_body -> M unit) -> Function_params_and_body -> Name_occurrences.t -> Code_metadata.create_type (t Function_params_and_body).
Extract Inlined Constant create => "Code0.create".
(* code0.mli:57  val free_names : _ t -> Name_occurrences.t *)
Parameter free_names : forall {A : Type}, t A -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Code0.free_names".
(* code0.mli:59  val apply_renaming : apply_renaming_function_params_and_body: ('function_params_and_body -> Renaming.t -> 'function_params_and_body) -> 'function_params_and_body t -> Renaming.t -> 'function_params_and_body t *)
Parameter apply_renaming : forall {Function_params_and_body : Type}, (Function_params_and_body -> Renaming.t -> M Function_params_and_body) -> t Function_params_and_body -> Renaming.t -> M (t Function_params_and_body).
Extract Inlined Constant apply_renaming => "Code0.apply_renaming".
(* code0.mli:66  val print : print_function_params_and_body: (Format.formatter -> 'function_params_and_body -> unit) -> Format.formatter -> 'function_params_and_body t -> unit *)
Parameter print : forall {Function_params_and_body : Type}, (Format.formatter -> Function_params_and_body -> M unit) -> Format.formatter -> t Function_params_and_body -> M unit.
Extract Inlined Constant print => "Code0.print".
