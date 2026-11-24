(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Vincent Laviron, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2020 OCamlPro SAS                                          *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Code_or_metadata], after its interface
   middle_end/flambda2/terms/code_or_metadata.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code Code_metadata.

(* code_or_metadata.mli:16  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Code_or_metadata.t".
Module View.
  (* code_or_metadata.mli:21  type t = private | Code_present of Code.t | Metadata_only of Code_metadata.t *)
  Inductive t : Type :=
  | Code_present : Code.t -> t
  | Metadata_only : Code_metadata.t -> t.
  Extract Inductive t => "Code_or_metadata.View.t" [ "Code_or_metadata.View.Code_present" "Code_or_metadata.View.Metadata_only" ].
End View.
(* code_or_metadata.mli:28  val view : t -> View.t *)
Parameter view : t -> M Code_or_metadata.View.t.
Extract Inlined Constant view => "Code_or_metadata.view".
(* code_or_metadata.mli:31  val get_code : t -> Code.t *)
Parameter get_code : t -> M Code.t.
Extract Inlined Constant get_code => "Code_or_metadata.get_code".
(* code_or_metadata.mli:39  val create : Code.t -> t *)
Parameter create : Code.t -> M t.
Extract Inlined Constant create => "Code_or_metadata.create".
(* code_or_metadata.mli:53  val code_metadata : t -> Code_metadata.t *)
Parameter code_metadata : t -> M Code_metadata.t.
Extract Inlined Constant code_metadata => "Code_or_metadata.code_metadata".
(* code_or_metadata.mli:55  val code_present : t -> bool *)
Parameter code_present : t -> M bool.
Extract Inlined Constant code_present => "Code_or_metadata.code_present".
