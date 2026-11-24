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
   Simplify uses of the compiler's module [Bound_static], after its interface
   middle_end/flambda2/bound_identifiers/bound_static.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Code_id_or_symbol Format Function_slot Symbol.

Module Pattern.
  (* bound_static.mli:22  type t = private | Code of Code_id.t | Set_of_closures of Symbol.t Function_slot.Lmap.t | Block_like of Symbol.t *)
  Inductive t : Type :=
  | Code : Code_id.t -> t
  | Set_of_closures : Function_slot.Lmap.t Symbol.t -> t
  | Block_like : Symbol.t -> t.
  Extract Inductive t => "Bound_static.Pattern.t" [ "Bound_static.Pattern.Code" "Bound_static.Pattern.Set_of_closures" "Bound_static.Pattern.Block_like" ].
  (* bound_static.mli:27  val code : Code_id.t -> t *)
  Parameter code : Code_id.t -> M t.
  Extract Inlined Constant code => "Bound_static.Pattern.code".
  (* bound_static.mli:29  val set_of_closures : Symbol.t Function_slot.Lmap.t -> t *)
  Parameter set_of_closures : Function_slot.Lmap.t Symbol.t -> M t.
  Extract Inlined Constant set_of_closures => "Bound_static.Pattern.set_of_closures".
  (* bound_static.mli:31  val block_like : Symbol.t -> t *)
  Parameter block_like : Symbol.t -> M t.
  Extract Inlined Constant block_like => "Bound_static.Pattern.block_like".
End Pattern.
(* bound_static.mli:36  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Bound_static.t".
(* bound_static.mli:38  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Bound_static.empty".
(* bound_static.mli:50  val create : Pattern.t list -> t *)
Parameter create : list Bound_static.Pattern.t -> M t.
Extract Inlined Constant create => "Bound_static.create".
(* bound_static.mli:52  val singleton : Pattern.t -> t *)
Parameter singleton : Bound_static.Pattern.t -> M t.
Extract Inlined Constant singleton => "Bound_static.singleton".
(* bound_static.mli:54  val to_list : t -> Pattern.t list *)
Parameter to_list : t -> M (list Bound_static.Pattern.t).
Extract Inlined Constant to_list => "Bound_static.to_list".
(* bound_static.mli:56  val binds_code : t -> bool *)
Parameter binds_code : t -> M bool.
Extract Inlined Constant binds_code => "Bound_static.binds_code".
(* bound_static.mli:58  val binds_symbols : t -> bool *)
Parameter binds_symbols : t -> M bool.
Extract Inlined Constant binds_symbols => "Bound_static.binds_symbols".
(* bound_static.mli:60  val symbols_being_defined : t -> Symbol.Set.t *)
Parameter symbols_being_defined : t -> M Symbol.Set_.t.
Extract Inlined Constant symbols_being_defined => "Bound_static.symbols_being_defined".
(* bound_static.mli:62  val code_being_defined : t -> Code_id.Set.t *)
Parameter code_being_defined : t -> M Code_id.Set_.t.
Extract Inlined Constant code_being_defined => "Bound_static.code_being_defined".
(* bound_static.mli:64  val everything_being_defined : t -> Code_id_or_symbol.Set.t *)
Parameter everything_being_defined : t -> M Code_id_or_symbol.Set_.t.
Extract Inlined Constant everything_being_defined => "Bound_static.everything_being_defined".
(* bound_static.mli:66  val everything_being_defined_as_list : t -> Code_id_or_symbol.t list *)
Parameter everything_being_defined_as_list : t -> M (list Code_id_or_symbol.t).
Extract Inlined Constant everything_being_defined_as_list => "Bound_static.everything_being_defined_as_list".
(* bound_static.mli:68  val concat : t -> t -> t *)
Parameter concat : t -> t -> M t.
Extract Inlined Constant concat => "Bound_static.concat".
(* bound_static.mli:72  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Bound_static.print".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Bound_static. End Bound_static.
