(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2020 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Symbol_projection], after its interface
   middle_end/flambda2/term_basics/symbol_projection.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_kind Format Function_slot Name_occurrences Symbol Target_ocaml_int Value_slot.

Module Projection.
  (* symbol_projection.mli:16  type t = private | Block_load of { index : Target_ocaml_int.t; block_shape : Flambda_kind.Block_shape.t } | Project_value_slot of { project_from : Function_slot.t; value_slot : Value_slot.t } *)
  Inductive t : Type :=
  | Block_load : Target_ocaml_int.t -> Flambda_kind.Block_shape.t -> t
  | Project_value_slot : Function_slot.t -> Value_slot.t -> t.
  Extract Inductive t => "Symbol_projection.Projection.t" [ "(fun (x__1, x__2) -> (Symbol_projection.Projection.Block_load { index = x__1; block_shape = x__2 } : Symbol_projection.Projection.t))" "(fun (x__1, x__2) -> (Symbol_projection.Projection.Project_value_slot { project_from = x__1; value_slot = x__2 } : Symbol_projection.Projection.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Symbol_projection.Projection.t) with Symbol_projection.Projection.Block_load { index = x__1; block_shape = x__2 } -> f__1 x__1 x__2 | Symbol_projection.Projection.Project_value_slot { project_from = x__1; value_slot = x__2 } -> f__2 x__1 x__2)".
  (* symbol_projection.mli:26  val block_load : index:Target_ocaml_int.t -> block_shape:Flambda_kind.Block_shape.t -> t *)
  Parameter block_load : Target_ocaml_int.t -> Flambda_kind.Block_shape.t -> M t.
  Extract Inlined Constant block_load => "Symbol_projection.Projection.block_load".
  (* symbol_projection.mli:29  val project_value_slot : Function_slot.t -> Value_slot.t -> t *)
  Parameter project_value_slot : Function_slot.t -> Value_slot.t -> M t.
  Extract Inlined Constant project_value_slot => "Symbol_projection.Projection.project_value_slot".
End Projection.
(* symbol_projection.mli:32  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Symbol_projection.t".
(* symbol_projection.mli:34  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Symbol_projection.print".
(* symbol_projection.mli:36  val create : Symbol.t -> Projection.t -> Flambda_kind.With_subkind.t -> t *)
Parameter create : Symbol.t -> Symbol_projection.Projection.t -> Flambda_kind.With_subkind.t -> M t.
Extract Inlined Constant create => "Symbol_projection.create".
(* symbol_projection.mli:38  val kind : t -> Flambda_kind.With_subkind.t *)
Parameter kind : t -> M Flambda_kind.With_subkind.t.
Extract Inlined Constant kind => "Symbol_projection.kind".
(* symbol_projection.mli:40  val symbol : t -> Symbol.t *)
Parameter symbol : t -> M Symbol.t.
Extract Inlined Constant symbol => "Symbol_projection.symbol".
(* symbol_projection.mli:42  val projection : t -> Projection.t *)
Parameter projection : t -> M Symbol_projection.Projection.t.
Extract Inlined Constant projection => "Symbol_projection.projection".
(* symbol_projection.mli:46  val equal : t -> t -> bool *)
Parameter equal : t -> t -> M bool.
Extract Inlined Constant equal => "Symbol_projection.equal".
(* symbol_projection.mli:50  include Contains_names.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Symbol_projection.free_names".
