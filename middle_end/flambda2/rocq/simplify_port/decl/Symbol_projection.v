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

Module Projection.
  (* symbol_projection.mli:16  type t = private | Block_load of { index : Target_ocaml_int.t; block_shape : Flambda_kind.Block_shape.t } | Project_value_slot of { project_from : Function_slot.t; value_slot : Value_slot.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Symbol_projection.Projection.t".
End Projection.
(* symbol_projection.mli:32  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Symbol_projection.t".
