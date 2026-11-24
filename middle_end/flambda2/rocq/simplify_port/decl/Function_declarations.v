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
   Simplify uses of the compiler's module [Function_declarations], after its interface
   middle_end/flambda2/terms/function_declarations.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Debuginfo Name_occurrences.

(* function_declarations.mli:19  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Function_declarations.t".
(* function_declarations.mli:21  include Expr_std.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Function_declarations.free_names".
(* function_declarations.mli:25  type code_id_in_function_declaration = | Deleted of { function_slot_size : int; dbg : Debuginfo.t } | Code_id of { code_id : Code_id.t; only_full_applications : bool } *)
Record deleted_payload_ : Type := { function_slot_size : int; dbg : Debuginfo.t }.
Record code_id_payload_ : Type := { code_id : Code_id.t; only_full_applications : bool }.
Inductive code_id_in_function_declaration : Type :=
| Deleted : deleted_payload_ -> code_id_in_function_declaration
| Code_id : code_id_payload_ -> code_id_in_function_declaration.
