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
   (Git blob 49bd466681ca21c4f42ce51f4e78b87e46f34bb2). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Debuginfo Name_occurrences.

(* function_declarations.mli:19  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Function_declarations.t".
(* function_declarations.mli:21  include Expr_std.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Function_declarations.free_names".
(* function_declarations.mli:25  type code_id_in_function_declaration = | Deleted of { function_slot_size : int; dbg : Debuginfo.t } | Code_id of { code_id : Code_id.t; only_full_applications : bool } *)
Inductive code_id_in_function_declaration : Type :=
| Deleted : int -> Debuginfo.t -> code_id_in_function_declaration
| Code_id : Code_id.t -> bool -> code_id_in_function_declaration.
Extract Inductive code_id_in_function_declaration => "Function_declarations.code_id_in_function_declaration" [ "(fun (x__1, x__2) -> (Function_declarations.Deleted { function_slot_size = x__1; dbg = x__2 } : Function_declarations.code_id_in_function_declaration))" "(fun (x__1, x__2) -> (Function_declarations.Code_id { code_id = x__1; only_full_applications = x__2 } : Function_declarations.code_id_in_function_declaration))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Function_declarations.code_id_in_function_declaration) with Function_declarations.Deleted { function_slot_size = x__1; dbg = x__2 } -> f__1 x__1 x__2 | Function_declarations.Code_id { code_id = x__1; only_full_applications = x__2 } -> f__2 x__1 x__2)".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Function_declarations. End Function_declarations.
