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
   Simplify uses of the compiler's module [Exported_code], after its interface
   middle_end/flambda2/cmx/exported_code.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code Code_id Code_or_metadata.

(* exported_code.mli:16  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Exported_code.t".
(* exported_code.mli:28  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Exported_code.empty".
(* exported_code.mli:32  val add_code : keep_code:(Code_id.t -> bool) -> Code.t Code_id.Map.t -> t -> t *)
Parameter add_code : (Code_id.t -> M bool) -> Code_id.Map.t Code.t -> t -> M t.
Extract Inlined Constant add_code => "Exported_code.add_code".
(* exported_code.mli:34  val mark_as_imported : t -> t *)
Parameter mark_as_imported : t -> M t.
Extract Inlined Constant mark_as_imported => "Exported_code.mark_as_imported".
(* exported_code.mli:36  val merge : t -> t -> t *)
Parameter merge : t -> t -> M t.
Extract Inlined Constant merge => "Exported_code.merge".
(* exported_code.mli:38  val mem : Code_id.t -> t -> bool *)
Parameter mem : Code_id.t -> t -> M bool.
Extract Inlined Constant mem => "Exported_code.mem".
(* exported_code.mli:41  val find_exn : t -> Code_id.t -> Code_or_metadata.t *)
Parameter find_exn : t -> Code_id.t -> M Code_or_metadata.t.
Extract Inlined Constant find_exn => "Exported_code.find_exn".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Exported_code. End Exported_code.
