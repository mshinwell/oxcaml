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
   Simplify uses of the compiler's module [Oxcaml_args], after its interface
   driver/oxcaml_args.mli
   (Git blob 3b3d2901f62143399568fdcd67210fbd642484f6). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Extra_options.
  (* oxcaml_args.mli:309  val symbol : string -> string -> 'a -> (string * 'a) list -> unit -> 'a *)
  Parameter symbol : forall {A : Type}, string -> string -> A -> list (string * A) -> unit -> M A.
  Extract Inlined Constant symbol => "Oxcaml_args.Extra_options.symbol".
End Extra_options.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Oxcaml_args. End Oxcaml_args.
