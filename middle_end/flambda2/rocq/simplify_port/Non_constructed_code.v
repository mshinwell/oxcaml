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

(* This file follows middle_end/flambda2/simplify/non_constructed_code.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the arguments
   by place) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code0 Code_metadata Format Name_occurrences Renaming
  Unit.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
Definition t : Type := Code0.t unit.

(* 19 *)
Definition code_metadata : t -> M Code_metadata.t := Code0.code_metadata.

(* PORT-GAP(verbatim): 21-27, the module [Metadata_view] and the [include]
   of the result of the functor [Code_metadata.Code_metadata_accessors] are
   the compiler's text, and they stand at the END of the extracted file, not
   here: nothing of this file uses what they define. *)
(*OCAML-END
module Metadata_view = struct
  type nonrec 'a t = t

  let metadata = code_metadata
end

include Code_metadata.Code_metadata_accessors [@inlined hint] (Metadata_view)
OCAML-END*)

(* 29-31 *)
Definition create_with_metadata
    : Name_occurrences.t -> Code_metadata.t -> M t :=
  Code0.create_with_metadata Unit.print tt.

(* 33-34 *)
Definition create : Name_occurrences.t -> Code_metadata.create_type t :=
  Code0.create Unit.print tt.

(* 36 *)
Definition print : Format.formatter -> t -> M unit := Code0.print Unit.print.

(* 38 *)
Definition free_names : t -> M Name_occurrences.t := Code0.free_names.

(* 40-41 *)
Definition apply_renaming : t -> Renaming.t -> M t :=
  Code0.apply_renaming (fun (_ : unit) (_ : Renaming.t) => ret tt).
