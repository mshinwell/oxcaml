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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Non_constructed_code.v, which follows
   middle_end/flambda2/simplify/non_constructed_code.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad

type t = unit Code0.t

(** val code_metadata : t -> Code_metadata.t coq_M **)

let code_metadata = Code0.code_metadata

(** val create_with_metadata : Name_occurrences.t -> Code_metadata.t -> t coq_M
    **)

let create_with_metadata = Code0.create_with_metadata Unit.print ()

(** val create : Name_occurrences.t -> t Code_metadata.create_type **)

let create = Code0.create Unit.print ()

(** val print : Format.formatter -> t -> unit coq_M **)

let print = Code0.print Unit.print

(** val free_names : t -> Name_occurrences.t coq_M **)

let free_names = Code0.free_names

(** val apply_renaming : t -> Renaming.t -> t coq_M **)

let apply_renaming = Code0.apply_renaming (fun _ _ -> ())

module Metadata_view = struct
  type nonrec 'a t = t

  let metadata = code_metadata
end

include Code_metadata.Code_metadata_accessors [@inlined hint] (Metadata_view)
