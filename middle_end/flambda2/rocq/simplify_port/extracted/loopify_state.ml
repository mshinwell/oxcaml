(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                     Nathanaëlle Courant, OCamlPro                      *)
(*                                                                        *)
(*   Copyright 2022 OCamlPro SAS                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Loopify_state.v, which follows
   middle_end/flambda2/simplify/loopify_state.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad

type t =
  | Do_not_loopify
  | Loopify of Continuation.t

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf = function
  | Do_not_loopify -> Format.fprintf ppf "do_not_loopify"
  | Loopify cont ->
    Format.fprintf ppf "@[<hov 1>(loopify@ %a)@]" Continuation.print cont

(** val do_not_loopify : t **)

let do_not_loopify = Do_not_loopify

(** val loopify : Continuation.t -> t coq_M **)

let loopify cont = Loopify cont
