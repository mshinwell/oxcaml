(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Are_lifting_conts.v, which follows
   middle_end/flambda2/simplify/are_lifting_conts.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

type reason =
  | At_toplevel
  | In_speculative_inlining
  | In_continuation_specialization
  | In_recursive_continuation
  | In_inlinable_continuation

type t =
  | Not_lifting of reason
  | Analyzing of
      { continuation : Continuation.t;
        is_exn_handler : bool;
        uses : Continuation_uses.t
      }
  | Lifting_out_of of { continuation : Continuation.t }

open Port_monad

(** val no_lifting : reason -> t coq_M **)

let no_lifting reason0 = Not_lifting reason0

(** val think_about_lifting_out_of : bool -> Continuation.t ->
    Continuation_uses.t -> t coq_M **)

let think_about_lifting_out_of is_exn_handler continuation uses =
  (fun (x__1, x__2, x__3) ->
    (Analyzing { continuation = x__1; is_exn_handler = x__2; uses = x__3 } : t))
    (continuation, is_exn_handler, uses)

(** val lift_continuations_out_of : Continuation.t -> t coq_M **)

let lift_continuations_out_of continuation =
  (fun x__1 -> (Lifting_out_of { continuation = x__1 } : t)) continuation

(** val print_reason : Format.formatter -> reason -> unit coq_M **)

let print_reason ppf = function
  | At_toplevel -> Format.fprintf ppf "at_toplevel"
  | In_speculative_inlining -> Format.fprintf ppf "in_speculative_inlining"
  | In_continuation_specialization ->
    Format.fprintf ppf "in_continuation_specialization"
  | In_recursive_continuation -> Format.fprintf ppf "in_recursive_continuation"
  | In_inlinable_continuation -> Format.fprintf ppf "in_inlinable_continuation"

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  (fun f__1 f__2 f__3 x__0 ->
    match (x__0 : t) with
    | Not_lifting x__1 -> f__1 x__1
    | Analyzing { continuation = x__1; is_exn_handler = x__2; uses = x__3 } ->
      f__2 x__1 x__2 x__3
    | Lifting_out_of { continuation = x__1 } -> f__3 x__1)
    (fun reason0 ->
      Format.fprintf ppf "@[<hov>(Not_lifting@ %a)@]" print_reason reason0)
    (fun continuation is_exn_handler uses ->
      Format.fprintf ppf
        "@[<hov>(analysing@ @[<hov 1>(continuation@ %a)@]@ @[<hov \
         1>(is_exn_handler@ %b)@]@ @[<hov 1>(uses@ %a)@])@]"
        Continuation.print continuation is_exn_handler Continuation_uses.print
        uses)
    (fun continuation ->
      Format.fprintf ppf
        "@[<hov>(lifting_out_of@ @[<hov 1>(continuation@ %a)@])@]"
        Continuation.print continuation)
    t0
