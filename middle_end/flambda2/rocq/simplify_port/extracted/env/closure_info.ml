(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*   Copyright 2021--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/env/Closure_info.v, which follows
   middle_end/flambda2/simplify/env/closure_info.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

type t =
  | Not_in_a_closure
  | In_a_set_of_closures_but_not_yet_in_a_specific_closure
  | Closure of
      { code_id : Code_id.t;
        return_continuation : Continuation.t;
        exn_continuation : Continuation.t;
        my_closure : Variable.t;
        my_alloc_region : Variable.t
      }

type in_or_out_of_closure =
  | In_a_closure
  | Not_in_a_closure

open Port_monad

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  (fun f__1 f__2 f__3 x__0 ->
    match (x__0 : t) with
    | Not_in_a_closure -> f__1 ()
    | In_a_set_of_closures_but_not_yet_in_a_specific_closure -> f__2 ()
    | Closure
        { code_id = x__1;
          return_continuation = x__2;
          exn_continuation = x__3;
          my_closure = x__4;
          my_alloc_region = x__5
        } ->
      f__3 x__1 x__2 x__3 x__4 x__5)
    (fun _ -> Format.fprintf ppf "not_in_a_closure")
    (fun _ -> Format.fprintf ppf "in_a_set_of_closures")
    (fun code_id return_continuation exn_continuation my_closure my_alloc_region
       ->
      Format.fprintf ppf
        "@[<hov 1>(@[<hov 1>(code_id@ %a)@]@ @[<hov 1>(return_continuation@ \
         %a)@]@ @[<hov 1>(exn_continuation@ %a)@]@ @[<hov 1>(my_closure@ \
         %a)@]@ @[<hov 1>(my_alloc_region@ %a)@])@]"
        Code_id.print code_id Continuation.print return_continuation
        Continuation.print exn_continuation Variable.print my_closure
        Variable.print my_alloc_region)
    t0

(** val not_in_a_closure : t **)

let not_in_a_closure = (Not_in_a_closure : t)

(** val in_a_set_of_closures : t **)

let in_a_set_of_closures =
  In_a_set_of_closures_but_not_yet_in_a_specific_closure

(** val in_a_closure : Code_id.t -> Continuation.t -> Continuation.t ->
    Variable.t -> Variable.t -> t coq_M **)

let in_a_closure code_id return_continuation exn_continuation my_closure
    my_alloc_region =
  (fun (x__1, x__2, x__3, x__4, x__5) ->
    (Closure
       { code_id = x__1;
         return_continuation = x__2;
         exn_continuation = x__3;
         my_closure = x__4;
         my_alloc_region = x__5
       }
      : t))
    (code_id, return_continuation, exn_continuation, my_closure, my_alloc_region)

(** val in_or_out_of_closure : t -> in_or_out_of_closure coq_M **)

let in_or_out_of_closure t0 =
  (fun f__1 f__2 f__3 x__0 ->
    match (x__0 : t) with
    | Not_in_a_closure -> f__1 ()
    | In_a_set_of_closures_but_not_yet_in_a_specific_closure -> f__2 ()
    | Closure
        { code_id = x__1;
          return_continuation = x__2;
          exn_continuation = x__3;
          my_closure = x__4;
          my_alloc_region = x__5
        } ->
      f__3 x__1 x__2 x__3 x__4 x__5)
    (fun _ -> (Not_in_a_closure : in_or_out_of_closure))
    (fun _ ->
      Misc.fatal_errorf
        "Expected to be either inside or outside a closure, but not \
         [In_a_set_of_closures_but_not_yet_in_a_specific_closure]")
    (fun _ _ _ _ _ -> In_a_closure)
    t0
