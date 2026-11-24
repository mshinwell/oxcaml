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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Simplify_coercion.v, which follows
   middle_end/flambda2/simplify/simplify_coercion.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad

(** val simplify_coercion : Downwards_acc.t -> Coercion.t -> Coercion.t coq_M **)

let simplify_coercion dacc coercion =
  (fun f__1 f__2 x__0 ->
    match (x__0 : Int_ids.Coercion.t) with
    | Int_ids.Coercion.Id -> f__1 ()
    | Int_ids.Coercion.Change_depth { from = x__1; to_ = x__2 } ->
      f__2 x__1 x__2)
    (fun _ -> coercion)
    (fun from to_ ->
      let from' = Simplify_rec_info_expr.simplify_rec_info_expr dacc from in
      let to_' = Simplify_rec_info_expr.simplify_rec_info_expr dacc to_ in
      if from' == from && to_' == to_
      then coercion
      else Coercion.change_depth from' to_')
    coercion
