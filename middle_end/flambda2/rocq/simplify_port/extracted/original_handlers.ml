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
   middle_end/flambda2/rocq/simplify_port/Original_handlers.v, which follows
   middle_end/flambda2/simplify/original_handlers.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

type t =
  | Recursive of
      { invariant_params : Bound_parameters.t;
        lifted_params : Lifted_cont_params.t;
        continuation_handlers : One_recursive_handler.t Continuation.Lmap.t;
        can_be_lifted : bool
      }
  | Non_recursive of Non_recursive_handler.t

open Port_monad

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | Recursive
        { invariant_params = x__1;
          lifted_params = x__2;
          continuation_handlers = x__3;
          can_be_lifted = x__4
        } ->
      f__1 x__1 x__2 x__3 x__4
    | Non_recursive x__1 -> f__2 x__1)
    (fun invariant_params lifted_params0 continuation_handlers can_be_lifted0 ->
      Format.fprintf ppf
        "@[<hov 1>(\n\
        \        @[<hv 1>(can_be_lifted@ %b)@]@ @[<hv 1>(invariant params@ \
         %a)@]@ @[<hv 1>(lifted_params@ %a)@]@ @[<hv 1>(continuation handlers@ \
         %a)@])@]"
        can_be_lifted0 Bound_parameters.print invariant_params
        Lifted_cont_params.print lifted_params0
        (Continuation.Lmap.print One_recursive_handler.print)
        continuation_handlers)
    (fun non_rec_handler -> Non_recursive_handler.print ppf non_rec_handler)
    t0

(** val create_recursive : Bound_parameters.t -> Lifted_cont_params.t ->
    One_recursive_handler.t Continuation.Lmap.t -> bool -> t coq_M **)

let create_recursive invariant_params lifted_params0 continuation_handlers
    can_be_lifted0 =
  (fun (x__1, x__2, x__3, x__4) ->
    Recursive
      { invariant_params = x__1;
        lifted_params = x__2;
        continuation_handlers = x__3;
        can_be_lifted = x__4
      })
    (invariant_params, lifted_params0, continuation_handlers, can_be_lifted0)

(** val create_non_recursive : Non_recursive_handler.t -> t coq_M **)

let create_non_recursive non_rec_handler = Non_recursive non_rec_handler

(** val bound_continuations : t -> Continuation.t list coq_M **)

let bound_continuations t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | Recursive
        { invariant_params = x__1;
          lifted_params = x__2;
          continuation_handlers = x__3;
          can_be_lifted = x__4
        } ->
      f__1 x__1 x__2 x__3 x__4
    | Non_recursive x__1 -> f__2 x__1)
    (fun _ _ continuation_handlers _ ->
      Continuation.Lmap.keys continuation_handlers)
    (fun non_rec_handler -> non_rec_handler.Non_recursive_handler.cont :: [])
    t0

(** val can_be_lifted : t -> bool coq_M **)

let can_be_lifted t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | Recursive
        { invariant_params = x__1;
          lifted_params = x__2;
          continuation_handlers = x__3;
          can_be_lifted = x__4
        } ->
      f__1 x__1 x__2 x__3 x__4
    | Non_recursive x__1 -> f__2 x__1)
    (fun _ _ _ can_be_lifted0 -> can_be_lifted0)
    (fun t1 -> t1.Non_recursive_handler.can_be_lifted)
    t0

(** val add_params_to_lift : t -> Lifted_cont_params.t -> t coq_M **)

let add_params_to_lift t0 params_to_lift =
  let lifted_params0, renaming = Lifted_cont_params.rename params_to_lift in
  let fail =
   fun _ ->
    Misc.fatal_errorf
      "Cannot add lifted params to a continuation that already has lifted \
       params:@ params_to_lift=%a@ t=%a"
      Lifted_cont_params.print params_to_lift print t0
  in
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | Recursive
        { invariant_params = x__1;
          lifted_params = x__2;
          continuation_handlers = x__3;
          can_be_lifted = x__4
        } ->
      f__1 x__1 x__2 x__3 x__4
    | Non_recursive x__1 -> f__2 x__1)
    (fun invariant_params old_lifted continuation_handlers can_be_lifted0 ->
      if Lifted_cont_params.is_empty old_lifted
      then
        let continuation_handlers0 =
          Continuation.Lmap.map
            (fun pat ->
              let { One_recursive_handler.params = params0;
                    One_recursive_handler.handler = handler0;
                    One_recursive_handler.is_cold = is_cold0
                  } =
                pat
              in
              let handler1 = Flambda.Expr.apply_renaming handler0 renaming in
              One_recursive_handler.create params0 handler1 is_cold0)
            continuation_handlers
        in
        (fun (x__1, x__2, x__3, x__4) ->
          Recursive
            { invariant_params = x__1;
              lifted_params = x__2;
              continuation_handlers = x__3;
              can_be_lifted = x__4
            })
          ( invariant_params,
            lifted_params0,
            continuation_handlers0,
            can_be_lifted0 )
      else fail ())
    (fun t1 ->
      let { Non_recursive_handler.cont = cont0;
            Non_recursive_handler.params = params0;
            Non_recursive_handler.lifted_params = old_lifted;
            Non_recursive_handler.handler = handler0;
            Non_recursive_handler.is_exn_handler = is_exn_handler0;
            Non_recursive_handler.can_be_lifted = can_be_lifted0;
            Non_recursive_handler.is_cold = is_cold0
          } =
        t1
      in
      if Lifted_cont_params.is_empty old_lifted
      then
        let handler1 = Flambda.Expr.apply_renaming handler0 renaming in
        let non_rec =
          Non_recursive_handler.create cont0 params0 lifted_params0 handler1
            is_exn_handler0 can_be_lifted0 is_cold0
        in
        Non_recursive non_rec
      else fail ())
    t0
