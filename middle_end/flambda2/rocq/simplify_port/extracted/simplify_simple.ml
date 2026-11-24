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
   middle_end/flambda2/rocq/simplify_port/Simplify_simple.v, which follows
   middle_end/flambda2/simplify/simplify_simple.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

exception Simple_not_in_scope

open Port_monad
module DA = Downwards_acc
module T = Flambda2_types
module TE = T.Typing_env

(** val simplify_simple0 : DA.t -> Simple.t -> Name_mode.t -> (T.t * Simple.t)
    coq_M **)

let simplify_simple0 dacc simple min_name_mode =
  let typing_env = DA.typing_env dacc in
  Port_monad.match_exn
    (fun _ ->
      (fun x__1 x__2 x__3 ->
        TE.type_simple_in_term_exn x__1 ?min_name_mode:x__2 x__3)
        typing_env (Some min_name_mode) simple)
    Port_monad.not_found
    (fun _ ->
      Port_monad.raise_
        ( (fun () -> Simple_not_in_scope),
          function Simple_not_in_scope -> Some () | _ -> None )
        ())
    (fun res ->
      let ty, simple0 = res in
      let coercion = Simple.coercion simple0 in
      if Coercion.is_id coercion
      then res
      else
        let coercion0 = Simplify_coercion.simplify_coercion dacc coercion in
        let simple1 =
          Simple.with_coercion (Simple.without_coercion simple0) coercion0
        in
        T.alias_type_of (T.kind ty) simple1, simple1)

(** val simplify_simple : DA.t -> Simple.t -> Name_mode.t -> (T.t * Simple.t)
    coq_M **)

let simplify_simple dacc simple min_name_mode =
  Port_monad.match_exn
    (fun _ -> simplify_simple0 dacc simple min_name_mode)
    ( (fun () -> Simple_not_in_scope),
      function Simple_not_in_scope -> Some () | _ -> None )
    (fun _ ->
      Misc.fatal_errorf
        "No canonical [Simple] for %a exists at the@ requested name mode (%a) \
         or one greater.@ Downwards accumulator:@ %a"
        Simple.print simple Name_mode.print min_name_mode DA.print dacc)
    (fun res -> res)

(** val simplify_simple_if_in_scope : DA.t -> Simple.t -> Name_mode.t -> T.t
    option coq_M **)

let simplify_simple_if_in_scope dacc simple min_name_mode =
  Port_monad.match_exn
    (fun _ -> simplify_simple0 dacc simple min_name_mode)
    ( (fun () -> Simple_not_in_scope),
      function Simple_not_in_scope -> Some () | _ -> None )
    (fun _ -> None)
    (fun pat ->
      let ty, _ = pat in
      Some ty)

type simplify_simples_result =
  { simples : Simple.t list;
    simple_tys : Flambda2_types.t list
  }

(** val simples : simplify_simples_result -> Simple.t list **)

let simples s = s.simples

(** val simple_tys : simplify_simples_result -> Flambda2_types.t list **)

let simple_tys s = s.simple_tys

(** val simplify_simples : DA.t -> Simple.t list -> simplify_simples_result
    coq_M **)

let simplify_simples dacc simples0 =
  List.fold_right
    (fun simple pat ->
      let { simples = simples1; simple_tys = simple_tys0 } = pat in
      let ty, simple0 = simplify_simple dacc simple Name_mode.normal in
      { simples = simple0 :: simples1; simple_tys = ty :: simple_tys0 })
    simples0
    { simples = []; simple_tys = [] }
