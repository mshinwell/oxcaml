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

(* This file follows middle_end/flambda2/simplify/simplify_simple.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. The file does
   not import Simplify_import, which the compiler's file does not open: its
   three abbreviations of modules are its own. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Coercion Downwards_acc Flambda2_types List
  Name_mode Simple Simplify_coercion.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17-19 *)
From SimplifyPort.abbrev.simplify_simple Require Import Port_abbreviations.
(*OCAML
module DA = Downwards_acc
module T = Flambda2_types
module TE = T.Typing_env
OCAML*)

(* 21. The exception of the file. *)
(*OCAML
exception Simple_not_in_scope
OCAML*)
Parameter Simple_not_in_scope : exception unit.
Extract Inlined Constant Simple_not_in_scope =>
  "((fun () -> Simple_not_in_scope), (function Simple_not_in_scope -> Some () | _ -> None))".

(* 22-36 *)
Definition simplify_simple0 (dacc : DA.t) (simple : Simple.t)
    (min_name_mode : Name_mode.t) : M (T.t * Simple.t) :=
  let* typing_env := DA.typing_env dacc in
  (* 25: [TE.type_simple_in_term_exn typing_env simple ~min_name_mode]: the
     arguments are in the order of the interface. *)
  match_exn
    (fun _ =>
      TE.type_simple_in_term_exn typing_env (Some min_name_mode) simple)
    Not_found
    (fun _ => raise_ Simple_not_in_scope tt)
    (fun '((ty, simple) as res) =>
      let* coercion := Simple.coercion simple in
      let! tmp1 := Coercion.is_id coercion in
      if tmp1
      then ret res
      else
        let* coercion := Simplify_coercion.simplify_coercion dacc coercion in
        let* simple :=
          let! tmp1 := Simple.without_coercion simple in
          Simple.with_coercion tmp1 coercion
        in
        let! tmp1 := T.kind ty in
        let! tmp2 := T.alias_type_of tmp1 simple in
        ret (tmp2, simple)).

(* 38-45 *)
Definition simplify_simple (dacc : DA.t) (simple : Simple.t)
    (min_name_mode : Name_mode.t) : M (T.t * Simple.t) :=
  match_exn
    (fun _ => simplify_simple0 dacc simple min_name_mode)
    Simple_not_in_scope
    (fun _ =>
      fatal_errorf6
        "No canonical [Simple] for %a exists at the@ requested name mode (%a) or one greater.@ Downwards accumulator:@ %a"
        Simple.print simple Name_mode.print min_name_mode DA.print dacc)
    (fun res => ret res).

(* 47-50 *)
Definition simplify_simple_if_in_scope (dacc : DA.t) (simple : Simple.t)
    (min_name_mode : Name_mode.t) : M (option T.t) :=
  match_exn
    (fun _ => simplify_simple0 dacc simple min_name_mode)
    Simple_not_in_scope
    (fun _ => ret None)
    (fun '(ty, _simple) => ret (Some ty)).

(* 52-55 *)
Record simplify_simples_result : Type := {
  simples : list Simple.t;
  simple_tys : list Flambda2_types.t
}.

(* 57-65 *)
Definition simplify_simples (dacc : DA.t) (simples : list Simple.t)
    : M simplify_simples_result :=
  List.fold_right
    (fun simple '{| simples := simples; simple_tys := simple_tys |} =>
      let* '(ty, simple) := simplify_simple dacc simple Name_mode.normal in
      ret {| simples := simple :: simples; simple_tys := ty :: simple_tys |})
    simples
    {| simples := []; simple_tys := [] |}.
