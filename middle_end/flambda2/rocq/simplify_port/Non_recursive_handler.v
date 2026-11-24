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

(* This file follows middle_end/flambda2/simplify/non_recursive_handler.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the arguments
   by place) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Continuation Flambda Format
  Lifted_cont_params Renaming.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16-24 *)
Record t : Type :=
  { cont : Continuation.t;
    params : Bound_parameters.t;
    lifted_params : Lifted_cont_params.t;
    handler : Flambda.Expr.t;
    is_exn_handler : bool;
    can_be_lifted : bool;
    is_cold : bool
  }.

(* 26-35 *)
Definition create (cont : Continuation.t) (params : Bound_parameters.t)
    (lifted_params : Lifted_cont_params.t) (handler : Flambda.Expr.t)
    (is_exn_handler can_be_lifted is_cold : bool) : M t :=
  ret
    {| cont := cont;
       params := params;
       lifted_params := lifted_params;
       handler := handler;
       is_exn_handler := is_exn_handler;
       can_be_lifted := can_be_lifted;
       is_cold := is_cold
    |}.

(* 37 *)
Definition with_can_be_lifted (can_be_lifted : bool)
    (t : Non_recursive_handler.t) : M Non_recursive_handler.t :=
  ret
    {| cont := t.(cont);
       params := t.(params);
       lifted_params := t.(lifted_params);
       handler := t.(handler);
       is_exn_handler := t.(is_exn_handler);
       can_be_lifted := can_be_lifted;
       is_cold := t.(is_cold)
    |}.

(* 39-57 *)
(* PORT-GAP(loose): 39, the attribute [@ocamlformat "disable"] is not kept. *)
Definition print (ppf : Format.formatter)
    '({| cont := cont;
         params := params;
         lifted_params := lifted_params;
         handler := handler;
         is_exn_handler := is_exn_handler;
         can_be_lifted := can_be_lifted;
         is_cold := is_cold
      |} : t) : M unit :=
  Format.fprintf11 ppf
    "@[<hov 1>(@[<hv 1>(cont@ %a)@]@ @[<hv 1>(params@ %a)@]@ @[<hv 1>(lifted_params@ %a)@]@ @[<hv 1>(is_exn_handler@ %b)@]@ @[<hv 1>(can_be_lifted@ %b)@]@ @[<hv 1>(is_cold@ %b)@]@ @[<hv 1>(handler@ %a)@]@ )@]"
    Continuation.print cont Bound_parameters.print params
    Lifted_cont_params.print lifted_params is_exn_handler can_be_lifted
    is_cold Flambda.Expr.print handler.

(* 59 *)
Definition with_handler (handler : Flambda.Expr.t)
    (t : Non_recursive_handler.t) : M Non_recursive_handler.t :=
  ret
    {| cont := t.(cont);
       params := t.(params);
       lifted_params := t.(lifted_params);
       handler := handler;
       is_exn_handler := t.(is_exn_handler);
       can_be_lifted := t.(can_be_lifted);
       is_cold := t.(is_cold)
    |}.

(* 61-75 *)
Definition rename_params (t : Non_recursive_handler.t)
    : M Non_recursive_handler.t :=
  let* params := Bound_parameters.rename t.(Non_recursive_handler.params) in
  (* 63-65: [Bound_parameters.renaming t.params ~guaranteed_fresh:params] *)
  let* params_renaming :=
    Bound_parameters.renaming t.(Non_recursive_handler.params) params
  in
  let* '(lifted_params, lifted_params_renaming) :=
    Lifted_cont_params.rename t.(Non_recursive_handler.lifted_params)
  in
  (* 71-73: [Renaming.compose ~first:params_renaming
     ~second:lifted_params_renaming]: the arguments are in the order of the
     interface, [second] then [first]. *)
  let* renaming :=
    Renaming.compose lifted_params_renaming params_renaming
  in
  let* handler :=
    Flambda.Expr.apply_renaming t.(Non_recursive_handler.handler) renaming
  in
  ret
    {| cont := t.(cont);
       params := params;
       lifted_params := lifted_params;
       handler := handler;
       is_exn_handler := t.(is_exn_handler);
       can_be_lifted := t.(can_be_lifted);
       is_cold := t.(is_cold)
    |}.
