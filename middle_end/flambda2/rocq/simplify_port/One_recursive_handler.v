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

(* This file follows middle_end/flambda2/simplify/one_recursive_handler.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the arguments
   by place) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Flambda Format.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16-20 *)
Record t : Type :=
  { params : Bound_parameters.t;
    handler : Flambda.Expr.t;
    is_cold : bool
  }.

(* 22 *)
Definition create (params : Bound_parameters.t) (handler : Flambda.Expr.t)
    (is_cold : bool) : M t :=
  ret {| params := params; handler := handler; is_cold := is_cold |}.

(* 24-28 *)
Definition print (ppf : Format.formatter)
    '({| params := params; handler := handler; is_cold := is_cold |} : t)
    : M unit :=
  Format.fprintf5 ppf
    "@[<hov 1>(@[<hv 1>(params@ %a)@]@ @[<hv 1>(is_cold@ %b)@]@ @[<hv 1>(handler@ %a)@])@]"
    Bound_parameters.print params is_cold Flambda.Expr.print handler.

(* 30. [{ t with handler }]. *)
Definition update_handler (t : One_recursive_handler.t)
    (handler : Flambda.Expr.t) : One_recursive_handler.t :=
  {| params := t.(params); handler := handler; is_cold := t.(is_cold) |}.
Extract Inlined Constant update_handler =>
  "(fun t handler -> { t with handler = handler })".

(* 30 *)
Definition with_handler (handler : Flambda.Expr.t)
    (t : One_recursive_handler.t) : M One_recursive_handler.t :=
  ret (update_handler t handler).
