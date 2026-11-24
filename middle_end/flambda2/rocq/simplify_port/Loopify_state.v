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

(* This file follows middle_end/flambda2/simplify/loopify_state.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition under
   the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad) is that of
   GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Format.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15-17 *)
Inductive t : Type :=
| Do_not_loopify : t
| Loopify : Continuation.t -> t.

(* 19-22 *)
Definition print (ppf : Format.formatter) (t : Loopify_state.t) : M unit :=
  match t with
  | Do_not_loopify => Format.fprintf0 ppf "do_not_loopify"
  | Loopify cont =>
    Format.fprintf2 ppf "@[<hov 1>(loopify@ %a)@]" Continuation.print cont
  end.

(* 24 *)
Definition do_not_loopify : t := Do_not_loopify.

(* 26 *)
Definition loopify (cont : Continuation.t) : M t := ret (Loopify cont).
