(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/flow/flow.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9: its two modules under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flow_acc Flow_analysis.

(* 15 *)
Module Acc := Flow_acc.

(* 16 *)
Module Analysis := Flow_analysis.
