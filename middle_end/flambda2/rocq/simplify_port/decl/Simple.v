(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simple], after its interface
   middle_end/flambda2/term_basics/simple.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Int_ids.

(* int_ids.mli:200  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Simple.t.
Extract Inlined Constant t => "Simple.t".
(* module T = Int_ids.Simple.T: declared again here under this name. *)
Module T.
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Simple.T.t.
  Extract Inlined Constant t => "Simple.T.t".
End T.
(* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
Parameter equal : Simple.T.t -> Simple.T.t -> M bool.
Extract Inlined Constant equal => "Simple.equal".
(* int_ids.mli:208  val var : Variable.t -> t *)
Parameter var : Int_ids.Variable_.t -> M t.
Extract Inlined Constant var => "Simple.var".
Module List.
  (* simple.mli:98  type nonrec t = t list *)
  Definition t : Type := list Simple.t.
  Extract Inlined Constant t => "Simple.List.t".
  Module T.
    (* simple.mli:102  include Container_types.S with type t := t *)
    Definition t : Type := Simple.List.t.
    Extract Inlined Constant t => "Simple.List.T.t".
  End T.
  (* simple.mli:102  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> Simple.List.T.t -> M unit.
  Extract Inlined Constant print => "Simple.List.print".
End List.
Module With_debuginfo.
  (* simple.mli:114  type nonrec t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Simple.With_debuginfo.t".
End With_debuginfo.
