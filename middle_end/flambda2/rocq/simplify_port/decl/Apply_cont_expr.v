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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Apply_cont_expr], after its interface
   middle_end/flambda2/terms/apply_cont_expr.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Debuginfo Simple Trap_action.

(* apply_cont_expr.mli:20  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Apply_cont_expr.t".
(* apply_cont_expr.mli:26  val create : ?trap_action:Trap_action.t -> Continuation.t -> args:Simple.t list -> dbg:Debuginfo.t -> t *)
Parameter create : option Trap_action.t -> Continuation.t -> list Simple.t -> Debuginfo.t -> M t.
Extract Inlined Constant create => "(fun x__1 x__2 x__3 x__4 -> Apply_cont_expr.create ?trap_action:x__1 x__2 x__3 x__4)".
Module T.
  (* apply_cont_expr.mli:60  include Container_types.S with type t := t *)
  Definition t : Type := Apply_cont_expr.t.
  Extract Inlined Constant t => "Apply_cont_expr.T.t".
End T.
Module Set_.
  (* apply_cont_expr.mli:60  include Container_types.S with type t := t *)
  Definition elt : Type := Apply_cont_expr.t.
  Extract Inlined Constant elt => "Apply_cont_expr.Set.elt".
  (* apply_cont_expr.mli:60  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Apply_cont_expr.Set.t".
  (* apply_cont_expr.mli:60  include Container_types.S with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Apply_cont_expr.Set.empty".
  (* apply_cont_expr.mli:60  include Container_types.S with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Apply_cont_expr.Set.add".
  (* apply_cont_expr.mli:60  include Container_types.S with type t := t *)
  Parameter get_singleton : t -> M (option elt).
  Extract Inlined Constant get_singleton => "Apply_cont_expr.Set.get_singleton".
End Set_.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Apply_cont_expr. End Apply_cont_expr.
