(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Nathanaëlle Courant, Guillaume Bury and Pierre Chambart, OCamlPro    *)
(*                                                                        *)
(*   Copyright 2022--2022 OCamlPro SAS                                    *)
(*   Copyright 2022--2022 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/named_rewrite.ml
   (Git blob 5dac36893ac6986009d7dbc1e2c0d331a5b46850), function by function
   under the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the arguments by
   place) is that of GUIDE.md; the Rocq form of the type [Prim_rewrite.t] is
   that of decl/Named_rewrite.v. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_kind Format Simple Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16-18: Rewriting of primitives. Currently this is only used by the mutable
   unboxing (aka ref-to-var) analysis, and these rewrite are applied when
   going upwards and rebuilding expressions. *)
(* 19-40 *)
Module Prim_rewrite.
  (* 20-26 *)
  (* The type has an inline record. In Rocq it is the inductive type [t_], in
     the form of decl/Named_rewrite.v (the fields by place); the OCaml
     definition is the compiler's text, which the directive of [t] puts at
     this place of the extracted module (a verbatim block cannot stand inside
     a module). *)
  Inductive t_ : Type :=
  | Remove_prim : t_
  | Invalid : Flambda_kind.t -> t_
  | Replace_by_binding : Variable_.t -> Simple.t -> t_.
  Extract Inductive t_ => "t"
    [ "Remove_prim" "Invalid"
      "(fun (x__1, x__2) -> Replace_by_binding { var = x__1; bound_to = x__2 })" ]
    "(fun f__1 f__2 f__3 x__0 -> match x__0 with Remove_prim -> f__1 () | Invalid x__1 -> f__2 x__1 | Replace_by_binding { var = x__1; bound_to = x__2 } -> f__3 x__1 x__2)".
  Definition t : Type := t_.
  Extract Constant t =>
    "| Remove_prim | Invalid of Flambda_kind.t | Replace_by_binding of { var : Variable.t; bound_to : Simple.t }".

  (* 28-33 *)
  Definition print (ppf : Format.formatter) (t : Prim_rewrite.t) : M unit :=
    match t with
    | Invalid _ => Format.fprintf0 ppf "Invalid"
    | Remove_prim => Format.fprintf0 ppf "Remove_prim"
    | Replace_by_binding var bound_to =>
      Format.fprintf4 ppf "Replace_by_binding { %a = %a }" Variable_.print var
        Simple.print bound_to
    end.

  (* 35 *)
  Definition invalid (k : Flambda_kind.t) : M t := ret (Invalid k).

  (* 37 *)
  Definition remove_prim : t := Remove_prim.

  (* 39 *)
  Definition replace_by_binding (var : Variable_.t) (bound_to : Simple.t)
      : M t :=
    ret (Replace_by_binding var bound_to).
End Prim_rewrite.

(* 42: We currently only rewrite primitives *)
(* 43 *)
Inductive t : Type := Prim_rewrite : Prim_rewrite.t -> t.

(* 45-46 *)
Definition print (ppf : Format.formatter) (t : Named_rewrite.t) : M unit :=
  match t with
  | Prim_rewrite prim_rewrite => Prim_rewrite.print ppf prim_rewrite
  end.

(* 48 *)
Definition prim_rewrite (prim_rewrite : Prim_rewrite.t) : M t :=
  ret (Prim_rewrite prim_rewrite).
