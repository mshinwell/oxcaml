(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2021 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplify_named_result.ml
   (Git blob 511432091b7d0b8e49c9f56158a41efe53eda49b), function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. The donor opens
   [Flambda.Import] and not [Simplify_import]: so does this file. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_pattern Bound_var Downwards_acc
  Downwards_env Flambda List Simple Simplified_named Symbol.
Import Flambda.Import_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15 *)
(*OCAML
open! Flambda.Import
OCAML*)

(* 17-21 *)
(* PORT-GAP(loose): 56, 61, 63: Rocq has one name space, and the compiler's
   three functions [dacc], [bindings_to_place] and
   [was_lifted_set_of_closures] have the names of the fields. They are the
   projections of this record: Rocq prints each as [let dacc t = t.dacc],
   which is the compiler's text, but here, after the type, and not at the
   compiler's lines; and in Rocq their results are not in [M]. *)
Record t : Type := {
  dacc : Downwards_acc.t;
  bindings_to_place : list Simplified_named.binding_to_place;
  was_lifted_set_of_closures : bool
}.

(* 23. [{ t with dacc }]. *)
Definition update_dacc (t : Simplify_named_result.t) (dacc : Downwards_acc.t)
    : Simplify_named_result.t :=
  {| dacc := dacc;
     bindings_to_place := t.(bindings_to_place);
     was_lifted_set_of_closures := t.(was_lifted_set_of_closures)
  |}.
Extract Inlined Constant update_dacc =>
  "(fun t dacc -> { t with dacc = dacc })".

(* 23 *)
Definition with_dacc (dacc : Downwards_acc.t) (t : Simplify_named_result.t)
    : M Simplify_named_result.t :=
  ret (update_dacc t dacc).

(* 25-31 *)
Definition create (dacc : Downwards_acc.t)
    (binding_to_place : Simplified_named.binding_to_place) : M t :=
  (* If [original_defining_expr] was simplified to a new term then the benefit
     of doing so is counted in [simplify_named]. *)
  ret
    {| dacc := dacc;
       bindings_to_place := [binding_to_place];
       was_lifted_set_of_closures := false
    |}.

(* 33-34 *)
Definition create_empty (dacc : Downwards_acc.t) : M t :=
  ret
    {| dacc := dacc;
       bindings_to_place := [];
       was_lifted_set_of_closures := false
    |}.

(* 36-54 *)
Definition create_have_lifted_set_of_closures (dacc : Downwards_acc.t)
    (bound_vars_to_symbols : list (Bound_var.t * Symbol.t))
    (original_defining_expr : Named.t) : M t :=
  (* The benefit of lifting the set of closures is added in [Simplify_named]. *)
  let* machine_width :=
    let! tmp1 := Downwards_acc.denv dacc in
    Downwards_env.machine_width tmp1
  in
  (* 42-52: the fields of the record of [Keep_binding] by place. *)
  (* PORT-GAP(record-order): 45-48, the record of [Keep_binding] has calls in
     two fields, [let_bound] and [simplified_defining_expr]. OCaml leaves the
     order of the fields of a record unspecified; this is the order that the
     port chooses for a record: the fields in the order of the type, the
     last first ([simplified_defining_expr], then [let_bound]). Each of the
     two calls is bound by [let*], so that the extracted code has that
     order too.
     VERDICT (record_order/README.md, place 19): COMMUTE. For a symbol no call
     reads or writes a table, a counter or a flag, and none can fail. *)
  let! tmp3 :=
    List.mapi
      (fun (i : int) '(var, sym) =>
        let* simplified_defining_expr :=
          let! tmp1 := Simple.symbol sym in
          let! tmp2 := Named.create_simple tmp1 in
          Simplified_named.create machine_width tmp2
        in
        let* let_bound := Bound_pattern.singleton var in
        ret
          (Simplified_named.Keep_binding let_bound simplified_defining_expr
             (if i =? 0 then Some original_defining_expr else None)))
      bound_vars_to_symbols
  in
  ret
    {| dacc := dacc;
       bindings_to_place := tmp3;
       was_lifted_set_of_closures := true
    |}.

(* 58-59 *)
Definition no_bindings (t : Simplify_named_result.t) : M bool :=
  match t.(bindings_to_place) with [] => ret true | _ :: _ => ret false end.
