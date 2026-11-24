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

(* This file follows middle_end/flambda2/simplify/simplify_primitive_result.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. The compiler's
   file does not open [Simplify_import], and neither does this one. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var Downwards_acc Downwards_env Flambda
  Flambda2_types Flambda_kind Or_invalid Simplified_named Target_ocaml_int.
(* CONSTRUCTORS-WITHOUT-MODULE: Or_invalid.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* PORT-GAP(loose): 17, the attribute [@@@ocaml.warning "+a-30-40-41-42"] is
   not kept. *)

(* 19-23 *)
Record t_simplified : Type := {
  simplified_named : Or_invalid.t Simplified_named.t;
  try_reify : bool;
  dacc : Downwards_acc.t
}.

(* 25 *)
Definition t : Type := Simplified_named.or_rewritten t_simplified.

(* 27-33 *)
Definition create (named : Flambda.Named.t) (try_reify : bool)
    (dacc : Downwards_acc.t) : M t :=
  let* machine_width :=
    let! tmp1 := Downwards_acc.denv dacc in
    Downwards_env.machine_width tmp1
  in
  let! tmp1 := Simplified_named.create machine_width named in
  ret
    (Simplified_named.Simplified
       {| simplified_named := Or_invalid.Ok tmp1;
          try_reify := try_reify;
          dacc := dacc |}).

(* 35-36 *)
Definition create_simplified (simplified_named : Simplified_named.t)
    (try_reify : bool) (dacc : Downwards_acc.t) : M t :=
  ret
    (Simplified_named.Simplified
       {| simplified_named := Or_invalid.Ok simplified_named;
          try_reify := try_reify;
          dacc := dacc |}).

(* 38-39 *)
Definition create_invalid (dacc : Downwards_acc.t) : M t :=
  ret
    (Simplified_named.Simplified
       {| simplified_named := Or_invalid.Invalid;
          try_reify := false;
          dacc := dacc |}).

(* 41-50 *)
Definition create_unit (dacc : Downwards_acc.t) (result_var : Bound_var.t)
    (original_term : Flambda.Named.t) : M t :=
  let* machine_width :=
    let! tmp1 := Downwards_acc.denv dacc in
    Downwards_env.machine_width tmp1
  in
  let* ty :=
    let! tmp1 := Target_ocaml_int.zero machine_width in
    Flambda2_types.this_tagged_immediate tmp1
  in
  let* dacc := Downwards_acc.add_variable dacc result_var ty in
  create original_term false dacc.

(* 52-55 *)
Definition create_unknown (dacc : Downwards_acc.t) (result_var : Bound_var.t)
    (kind : Flambda_kind.t) (original_term : Flambda.Named.t) : M t :=
  let* ty := Flambda2_types.unknown kind in
  let* dacc := Downwards_acc.add_variable dacc result_var ty in
  create original_term false dacc.

(* 57 *)
Definition create_rewritten (f : Flambda.Expr.t -> M Flambda.Expr.t) : M t :=
  ret (Simplified_named.Rewritten f).

(* 59-62 *)
Definition is_invalid (t : Simplify_primitive_result.t) : M bool :=
  match t with
  | Simplified_named.Simplified
      {| simplified_named := Or_invalid.Invalid |} =>
    ret true
  | Simplified_named.Simplified {| simplified_named := Or_invalid.Ok _ |}
  | Simplified_named.Rewritten _ =>
    ret false
  end.

(* 64-67 *)
Definition map_dacc (t : Simplify_primitive_result.t)
    (f : Downwards_acc.t -> M Downwards_acc.t)
    : M Simplify_primitive_result.t :=
  match t with
  | Simplified_named.Simplified t =>
    (* 66: [{ t with dacc = f t.dacc }], all the fields. *)
    let! tmp1 := f t.(dacc) in
    ret
      (Simplified_named.Simplified
         {| simplified_named := t.(simplified_named);
            try_reify := t.(try_reify);
            dacc := tmp1 |})
  | Simplified_named.Rewritten _ => ret t
  end.
