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

(* This file follows middle_end/flambda2/simplify/simplified_named.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the arguments by place) is that of
   GUIDE.md; the Rocq form of the type [binding_to_place] is that of
   decl/Simplified_named.v. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Bound_pattern Code_id Code_size
  Cost_metrics Debuginfo Flambda Flambda_primitive Format Name_occurrences
  Rec_info_expr Simple Target_system.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
(*OCAML
open! Flambda.Import
OCAML*)
Import Flambda.Import_.

(* 19-23 *)
Inductive simplified_named : Type :=
| Simple : Simple.t -> simplified_named
| Prim : Flambda_primitive.t -> Debuginfo.t -> simplified_named
| Set_of_closures :
    Set_of_closures.t -> Alloc_mode.For_allocations.t -> simplified_named
| Rec_info : Rec_info_expr.t -> simplified_named.

(* 25-30 *)
Definition to_named (simplified_named : Simplified_named.simplified_named)
    : M Named.t :=
  match simplified_named with
  | Simple simple => Named.create_simple simple
  | Prim prim dbg => Named.create_prim prim dbg
  | Set_of_closures set alloc_mode =>
    (* 29: [Named.create_set_of_closures ~alloc_mode set] *)
    Named.create_set_of_closures alloc_mode set
  | Rec_info rec_info_expr => Named.create_rec_info rec_info_expr
  end.

(* 32-36 *)
Record t : Type :=
  { named : simplified_named;
    cost_metrics : Cost_metrics.t;
    free_names : Name_occurrences.t
  }.

(* 38-61 *)
Definition create (machine_width : Target_system.Machine_width.t)
    (named : Named.t) : M t :=
  let* '(simplified_named, cost_metrics) :=
    match named with
    | Flambda.Simple simple =>
      let! tmp1 := Code_size.simple simple in
      let! tmp2 := Cost_metrics.from_size tmp1 in
      ret (Simple simple, tmp2)
    | Flambda.Prim prim dbg =>
      let! tmp1 := Code_size.prim machine_width prim in
      let! tmp2 := Cost_metrics.from_size tmp1 in
      ret (Prim prim dbg, tmp2)
    | Flambda.Set_of_closures _ _ =>
      fatal_errorf2
        "Cannot use [Simplified_named.create] on [Set_of_closures];@ use [create_with_known_free_names] instead:@ %a"
        Named.print named
    | Flambda.Static_consts _ =>
      fatal_errorf2
        "Cannot create [Simplified_named] from [Static_consts];@ use the lifted constant infrastructure instead:@ %a"
        Named.print named
    | Flambda.Rec_info rec_info_expr =>
      ret (Rec_info rec_info_expr, Cost_metrics.zero)
    end
  in
  let! tmp1 := Named.free_names named in
  ret
    {| Simplified_named.named := simplified_named;
       Simplified_named.cost_metrics := cost_metrics;
       free_names := tmp1
    |}.

(* 63-82. In the compiler: [~machine_width ~find_code_characteristics (named
   : Named.t) ~free_names]. *)
Definition create_with_known_free_names
    (machine_width : Target_system.Machine_width.t)
    (find_code_characteristics :
      Code_id.t -> M Cost_metrics.code_characteristics)
    (named : Named.t) (free_names : Name_occurrences.t) : M t :=
  let* '(simplified_named, cost_metrics) :=
    match named with
    | Flambda.Simple simple =>
      let! tmp1 := Code_size.simple simple in
      let! tmp2 := Cost_metrics.from_size tmp1 in
      ret (Simple simple, tmp2)
    | Flambda.Prim prim dbg =>
      let! tmp1 := Code_size.prim machine_width prim in
      let! tmp2 := Cost_metrics.from_size tmp1 in
      ret (Prim prim dbg, tmp2)
    | Flambda.Set_of_closures set alloc_mode =>
      let! tmp1 := Cost_metrics.set_of_closures find_code_characteristics set in
      ret (Set_of_closures set alloc_mode, tmp1)
    | Flambda.Static_consts _ =>
      fatal_errorf2
        "Cannot create [Simplified_named] from [Static_consts];@ use the lifted constant infrastructure instead:@ %a"
        Named.print named
    | Flambda.Rec_info rec_info_expr =>
      ret (Rec_info rec_info_expr, Cost_metrics.zero)
    end
  in
  ret
    {| Simplified_named.named := simplified_named;
       Simplified_named.cost_metrics := cost_metrics;
       Simplified_named.free_names := free_names
    |}.

(* 84 *)
Definition print (ppf : Format.formatter)
    '({| named := named |} : t) : M unit :=
  let! tmp1 := to_named named in
  Named.print ppf tmp1.

(* 86 *)
(* PORT-GAP(loose): 86, [let cost_metrics { cost_metrics; _ } =
   cost_metrics] is the projection [cost_metrics] of the record [t] above
   (Rocq has one name space for fields and functions): Rocq extracts it as
   [let cost_metrics t = t.cost_metrics], after the type and not here, and
   its Rocq type is not in the monad. *)

(* 88 *)
Definition update_cost_metrics (cost_metrics : Cost_metrics.t)
    (t : Simplified_named.t) : M Simplified_named.t :=
  ret
    {| named := t.(named);
       Simplified_named.cost_metrics := cost_metrics;
       free_names := t.(free_names)
    |}.

(* 90-92 *)
Inductive or_rewritten (A : Type) : Type :=
| Simplified : A -> or_rewritten A
| Rewritten : (Flambda.Expr.t -> M Flambda.Expr.t) -> or_rewritten A.
Arguments Simplified {A}.
Arguments Rewritten {A}.

(* 94-100 *)
(* PORT-GAP(type): the type has inline records: the OCaml definition is the
   compiler's text, at the end of the extracted file (as in the compiler);
   in Rocq, the form of decl/Simplified_named.v (the fields by place). *)
(*OCAML-END
type binding_to_place =
  | Keep_binding of
      { let_bound : Bound_pattern.t;
        simplified_defining_expr : t;
        original_defining_expr : Named.t option
      }
  | Delete_binding of { original_defining_expr : Named.t option }
OCAML-END*)
Inductive binding_to_place : Type :=
| Keep_binding : Bound_pattern.t -> t -> option Named.t -> binding_to_place
| Delete_binding : option Named.t -> binding_to_place.
Extract Inductive binding_to_place => "binding_to_place"
  [ "(fun (x__1, x__2, x__3) -> (Keep_binding { let_bound = x__1; simplified_defining_expr = x__2; original_defining_expr = x__3 } : binding_to_place))"
    "(fun x__1 -> (Delete_binding { original_defining_expr = x__1 } : binding_to_place))" ]
  "(fun f__1 f__2 x__0 -> match (x__0 : binding_to_place) with Keep_binding { let_bound = x__1; simplified_defining_expr = x__2; original_defining_expr = x__3 } -> f__1 x__1 x__2 x__3 | Delete_binding { original_defining_expr = x__1 } -> f__2 x__1)".
