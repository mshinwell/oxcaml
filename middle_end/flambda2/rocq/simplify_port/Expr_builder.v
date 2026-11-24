(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/expr_builder.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition under
   the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries
   [tmpN] and their order, the arguments by place, the fuel of the local
   recursive function, the types with inline records kept as OCaml text) is
   that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Apply_cont_rewrite
  Apply_cont_rewrite_id Apply_expr Are_rebuilding_terms ArrayLabels
  Bound_parameter Bound_parameters Bound_pattern Bound_static Bound_var Code
  Code_id Code_id_or_symbol Code_metadata Code_or_metadata Code_size Coercion
  Continuation Continuation_callsite_map Continuation_shortcut Cost_metrics
  Debuginfo Downwards_acc Downwards_env Exn_continuation Flambda
  Flambda_arity Flambda_debug_uid Flambda_features Flambda_kind
  Flambda_primitive Flow_types Lifted_constant Lifted_constant_state List
  ListLabels Mutability Name_mode Name_occurrences Or_invalid Or_null
  Or_unknown Rebuilt_expr Rebuilt_static_const Removed_operations Simple
  Simplified_named Slot_offsets Switch_arm Symbol_projection Target_ocaml_int
  Upwards_acc Upwards_env Value_slot Variable_.
Import Flambda.Import_.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17 *)
(*OCAML
open! Flambda.Import
OCAML*)

(* 18-26 *)
From SimplifyPort.abbrev.expr_builder Require Import Port_abbreviations.
(*OCAML
module BP = Bound_parameter
module LC = Lifted_constant
module LCS = Lifted_constant_state
module P = Flambda_primitive
module RE = Rebuilt_expr
module UA = Upwards_acc
module UE = Upwards_env
module DA = Downwards_acc
module VB = Bound_var
OCAML*)

(* 28-58 *)
Definition add_set_of_closures_offsets (is_phantom : bool) (named : Named.t)
    (uacc : UA.t) : M UA.t :=
  let& add_offsets_from_set :=
    fun (uacc : UA.t) (set_of_closures : Set_of_closures.t) =>
    let! tmp1 := UA.slot_offsets uacc in
    match tmp1 with
    | Or_unknown.Unknown => ret uacc
    | Or_unknown.Known slot_offsets =>
      let* slot_offsets :=
        Slot_offsets.add_set_of_closures slot_offsets is_phantom
          set_of_closures
      in
      UA.with_slot_offsets uacc (Or_unknown.Known slot_offsets)
    end
  in
  let& add_offsets_from_code :=
    fun (uacc : UA.t) (code : Code.t) =>
    (* XXX consider removing this Or_unknown.t *)
    let! tmp1 := UA.slot_offsets uacc in
    match tmp1 with
    | Or_unknown.Unknown => ret uacc
    | Or_unknown.Known slot_offsets =>
      let* dacc := UA.creation_dacc uacc in
      let* code_id := Code.code_id code in
      let* from_function :=
        try_with
          (fun _ =>
            let! tmp2 := DA.slot_offsets dacc in
            Code_id.Map.find code_id tmp2)
          Not_found
          (fun _ =>
            fatal_errorf2 "Missing offsets for code ID %a" Code_id.print
              code_id)
      in
      let* slot_offsets :=
        Slot_offsets.add_offsets_from_function slot_offsets from_function
      in
      UA.with_slot_offsets uacc (Or_unknown.Known slot_offsets)
    end
  in
  Named.fold_code_and_sets_of_closures named uacc add_offsets_from_code
    add_offsets_from_set.

(* 60-96 *)
Definition create_let (uacc : UA.t) (bound_vars : Bound_pattern.t)
    (defining_expr : Named.t) (free_names_of_defining_expr : Name_occurrences.t)
    (body : RE.t) (cost_metrics_of_defining_expr : Cost_metrics.t)
    : M (RE.t * UA.t) :=
  (* The name occurrences component of [uacc] is expected to be in the state
     described in the comment at the top of [Simplify_let.rebuild_let]. *)
  let* name_mode := Bound_pattern.name_mode bound_vars in
  let* is_phantom := Name_mode.is_phantom name_mode in
  let* free_names_of_body := UA.name_occurrences uacc in
  let* free_names_of_defining_expr :=
    if negb is_phantom
    then ret free_names_of_defining_expr
    else
      Name_occurrences.downgrade_occurrences_at_strictly_greater_name_mode
        free_names_of_defining_expr name_mode
  in
  let* free_names_of_let :=
    let* without_bound_vars :=
      Bound_pattern.fold_all_bound_vars bound_vars free_names_of_body
        (fun free_names bound_var =>
          let! tmp1 := VB.var bound_var in
          Name_occurrences.remove_var free_names tmp1)
    in
    Name_occurrences.union without_bound_vars free_names_of_defining_expr
  in
  let* uacc :=
    let! tmp1 :=
      Cost_metrics.increase_due_to_let_expr is_phantom
        cost_metrics_of_defining_expr
    in
    UA.add_cost_metrics_and_with_name_occurrences uacc tmp1 free_names_of_let
  in
  let* uacc :=
    let! tmp1 := UA.are_rebuilding_terms uacc in
    let! tmp2 := Are_rebuilding_terms.do_not_rebuild_terms tmp1 in
    if tmp2
    then ret uacc
    else add_set_of_closures_offsets is_phantom defining_expr uacc
  in
  let! tmp1 := UA.are_rebuilding_terms uacc in
  let! tmp2 :=
    RE.create_let tmp1 bound_vars defining_expr body free_names_of_body
  in
  ret (tmp2, uacc).

(* 98-104 *)
Definition create_let_binding (uacc : UA.t) (bound_vars : Bound_pattern.t)
    (defining_expr : Named.t) (free_names_of_defining_expr : Name_occurrences.t)
    (body : RE.t) (cost_metrics_of_defining_expr : Cost_metrics.t)
    : M (RE.t * UA.t) :=
  let* '(re, uacc) :=
    create_let uacc bound_vars defining_expr free_names_of_defining_expr body
      cost_metrics_of_defining_expr
  in
  ret (re, uacc).

(* 106-162 *)
Definition create_coerced_singleton_let (uacc : UA.t) (var : VB.t)
    (defining_expr : Named.t) (coercion_from_defining_expr_to_var : Coercion.t)
    (free_names_of_defining_expr : Name_occurrences.t) (body : RE.t)
    (cost_metrics_of_defining_expr : Cost_metrics.t) : M (RE.t * UA.t) :=
  let! tmp1 := Coercion.is_id coercion_from_defining_expr_to_var in
  if tmp1
  then
    let! tmp2 := Bound_pattern.singleton var in
    create_let uacc tmp2 defining_expr free_names_of_defining_expr body
      cost_metrics_of_defining_expr
  else
    match defining_expr with
    | Flambda.Simple simple =>
      (* 118-121: [a |> f] is [f a] *)
      let* defining_expr :=
        let! tmp1 :=
          Simple.apply_coercion_exn simple coercion_from_defining_expr_to_var
        in
        Named.create_simple tmp1
      in
      let! tmp1 := Bound_pattern.singleton var in
      create_let uacc tmp1 defining_expr free_names_of_defining_expr body
        cost_metrics_of_defining_expr
    | Flambda.Prim _ _
    | Flambda.Set_of_closures _ _
    | Flambda.Static_consts _
    | Flambda.Rec_info _ =>
      let* uncoerced_var :=
        let* name :=
          let! tmp1 := VB.var var in
          let! tmp2 := Variable_.canonical_name tmp1 in
          ret ("uncoerced_" ++ tmp2)%string
        in
        let! tmp1 := VB.var var in
        let! tmp2 := Variable_.kind tmp1 in
        Variable_.create None name tmp2
      in
      let& uncoerced_var_duid := Flambda_debug_uid.none in
      (* Generate [let var = uncoerced_var @ <coercion>] *)
      let* '(body, uacc) :=
        let* defining_simple :=
          let! tmp1 := Simple.var uncoerced_var in
          Simple.with_coercion tmp1 coercion_from_defining_expr_to_var
        in
        let* defining_expr := Named.create_simple defining_simple in
        let* free_names_of_defining_expr := Named.free_names defining_expr in
        let* cost_metrics_of_defining_expr :=
          let! tmp1 := Code_size.simple defining_simple in
          Cost_metrics.from_size tmp1
        in
        let! tmp1 := Bound_pattern.singleton var in
        create_let uacc tmp1 defining_expr free_names_of_defining_expr body
          cost_metrics_of_defining_expr
      in
      let& generate_outer_binding :=
        fun (name_mode : Name_mode.t) =>
        (* Generate [let uncoerced_var = <defining_expr>] *)
        (* PORT-GAP(loose): 152, [let ((_body, _uacc) as outer) = ... in
           outer]: the pair is not taken apart. *)
        let* outer :=
          let* bound :=
            let! tmp1 := VB.create uncoerced_var uncoerced_var_duid name_mode in
            Bound_pattern.singleton tmp1
          in
          create_let uacc bound defining_expr free_names_of_defining_expr body
            cost_metrics_of_defining_expr
        in
        ret outer
      in
      let! tmp1 := Bound_var.name_mode var in
      generate_outer_binding tmp1
    end.

(* 164-202. [ListLabels.fold_left l ~init ~f]: the arguments are in the
   order of the interface. *)
Definition make_new_let_bindings (uacc : UA.t)
    (bindings_outermost_first : list Simplified_named.binding_to_place)
    (body : RE.t) : M (RE.t * UA.t) :=
  (* The name occurrences component of [uacc] is expected to be in the state
     described in the comment at the top of [Simplify_let.rebuild_let]. *)
  let& notify_removed :=
    fun (uacc : UA.t) (original_defining_expr : option Named.t) =>
    match original_defining_expr with
    | Some (Flambda.Prim prim _dbg) =>
      let! tmp1 := Removed_operations.prim prim in
      UA.notify_removed tmp1 uacc
    | Some (Flambda.Set_of_closures _ _) =>
      UA.notify_removed Removed_operations.alloc uacc
    | Some (Flambda.Simple _ | Flambda.Static_consts _ | Flambda.Rec_info _)
    | None =>
      ret uacc
    end
  in
  let! tmp1 := List.rev bindings_outermost_first in
  ListLabels.fold_left
    (fun acc binding =>
      (* PORT-GAP(loose): 176, the pair pattern of the parameter is a
         [let]. *)
      let* '(expr, uacc) := ret acc in
      match binding with
      | Simplified_named.Delete_binding original_defining_expr =>
        let! tmp2 := notify_removed uacc original_defining_expr in
        ret (expr, tmp2)
      | Simplified_named.Keep_binding let_bound simplified_defining_expr _ =>
        let* '{| Simplified_named.named := defining_expr;
                 Simplified_named.cost_metrics := cost_metrics_of_defining_expr;
                 Simplified_named.free_names := free_names_of_defining_expr
              |} :=
          ret simplified_defining_expr
        in
        let* defining_expr := Simplified_named.to_named defining_expr in
        let* '(expr, uacc) :=
          match let_bound with
          | Bound_pattern.Singleton _ | Bound_pattern.Set_of_closures _ =>
            create_let uacc let_bound defining_expr
              free_names_of_defining_expr expr cost_metrics_of_defining_expr
          | Bound_pattern.Static _ =>
            (* Since [Simplified_named] doesn't permit the [Static_consts]
               case, this must be a malformed binding. *)
            fatal_errorf4
              "Mismatch between bound name(s) and defining expression:@ %a@ =@ %a"
              Bound_pattern.print let_bound Named.print defining_expr
          end
        in
        ret (expr, uacc)
      end)
    (body, uacc) tmp1.

(* 204-251 *)
Definition create_raw_let_symbol (uacc : UA.t) (bound_static : Bound_static.t)
    (static_consts : Rebuilt_static_const.Group.t) (body : RE.t)
    : M (RE.t * UA.t) :=
  (* Upon entry to this function, [UA.name_occurrences uacc] must precisely
     indicate the free names of [body]. *)
  let* bindable := Bound_pattern.static bound_static in
  let* free_names_of_static_consts :=
    Rebuilt_static_const.Group.free_names static_consts
  in
  let* free_names_of_body := UA.name_occurrences uacc in
  let* free_names_of_let :=
    (* Care: these bindings can be recursive (e.g. via a set of closures). *)
    let* name_occurrences :=
      Name_occurrences.union free_names_of_static_consts free_names_of_body
    in
    let! tmp1 := Bound_static.everything_being_defined bound_static in
    Code_id_or_symbol.Set_.fold
      (fun code_id_or_symbol free_names =>
        Name_occurrences.remove_code_id_or_symbol free_names code_id_or_symbol)
      tmp1 name_occurrences
  in
  let* cost_metrics_of_static_consts :=
    let! tmp1 :=
      Flambda_features.Inlining.speculative_inlining_track_lifted_constants tt
    in
    if tmp1
    then Rebuilt_static_const.Group.cost_metrics static_consts
    else
      (* Static consts used to always have zero cost metrics. That is now
         considered to be a bug, but it can have unexpected consequences on
         speculative inlining -- the flag above is used to control a
         progressive rollout of the fix and will be removed in due time. *)
      ret Cost_metrics.zero
  in
  (* 233-240: [a |> f b] is [f b a] *)
  let* uacc :=
    let! tmp1 := UA.with_name_occurrences uacc free_names_of_let in
    (* Static consts always have zero cost metrics at present. *)
    let! tmp2 :=
      Cost_metrics.increase_due_to_let_expr false cost_metrics_of_static_consts
    in
    UA.add_cost_metrics tmp2 tmp1
  in
  let! tmp1 := UA.are_rebuilding_terms uacc in
  let! tmp2 := Are_rebuilding_terms.do_not_rebuild_terms tmp1 in
  if tmp2
  then ret (RE.term_not_rebuilt, uacc)
  else
    let* defining_expr := Rebuilt_static_const.Group.to_named static_consts in
    let* uacc := add_set_of_closures_offsets false defining_expr uacc in
    let! tmp1 := UA.are_rebuilding_terms uacc in
    let! tmp2 :=
      RE.create_let tmp1 bindable defining_expr body free_names_of_body
    in
    ret (tmp2, uacc).

(* 253-290 *)
Definition create_let_symbol0 (uacc : UA.t) (bound_static : Bound_static.t)
    (static_consts : Rebuilt_static_const.Group.t) (body : RE.t)
    : M (RE.t * UA.t) :=
  (* Upon entry to this function, [UA.name_occurrences uacc] must precisely
     indicate the free names of [body]. *)
  let* will_bind_code := Bound_static.binds_code bound_static in
  (* Turn pieces of code that are only referenced in [newer_version_of]
     fields into [Deleted_code]. *)
  let* code_ids_to_make_deleted :=
    if negb will_bind_code
    then ret Code_id.Set_.empty
    else
      let* all_code_ids_bound_names :=
        Bound_static.code_being_defined bound_static
      in
      let! tmp1 := UA.reachable_code_ids uacc in
      match tmp1 with
      | Or_unknown.Unknown => ret Code_id.Set_.empty
      | Or_unknown.Known
          {| Flow_types.Reachable_code_ids.live_code_ids := live_code_ids;
             Flow_types.Reachable_code_ids.ancestors_of_live_code_ids := _
          |} =>
        Code_id.Set_.diff all_code_ids_bound_names live_code_ids
      end
  in
  let* static_consts :=
    let! tmp1 := Code_id.Set_.is_empty code_ids_to_make_deleted in
    if tmp1
    then ret static_consts
    else
      Rebuilt_static_const.Group.map static_consts
        (fun static_const =>
          Rebuilt_static_const.make_code_deleted static_const
            code_ids_to_make_deleted)
  in
  let* '(expr, uacc) :=
    create_raw_let_symbol uacc bound_static static_consts body
  in
  let* uacc :=
    if negb will_bind_code
    then ret uacc
    else
      (* 287-288: [a |> f b] is [f b a] *)
      let! tmp1 :=
        Rebuilt_static_const.Group.pieces_of_code_for_cmx static_consts
      in
      UA.remember_code_for_cmx uacc tmp1
  in
  ret (expr, uacc).

(* 292-313 *)
Definition remove_unused_value_slots (uacc : UA.t)
    (static_const : Rebuilt_static_const.t) : M Rebuilt_static_const.t :=
  let& find_code_metadata :=
    fun (code_id : Code_id.t) =>
    let* dacc := UA.creation_dacc uacc in
    let* env := DA.denv dacc in
    let! tmp1 :=
      try_with
        (fun _ => Downwards_env.find_code_exn env code_id)
        Not_found
        (fun _ =>
          fatal_errorf2 "Could not find code for %a" Code_id.print code_id)
    in
    Code_or_metadata.code_metadata tmp1
  in
  Rebuilt_static_const.map_set_of_closures static_const find_code_metadata
    (fun set_of_closures =>
      let* name_occurrences := UA.used_value_slots uacc in
      let* value_slots :=
        let! tmp1 := Set_of_closures.value_slots set_of_closures in
        Value_slot.Map.filter
          (fun value_slot _ =>
            Name_occurrences.value_slot_is_used_or_imported name_occurrences
              value_slot)
          tmp1
      in
      let! tmp1 := Set_of_closures.function_decls set_of_closures in
      let! tmp2 := Set_of_closures.debuginfo set_of_closures in
      Set_of_closures.create value_slots tmp2 tmp1).

(* 315-434. [Simple.pattern_match' simple ~const ~symbol ~var]: the
   arguments are in the order of the interface ([~var ~symbol ~const]). *)
Definition create_let_symbols (uacc : UA.t) (lifted_constant : LC.t)
    (body : RE.t) : M (RE.t * UA.t) :=
  let* bound_static := LC.bound_static lifted_constant in
  let* symbol_projections := LC.symbol_projections lifted_constant in
  let* static_consts :=
    let! tmp1 := LC.defining_exprs lifted_constant in
    Rebuilt_static_const.Group.map tmp1 (remove_unused_value_slots uacc)
  in
  let* '(expr, uacc) :=
    create_let_symbol0 uacc bound_static static_consts body
  in
  Variable_.Map.fold
    (fun var proj acc =>
      (* PORT-GAP(loose): 325, the pair pattern of the parameter is a
         [let]. *)
      let* '(expr, uacc) := ret acc in
      (* 326: a local [let rec] is Rocq's own [let] of a [fix]. *)
      let apply_projection :=
        fix apply_projection (fuel : Port_monad.fuel)
            (proj : Symbol_projection.t)
            (coercion_from_proj_to_var : Coercion.t) {struct fuel}
            : M (tuple3 Named.t Coercion.t Code_size.t) :=
          recursive! fuel in
          let! tmp1 := LC.apply_projection lifted_constant proj in
          match tmp1 with
          | Some simple =>
            let& stop_here :=
              fun (_ : unit) =>
              let& coercion_from_simple_to_var :=
                (* Since [simple] is just an evaluated form of [proj] *)
                coercion_from_proj_to_var
              in
              let! tmp1 := Code_size.simple simple in
              let! tmp2 := Named.create_simple simple in
              ret (T3 tmp2 coercion_from_simple_to_var tmp1)
            in
            (* If the projection is from one of the symbols bound by the
               "let symbol" that we've just created, we'll always end up
               here (i.e. in the case where the result of the projection is
               known now as a [Simple]), avoiding any problem about where to
               do the projection versus the initialisation of a
               possibly-recursive group of symbols. The result of the
               projection can here be assumed to always be known (as a
               [Simple]) in this case (see LC.apply_projection). We may end
               up with a "variable = variable" [Let] here, but [To_cmm] (or
               a subsequent pass of [Simplify]) will remove it. This is the
               same situation as when continuations are inlined; we can't
               use a name permutation to resolve the problem as both [var]
               and [var'] may occur in [expr], and permuting could cause an
               unbound name.

               One might consider the case where a symbol's field is defined
               using a variable that itself is assigned a symbol projection
               from that same field. However we believe such cases cannot
               arise at present because there is a strict ordering of
               lifting decisions. All symbol projections are introduced
               based on lifting decisions made in the past.

               The ordering of lifting decisions notwithstanding, it would
               still not be possible to create this kind of cycle, because
               the translation from the source language will ensure that the
               recursion goes through at least one piece of [Code] -- from
               which no symbol projections are possible. These properties
               are preserved by [Simplify].

               It is possible for one projection to yield a variable that is
               in turn defined by another symbol projection, so we need to
               expand transitively. This process will always terminate by
               virtue of the arguments just made. *)
            Simple.pattern_match' simple
              (fun var' coercion_from_var'_to_simple =>
                let! tmp1 :=
                  Variable_.Map.find_or_null var' symbol_projections
                in
                match tmp1 with
                | Or_null.Null => stop_here tt
                | Or_null.This proj' =>
                  let& coercion_from_var'_to_proj :=
                    (* Since [simple] is just an evaluated form of [proj] *)
                    coercion_from_var'_to_simple
                  in
                  let& coercion_from_proj'_to_proj :=
                    (* Since [proj'] is just an expanded form of [var'] *)
                    coercion_from_var'_to_proj
                  in
                  let* coercion_from_proj'_to_var :=
                    Coercion.compose_exn coercion_from_proj'_to_proj
                      coercion_from_proj_to_var
                  in
                  apply_projection fuel proj' coercion_from_proj'_to_var
                end)
              (fun _ _ =>
                (* We're not dropping the coercion: it gets used in
                   [stop_here] *)
                stop_here tt)
              (fun _ => stop_here tt)
          | None =>
            let* prim :=
              let* symbol :=
                let! tmp1 := Symbol_projection.symbol proj in
                Simple.symbol tmp1
              in
              let* result_kind := Symbol_projection.kind proj in
              let! tmp1 := Symbol_projection.projection proj in
              match tmp1 with
              | Symbol_projection.Projection.Block_load index block_shape =>
                let* block_access_kind :=
                  P.Block_access_kind.from_block_shape block_shape index
                    result_kind
                in
                ret
                  (P.Unary
                     (P.Block_load block_access_kind Mutability.Immutable index)
                     symbol)
              | Symbol_projection.Projection.Project_value_slot project_from
                  value_slot =>
                ret
                  (P.Unary
                     (P.Project_value_slot project_from value_slot)
                     symbol)
              end
            in
            let* machine_width :=
              let! tmp1 := UA.uenv uacc in
              UE.machine_width tmp1
            in
            let! tmp1 := Code_size.prim machine_width prim in
            let! tmp2 := Named.create_prim prim Debuginfo.none in
            ret (T3 tmp2 coercion_from_proj_to_var tmp1)
          end
      in
      (* It's possible that this might create duplicates of the same
         projection operation, but it's unlikely there will be a significant
         number, and since we're at toplevel we tolerate them. *)
      let* '(T3 defining_expr coercion_from_defining_expr_to_var
               code_size_of_defining_expr) :=
        let_fuel! fuel in
        apply_projection fuel proj Coercion.id
      in
      let* cost_metrics_of_defining_expr :=
        Cost_metrics.from_size code_size_of_defining_expr
      in
      let* free_names_of_defining_expr := Named.free_names defining_expr in
      let* '(expr, uacc) :=
        let! tmp1 := VB.create var Flambda_debug_uid.none Name_mode.normal in
        create_coerced_singleton_let uacc tmp1 defining_expr
          coercion_from_defining_expr_to_var free_names_of_defining_expr expr
          cost_metrics_of_defining_expr
      in
      (* Not removing any operation here as the let bindings would have been
         created for the first time here.*)
      ret (expr, uacc))
    symbol_projections (expr, uacc).

(* 436-456 *)
Definition place_lifted_constants (uacc : UA.t)
    (lifted_constants_from_defining_expr lifted_constants_from_body : LCS.t)
    (put_bindings_around_body : UA.t -> RE.t -> M (RE.t * UA.t)) (body : RE.t)
    : M (RE.t * UA.t) :=
  (* Lifted constants are placed as soon as they reach toplevel. *)
  (let! tmp1 := UA.no_lifted_constants uacc in
   if negb tmp1
   then
     fatal_errorf0
       "All lifted constants of the body should have been
                        removed from the uacc"
   else ret tt) ;;
  let& place_constants :=
    fun (uacc : UA.t) (around : RE.t) (constants : LCS.t) =>
    let* sorted := LCS.sort constants in
    ArrayLabels.fold_left
      (fun acc lifted_const =>
        (* PORT-GAP(loose): 447, the pair pattern of the parameter is a
           [let]. *)
        let* '(body, uacc) := ret acc in
        create_let_symbols uacc lifted_const body)
      (* 446: [sorted.innermost_first]. The field is written with the
         module's own name: through [LCS] Rocq prints it as a function
         ([LCS.innermost_first sorted]), which OCaml does not have. *)
      (around, uacc) sorted.(Lifted_constant_state.innermost_first)
  in
  (* Place constants whose definitions may depend on the bound name(s) of the
     current binding(s) to be introduced by [put_bindings_around_body]. *)
  let* '(body, uacc) :=
    place_constants uacc body lifted_constants_from_body
  in
  let* '(body, uacc) := put_bindings_around_body uacc body in
  place_constants uacc body lifted_constants_from_defining_expr.

(* 458-503 *)
Definition create_switch (uacc : UA.t) (condition_dbg : Debuginfo.t)
    (scrutinee : Simple.t) (arms : Target_ocaml_int.Map.t Switch_arm.t)
    : M (RE.t * UA.t) :=
  let! tmp1 := Target_ocaml_int.Map.cardinal arms in
  if tmp1 <? 1
  then
    let! tmp2 := UA.notify_added Code_size.invalid uacc in
    let! tmp3 := RE.create_invalid Flambda.Invalid.Zero_switch_arms in
    ret (tmp3, tmp2)
  else
    let& change_to_apply_cont :=
      fun (action : Apply_cont.t) =>
      (* 465-468: [a |> f b] is [f b a] *)
      let* uacc :=
        let! tmp1 := Apply_cont.free_names action in
        let! tmp2 := UA.add_free_names uacc tmp1 in
        let! tmp3 := Code_size.apply_cont action in
        UA.notify_added tmp3 tmp2
      in
      let* is_cold :=
        let! tmp1 := Apply_cont.continuation action in
        let! tmp2 := UA.uenv uacc in
        UE.is_cold_continuation tmp2 tmp1
      in
      let! tmp1 := RE.create_apply_cont is_cold action in
      ret (tmp1, uacc)
    in
    let! tmp1 := Target_ocaml_int.Map.get_singleton arms in
    match tmp1 with
    | Some (_discriminant, action) =>
      let! tmp1 := Switch_arm.action action in
      change_to_apply_cont tmp1
    | None =>
      (* At that point, we've already applied the apply cont rewrite to the
         action of the arms. *)
      let* actions :=
        Target_ocaml_int.Map.fold
          (fun _ arm actions =>
            let! tmp1 := Switch_arm.action arm in
            Apply_cont_expr.Set_.add tmp1 actions)
          arms Apply_cont_expr.Set_.empty
      in
      let! tmp1 := Apply_cont_expr.Set_.get_singleton actions in
      match tmp1 with
      | Some action =>
        (* The resulting [Debuginfo] on the [Apply_cont] will be arbitrarily
           chosen from amongst the [Debuginfo] values on the arms, but this
           seems fine. *)
        change_to_apply_cont action
      | None =>
        let* switch := Switch.create condition_dbg scrutinee arms in
        let* uacc :=
          let! tmp1 := Switch.free_names switch in
          let! tmp2 := UA.add_free_names uacc tmp1 in
          let! tmp3 := Code_size.switch switch in
          UA.notify_added tmp3 tmp2
        in
        let* is_cold :=
          Target_ocaml_int.Map.for_all
            (fun _ arm => Switch_arm.is_cold arm)
            arms
        in
        let! tmp1 := UA.are_rebuilding_terms uacc in
        let! tmp2 := RE.create_switch tmp1 is_cold switch in
        ret (tmp2, uacc)
      end
    end.

(* 505-510 *)
Record new_let_cont : Type :=
  { cont : Continuation.t;
    handler : RE.Continuation_handler.t;
    free_names_of_handler : Name_occurrences.t;
    cost_metrics_of_handler : Cost_metrics.t
  }.

(* 512-531 *)
(* PORT-GAP(loose): the record pattern of the parameter is a match. *)
Definition bind_let_cont (uacc : UA.t) (body : RE.t)
    (new_let_cont : Expr_builder.new_let_cont) : M (UA.t * RE.t) :=
  match new_let_cont with
  | {| cont := cont;
       handler := handler;
       free_names_of_handler := free_names_of_handler;
       cost_metrics_of_handler := cost_metrics_of_handler
    |} =>
    let* free_names_of_body := UA.name_occurrences uacc in
    let* expr :=
      let! tmp1 := UA.are_rebuilding_terms uacc in
      RE.create_non_recursive_let_cont tmp1 cont handler body free_names_of_body
    in
    let* name_occurrences :=
      let! tmp1 :=
        Name_occurrences.union free_names_of_body free_names_of_handler
      in
      Name_occurrences.remove_continuation tmp1 cont
    in
    (* 525-530: [a |> f b] is [f b a] *)
    let* uacc :=
      let! tmp1 := UA.with_name_occurrences uacc name_occurrences in
      let! tmp2 :=
        Cost_metrics.increase_due_to_let_cont_non_recursive
          cost_metrics_of_handler
      in
      UA.add_cost_metrics tmp2 tmp1
    in
    ret (uacc, expr)
  end.

(* 533-535 *)
Definition bind_let_conts (uacc : UA.t) (body : RE.t)
    (new_handlers : list new_let_cont) : M (UA.t * RE.t) :=
  ListLabels.fold_left
    (fun acc new_let_cont =>
      (* PORT-GAP(loose): 535, the pair pattern of the parameter is a
         [let]. *)
      let* '(uacc, body) := ret acc in
      bind_let_cont uacc body new_let_cont)
    (uacc, body) new_handlers.

(* 537-538 *)
Definition rebuild_invalid (uacc : UA.t) (reason : Flambda.Invalid.t)
    (after_rebuild : RE.t -> UA.t -> M (RE.t * UA.t)) : M (RE.t * UA.t) :=
  let! tmp1 := RE.create_invalid reason in
  after_rebuild tmp1 uacc.

(* PORT-GAP(type): 540-546. Four types of the file (here, 609-613, 615-617
   and 743-746) share the constructors [Invalid], [Apply_cont] and
   [New_wrapper]; three of them have a constructor with an inline record
   and this one a function with a label; and each must stand at its place,
   after [new_let_cont]. In Rocq each is a type whose name ends in [_]; a
   constructor that another of them has already gets one more [_]
   ([Invalid], [Invalid_], [Invalid__]); the extraction is told the
   compiler's constructor and its type, and the compiler's definition is
   printed at the place of the [Definition]. *)
Inductive rewrite_apply_cont_result_ : Type :=
| Invalid : string -> rewrite_apply_cont_result_
| Apply_cont : Apply_cont.t -> rewrite_apply_cont_result_
| Expr :
    ((Apply_cont.t -> M (tuple3 RE.t Cost_metrics.t Name_occurrences.t)) ->
     M (tuple3 RE.t Cost_metrics.t Name_occurrences.t)) ->
    rewrite_apply_cont_result_.
Extract Inductive rewrite_apply_cont_result_ => "rewrite_apply_cont_result" [ "(fun x__1 -> (Invalid { message = x__1 } : rewrite_apply_cont_result))" "(fun x__1 -> (Apply_cont x__1 : rewrite_apply_cont_result))" "(fun x__1 -> (Expr x__1 : rewrite_apply_cont_result))" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : rewrite_apply_cont_result) with Invalid { message = x__1 } -> f__1 x__1 | Apply_cont x__1 -> f__2 x__1 | Expr x__1 -> f__3 x__1)".
Definition rewrite_apply_cont_result : Type := rewrite_apply_cont_result_.
Extract Constant rewrite_apply_cont_result => "| Invalid of { message : string } | Apply_cont of Apply_cont.t | Expr of (apply_cont_to_expr:(Apply_cont.t -> RE.t * Cost_metrics.t * Name_occurrences.t) -> RE.t * Cost_metrics.t * Name_occurrences.t)".

(* 548-561. The compiler's comment of lines 549-552, a note for later, is
   left out. *)
Definition apply_continuation_shortcuts (uenv : UE.t)
    (apply_cont : Apply_cont.t) : M Apply_cont.t :=
  let! tmp1 := Apply_cont.continuation apply_cont in
  let! tmp2 := UE.find_continuation_shortcut uenv tmp1 in
  match tmp2 with
  | None => ret apply_cont
  | Some shortcut =>
    let* '(cont, args) :=
      let! tmp1 := Apply_cont.args apply_cont in
      Continuation_shortcut.apply shortcut tmp1
    in
    Apply_cont.with_continuation_and_args apply_cont cont args
  end.

(* 563-569 *)
Definition apply_continuation_aliases (uenv : UE.t) (cont : Continuation.t)
    : M Continuation.t :=
  let! tmp1 := UE.find_continuation_shortcut uenv cont in
  match tmp1 with
  | None => ret cont
  | Some shortcut =>
    let! tmp1 := Continuation_shortcut.to_alias shortcut in
    match tmp1 with
    | None => ret cont
    | Some cont => ret cont
    end
  end.

(* 571-578 *)
Definition apply_exn_continuation_aliases (uenv : UE.t)
    (exn_cont : Exn_continuation.t) : M Exn_continuation.t :=
  let* cont := Exn_continuation.exn_handler exn_cont in
  let! tmp1 := UE.find_continuation_shortcut uenv cont in
  match tmp1 with
  | None => ret exn_cont
  | Some shortcut =>
    let! tmp1 := Continuation_shortcut.to_alias shortcut in
    match tmp1 with
    | None => ret exn_cont
    | Some cont => Exn_continuation.with_exn_handler exn_cont cont
    end
  end.

(* 580-582 *)
Definition no_rewrite_apply_cont (uenv : UE.t) (apply_cont : Apply_cont.t)
    : M rewrite_apply_cont_result :=
  let* apply_cont := apply_continuation_shortcuts uenv apply_cont in
  ret (Apply_cont apply_cont).

(* 584-604. In the compiler: [uacc rewrite ~ctx id apply_cont]. *)
Definition rewrite_apply_cont0 (uacc : UA.t) (rewrite : Apply_cont_rewrite.t)
    (ctx : Apply_cont_rewrite.rewrite_apply_cont_ctx)
    (id : Apply_cont_rewrite_id.t) (apply_cont : Apply_cont.t)
    : M rewrite_apply_cont_result :=
  let* args := Apply_cont.args apply_cont in
  let* machine_width :=
    let! tmp1 := UA.uenv uacc in
    UE.machine_width tmp1
  in
  let! tmp1 :=
    Apply_cont_rewrite.make_rewrite rewrite machine_width ctx id args
  in
  match tmp1 with
  | Or_invalid.Invalid => ret (Invalid "")
  | Or_invalid.Ok (extra_lets, args) =>
    let* apply_cont := Apply_cont.update_args apply_cont args in
    let* apply_cont :=
      let! tmp1 := UA.uenv uacc in
      apply_continuation_shortcuts tmp1 apply_cont
    in
    match extra_lets with
    | [] => ret (Apply_cont apply_cont)
    | _ :: _ =>
      let& build_expr :=
        fun (apply_cont_to_expr :
              Apply_cont.t ->
              M (tuple3 RE.t Cost_metrics.t Name_occurrences.t)) =>
        let* '(T3 body cost_metrics_of_body free_names_of_body) :=
          apply_cont_to_expr apply_cont
        in
        let! tmp1 := UA.are_rebuilding_terms uacc in
        RE.bind_no_simplification tmp1 extra_lets body cost_metrics_of_body
          free_names_of_body
      in
      ret (Expr build_expr)
    end
  end.

(* 606-607 *)
Definition rewrite_apply_cont (uacc : UA.t) (rewrite : Apply_cont_rewrite.t)
    (id : Apply_cont_rewrite_id.t) (apply_cont : Apply_cont.t)
    : M rewrite_apply_cont_result :=
  rewrite_apply_cont0 uacc rewrite Apply_cont_rewrite.Apply_cont id apply_cont.

(* PORT-GAP(type): 609-613, as at 540: [Invalid_] and [Apply_cont_] are the
   compiler's [Invalid] and [Apply_cont] of this type. *)
Inductive rewrite_fixed_arity_continuation0_result_ : Type :=
| Invalid_ : string -> rewrite_fixed_arity_continuation0_result_
| This_continuation :
    Continuation.t -> rewrite_fixed_arity_continuation0_result_
| Apply_cont_ : Apply_cont.t -> rewrite_fixed_arity_continuation0_result_
| New_wrapper : new_let_cont -> rewrite_fixed_arity_continuation0_result_.
Extract Inductive rewrite_fixed_arity_continuation0_result_ => "rewrite_fixed_arity_continuation0_result" [ "(fun x__1 -> (Invalid { message = x__1 } : rewrite_fixed_arity_continuation0_result))" "(fun x__1 -> (This_continuation x__1 : rewrite_fixed_arity_continuation0_result))" "(fun x__1 -> (Apply_cont x__1 : rewrite_fixed_arity_continuation0_result))" "(fun x__1 -> (New_wrapper x__1 : rewrite_fixed_arity_continuation0_result))" ] "(fun f__1 f__2 f__3 f__4 x__0 -> match (x__0 : rewrite_fixed_arity_continuation0_result) with Invalid { message = x__1 } -> f__1 x__1 | This_continuation x__1 -> f__2 x__1 | Apply_cont x__1 -> f__3 x__1 | New_wrapper x__1 -> f__4 x__1)".
Definition rewrite_fixed_arity_continuation0_result : Type :=
  rewrite_fixed_arity_continuation0_result_.
Extract Constant rewrite_fixed_arity_continuation0_result => "| Invalid of { message : string } | This_continuation of Continuation.t | Apply_cont of Apply_cont.t | New_wrapper of new_let_cont".

(* PORT-GAP(type): 615-617, as at 540: [Apply_cont__] is the compiler's
   [Apply_cont] of this type. *)
Inductive cont_or_apply_cont_ : Type :=
| Continuation : Continuation.t -> cont_or_apply_cont_
| Apply_cont__ : Apply_cont.t -> cont_or_apply_cont_.
Extract Inductive cont_or_apply_cont_ => "cont_or_apply_cont" [ "(fun x__1 -> (Continuation x__1 : cont_or_apply_cont))" "(fun x__1 -> (Apply_cont x__1 : cont_or_apply_cont))" ] "(fun f__1 f__2 x__0 -> match (x__0 : cont_or_apply_cont) with Continuation x__1 -> f__1 x__1 | Apply_cont x__1 -> f__2 x__1)".
Definition cont_or_apply_cont : Type := cont_or_apply_cont_.
Extract Constant cont_or_apply_cont => "| Continuation of Continuation.t | Apply_cont of Apply_cont.t".

(* 619 *)
Definition rewrite_exn_continuation
    : Apply_cont_rewrite.t -> Apply_cont_rewrite_id.t -> Exn_continuation.t ->
      M Exn_continuation.t :=
  Apply_cont_rewrite.rewrite_exn_continuation.

(* 621-741. In the compiler: [uacc cont_or_apply_cont ~use_id arity]. *)
Definition rewrite_fixed_arity_continuation0 (uacc : UA.t)
    (cont_or_apply_cont : Expr_builder.cont_or_apply_cont)
    (use_id : Apply_cont_rewrite_id.t) (arity : Flambda_arity.t_Unarized)
    : M rewrite_fixed_arity_continuation0_result :=
  let* uenv := UA.uenv uacc in
  let& specialize_if_needed :=
    fun (cont : Continuation.t) =>
    try_with
      (fun _ =>
        let! tmp1 := UA.specialization_map uacc in
        Continuation_callsite_map.find cont use_id tmp1)
      Not_found
      (fun _ => ret cont)
  in
  let* '(cont, cont_or_apply_cont) :=
    match cont_or_apply_cont with
    | Continuation cont =>
      let* cont := specialize_if_needed cont in
      ret (cont, Continuation cont)
    | Apply_cont__ apply_cont =>
      let* cont :=
        let! tmp1 := Apply_cont.continuation apply_cont in
        specialize_if_needed tmp1
      in
      let* apply_cont := Apply_cont.with_continuation apply_cont cont in
      ret (cont, Apply_cont__ apply_cont)
    end
  in
  (* PORT-GAP(loose): 638, the attribute [@local] is not kept. *)
  let& shortcut_this_continuation_if_possible :=
    fun (_ : unit) =>
    (* Apply the shortcut if we can, but not if we are rewriting a
       [Continuation] since we would need to introduce a new wrapper
       anyway. *)
    match cont_or_apply_cont with
    | Continuation cont =>
      let! tmp1 := apply_continuation_aliases uenv cont in
      ret (This_continuation tmp1)
    | Apply_cont__ apply_cont =>
      let! tmp1 := apply_continuation_shortcuts uenv apply_cont in
      ret (Apply_cont_ tmp1)
    end
  in
  let! tmp1 := UE.find_apply_cont_rewrite uenv cont in
  match tmp1 with
  | None => shortcut_this_continuation_if_possible tt
  | Some rewrite =>
    (* 650: [when Apply_cont_rewrite.does_nothing rewrite] *)
    let! tmp1 := Apply_cont_rewrite.does_nothing rewrite in
    if tmp1
    then
      let* arity_in_rewrite :=
        Apply_cont_rewrite.original_params_arity rewrite
      in
      (let! tmp1 :=
         Flambda_arity.equal_ignoring_subkinds arity arity_in_rewrite
       in
       if negb tmp1
       then
         fatal_errorf6
           "Arity %a provided to fixed-arity-wrapper addition function does not match arity %a in rewrite:@ %a"
           Flambda_arity.print arity Flambda_arity.print arity_in_rewrite
           Apply_cont_rewrite.print rewrite
       else ret tt) ;;
      shortcut_this_continuation_if_possible tt
    else
      (* 661-662. In the compiler: [params expr ~free_names
         ~cost_metrics:cost_metrics_of_handler]. *)
      let& new_wrapper :=
        fun (params : Bound_parameters.t) (expr : RE.t)
            (free_names : Name_occurrences.t)
            (cost_metrics_of_handler : Cost_metrics.t) =>
        let* cont := Continuation.create None None tt in
        let* handler :=
          let! tmp1 := UA.are_rebuilding_terms uacc in
          RE.Continuation_handler.create tmp1 params expr free_names false false
          (* This is only a wrapper that will immediately call the
             continuation, so we set [is_cold] to false so that this wrapper
             can be inlined by [to_cmm]. *)
        in
        let* free_names_of_handler :=
          let! tmp1 := Bound_parameters.to_list params in
          ListLabels.fold_left
            (fun free_names param =>
              let! tmp2 := Bound_parameter.var param in
              Name_occurrences.remove_var free_names tmp2)
            free_names tmp1
        in
        ret
          (New_wrapper
             {| cont := cont;
                handler := handler;
                free_names_of_handler := free_names_of_handler;
                cost_metrics_of_handler := cost_metrics_of_handler
             |})
      in
      match cont_or_apply_cont with
      | Continuation _ =>
        (* In this case, any generated [Apply_cont] will sit inside a wrapper
           that binds [kinded_params]. *)
        let* params :=
          let! tmp1 := Flambda_arity.unarized_components arity in
          List.map
            (fun kind =>
              let* param_var :=
                let! tmp2 := Flambda_kind.With_subkind.kind kind in
                Variable_.create None "param" tmp2
              in
              let& param_var_duid := Flambda_debug_uid.none in
              BP.create param_var kind param_var_duid)
            tmp1
        in
        let* args := List.map BP.simple params in
        let* params := Bound_parameters.create params in
        let* apply_cont := Apply_cont.create None cont args Debuginfo.none in
        let& ctx := Apply_cont_rewrite.Apply_expr args in
        let! tmp1 := rewrite_apply_cont0 uacc rewrite ctx use_id apply_cont in
        match tmp1 with
        | Invalid message => ret (Invalid_ message)
        | Apply_cont apply_cont =>
          let* is_cold :=
            let! tmp1 := Apply_cont.continuation apply_cont in
            UE.is_cold_continuation uenv tmp1
          in
          let* cost_metrics :=
            let! tmp1 := Code_size.apply_cont apply_cont in
            Cost_metrics.from_size tmp1
          in
          let! tmp1 := Apply_cont.free_names apply_cont in
          let! tmp2 := RE.create_apply_cont is_cold apply_cont in
          new_wrapper params tmp2 tmp1 cost_metrics
        | Expr build_expr =>
          let* '(T3 expr cost_metrics free_names) :=
            build_expr
              (fun apply_cont =>
                let* is_cold :=
                  let! tmp1 := Apply_cont.continuation apply_cont in
                  UE.is_cold_continuation uenv tmp1
                in
                let! tmp1 := Apply_cont.free_names apply_cont in
                let! tmp2 := Code_size.apply_cont apply_cont in
                let! tmp3 := Cost_metrics.from_size tmp2 in
                let! tmp4 := RE.create_apply_cont is_cold apply_cont in
                ret (T3 tmp4 tmp3 tmp1))
          in
          new_wrapper params expr free_names cost_metrics
        end
      | Apply_cont__ apply_cont =>
        let* apply_cont := Apply_cont.with_continuation apply_cont cont in
        let! tmp1 := rewrite_apply_cont uacc rewrite use_id apply_cont in
        match tmp1 with
        | Invalid message => ret (Invalid_ message)
        | Apply_cont apply_cont => ret (Apply_cont_ apply_cont)
        | Expr build_expr =>
          let* '(T3 expr cost_metrics free_names) :=
            build_expr
              (fun apply_cont =>
                let* is_cold :=
                  let! tmp1 := Apply_cont.continuation apply_cont in
                  UE.is_cold_continuation uenv tmp1
                in
                let! tmp1 := Apply_cont.free_names apply_cont in
                let! tmp2 := Code_size.apply_cont apply_cont in
                let! tmp3 := Cost_metrics.from_size tmp2 in
                let! tmp4 := RE.create_apply_cont is_cold apply_cont in
                ret (T3 tmp4 tmp3 tmp1))
          in
          new_wrapper Bound_parameters.empty expr free_names cost_metrics
        end
      end
  end.

(* PORT-GAP(type): 743-746, as at 540: [Invalid__], [Apply_cont___] and
   [New_wrapper_] are the compiler's [Invalid], [Apply_cont] and
   [New_wrapper] of this type. *)
Inductive rewrite_switch_arm_result_ : Type :=
| Invalid__ : string -> rewrite_switch_arm_result_
| Apply_cont___ : Apply_cont.t -> rewrite_switch_arm_result_
| New_wrapper_ : new_let_cont -> rewrite_switch_arm_result_.
Extract Inductive rewrite_switch_arm_result_ => "rewrite_switch_arm_result" [ "(fun x__1 -> (Invalid { message = x__1 } : rewrite_switch_arm_result))" "(fun x__1 -> (Apply_cont x__1 : rewrite_switch_arm_result))" "(fun x__1 -> (New_wrapper x__1 : rewrite_switch_arm_result))" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : rewrite_switch_arm_result) with Invalid { message = x__1 } -> f__1 x__1 | Apply_cont x__1 -> f__2 x__1 | New_wrapper x__1 -> f__3 x__1)".
Definition rewrite_switch_arm_result : Type := rewrite_switch_arm_result_.
Extract Constant rewrite_switch_arm_result => "| Invalid of { message : string } | Apply_cont of Apply_cont.t | New_wrapper of new_let_cont".

(* 748-757 *)
Definition rewrite_switch_arm (uacc : UA.t) (apply_cont : Apply_cont.t)
    (use_id : Apply_cont_rewrite_id.t) (arity : Flambda_arity.t_Unarized)
    : M rewrite_switch_arm_result :=
  let! tmp1 :=
    rewrite_fixed_arity_continuation0 uacc (Apply_cont__ apply_cont) use_id
      arity
  in
  match tmp1 with
  | Invalid_ message => ret (Invalid__ message)
  | This_continuation cont =>
    let! tmp1 := Apply_cont.with_continuation apply_cont cont in
    ret (Apply_cont___ tmp1)
  | Apply_cont_ apply_cont => ret (Apply_cont___ apply_cont)
  | New_wrapper new_let_cont => ret (New_wrapper_ new_let_cont)
  end.

(* 759-773. In the compiler: [uacc cont ~use_id arity ~around]. At 772-773
   the compiler names [body] the accumulator that [around] gives back and
   [uacc] the expression; the names are kept. The compiler's comment of
   lines 766-767, a note for later, is left out. *)
Definition rewrite_fixed_arity_continuation (uacc : UA.t)
    (cont : Continuation.t) (use_id : Apply_cont_rewrite_id.t)
    (arity : Flambda_arity.t_Unarized)
    (around : UA.t -> Continuation.t -> M (UA.t * RE.t)) : M (UA.t * RE.t) :=
  let! tmp1 :=
    rewrite_fixed_arity_continuation0 uacc (Continuation cont) use_id arity
  in
  match tmp1 with
  | Invalid_ message =>
    (* Continuation calls are not counted as operations for cost benefit in
       the uacc *)
    let! tmp1 := RE.create_invalid (Flambda.Invalid.Message message) in
    ret (uacc, tmp1)
  | This_continuation cont => around uacc cont
  | Apply_cont_ _ => assert_false
  | New_wrapper new_let_cont =>
    let* '(body, uacc) := around uacc new_let_cont.(Expr_builder.cont) in
    bind_let_cont body uacc new_let_cont
  end.

(* 775-800 *)
Definition rewrite_fixed_arity_apply (uacc : UA.t)
    (use_id : option Apply_cont_rewrite_id.t) (is_cold : bool)
    (arity : Flambda_arity.t_Unarized) (apply : Apply.t) : M (UA.t * RE.t) :=
  let& make_apply :=
    fun (apply : Apply.t) =>
    (* 777-780: [a |> f b] is [f b a] *)
    let* uacc :=
      let! tmp1 := Apply.free_names apply in
      let! tmp2 := UA.add_free_names uacc tmp1 in
      let! tmp3 := Code_size.apply apply in
      UA.notify_added tmp3 tmp2
    in
    let! tmp1 := UA.are_rebuilding_terms uacc in
    let! tmp2 := RE.create_apply tmp1 is_cold apply in
    ret (uacc, tmp2)
  in
  (* PORT-GAP(loose): 783, the call that is the second value of the match is
     bound first. *)
  let* result_continuation := Apply.continuation apply in
  match use_id, result_continuation with
  | _, Apply_expr.Result_continuation.Never_returns => make_apply apply
  | None, Apply_expr.Result_continuation.Return _ =>
    fatal_errorf2
      "Expr_builder.rewrite_fixed_arity_apply: got no use_id for the return continuation but the apply could return:@ %a@."
      Apply.print apply
  | Some use_id, Apply_expr.Result_continuation.Return cont =>
    rewrite_fixed_arity_continuation uacc cont use_id arity
      (fun uacc return_cont =>
        let* exn_cont :=
          let! tmp1 := Apply.exn_continuation apply in
          let! tmp2 := UA.uenv uacc in
          apply_exn_continuation_aliases tmp2 tmp1
        in
        let* apply :=
          Apply.with_continuations apply
            (Apply_expr.Result_continuation.Return return_cont)
            exn_cont
        in
        make_apply apply)
  end.
