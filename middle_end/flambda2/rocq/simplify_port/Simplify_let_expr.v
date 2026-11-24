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

(* This file follows middle_end/flambda2/simplify/simplify_let_expr.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Simplified_expr Simplify_simple.
From SimplifyPort.decl Require Bound_pattern Bound_static Bound_var
  Closure_info Code_id Flow Flow_types List ListLabels Name Name_mode
  Name_occurrences Named_rewrite Named_rewrite_id Or_invalid Or_unknown
  Removed_operations Simple Simplified_named Simplify_common Simplify_named
  Simplify_named_result Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Closure_info.in_or_out_of_closure_
   Flambda.Invalid.t Flambda.named Name_mode.Or_absent.t Named_rewrite.t
   Or_unknown.t Simplified_named.or_rewritten
   Simplified_named.simplified_named *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 19-38 *)
Definition keep_lifted_constant_only_if_used (uacc : UA.t) (acc : LCS.t)
    (lifted_constant : LC.t) : M LCS.t :=
  let* bound := LC.bound_static lifted_constant in
  let* code_ids_live :=
    let! tmp1 := UA.reachable_code_ids uacc in
    match tmp1 with
    | Or_unknown.Unknown => Bound_static.binds_code bound
    | Or_unknown.Known
        {| Flow_types.Reachable_code_ids.ancestors_of_live_code_ids :=
             ancestors_of_live_code_ids
        |} =>
      let! tmp1 := Bound_static.code_being_defined bound in
      let! tmp2 := Code_id.Set_.disjoint tmp1 ancestors_of_live_code_ids in
      ret (negb tmp2)
    end
  in
  let* symbols_live :=
    let! tmp1 := UA.required_names uacc in
    let! tmp2 := Bound_static.symbols_being_defined bound in
    let! tmp3 := Name.set_of_symbol_set tmp2 in
    let! tmp4 := Name.Set_.disjoint tmp3 tmp1 in
    ret (negb tmp4)
  in
  if symbols_live || code_ids_live then LCS.add acc lifted_constant else ret acc.

(* 40-346 *)
(* PORT-GAP(loose): 40-48, the compiler's first parameter is the pattern
   [({ SE.bindings_to_place; ... }, body)]; here it has a name and is taken
   apart on the next lines. *)
Definition rebuild_let (arg : Simplified_expr.simplified_defining_expr * RE.t)
    (uacc : UA.t) (after_rebuild : Simplify_common.after_rebuild)
    : M (RE.t * UA.t) :=
  let '({| Simplified_expr.bindings_to_place := bindings_to_place;
           Simplified_expr.removed_operations := removed_operations;
           Simplified_expr.lifted_constants_from_defining_expr :=
             lifted_constants_from_defining_expr;
           Simplified_expr.at_unit_toplevel := at_unit_toplevel;
           Simplified_expr.closure_info := closure_info;
           Simplified_expr.rewrite_id := rewrite_id
        |}, body) := arg in
  (* 49-59 *)
  let* lifted_constants_from_defining_expr :=
    let! tmp1 := Closure_info.in_or_out_of_closure closure_info in
    match tmp1 with
    | Closure_info.In_a_closure =>
      (* See the comment in [simplify_let], below; this case is analogous. *)
      ret lifted_constants_from_defining_expr
    | Closure_info.Not_in_a_closure_ =>
      (* We must filter even if not rebuilding terms, otherwise the free names
         of the terms might get out of sync with [Data_flow]. 58: the function
         [keep_lifted_constant_only_if_used], of this file, given its first
         argument only, is a value. *)
      LCS.fold lifted_constants_from_defining_expr LCS.empty
        (keep_lifted_constant_only_if_used uacc)
    end
  in
  (* At this point, the free names in [uacc] are the free names of [body], plus
     all used value slots seen in the whole compilation unit. *)
  let* no_constants_from_defining_expr :=
    LCS.is_empty lifted_constants_from_defining_expr
  in
  (* The lifted constants present in [uacc] are the ones arising from the
     simplification of [body] which still have to be placed. We augment these
     with any constants arising from the simplification of the defining
     expression. Then we either place all of them, if we are at toplevel, or
     else return them in [uacc] for an outer [Let]-binding to deal with.

     It may be surprising that lifted constants can arise from the
     simplification of the body in the case where they have also arisen from the
     defining expression (since the latter implies that we must be at toplevel).
     However this can happen in the case of recursive continuations, in which
     constants cannot be placed. *)
  let* no_constants_to_place :=
    and_then no_constants_from_defining_expr (UA.no_lifted_constants uacc)
  in
  (* 81-322 *)
  let& put_bindings_around_body :=
    fun (uacc : UA.t) (body : RE.t) =>
    let* uacc := UA.notify_removed removed_operations uacc in
    (* 83-115. 89-93, 108-112: [{ kept_binding with simplified_defining_expr =
       ... }] is the constructor with all its fields, by place. *)
    let* bindings :=
      List.map
        (fun (binding : Simplified_named.binding_to_place) =>
          match binding with
          | Simplified_named.Delete_binding _ => ret binding
          | Simplified_named.Keep_binding let_bound simplified_defining_expr
              original_defining_expr =>
            match simplified_defining_expr.(Simplified_named.named) with
            | Simplified_named.Prim prim _dbg =>
              let! tmp1 := Bound_pattern.must_be_singleton_opt let_bound in
              match tmp1 with
              | None => ret binding
              | Some bound_var =>
                let* simple :=
                  let! tmp1 := Bound_var.var bound_var in
                  Simple.var tmp1
                in
                let! tmp1 := UA.creation_dacc uacc in
                let! tmp2 := DA.find_debuginfo_rewrite tmp1 simple in
                match tmp2 with
                | None => ret binding
                | Some dbg =>
                  let* machine_width :=
                    let! tmp1 := UA.uenv uacc in
                    UE.machine_width tmp1
                  in
                  let! tmp1 := Named.create_prim prim dbg in
                  let! tmp2 := Simplified_named.create machine_width tmp1 in
                  ret
                    (Simplified_named.Keep_binding let_bound tmp2
                       original_defining_expr)
                end
              end
            | Simplified_named.Simple _ | Simplified_named.Set_of_closures _ _
            | Simplified_named.Rec_info _ =>
              ret binding
            end
          end)
        bindings_to_place
    in
    (* Phantom let creation *)
    let* generate_phantom_lets := UA.generate_phantom_lets uacc in
    let* free_names_of_body := UA.name_occurrences uacc in
    (* 119-134 *)
    let& compute_greatest_name_mode :=
      fun (bound_vars : Bound_pattern.t) =>
      match bound_vars with
      | Bound_pattern.Singleton bound_var =>
        (* We avoid the closure allocation (below) in this case. *)
        let! tmp1 := VB.var bound_var in
        Name_occurrences.greatest_name_mode_var free_names_of_body tmp1
      | Bound_pattern.Set_of_closures _ =>
        Bound_pattern.fold_all_bound_vars bound_vars
          Name_mode.Or_absent.absent
          (fun greatest_name_mode bound_var =>
            let! tmp1 := VB.var bound_var in
            let! tmp2 :=
              Name_occurrences.greatest_name_mode_var free_names_of_body tmp1
            in
            Name_mode.Or_absent.join_in_terms greatest_name_mode tmp2)
      | Bound_pattern.Static _ => assert_false
      (* see below *)
      end
    in
    (* 135-249 *)
    let* bindings :=
      List.map
        (fun (binding_to_place : Simplified_named.binding_to_place) =>
          match binding_to_place with
          | Simplified_named.Delete_binding _ => ret binding_to_place
          | Simplified_named.Keep_binding bound_vars simplified_defining_expr
              original_defining_expr =>
            let* greatest_name_mode := compute_greatest_name_mode bound_vars in
            let* declared_name_mode := Bound_pattern.name_mode bound_vars in
            let* mismatched_modes :=
              let! tmp1 := Name_mode.Or_absent.present declared_name_mode in
              let! tmp2 :=
                Name_mode.Or_absent.compare_partial_order greatest_name_mode
                  tmp1
              in
              match tmp2 with
              | None => ret true
              | Some c => ret (c >? 0)
              end
            in
            let* defining_expr :=
              Simplified_named.to_named
                simplified_defining_expr.(Simplified_named.named)
            in
            (* 159-171 *)
            (if mismatched_modes
             then
               let! tmp1 := UA.are_rebuilding_terms uacc in
               (* PORT-GAP(papp): [RE.print] is given its first argument
                  only. *)
               let! tmp2 := papp1 RE.print tmp1 in
               fatal_errorf12
                 "[Let]-binding declares variable(s) %a (mode %a) to be bound to@ %a,@ but there exist occurrences for such variable(s) at incompatible mode(s)@ (compared to %a)@ in the body (free names %a):@ %a"
                 Bound_pattern.print bound_vars Name_mode.print
                 declared_name_mode Named.print defining_expr
                 Name_mode.Or_absent.print greatest_name_mode
                 Name_occurrences.print free_names_of_body tmp2 body
             else ret tt) ;;
            let* is_end_region :=
              match defining_expr with
              | Flambda.Prim prim _ => P.is_end_region prim
              | Flambda.Simple _ | Flambda.Set_of_closures _ _
              | Flambda.Static_consts _ | Flambda.Rec_info _ =>
                ret None
              end
            in
            let* '(is_end_region_for_unused_region,
                   is_end_region_for_used_region) :=
              match is_end_region with
              | None => ret (false, false)
              | Some region =>
                let* is_used :=
                  let! tmp1 := UA.required_names uacc in
                  let! tmp2 := Name.var region in
                  Name.Set_.mem tmp2 tmp1
                in
                ret (negb is_used, is_used)
              end
            in
            let* must_be_kept_for_its_effects :=
              or_else is_end_region_for_used_region
                (and_then (negb is_end_region_for_unused_region)
                   (let! tmp1 :=
                      Named.at_most_generative_effects defining_expr
                    in
                    ret (negb tmp1)))
            in
            if must_be_kept_for_its_effects
            then
              (let! tmp1 := Name_mode.is_normal declared_name_mode in
               if negb tmp1
               then
                 fatal_errorf4
                   "Cannot [Let]-bind non-normal variable(s) to a [Named] that has more than generative effects:@ %a@ =@ %a"
                   Bound_pattern.print bound_vars Named.print defining_expr
               else ret tt) ;;
              ret binding_to_place
            else
              let* is_depth :=
                match defining_expr with
                | Flambda.Rec_info _ => ret true
                | Flambda.Simple _ | Flambda.Prim _ _
                | Flambda.Set_of_closures _ _ | Flambda.Static_consts _ =>
                  ret false
                end
              in
              let* has_uses :=
                Name_mode.Or_absent.is_present greatest_name_mode
              in
              let* can_phantomise :=
                and_then (negb is_depth)
                  (Bound_pattern.exists_all_bound_vars bound_vars
                     (fun bound_var =>
                       let! tmp1 := VB.var bound_var in
                       Variable_.user_visible tmp1))
              in
              let* will_delete_binding :=
                if is_end_region_for_unused_region
                then ret true
                else
                  ret
                    (negb
                       (has_uses || (generate_phantom_lets && can_phantomise)))
              in
              if will_delete_binding
              then ret (Simplified_named.Delete_binding original_defining_expr)
              else
                let* name_mode :=
                  match greatest_name_mode with
                  | Name_mode.Or_absent.Absent => ret Name_mode.phantom
                  | Name_mode.Or_absent.Present name_mode => ret name_mode
                  end
                in
                (let! tmp1 := Name_mode.can_be_in_terms name_mode in
                 assert_ tmp1) ;;
                let* bound_vars :=
                  Bound_pattern.with_name_mode bound_vars name_mode
                in
                (* 246-247: [{ binding with let_bound = bound_vars }] *)
                ret
                  (Simplified_named.Keep_binding bound_vars
                     simplified_defining_expr original_defining_expr)
          end)
        bindings
    in
    (* 250-320 *)
    let* '(uacc, bindings) :=
      let* '{| Flow_types.Mutable_unboxing_result.let_rewrites :=
                 let_rewrites
            |} :=
        UA.mutable_unboxing_result uacc
      in
      match_exn
        (fun _ => Named_rewrite_id.Map.find rewrite_id let_rewrites)
        Not_found
        (fun _ => ret (uacc, bindings))
        (fun rewrite =>
          (* 257-261: the compiler's two cases of a list of one binding are
             one case here, and a match on that binding (as nested patterns
             Rocq puts the match on the tail inside each case of the
             binding). *)
          match bindings with
          | [] => ret (uacc, [])
          | _ :: _ :: _ => assert_false
          | [binding] =>
          match binding with
          | Simplified_named.Delete_binding _ => ret (uacc, [binding])
          (* 261: [Keep_binding binding], and below [binding.let_bound],
             [binding.original_defining_expr] and [{ binding with ... }]: the
             fields are taken by place. *)
          | Simplified_named.Keep_binding let_bound simplified_defining_expr
              original_defining_expr =>
            match rewrite, original_defining_expr with
            | Named_rewrite.Prim_rewrite prim_rewrite,
              Some (Flambda.Prim original_prim dbg) =>
              let* uacc :=
                let! tmp1 := Removed_operations.prim original_prim in
                UA.notify_removed tmp1 uacc
              in
              let* machine_width :=
                let! tmp1 := UA.uenv uacc in
                UE.machine_width tmp1
              in
              let* new_bindings :=
                match prim_rewrite with
                | Named_rewrite.Prim_rewrite.Remove_prim =>
                  let* greatest_name_mode :=
                    compute_greatest_name_mode let_bound
                  in
                  match greatest_name_mode with
                  | Name_mode.Or_absent.Absent =>
                    ret
                      [Simplified_named.Delete_binding original_defining_expr]
                  | Name_mode.Or_absent.Present name_mode =>
                    let! tmp1 := Name_mode.is_phantom name_mode in
                    if tmp1
                    then
                      let* let_bound :=
                        Bound_pattern.with_name_mode let_bound name_mode
                      in
                      ret
                        [Simplified_named.Keep_binding let_bound
                           simplified_defining_expr original_defining_expr]
                    else
                      fatal_errorf4
                        "Binding for %a was supposed to be removed but occurs in free names:@ %a"
                        Bound_pattern.print let_bound Name_occurrences.print
                        free_names_of_body
                  end
                | Named_rewrite.Prim_rewrite.Invalid k =>
                  let& prim := P.Nullary (P.Invalid k) in
                  let* simplified_defining_expr :=
                    let! tmp1 := Named.create_prim prim dbg in
                    Simplified_named.create machine_width tmp1
                  in
                  ret
                    [Simplified_named.Keep_binding let_bound
                       simplified_defining_expr original_defining_expr]
                | Named_rewrite.Prim_rewrite.Replace_by_binding var bound_to =>
                  let* bv := Bound_pattern.must_be_singleton let_bound in
                  let* var' := Bound_var.var bv in
                  (let! tmp1 := Variable_.equal var var' in
                   assert_ tmp1) ;;
                  let* simplified_defining_expr :=
                    let! tmp1 := Named.create_simple bound_to in
                    Simplified_named.create machine_width tmp1
                  in
                  ret
                    [Simplified_named.Keep_binding let_bound
                       simplified_defining_expr original_defining_expr]
                end
              in
              ret (uacc, new_bindings)
            | Named_rewrite.Prim_rewrite _,
              ( None
              | Some
                  ( Flambda.Simple _ | Flambda.Set_of_closures _ _
                  | Flambda.Static_consts _ | Flambda.Rec_info _ ) ) =>
              fatal_errorf0 "Prim_rewrite applied to a non-prim Named.t"
            end
          end
          end)
    in
    EB.make_new_let_bindings uacc bindings body
  in
  (* Return as quickly as possible if there is nothing to do. In this case, all
     constants get floated up to an outer binding. *)
  if no_constants_to_place || negb at_unit_toplevel
  then
    let* uacc :=
      (* Avoid re-allocating [uacc] unless necessary. *)
      if no_constants_from_defining_expr
      then ret uacc
      else
        let* lifted_constants_from_body := UA.lifted_constants uacc in
        let! tmp1 :=
          LCS.union lifted_constants_from_body
            lifted_constants_from_defining_expr
        in
        UA.with_lifted_constants uacc tmp1
    in
    let* '(body, uacc) := put_bindings_around_body uacc body in
    after_rebuild body uacc
  else
    let* '(uacc, lifted_constants_from_body) :=
      UA.get_and_clear_lifted_constants uacc
    in
    let* '(body, uacc) :=
      EB.place_lifted_constants uacc lifted_constants_from_defining_expr
        lifted_constants_from_body put_bindings_around_body body
    in
    after_rebuild body uacc.

(* 348-356. In the compiler: [dacc ~rewrite_id data_flow binding]. *)
Definition record_new_defining_expression_binding_for_data_flow (dacc : DA.t)
    (rewrite_id : Named_rewrite_id.t) (data_flow : Flow.Acc.t)
    (binding : Simplified_named.binding_to_place) : M Flow.Acc.t :=
  let* generate_phantom_lets :=
    let! tmp1 := DA.denv dacc in
    DE.generate_phantom_lets tmp1
  in
  match binding with
  | Simplified_named.Delete_binding _ => ret data_flow
  | Simplified_named.Keep_binding let_bound simplified_defining_expr _ =>
    Flow.Acc.record_let_binding rewrite_id generate_phantom_lets let_bound
      simplified_defining_expr data_flow
  end.

(* 358-375. In the compiler: [dacc closure_info
   ~lifted_constants_from_defining_expr simplify_named_result ~rewrite_id
   data_flow]. *)
Definition update_data_flow (dacc : DA.t) (closure_info : Closure_info.t)
    (lifted_constants_from_defining_expr : LCS.t)
    (simplify_named_result : Simplify_named_result.t)
    (rewrite_id : Named_rewrite_id.t) (data_flow : Flow.Acc.t)
    : M Flow.Acc.t :=
  let* data_flow :=
    let! tmp1 := Closure_info.in_or_out_of_closure closure_info in
    match tmp1 with
    | Closure_info.In_a_closure =>
      (* The dependency information for lifted constants (stored in [Data_flow])
         is only required at the point when the constants are placed. That
         always happens at toplevel, never inside closures -- so we don't need
         to do anything here. *)
      ret data_flow
    | Closure_info.Not_in_a_closure_ =>
      Flow.Acc.record_lifted_constants lifted_constants_from_defining_expr
        data_flow
    end
  in
  (* 372-375: the arguments are in the order of the interface; the function
     [record_new_defining_expression_binding_for_data_flow], of this file,
     given its first two arguments only, is a value. *)
  let! tmp1 := Simplify_named_result.bindings_to_place simplify_named_result in
  ListLabels.fold_left
    (record_new_defining_expression_binding_for_data_flow dacc rewrite_id)
    data_flow tmp1.

(* 377-453. In the compiler: [~simplify_expr ~simplify_function_body dacc
   let_expr ~down_to_up bound_pattern ~body]. *)
(* PORT-GAP(loose): 379 and 457, [let module L = Flambda.Let in] is not kept:
   [L.defining_expr] and [L.pattern_match] are written [Let.defining_expr]
   and [Let.pattern_match]. *)
Definition simplify_let0
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    (dacc : DA.t) (let_expr : Let.t)
    (down_to_up : Simplify_common.down_to_up SE.t)
    (bound_pattern : Bound_pattern.t) (body : Expr.t) : M (SE.t * DA.t) :=
  let& original_dacc := dacc in
  (* Remember then clear the lifted constants memory in [DA] so we can easily
     find out which constants are generated during simplification of the
     defining expression and the [body]. *)
  let* '(dacc, prior_lifted_constants) :=
    DA.get_and_clear_lifted_constants dacc
  in
  (* Simplify the defining expression. *)
  let* defining_expr := Let.defining_expr let_expr in
  let! tmp1 :=
    Simplify_named.simplify_named dacc bound_pattern defining_expr
      simplify_function_body
  in
  match tmp1 with
  | Simplified_named.Rewritten f =>
    let! tmp1 := f body in
    simplify_expr dacc tmp1 down_to_up
  | Simplified_named.Simplified (simplify_named_result, removed_operations) =>
    (* We must make sure that if [Invalid] is going to be produced, [uacc]
       doesn't contain any extraneous data for e.g. lifted constants that will
       never be placed, since this can lead to errors when loading .cmx files or
       similar. To avoid this we don't traverse [body]. *)
    match simplify_named_result with
    | Or_invalid.Invalid =>
      let! tmp1 :=
        SE.simplified_invalid
          (Flambda.Invalid.Defining_expr_of_let bound_pattern defining_expr)
      in
      let! tmp2 := SE.notify_removed removed_operations tmp1 in
      down_to_up original_dacc tmp2
    | Or_invalid.Ok simplify_named_result =>
      let* dacc := Simplify_named_result.dacc simplify_named_result in
      (* First accumulate variable, symbol and code ID usage information. *)
      (* We currently over-approximate the use of variables in symbols: both in
         the lifted constants, and in the bound constants, which we consider to
         be always used, leading to the free_names in their defining expressions
         to be considered as used unconditionally. *)
      let* closure_info :=
        let! tmp1 := DA.denv dacc in
        DE.closure_info tmp1
      in
      (* Next remember any lifted constants that were generated during the
         simplification of the defining expression and sort them, since they may
         be mutually recursive. Then add back in to [dacc] the
         [prior_lifted_constants] remembered above. This results in the
         definitions and types for all these constants being available at a
         subsequent [Let_cont]. At such a point, [dacc] will be queried to
         retrieve all of the constants, which are then manually transferred into
         the computed [dacc] at the join point for subsequent simplification of
         the continuation handler(s).

         Note that no lifted constants are ever placed during the simplification
         of the defining expression. (Not even in the case of a
         [Set_of_closures] binding, since "let symbol" is disallowed under a
         lambda.) *)
      let* lifted_constants_from_defining_expr :=
        DA.get_lifted_constants dacc
      in
      let* dacc :=
        DA.add_to_lifted_constant_accumulator None dacc prior_lifted_constants
      in
      let* rewrite_id := Named_rewrite_id.create tt in
      (* 434-439: [update_data_flow], of this file, is given all its arguments
         but the last: the [fun] is written. *)
      let* dacc :=
        DA.map_flow_acc dacc
          (fun data_flow =>
            update_data_flow dacc closure_info
              lifted_constants_from_defining_expr simplify_named_result
              rewrite_id data_flow)
      in
      let* at_unit_toplevel :=
        let! tmp1 := DA.denv dacc in
        DE.at_unit_toplevel tmp1
      in
      (* Simplify the body of the let-expression and make the new [Let] bindings
         around the simplified body. [Simplify_named] will already have prepared
         [dacc] with the necessary bindings for the simplification of the
         body. *)
      let& down_to_up :=
        fun (dacc : DA.t) (simplified_body : SE.t) =>
        let! tmp1 :=
          Simplify_named_result.bindings_to_place simplify_named_result
        in
        let! tmp2 :=
          SE.simplified_let tmp1 removed_operations
            lifted_constants_from_defining_expr at_unit_toplevel closure_info
            rewrite_id simplified_body
        in
        down_to_up dacc tmp2
      in
      simplify_expr dacc body down_to_up
    end
  end.

(* 455-461. In the compiler: [~simplify_expr ~simplify_function_body dacc
   let_expr ~down_to_up]. *)
Definition simplify_let
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    (dacc : DA.t) (let_expr : Let.t)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  (* 458-461: [simplify_let0], of this file, is given all its arguments but
     the last two: the [fun] is written. *)
  Let.pattern_match let_expr
    (fun bound_pattern body =>
      simplify_let0 simplify_expr simplify_function_body dacc let_expr
        down_to_up bound_pattern body).
