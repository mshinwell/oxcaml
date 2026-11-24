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

(* This file follows middle_end/flambda2/simplify/simplify_named.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Bound_pattern Bound_static Bound_var
  Flambda_colours Flambda_features Format Function_slot List ListLabels Name
  Name_mode Or_invalid Printexc Reification Removed_operations Simple
  Simplified_named Simplify_common Simplify_named_result Simplify_primitive
  Simplify_rec_info_expr Simplify_set_of_closures Simplify_static_const
  Specialization_cost Stdlib_ Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 19-61 *)
(* PORT-GAP(loose): 19, the compiler's first parameter is the pattern
   [(dacc, lifted_constants)]; here it has a name and is taken apart on the
   next line (as a pattern, Rocq prints the function as [function | dacc,
   lifted_constants -> (fun pat static_const -> ...)]). *)
Definition create_lifted_constant (acc : DA.t * list LC.t)
    (pat : Bound_static.Pattern.t) (static_const : Rebuilt_static_const.t)
    : M (DA.t * list LC.t) :=
  let '(dacc, lifted_constants) := acc in
  match pat with
  | Bound_static.Pattern.Block_like symbol =>
    let* typ :=
      let! tmp1 := Name.symbol symbol in
      let! tmp2 := DA.typing_env dacc in
      TE.find tmp2 tmp1 (Some K.value)
    in
    (* The [symbol_projections] map is empty because we only introduce symbol
       projections when lifting -- and [static_const] has already been
       lifted. 32-33: the arguments are in the order of the interface. *)
    let* lifted_constant :=
      let! tmp1 := DA.typing_env dacc in
      LC.create_block_like symbol Variable_.Map.empty static_const tmp1 typ
    in
    let* dacc :=
      let! tmp1 := Rebuilt_static_const.to_const static_const in
      match tmp1 with
      | None | Some (Flambda.Code _ | Flambda.Deleted_code) => ret dacc
      | Some (Flambda.Static_const static_const) =>
        DA.consider_constant_for_sharing dacc symbol static_const
      end
    in
    ret (dacc, lifted_constant :: lifted_constants)
  | Bound_static.Pattern.Code code_id =>
    let* lifted_constant := LC.create_code code_id static_const in
    ret (dacc, lifted_constant :: lifted_constants)
  | Bound_static.Pattern.Set_of_closures closure_symbols =>
    let* closure_symbols_with_types :=
      Function_slot.Lmap.map
        (fun symbol =>
          let* typ :=
            let! tmp1 := Name.symbol symbol in
            let! tmp2 := DA.typing_env dacc in
            TE.find tmp2 tmp1 (Some K.value)
          in
          ret (symbol, typ))
        closure_symbols
    in
    (* 55-60: the arguments are in the order of the interface. *)
    let* lifted_constant :=
      let! tmp1 := DA.typing_env dacc in
      LC.create_set_of_closures tmp1 closure_symbols_with_types
        (* Same comment as above re. [symbol_projections]. *)
        Variable_.Map.empty static_const
    in
    ret (dacc, lifted_constant :: lifted_constants)
  end.

(* It is important that every set of closures returned by this function (in
   [bindings_outermost_first]) arises from simplification in
   [Simplify_set_of_closures], and not some other path such as reification. This
   ensures that the returned [dacc] is equipped with the free name information
   for such sets. See comment in [Simplify_let_expr], function [rebuild_let]. *)

(* 69-250. In the compiler: [dacc bound_pattern named
   ~simplify_function_body]. *)
Definition simplify_named0 (dacc : DA.t) (bound_pattern : Bound_pattern.t)
    (named : Named.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M (Simplified_named.or_rewritten (Or_invalid.t Simplify_named_result.t))
    :=
  (* PORT-GAP(loose): 71, the attribute [@inline] is not kept. *)
  let& ok :=
    fun (result : Simplify_named_result.t) =>
    ret (Simplified_named.Simplified (Or_invalid.Ok result))
  in
  let& invalid :=
    (Simplified_named.Simplified Or_invalid.Invalid
      : Simplified_named.or_rewritten (Or_invalid.t Simplify_named_result.t))
  in
  let* machine_width :=
    let! tmp1 := DA.denv dacc in
    DE.machine_width tmp1
  in
  match named with
  | Flambda.Simple simple =>
    let* bound_var := Bound_pattern.must_be_singleton bound_pattern in
    let* min_name_mode := Bound_var.name_mode bound_var in
    let* '(ty, new_simple) := S.simplify_simple dacc simple min_name_mode in
    let* dacc := DA.add_variable dacc bound_var ty in
    let* defining_expr :=
      let! tmp1 := phys_equal simple new_simple in
      if tmp1
      then Simplified_named.create machine_width named
      else
        let! tmp2 := Named.create_simple new_simple in
        Simplified_named.create machine_width tmp2
    in
    let! tmp1 :=
      Simplify_named_result.create dacc
        (Simplified_named.Keep_binding bound_pattern defining_expr (Some named))
    in
    ok tmp1
  | Flambda.Prim prim dbg =>
    let! tmp1 := Bound_pattern.name_mode bound_pattern in
    let! tmp2 := Name_mode.is_normal tmp1 in
    if negb tmp2
    then
      let* min_name_mode := Bound_pattern.name_mode bound_pattern in
      (* 99-110 *)
      let* defining_expr :=
        let! tmp1 :=
          P.map_args
            (fun simple =>
              let! tmp2 := S.simplify_simple dacc simple min_name_mode in
              Stdlib_.snd tmp2)
            prim
        in
        Named.create_prim tmp1 dbg
      in
      let* bound_var := Bound_pattern.must_be_singleton bound_pattern in
      let* dacc :=
        DA.map_denv dacc
          (fun denv =>
            let! tmp1 := P.result_kind' prim in
            DE.define_variable denv bound_var tmp1)
      in
      let! tmp1 := Simplified_named.create machine_width defining_expr in
      let! tmp2 :=
        Simplify_named_result.create dacc
          (Simplified_named.Keep_binding bound_pattern tmp1 (Some named))
      in
      ok tmp2
    else
      let* bound_var := Bound_pattern.must_be_singleton bound_pattern in
      (* PORT-GAP(papp): 126-131, [Specialization_cost.add_prim] is given its
         first two arguments only, and [DE.map_specialization_cost] its
         first. *)
      let* dacc :=
        let! tmp1 := papp2 Specialization_cost.add_prim bound_var prim in
        let! tmp2 := papp1 DE.map_specialization_cost tmp1 in
        DA.map_denv dacc tmp2
      in
      let* dbg :=
        let! tmp1 := DA.denv dacc in
        DE.add_inlined_debuginfo tmp1 dbg
      in
      let! tmp1 := Simplify_primitive.simplify_primitive dacc prim dbg bound_var in
      match tmp1 with
      | Simplified_named.Rewritten f => ret (Simplified_named.Rewritten f)
      | Simplified_named.Simplified
          {| SPR.simplified_named := simplified_named;
             SPR.try_reify := try_reify;
             SPR.dacc := dacc
          |} =>
        match simplified_named with
        | Or_invalid.Invalid => ret invalid
        | Or_invalid.Ok simplified_named =>
          (* 142-149 *)
          (let! tmp1 := Flambda_features.check_invariants tt in
           let! tmp2 :=
             and_then tmp1
               (let! tmp3 := Bound_var.var bound_var in
                let! tmp4 := Name.var tmp3 in
                let! tmp5 := DA.typing_env dacc in
                let! tmp6 := TE.mem None tmp5 tmp4 in
                ret (negb tmp6))
           in
           if tmp2
           then
             fatal_errorf4 "Primitive %a = %a did not yield a result var"
               Bound_var.print bound_var P.print prim
           else ret tt) ;;
          if negb try_reify
          then
            let! tmp1 :=
              Simplify_named_result.create dacc
                (Simplified_named.Keep_binding bound_pattern simplified_named
                   (Some named))
            in
            ok tmp1
          else
            (* Primitives with generative effects correspond to allocations.
               Without this check, we could end up lifting definitions that have
               a type that looks like an allocation but that are instead a
               projection from a bigger structure. *)
            let* allow_lifting :=
              let! tmp1 := P.only_generative_effects prim in
              and_then tmp1
                (let! tmp2 := Bound_var.name_mode bound_var in
                 Name_mode.is_normal tmp2)
            in
            let* '(defining_expr, dacc) :=
              let! tmp1 := P.result_kind' prim in
              Reification.try_to_reify dacc dbg simplified_named bound_var tmp1
                allow_lifting
            in
            let* result :=
              Or_invalid.map defining_expr
                (fun defining_expr =>
                  Simplify_named_result.create dacc
                    (Simplified_named.Keep_binding bound_pattern defining_expr
                       (Some named)))
            in
            ret (Simplified_named.Simplified result)
        end
      end
  | Flambda.Set_of_closures set_of_closures alloc_mode =>
    let! tmp1 :=
      Simplify_set_of_closures.simplify_non_lifted_set_of_closures dacc
        bound_pattern set_of_closures alloc_mode simplify_function_body
    in
    ok tmp1
  | Flambda.Static_consts static_consts =>
    let* bound_static := Bound_pattern.must_be_static bound_pattern in
    let* binds_symbols := Bound_static.binds_symbols bound_static in
    (* 193-198 *)
    (let! tmp1 :=
       and_then binds_symbols
         (let! tmp2 := DA.denv dacc in
          let! tmp3 := DE.at_unit_toplevel tmp2 in
          ret (negb tmp3))
     in
     if tmp1
     then
       fatal_errorf4
         "[Let] binding symbols is only allowed at the toplevel of compilation units (not even at the toplevel of function bodies):@ %a@ =@ %a"
         Bound_pattern.print bound_pattern Named.print named
     else ret tt) ;;
    (* 199-212 *)
    let* '(T3 bound_static static_consts dacc) :=
      try_with
        (fun _ =>
          Simplify_static_const.simplify_static_consts dacc bound_static
            static_consts simplify_function_body)
        Fatal_error
        (fun _ =>
          let* bt := Printexc.get_raw_backtrace tt in
          Format.eprintf6
            "
%tContext is:%t simplifying 'let symbol' binding of@ %a@ with downwards accumulator:@ %a
"
            Flambda_colours.error Flambda_colours.pop Bound_static.print
            bound_static DA.print dacc ;;
          (* 211: the value [Misc.Fatal_error] is [exn_make Fatal_error
             tt]. *)
          Printexc.raise_with_backtrace (exn_make Fatal_error tt) bt)
    in
    (* 213-218: the arguments are in the order of the interface. *)
    let* '(dacc, lifted_constants) :=
      let! tmp1 := Rebuilt_static_const.Group.to_list static_consts in
      let! tmp2 := Bound_static.to_list bound_static in
      ListLabels.fold_left2 create_lifted_constant (dacc, []) tmp2 tmp1
    in
    let* dacc :=
      let! tmp1 := LC.concat lifted_constants in
      let! tmp2 := LCS.singleton tmp1 in
      DA.add_to_lifted_constant_accumulator None dacc tmp2
    in
    (* We don't need to return any bindings; [Simplify_expr.simplify_let] will
       create the "let symbol" binding when it sees the lifted constant. *)
    let! tmp1 := Simplify_named_result.create_empty dacc in
    ok tmp1
  | Flambda.Rec_info rec_info_expr =>
    (* We could simplify away things like [let depth x = y in ...], but those
       don't actually happen (as of this writing). We could also do CSE,
       though. *)
    let* bound_var := Bound_pattern.must_be_singleton bound_pattern in
    let* new_rec_info_expr :=
      Simplify_rec_info_expr.simplify_rec_info_expr dacc rec_info_expr
    in
    let* ty := T.this_rec_info new_rec_info_expr in
    let* dacc := DA.add_variable dacc bound_var ty in
    let* machine_width :=
      let! tmp1 := DA.denv dacc in
      DE.machine_width tmp1
    in
    let* defining_expr :=
      let! tmp1 := phys_equal rec_info_expr new_rec_info_expr in
      if tmp1
      then Simplified_named.create machine_width named
      else
        let! tmp2 := Named.create_rec_info new_rec_info_expr in
        Simplified_named.create machine_width tmp2
    in
    let! tmp1 :=
      Simplify_named_result.create dacc
        (Simplified_named.Keep_binding bound_pattern defining_expr (Some named))
    in
    ok tmp1
  end.

(* 252-315. In the compiler: [~min_name_mode ~original dacc result]. *)
Definition removed_operations (min_name_mode : Name_mode.t)
    (original : Named.t) (dacc : DA.t)
    (result : Or_invalid.t Simplify_named_result.t) : M Removed_operations.t :=
  let& zero := Removed_operations.zero in
  match result with
  | Or_invalid.Invalid =>
    (* We're not removing any instructions that would actually have been
       executed. *)
    ret zero
  | Or_invalid.Ok result =>
    match original with
    | Flambda.Set_of_closures _ _ =>
      let! tmp1 := Simplify_named_result.was_lifted_set_of_closures result in
      let! tmp2 := or_else tmp1 (Simplify_named_result.no_bindings result) in
      if tmp2 then ret Removed_operations.alloc else ret zero
    | Flambda.Static_consts _ =>
      (* There are no operations to remove in a [Static_consts] binding. *)
      ret zero
    | Flambda.Simple _ =>
      (* [Simple]s only simplify to other [Simple]s. *)
      ret zero
    | Flambda.Prim original_prim _ =>
      let! tmp1 := Simplify_named_result.bindings_to_place result in
      let! tmp2 :=
        List.exists_
          (fun (binding : Simplified_named.binding_to_place) =>
            match binding with
            | Simplified_named.Keep_binding _
                {| Simplified_named.named :=
                     Simplified_named.Prim rewritten_prim _
                |} _ =>
              (* Do not consider the original primitive to have been removed if
                 there is a rewritten primitive that is equivalent modulo
                 changes of canonical names.

                 Previously, we simply checked the equality of [original_prim]
                 and [rewritten_prim], but this meant that a primitive [%prim
                 param] that gets transformed into [%prim arg] due to inlining
                 was counted as having been removed. *)
              let* c :=
                Flambda_primitive.compare_primitive_application
                  (fun original_simple rewritten_simple =>
                    let* '(_, original_simple) :=
                      S.simplify_simple dacc original_simple min_name_mode
                    in
                    let* '(_, rewritten_simple) :=
                      S.simplify_simple dacc rewritten_simple min_name_mode
                    in
                    Simple.compare original_simple rewritten_simple)
                  original_prim rewritten_prim
              in
              ret (c =? 0)
            | Simplified_named.Keep_binding _
                {| Simplified_named.named :=
                     ( Simplified_named.Simple _
                     | Simplified_named.Set_of_closures _ _
                     | Simplified_named.Rec_info _ )
                |} _
            | Simplified_named.Delete_binding _ =>
              ret false
            end)
          tmp1
      in
      if tmp2 then ret zero else Removed_operations.prim original_prim
    | Flambda.Rec_info _ => ret zero
    end
  end.

(* 317-333. In the compiler: [dacc bound_pattern named
   ~simplify_function_body]. *)
Definition simplify_named (dacc : DA.t) (bound_pattern : Bound_pattern.t)
    (named : Named.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M (Simplified_named.or_rewritten
           (Or_invalid.t Simplify_named_result.t * Removed_operations.t)) :=
  match_exn
    (fun _ => simplify_named0 dacc bound_pattern named simplify_function_body)
    Fatal_error
    (fun _ =>
      let* bt := Printexc.get_raw_backtrace tt in
      Format.eprintf8
        "
%tContext is:%t simplifying [Let] binding@ %a =@ %a@ with downwards accumulator:@ %a
"
        Flambda_colours.error Flambda_colours.pop Bound_pattern.print
        bound_pattern Named.print named DA.print dacc ;;
      Printexc.raise_with_backtrace (exn_make Fatal_error tt) bt)
    (fun x =>
      match x with
      | Simplified_named.Rewritten f => ret (Simplified_named.Rewritten f)
      | Simplified_named.Simplified result =>
        let* min_name_mode := Bound_pattern.name_mode bound_pattern in
        let! tmp1 := removed_operations min_name_mode named dacc result in
        ret (Simplified_named.Simplified (result, tmp1))
      end).
