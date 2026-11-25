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
(*   special exception on linking described in the file LICENSDE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/lifting/reification.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Bound_var Coercion Current_unit Debuginfo
  Flambda Flambda_features List ListLabels Mutability Name Name_mode Option
  Or_invalid Or_variable Simple Simplified_named Symbol Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda.static_const_or_code
   Flambda2_types.reification_result Flambda2_types.to_lift *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 19-93 *)
Definition create_static_const (dacc : DA.t) (dbg : Debuginfo.t)
    (to_lift : T.to_lift) : M RSC.t :=
  (* PORT-GAP(loose): 20, the attribute [@inline always] is not kept.
     21, [ListLabels.map fields ~f]: the arguments are in the order of the
     interface. *)
  let& convert_fields :=
    fun (fields : list Simple.t) =>
    ListLabels.map
      (fun (field : Simple.t) =>
        Simple.pattern_match' field
          (fun _var coercion =>
            let! tmp1 := Coercion.is_id coercion in
            if negb tmp1
            then
              fatal_errorf2 "Expected identity coercion on variable:@ %a"
                Simple.print field
            else ret tt)
          (fun _sym coercion =>
            let! tmp1 := Coercion.is_id coercion in
            if negb tmp1
            then
              fatal_errorf2 "Expected identity coercion on symbol:@ %a"
                Simple.print field
            else ret tt)
          (fun _const => ret tt) ;;
        Simple.With_debuginfo.create field dbg)
      fields
  in
  (* 36-37 *)
  let* art := DA.are_rebuilding_terms dacc in
  let* machine_width :=
    let! tmp1 := DA.denv dacc in
    DE.machine_width tmp1
  in
  (* 38-93 *)
  match to_lift with
  | T.Immutable_block tag is_unique shape fields =>
    let* fields := convert_fields fields in
    let& mut :=
      if is_unique then Mutability.Immutable_unique else Mutability.Immutable
    in
    RSC.create_block art tag mut shape fields
  | T.Boxed_float32 f =>
    RSC.create_boxed_float32 art machine_width (Or_variable.Const f)
  | T.Boxed_float f =>
    RSC.create_boxed_float art machine_width (Or_variable.Const f)
  | T.Boxed_int32 i =>
    RSC.create_boxed_int32 art machine_width (Or_variable.Const i)
  | T.Boxed_int64 i =>
    RSC.create_boxed_int64 art machine_width (Or_variable.Const i)
  | T.Boxed_nativeint i =>
    RSC.create_boxed_nativeint art machine_width (Or_variable.Const i)
  | T.Boxed_vec128 v =>
    RSC.create_boxed_vec128 art machine_width (Or_variable.Const v)
  | T.Boxed_vec256 v =>
    RSC.create_boxed_vec256 art machine_width (Or_variable.Const v)
  | T.Boxed_vec512 v =>
    RSC.create_boxed_vec512 art machine_width (Or_variable.Const v)
  | T.Boxed_mask v =>
    RSC.create_boxed_mask art machine_width (Or_variable.Const v)
  | T.Immutable_float32_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_float32_array art fields
  | T.Immutable_float_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_float_array art fields
  | T.Immutable_int_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_int_array art fields
  | T.Immutable_int8_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_int8_array art fields
  | T.Immutable_int16_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_int16_array art fields
  | T.Immutable_int32_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_int32_array art fields
  | T.Immutable_int64_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_int64_array art fields
  | T.Immutable_nativeint_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_nativeint_array art fields
  | T.Immutable_vec128_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_vec128_array art fields
  | T.Immutable_vec256_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_vec256_array art fields
  | T.Immutable_vec512_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_vec512_array art fields
  | T.Immutable_mask_array fields =>
    let* fields := List.map (fun f => ret (Or_variable.Const f)) fields in
    RSC.create_immutable_mask_array art fields
  | T.Immutable_value_array fields =>
    let* fields := convert_fields fields in
    RSC.create_immutable_value_array art fields
  | T.Empty_array array_kind => RSC.create_empty_array art array_kind
  end.

(* 95-154. In the compiler: [dacc ty ~bound_to static_const]. *)
Definition lift (dacc : DA.t) (ty : T.t) (bound_to : Variable_.t)
    (static_const : RSC.t) : M (Or_invalid.t Simplified_named.t * DA.t) :=
  (* 96-145 *)
  let* '(dacc, symbol) :=
    let* existing_symbol :=
      let! tmp1 := RSC.to_const static_const in
      match tmp1 with
      | None => ret None
      | Some (Flambda.Code _) | Some Flambda.Deleted_code => ret None
      | Some (Flambda.Static_const const) =>
        DA.find_shareable_constant dacc const
      end
    in
    match existing_symbol with
    | Some symbol =>
      (* 105-111 *)
      (let! tmp1 := Flambda_features.check_invariants tt in
       let! tmp2 :=
         and_then tmp1
           (let! tmp3 := DA.denv dacc in
            let! tmp4 := DE.mem_symbol tmp3 symbol in
            ret (negb tmp4))
       in
       if tmp2
       then
         fatal_errorf4
           "Constant with symbol %a is shareable but not in the environment:@ %a"
           Symbol.print symbol DA.print dacc
       else ret tt) ;;
      ret (dacc, symbol)
    | None =>
      (* 114-118 *)
      let* symbol :=
        let! tmp1 := Variable_.canonical_name bound_to in
        let! tmp2 := Current_unit.get_cu_exn tt in
        Symbol.manufacture tmp2 tmp1
      in
      (* 119-122 *)
      (let! tmp1 := T.kind ty in
       let! tmp2 := K.equal tmp1 K.value in
       if negb tmp2
       then
         fatal_errorf2 "Cannot lift non-[Value] variable: %a" Variable_.print
           bound_to
       else ret tt) ;;
      (* 123-130 *)
      let* symbol_projections :=
        let* free_names := RSC.free_names static_const in
        NO.fold_variables free_names Variable_.Map.empty
          (fun symbol_projections var =>
            let! tmp1 := DA.denv dacc in
            let! tmp2 := DE.find_symbol_projection tmp1 var in
            match tmp2 with
            | None => ret symbol_projections
            | Some proj => Variable_.Map.add var proj symbol_projections
            end)
      in
      (* 131-137: [a |> f b] is [f b a]; the arguments are in the order of
         the interfaces. *)
      let* dacc :=
        let* denv := DA.denv dacc in
        let! tmp1 := DE.typing_env denv in
        let! tmp2 :=
          LC.create_block_like symbol symbol_projections static_const tmp1 ty
        in
        let! tmp3 := LCS.singleton tmp2 in
        DA.add_to_lifted_constant_accumulator (Some tt) dacc tmp3
      in
      (* 138-143 *)
      let* dacc :=
        let! tmp1 := RSC.to_const static_const in
        match tmp1 with
        | None | Some (Flambda.Code _) | Some Flambda.Deleted_code => ret dacc
        | Some (Flambda.Static_const static_const) =>
          DA.consider_constant_for_sharing dacc symbol static_const
        end
      in
      ret (dacc, symbol)
    end
  in
  (* 146-154 *)
  let* symbol := Simple.symbol symbol in
  let* term := Named.create_simple symbol in
  let* var_ty :=
    let! tmp1 := T.kind ty in
    T.alias_type_of tmp1 symbol
  in
  let* dacc :=
    DA.map_denv dacc
      (fun denv => DE.add_equation_on_variable denv bound_to var_ty)
  in
  let* machine_width :=
    let! tmp1 := DA.denv dacc in
    DE.machine_width tmp1
  in
  let! tmp1 := Simplified_named.create machine_width term in
  ret (Or_invalid.Ok tmp1, dacc).

(* 156-199 *)
Definition try_to_reify (dacc : DA.t) (dbg : Debuginfo.t)
    (term : Simplified_named.t) (bound_to : Bound_var.t)
    (kind_of_bound_to : Flambda_kind.t) (allow_lifting : bool)
    : M (Or_invalid.t Simplified_named.t * DA.t) :=
  let* occ_kind := Bound_var.name_mode bound_to in
  let* bound_to := Bound_var.var bound_to in
  let* denv := DA.denv dacc in
  (* 161-163 *)
  let* ty :=
    let! tmp1 := Name.var bound_to in
    let! tmp2 := DE.typing_env denv in
    TE.find tmp2 tmp1 (Some kind_of_bound_to)
  in
  let* typing_env := DE.typing_env denv in
  (* 165-172 *)
  let* reify_result :=
    T.reify typing_env
      (fun var => DE.is_defined_at_toplevel denv var)
      (fun var =>
        let! tmp1 := DE.find_symbol_projection denv var in
        Option.is_some tmp1)
      typing_env ty
  in
  (* 173-199 *)
  match reify_result with
  | T.Lift to_lift =>
    let! tmp1 := Name_mode.is_normal occ_kind in
    if tmp1 && allow_lifting
    then
      let* static_const := create_static_const dacc dbg to_lift in
      lift dacc ty bound_to static_const
    else ret (Or_invalid.Ok term, dacc)
  | T.Simple simple =>
    (* 180: the guard [when Simple.equal simple (Simple.var bound_to)]. *)
    let! tmp1 := Simple.var bound_to in
    let! tmp2 := Simple.equal simple tmp1 in
    if tmp2
    then
      (* This could happen if [ty] is an alias type to a canonical that has
         [In_types], meaning that it cannot be returned when reifying at mode
         [Normal] as we are here. However, since the equations arising from
         simplification of the primitive (in our caller) have already been
         added to the environment, [bound_to] can in fact be returned by
         [get_canonical_simple] during [T.reify]. As such we need to catch
         this case here to avoid creating circular let-bindings. *)
      ret (Or_invalid.Ok term, dacc)
    else
      (* 190-197 *)
      let* dacc :=
        let* ty :=
          let! tmp1 := T.kind ty in
          T.alias_type_of tmp1 simple
        in
        let* denv := DE.add_equation_on_variable denv bound_to ty in
        DA.with_denv dacc denv
      in
      let* machine_width :=
        let! tmp1 := DA.denv dacc in
        DE.machine_width tmp1
      in
      let! tmp1 := Named.create_simple simple in
      let! tmp2 := Simplified_named.create machine_width tmp1 in
      ret (Or_invalid.Ok tmp2, dacc)
  | T.Cannot_reify => ret (Or_invalid.Ok term, dacc)
  | T.Invalid_ => ret (Or_invalid.Invalid, dacc)
  end.
