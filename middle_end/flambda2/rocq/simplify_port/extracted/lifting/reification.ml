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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/lifting/Reification.v, which follows
   middle_end/flambda2/simplify/lifting/reification.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import
open Port_monad

(** val create_static_const : DA.t -> Debuginfo.t -> T.to_lift -> RSC.t coq_M **)

let create_static_const dacc dbg to_lift =
  let convert_fields =
   fun fields ->
    ListLabels.map
      (fun field ->
        let () =
          Simple.pattern_match' field
            (fun _ coercion ->
              if not (Coercion.is_id coercion)
              then
                Misc.fatal_errorf "Expected identity coercion on variable:@ %a"
                  Simple.print field
              else ())
            (fun _ coercion ->
              if not (Coercion.is_id coercion)
              then
                Misc.fatal_errorf "Expected identity coercion on symbol:@ %a"
                  Simple.print field
              else ())
            (fun _ -> ())
        in
        Simple.With_debuginfo.create field dbg)
      fields
  in
  let art = DA.are_rebuilding_terms dacc in
  let machine_width = DE.machine_width (DA.denv dacc) in
  (fun f__1
    f__2
    f__3
    f__4
    f__5
    f__6
    f__7
    f__8
    f__9
    f__10
    f__11
    f__12
    f__13
    f__14
    f__15
    f__16
    f__17
    f__18
    f__19
    f__20
    f__21
    f__22
    f__23
    f__24
    x__0
  ->
    match (x__0 : T.to_lift) with
    | T.Immutable_block
        { tag = x__1; is_unique = x__2; shape = x__3; fields = x__4 } ->
      f__1 x__1 x__2 x__3 x__4
    | T.Boxed_float32 x__1 -> f__2 x__1
    | T.Boxed_float x__1 -> f__3 x__1
    | T.Boxed_int32 x__1 -> f__4 x__1
    | T.Boxed_int64 x__1 -> f__5 x__1
    | T.Boxed_nativeint x__1 -> f__6 x__1
    | T.Boxed_vec128 x__1 -> f__7 x__1
    | T.Boxed_vec256 x__1 -> f__8 x__1
    | T.Boxed_vec512 x__1 -> f__9 x__1
    | T.Boxed_mask x__1 -> f__10 x__1
    | T.Immutable_float32_array { fields = x__1 } -> f__11 x__1
    | T.Immutable_float_array { fields = x__1 } -> f__12 x__1
    | T.Immutable_int_array { fields = x__1 } -> f__13 x__1
    | T.Immutable_int8_array { fields = x__1 } -> f__14 x__1
    | T.Immutable_int16_array { fields = x__1 } -> f__15 x__1
    | T.Immutable_int32_array { fields = x__1 } -> f__16 x__1
    | T.Immutable_int64_array { fields = x__1 } -> f__17 x__1
    | T.Immutable_nativeint_array { fields = x__1 } -> f__18 x__1
    | T.Immutable_vec128_array { fields = x__1 } -> f__19 x__1
    | T.Immutable_vec256_array { fields = x__1 } -> f__20 x__1
    | T.Immutable_vec512_array { fields = x__1 } -> f__21 x__1
    | T.Immutable_mask_array { fields = x__1 } -> f__22 x__1
    | T.Immutable_value_array { fields = x__1 } -> f__23 x__1
    | T.Empty_array x__1 -> f__24 x__1)
    (fun tag is_unique shape fields ->
      let fields0 = convert_fields fields in
      let mut =
        if is_unique then Mutability.Immutable_unique else Mutability.Immutable
      in
      RSC.create_block art tag mut shape fields0)
    (fun f -> RSC.create_boxed_float32 art machine_width (Or_variable.Const f))
    (fun f -> RSC.create_boxed_float art machine_width (Or_variable.Const f))
    (fun i -> RSC.create_boxed_int32 art machine_width (Or_variable.Const i))
    (fun i -> RSC.create_boxed_int64 art machine_width (Or_variable.Const i))
    (fun i ->
      RSC.create_boxed_nativeint art machine_width (Or_variable.Const i))
    (fun v -> RSC.create_boxed_vec128 art machine_width (Or_variable.Const v))
    (fun v -> RSC.create_boxed_vec256 art machine_width (Or_variable.Const v))
    (fun v -> RSC.create_boxed_vec512 art machine_width (Or_variable.Const v))
    (fun v -> RSC.create_boxed_mask art machine_width (Or_variable.Const v))
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_float32_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_float_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_int_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_int8_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_int16_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_int32_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_int64_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_nativeint_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_vec128_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_vec256_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_vec512_array art fields0)
    (fun fields ->
      let fields0 = List.map (fun f -> Or_variable.Const f) fields in
      RSC.create_immutable_mask_array art fields0)
    (fun fields ->
      let fields0 = convert_fields fields in
      RSC.create_immutable_value_array art fields0)
    (fun array_kind -> RSC.create_empty_array art array_kind)
    to_lift

(** val lift : DA.t -> T.t -> Variable.t -> RSC.t -> (Simplified_named.t
    Or_invalid.t * DA.t) coq_M **)

let lift dacc ty bound_to static_const =
  let dacc0, symbol =
    let existing_symbol =
      match RSC.to_const static_const with
      | Some t0 -> (
        match t0 with
        | Code _ -> None
        | Deleted_code -> None
        | Static_const const -> DA.find_shareable_constant dacc const)
      | None -> None
    in
    match existing_symbol with
    | Some symbol ->
      let () =
        if
          Flambda_features.check_invariants ()
          && not (DE.mem_symbol (DA.denv dacc) symbol)
        then
          Misc.fatal_errorf
            "Constant with symbol %a is shareable but not in the environment:@ \
             %a"
            Symbol.print symbol DA.print dacc
        else ()
      in
      dacc, symbol
    | None ->
      let symbol =
        Symbol.manufacture
          (Current_unit.get_cu_exn ())
          (Variable.canonical_name bound_to)
      in
      let () =
        if not (K.equal (T.kind ty) K.value)
        then
          Misc.fatal_errorf "Cannot lift non-[Value] variable: %a"
            Variable.print bound_to
        else ()
      in
      let symbol_projections =
        let free_names = RSC.free_names static_const in
        NO.fold_variables free_names Variable.Map.empty
          (fun symbol_projections var ->
            match DE.find_symbol_projection (DA.denv dacc) var with
            | Some proj -> Variable.Map.add var proj symbol_projections
            | None -> symbol_projections)
      in
      let dacc0 =
        let denv = DA.denv dacc in
        (fun x__1 x__2 x__3 ->
          DA.add_to_lifted_constant_accumulator ?also_add_to_env:x__1 x__2 x__3)
          (Some ()) dacc
          (LCS.singleton
             (LC.create_block_like symbol symbol_projections static_const
                (DE.typing_env denv) ty))
      in
      let dacc1 =
        match RSC.to_const static_const with
        | Some t0 -> (
          match t0 with
          | Code _ -> dacc0
          | Deleted_code -> dacc0
          | Static_const static_const0 ->
            DA.consider_constant_for_sharing dacc0 symbol static_const0)
        | None -> dacc0
      in
      dacc1, symbol
  in
  let symbol0 = Simple.symbol symbol in
  let term = Named.create_simple symbol0 in
  let var_ty = T.alias_type_of (T.kind ty) symbol0 in
  let dacc1 =
    DA.map_denv dacc0 (fun denv ->
        DE.add_equation_on_variable denv bound_to var_ty)
  in
  let machine_width = DE.machine_width (DA.denv dacc1) in
  Or_invalid.Ok (Simplified_named.create machine_width term), dacc1

(** val try_to_reify : DA.t -> Debuginfo.t -> Simplified_named.t -> Bound_var.t
    -> Flambda_kind.t -> bool -> (Simplified_named.t Or_invalid.t * DA.t) coq_M
    **)

let try_to_reify dacc dbg term bound_to kind_of_bound_to allow_lifting =
  let occ_kind = Bound_var.name_mode bound_to in
  let bound_to0 = Bound_var.var bound_to in
  let denv = DA.denv dacc in
  let ty =
    TE.find (DE.typing_env denv) (Name.var bound_to0) (Some kind_of_bound_to)
  in
  let typing_env = DE.typing_env denv in
  let reify_result =
    T.reify typing_env
      (fun var -> DE.is_defined_at_toplevel denv var)
      (fun var -> Option.is_some (DE.find_symbol_projection denv var))
      typing_env ty
  in
  match reify_result with
  | T.Lift to_lift ->
    if Name_mode.is_normal occ_kind && allow_lifting
    then
      let static_const = create_static_const dacc dbg to_lift in
      lift dacc ty bound_to0 static_const
    else Or_invalid.Ok term, dacc
  | T.Simple simple ->
    if Simple.equal simple (Simple.var bound_to0)
    then Or_invalid.Ok term, dacc
    else
      let dacc0 =
        let ty0 = T.alias_type_of (T.kind ty) simple in
        let denv0 = DE.add_equation_on_variable denv bound_to0 ty0 in
        DA.with_denv dacc denv0
      in
      let machine_width = DE.machine_width (DA.denv dacc0) in
      ( Or_invalid.Ok
          (Simplified_named.create machine_width (Named.create_simple simple)),
        dacc0 )
  | T.Cannot_reify -> Or_invalid.Ok term, dacc
  | T.Invalid -> Or_invalid.Invalid, dacc
