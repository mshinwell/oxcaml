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

(* This file follows middle_end/flambda2/simplify/simplify_static_const.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda.
Import Flambda.Import_.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Are_rebuilding_terms Array
  Bound_name Bound_static Code_id Flambda_features Function_slot List
  Mutability Name Name_mode Or_unknown_or_bottom Or_variable Simple
  Simplify_common Simplify_set_of_closures Symbol Tag Target_ocaml_int
  Target_system.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda_kind.Scannable_block_shape.t
   Or_unknown_or_bottom.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17-18 *)
(*OCAML
open! Flambda.Import
open! Simplify_import
OCAML*)

(* 20-38 *)
Definition simplify_field_of_block (dacc : DA.t)
    '((field, expected_kind) : Simple.With_debuginfo.t * K.t)
    : M (Simple.With_debuginfo.t * T.t) :=
  let* '(ty, simple) :=
    let! tmp1 := Simple.With_debuginfo.simple field in
    S.simplify_simple dacc tmp1 Name_mode.normal
  in
  let* field :=
    let! tmp1 := Simple.With_debuginfo.dbg field in
    Simple.With_debuginfo.create simple tmp1
  in
  (* We would like to prevent kind mismatches at toplevel, since they will
     turn into programs that potentially always fail with an invalid
     trap. *)
  (let! tmp1 := T.kind ty in
   let! tmp2 := K.equal tmp1 expected_kind in
   if negb tmp2
   then
     fatal_errorf4
       "Kind %a specified for a field of a static block, but the field has type:@ %a"
       K.print expected_kind T.print ty
   else ret tt) ;;
  ret (field, ty).

(* 40-47 *)
Definition simplify_or_variable {A : Type} (dacc : DA.t)
    (type_for_const : A -> M T.t) (or_variable : Or_variable.t A)
    (kind : K.t) : M (Or_variable.t A * T.t) :=
  let* denv := DA.denv dacc in
  match or_variable with
  | Or_variable.Const const =>
    let! tmp1 := type_for_const const in
    ret (or_variable, tmp1)
  | Or_variable.Var var _dbg =>
    let! tmp1 := Name.var var in
    let! tmp2 := DE.typing_env denv in
    let! tmp3 := TE.find tmp2 tmp1 (Some kind) in
    ret (or_variable, tmp3)
  end.

(* 49-64. In the compiler: [dacc ~bind_result_sym kind type_creator creator
   ~fields]. *)
Definition rebuild_naked_number_array {A : Type} (dacc : DA.t)
    (bind_result_sym : T.t -> M DA.t) (kind : KS.t)
    (type_creator : A -> M T.t)
    (creator : Are_rebuilding_terms.t -> list (Or_variable.t A) -> M RSC.t)
    (fields : list (Or_variable.t A)) : M (RSC.t * DA.t) :=
  (* 51-57: [a |> f] is [f a]. *)
  let* '(fields, field_tys) :=
    let* kind := KS.kind kind in
    let! tmp1 :=
      List.map
        (fun field => simplify_or_variable dacc type_creator field kind)
        fields
    in
    List.split tmp1
  in
  (* 58-63 *)
  let* dacc :=
    let* machine_width :=
      let! tmp1 := DA.denv dacc in
      DE.machine_width tmp1
    in
    let! tmp1 :=
      T.immutable_array (Or_unknown_or_bottom.Ok kind) field_tys
        Alloc_mode.For_types.heap machine_width
    in
    bind_result_sym tmp1
  in
  let! tmp1 := DA.are_rebuilding_terms dacc in
  let! tmp2 := creator tmp1 fields in
  ret (tmp2, dacc).

(* 66-78. In the compiler: [~machine_width ~tag ~fields ~shape
   ~is_mutable]. *)
Definition simplify_static_const_block_type
    (machine_width : Target_system.Machine_width.t) (tag : Tag.Scannable.t)
    (fields : list T.t) (shape : K.Scannable_block_shape.t)
    (is_mutable : Mutability.t) : M T.t :=
  (* Similar to Simplify_variadic_primitive.simplify_make_block_of_values *)
  let* tag := Tag.Scannable.to_tag tag in
  let& shape := K.Block_shape.Scannable shape in
  match is_mutable with
  | Mutability.Immutable =>
    T.immutable_block machine_width false tag shape
      Alloc_mode.For_types.heap fields
  | Mutability.Immutable_unique =>
    T.immutable_block machine_width true tag shape Alloc_mode.For_types.heap
      fields
  | Mutability.Mutable => T.mutable_block Alloc_mode.For_types.heap
  end.

(* 80-308. In the compiler: [dacc static_const ~result_sym]. *)
Definition simplify_static_const_of_kind_value (dacc : DA.t)
    (static_const : Static_const.t) (result_sym : Symbol.t)
    : M (Rebuilt_static_const.t * DA.t) :=
  let& bind_result_sym :=
    fun (typ : T.t) =>
    DA.map_denv dacc
      (fun denv =>
        let* denv := DE.define_symbol denv result_sym K.value in
        DE.add_equation_on_symbol denv result_sym typ)
  in
  match static_const with
  | Static_const.Block tag is_mutable shape fields =>
    (* 89-98 *)
    let* fields_with_tys :=
      let* fields_with_kinds :=
        match shape with
        | K.Scannable_block_shape.Value_only =>
          List.map (fun field => ret (field, K.value)) fields
        | K.Scannable_block_shape.Mixed_record shape =>
          let! tmp1 := K.Mixed_block_shape.field_kinds shape in
          let! tmp2 := Array.to_list tmp1 in
          List.combine fields tmp2
        end
      in
      List.map (simplify_field_of_block dacc) fields_with_kinds
    in
    let* '(fields, field_tys) := List.split fields_with_tys in
    (* 100-103: the arguments are in the order of the definition. *)
    let* ty :=
      let! tmp1 := DA.denv dacc in
      let! tmp2 := DE.machine_width tmp1 in
      simplify_static_const_block_type tmp2 tag field_tys shape is_mutable
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.are_rebuilding_terms dacc in
    let! tmp2 :=
      Rebuilt_static_const.create_block tmp1 tag is_mutable shape fields
    in
    ret (tmp2, dacc)
  | Static_const.Boxed_float32 or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_float32 f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 := Rebuilt_static_const.create_boxed_float32 tmp3 tmp2 or_var in
    ret (tmp4, dacc)
  | Static_const.Boxed_float or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_float f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 := Rebuilt_static_const.create_boxed_float tmp3 tmp2 or_var in
    ret (tmp4, dacc)
  | Static_const.Boxed_int32 or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_int32 f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 := Rebuilt_static_const.create_boxed_int32 tmp3 tmp2 or_var in
    ret (tmp4, dacc)
  | Static_const.Boxed_int64 or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_int64 f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 := Rebuilt_static_const.create_boxed_int64 tmp3 tmp2 or_var in
    ret (tmp4, dacc)
  | Static_const.Boxed_nativeint or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_nativeint f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 :=
      Rebuilt_static_const.create_boxed_nativeint tmp3 tmp2 or_var
    in
    ret (tmp4, dacc)
  | Static_const.Boxed_vec128 or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_vec128 f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 := Rebuilt_static_const.create_boxed_vec128 tmp3 tmp2 or_var in
    ret (tmp4, dacc)
  | Static_const.Boxed_vec256 or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_vec256 f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 := Rebuilt_static_const.create_boxed_vec256 tmp3 tmp2 or_var in
    ret (tmp4, dacc)
  | Static_const.Boxed_vec512 or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_vec512 f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 := Rebuilt_static_const.create_boxed_vec512 tmp3 tmp2 or_var in
    ret (tmp4, dacc)
  | Static_const.Boxed_mask or_var =>
    let* '(or_var, ty) :=
      simplify_or_variable dacc
        (fun f => T.this_boxed_mask f Alloc_mode.For_types.heap)
        or_var K.value
    in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := DA.are_rebuilding_terms dacc in
    let! tmp4 := Rebuilt_static_const.create_boxed_mask tmp3 tmp2 or_var in
    ret (tmp4, dacc)
  | Static_const.Immutable_float_block fields =>
    let* fields_with_tys :=
      List.map
        (fun field =>
          simplify_or_variable dacc
            (fun f => T.this_naked_float f)
            field K.naked_float)
        fields
    in
    let* '(fields, _field_tys) := List.split fields_with_tys in
    let* dacc := bind_result_sym T.any_value in
    let! tmp1 := DA.are_rebuilding_terms dacc in
    let! tmp2 :=
      Rebuilt_static_const.create_immutable_float_block tmp1 fields
    in
    ret (tmp2, dacc)
  | Static_const.Immutable_float_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_float
      T.this_naked_float RSC.create_immutable_float_array fields
  | Static_const.Immutable_float32_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_float32
      T.this_naked_float32 RSC.create_immutable_float32_array fields
  | Static_const.Immutable_int_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_immediate
      T.this_naked_immediate RSC.create_immutable_int_array fields
  | Static_const.Immutable_int8_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_int8
      T.this_naked_int8 RSC.create_immutable_int8_array fields
  | Static_const.Immutable_int16_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_int16
      T.this_naked_int16 RSC.create_immutable_int16_array fields
  | Static_const.Immutable_int32_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_int32
      T.this_naked_int32 RSC.create_immutable_int32_array fields
  | Static_const.Immutable_int64_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_int64
      T.this_naked_int64 RSC.create_immutable_int64_array fields
  | Static_const.Immutable_nativeint_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_nativeint
      T.this_naked_nativeint RSC.create_immutable_nativeint_array fields
  | Static_const.Immutable_vec128_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_vec128
      T.this_naked_vec128 RSC.create_immutable_vec128_array fields
  | Static_const.Immutable_vec256_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_vec256
      T.this_naked_vec256 RSC.create_immutable_vec256_array fields
  | Static_const.Immutable_vec512_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_vec512
      T.this_naked_vec512 RSC.create_immutable_vec512_array fields
  | Static_const.Immutable_mask_array fields =>
    rebuild_naked_number_array dacc bind_result_sym KS.naked_mask
      T.this_naked_mask RSC.create_immutable_mask_array fields
  | Static_const.Immutable_value_array fields =>
    let* fields_with_tys :=
      List.map
        (fun field => simplify_field_of_block dacc (field, K.value))
        fields
    in
    let* '(fields, field_tys) := List.split fields_with_tys in
    (* 275-280 *)
    let* dacc :=
      let* machine_width :=
        let! tmp1 := DA.denv dacc in
        DE.machine_width tmp1
      in
      let! tmp1 :=
        T.immutable_array (Or_unknown_or_bottom.Ok KS.any_value) field_tys
          Alloc_mode.For_types.heap machine_width
      in
      bind_result_sym tmp1
    in
    let! tmp1 := DA.are_rebuilding_terms dacc in
    let! tmp2 :=
      Rebuilt_static_const.create_immutable_value_array tmp1 fields
    in
    ret (tmp2, dacc)
  | Static_const.Empty_array array_kind =>
    (* PORT-GAP(loose): 290, the [let machine_width = ... in] that the
       compiler has inside the argument [~length] is not kept: its call
       stands where [machine_width] is used. *)
    let* dacc :=
      let! tmp1 := DA.denv dacc in
      let! tmp2 := DE.machine_width tmp1 in
      let! tmp3 := Target_ocaml_int.zero tmp2 in
      let! tmp4 := T.this_tagged_immediate tmp3 in
      let! tmp5 :=
        T.array_of_length Or_unknown_or_bottom.Bottom tmp4
          Alloc_mode.For_types.heap
      in
      bind_result_sym tmp5
    in
    let! tmp1 := DA.are_rebuilding_terms dacc in
    let! tmp2 := Rebuilt_static_const.create_empty_array tmp1 array_kind in
    ret (tmp2, dacc)
  | Static_const.Immutable_string str =>
    let* ty := T.this_immutable_string str in
    let* dacc := bind_result_sym ty in
    let! tmp1 := DA.are_rebuilding_terms dacc in
    let! tmp2 := Rebuilt_static_const.create_immutable_string tmp1 str in
    ret (tmp2, dacc)
  | Static_const.Set_of_closures _ =>
    fatal_errorf2
      "[Set_of_closures] values cannot be bound by a [Block_like] binding:@ %a"
      SC.print static_const
  end.

(* 310-483. In the compiler: [dacc bound_static static_consts
   ~simplify_function_body]. The functions given to
   [Static_const_group.match_against_bound_static] are in the order of its
   interface: [~init ~code ~deleted_code ~set_of_closures ~block_like]. *)
Definition simplify_static_consts (dacc : DA.t)
    (bound_static : Bound_static.t) (static_consts : Static_const_group.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M (tuple3 Bound_static.t Rebuilt_static_const.Group.t DA.t) :=
  let* bound_static_list := Bound_static.to_list bound_static in
  let* static_consts_list := Static_const_group.to_list static_consts in
  (* 314-317 *)
  (let! tmp1 := List.compare_lengths bound_static_list static_consts_list in
   if tmp1 <>? 0
   then
     fatal_errorf4 "Bound symbols don't match static constants:@ %a@ =@ %a"
       Bound_static.print bound_static Static_const_group.print static_consts
   else ret tt) ;;
  (* The closure symbols are bound recursively across all of the
     definitions. We can start by giving these type [Unknown], since
     simplification of the constants that are neither pieces of code nor
     closures will not look at the structure of these closure symbols'
     definitions. *)
  let* dacc :=
    Static_const_group.match_against_bound_static static_consts bound_static
      dacc
      (fun dacc _ _ => ret dacc)
      (fun dacc _ => ret dacc)
      (fun dacc closure_symbols _ =>
        Function_slot.Lmap.fold
          (fun _ closure_symbol dacc =>
            let! tmp1 := DA.denv dacc in
            let! tmp2 := DE.define_symbol tmp1 closure_symbol K.value in
            DA.with_denv dacc tmp2)
          closure_symbols dacc)
      (fun dacc _ _ => ret dacc)
  in
  let* all_code := Static_const_group.pieces_of_code static_consts in
  (* Next we simplify all the constants that are not closures. The ordering
     of the bindings is respected. This step also adds code into the
     environment. We can do that here because we're not simplifying the code
     (which may contain recursive references to symbols and/or code IDs
     being defined). This step will give values such as blocks various types
     involving aliases whose types in turn may currently be imprecise, for
     example if they reference a mutually-defined closure, but will be able
     to be refined further. *)
  (* 377-393 *)
  let* dacc :=
    let* old_code_ids :=
      Code_id.Map.fold
        (fun code_id code old_code_ids =>
          let! tmp1 := Code.stub code in
          let! tmp2 :=
            and_then tmp1
              (let! tmp3 := Flambda_features.simplify_stubs tt in
               ret (negb tmp3))
          in
          if tmp2
          then ret old_code_ids
          else
            let! tmp1 := Code.newer_version_of code in
            match tmp1 with
            | None =>
              let! tmp1 := Code_id.is_imported code_id in
              if tmp1
              then ret old_code_ids
              else Code_id.Set_.add code_id old_code_ids
            | Some _ => ret old_code_ids
            end)
        all_code Code_id.Set_.empty
    in
    DA.add_code_ids_never_simplified dacc old_code_ids
  in
  (* 394-444 *)
  let* '(T3 bound_static' static_consts' dacc) :=
    Static_const_group.match_against_bound_static static_consts bound_static
      (T3 [] [] dacc)
      (fun '(T3 bound_static static_consts dacc) code_id code =>
        let* '(T3 code static_const dacc) :=
          let! tmp1 := Code.stub code in
          let! tmp2 :=
            and_then tmp1
              (* With "-flambda2-simplify-stubs" stubs are simplified like
                 other functions at the definition of the set of
                 closures. *)
              (let! tmp3 := Flambda_features.simplify_stubs tt in
               ret (negb tmp3))
          in
          if tmp2
          then
            let* '(dacc, prior_lifted_constants) :=
              DA.get_and_clear_lifted_constants dacc
            in
            let* '(static_const, dacc_after_function) :=
              Simplify_set_of_closures.simplify_static_stub_function dacc
                code all_code simplify_function_body
            in
            let* dacc_after_function :=
              DA.add_to_lifted_constant_accumulator None dacc_after_function
                prior_lifted_constants
            in
            let! tmp1 := Rebuilt_static_const.to_const static_const in
            match tmp1 with
            | None =>
              (* Not rebuilding terms: return the original code *)
              let! tmp1 := Rebuilt_static_const.create_code' code in
              ret (T3 code tmp1 dacc)
            | Some static_const_or_code =>
              let! tmp1 :=
                Static_const_or_code.to_code static_const_or_code
              in
              match tmp1 with
              | None => assert_false
              | Some code => ret (T3 code static_const dacc_after_function)
              end
            end
          else
            let! tmp1 := Rebuilt_static_const.create_code' code in
            ret (T3 code tmp1 dacc)
        in
        let* dacc :=
          DA.map_denv dacc (fun denv => DE.define_code denv code_id code)
        in
        let! tmp1 := Bound_static.Pattern.code code_id in
        ret (T3 (tmp1 :: bound_static) (static_const :: static_consts) dacc))
      (fun acc _code_id => ret acc)
      (fun acc _ _ => ret acc)
      (fun '(T3 bound_static static_consts dacc) symbol static_const =>
        let* '(static_const, dacc) :=
          simplify_static_const_of_kind_value dacc static_const symbol
        in
        let! tmp1 := Bound_static.Pattern.block_like symbol in
        ret (T3 (tmp1 :: bound_static) (static_const :: static_consts) dacc))
  in
  let* bound_static' := Bound_static.create bound_static' in
  let* static_consts' := Rebuilt_static_const.Group.create static_consts' in
  (* We now collect together all of the closures, from all of the sets being
     defined, and simplify them together. It's important to do this step of
     simplification at the end to maximise the information available, since
     this can be highly beneficial to simplifying [Code] (which will be done
     as part of simplifying the closures). *)
  (* 452-473 *)
  let* '(closure_bound_names_all_sets, all_sets_of_closures_and_symbols) :=
    Static_const_group.match_against_bound_static static_consts bound_static
      ([], [])
      (fun acc _ _ => ret acc)
      (fun acc _ => ret acc)
      (fun '(closure_bound_names_all_sets, sets_of_closures) closure_symbols
           set_of_closures =>
        let* closure_bound_names :=
          Function_slot.Lmap.fold
            (fun function_slot symbol closure_bound_names_all_sets =>
              let! tmp1 := Bound_name.create_symbol symbol in
              Function_slot.Map.add function_slot tmp1
                closure_bound_names_all_sets)
            closure_symbols Function_slot.Map.empty
        in
        ret
          ( closure_bound_names :: closure_bound_names_all_sets,
            (closure_symbols, set_of_closures) :: sets_of_closures ))
      (fun acc _ _ => ret acc)
  in
  (* 474-478 *)
  let* '(T3 bound_static'' static_consts'' dacc) :=
    Simplify_set_of_closures.simplify_lifted_sets_of_closures dacc
      all_sets_of_closures_and_symbols closure_bound_names_all_sets
      simplify_function_body
  in
  (* The ordering of these lists doesn't matter as they will go through
     [Sort_lifted_constants] before the terms are constructed. *)
  let! tmp1 :=
    Rebuilt_static_const.Group.concat static_consts' static_consts''
  in
  let! tmp2 := Bound_static.concat bound_static' bound_static'' in
  ret (T3 tmp2 tmp1 dacc).
