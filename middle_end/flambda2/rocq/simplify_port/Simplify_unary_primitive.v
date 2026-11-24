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

(* This file follows middle_end/flambda2/simplify/simplify_unary_primitive.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md; and the form
   of the four functors of the file, which is that of GUIDE.md, section 4:
   each is a Rocq [Module] with a [Section] whose variables are the
   operations that the functor uses of its parameter, and each instance is
   a [Module] of the compiler's name whose [simplify] is the function
   applied to the operations of the argument. The functions that the
   interface does not export have their arguments in the order of each
   definition, and an argument that the compiler does not use has here the
   type of the one call. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Array Bound_pattern Bound_var
  Closure_info Coercion Debuginfo Flambda_debug_uid Flambda_kind Function_slot
  List Mutability Name Number_adjuncts Numeric_types Or_unknown
  Or_unknown_or_bottom Reg_width_const Simple Simplify_common Stdlib_ String
  String_info Symbol_projection Tag Target_ocaml_int Target_system
Targetint_32_64 Value_slot Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Alloc_mode.For_types.t
   Closure_info.in_or_out_of_closure_ Closure_info.t
   Flambda2_types.boxed_or_tagged_number Flambda2_types.meet_shortcut
   Flambda2_types.proof_of_property Flambda2_types.reification_result
   Flambda_kind.Scannable_block_shape.t Flambda_kind.Standard_int.t
   Flambda_primitive.binary_primitive Flambda_primitive.float_bitwidth
   Flambda_primitive.t Flambda_primitive.unary_primitive
   Flambda_primitive.variadic_primitive Or_unknown_or_bottom.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 18-22 *)
From SimplifyPort.abbrev.simplify_unary_primitive Require Import Port_abbreviations.
(*OCAML
module A = Number_adjuncts
module Float32 = Numeric_types.Float32_by_bit_pattern
module Float = Numeric_types.Float_by_bit_pattern
module Int32 = Numeric_types.Int32
module Int64 = Numeric_types.Int64
OCAML*)

(* The literals [2L] and [1L] of line 583. *)
Parameter int64_2L : Stdlib_.int64.
Extract Inlined Constant int64_2L => "2L".
Parameter int64_1L : Stdlib_.int64.
Extract Inlined Constant int64_1L => "1L".

(* 24-30 *)
Definition get_my_alloc_region (dacc : DA.t) : M Variable_.t :=
  let! tmp1 := DA.denv dacc in
  let! tmp2 := DE.closure_info tmp1 in
  match tmp2 with
  | Closure_info.Closure _ _ _ _ my_alloc_region => ret my_alloc_region
  | Closure_info.In_a_set_of_closures_but_not_yet_in_a_specific_closure =>
    fatal_error
      "Inconsistent closure_info in [simplify_immutable_block_load0]"
  | Closure_info.Not_in_a_closure =>
    let! tmp1 := DA.denv dacc in
    DE.unit_toplevel_alloc_region tmp1
  end.

(* 32-53. In the compiler: [~move_from ~move_to ~min_name_mode dacc
   ~original_term ~arg:closure ~arg_ty:closure_ty ~result_var]. *)
Definition simplify_project_function_slot (move_from move_to : Function_slot.t)
    (min_name_mode : Name_mode.t) (dacc : DA.t) (original_term : Named.t)
    (closure : Simple.t) (closure_ty : T.t) (result_var : Bound_var.t)
    : M SPR.t :=
  let! tmp1 := DA.typing_env dacc in
  let! tmp2 :=
    T.meet_project_function_slot_simple tmp1 min_name_mode closure_ty move_to
  in
  match tmp2 with
  | T.Invalid => SPR.create_invalid dacc
  | T.Known_result simple =>
    (* 40-41: [a |> f b] is [f b a] *)
    let! tmp1 := T.alias_type_of K.value simple in
    let! tmp2 := DA.add_variable dacc result_var tmp1 in
    let! tmp3 := Named.create_simple simple in
    SPR.create tmp3 true tmp2
  | T.Need_meet =>
    (* 43-47: [a |> f b |> g c d] is [g c d (f b a)] *)
    let* closures :=
      let! tmp1 :=
        Function_slot.Map.add move_from closure Function_slot.Map.empty
      in
      let! tmp2 := Bound_var.var result_var in
      let! tmp3 := Simple.var tmp2 in
      Function_slot.Map.add move_to tmp3 tmp1
    in
    (* 48-53: the arguments are in the order of the interface. *)
    let! tmp1 :=
      T.closure_with_at_least_these_function_slots move_from closures
    in
    Simplify_common.simplify_projection dacc original_term closure_ty tmp1
      result_var K.value
  end.

(* 55-100. In the compiler: [function_slot value_slot ~min_name_mode dacc
   ~original_term ~arg:closure ~arg_ty:closure_ty ~result_var]. *)
Definition simplify_project_value_slot (function_slot : Function_slot.t)
    (value_slot : Value_slot.t) (min_name_mode : Name_mode.t) (dacc : DA.t)
    (original_term : Named.t) (closure : Simple.t) (closure_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* kind := Value_slot.kind value_slot in
  let* result :=
    (* We try a faster method before falling back to
       [simplify_projection]. *)
    let! tmp1 := DA.typing_env dacc in
    let! tmp2 :=
      T.meet_project_value_slot_simple tmp1 min_name_mode closure_ty
        value_slot
    in
    match tmp2 with
    | T.Invalid => SPR.create_invalid dacc
    | T.Known_result simple =>
      (* Owing to the semantics of [Simplify_set_of_closures] when computing the
         types of value slots -- in particular because it allows depth variables
         to exist in such types that are not in scope in the body of the
         function -- we need to ensure that any [Simple] retrieved here from the
         closure environment is simplified. This will ensure that if it is not
         in scope, any associated coercion will be erased appropriately. *)
      (* 72-78 *)
      let* simple :=
        let! tmp1 := Simple.coercion simple in
        let! tmp2 := Coercion.is_id tmp1 in
        if tmp2
        then ret simple
        else
          let* '(_ty, simple) := S.simplify_simple dacc simple min_name_mode in
          ret simple
      in
      let* dacc :=
        let! tmp1 := T.alias_type_of kind simple in
        DA.add_variable dacc result_var tmp1
      in
      let! tmp1 := Named.create_simple simple in
      SPR.create tmp1 true dacc
    | T.Need_meet =>
      (* 84-93 *)
      let* result :=
        let! tmp1 := Bound_var.var result_var in
        let! tmp2 :=
          T.closure_with_at_least_this_value_slot function_slot value_slot
            tmp1 kind
        in
        Simplify_common.simplify_projection dacc original_term closure_ty
          tmp2 result_var kind
      in
      SPR.map_dacc result
        (fun dacc => DA.add_use_of_value_slot dacc value_slot)
    end
  in
  (* 95-100 *)
  SPR.map_dacc result
    (fun dacc =>
      let! tmp1 := Flambda_kind.With_subkind.anything kind in
      let! tmp2 :=
        Symbol_projection.Projection.project_value_slot function_slot
          value_slot
      in
      Simplify_common.add_symbol_projection dacc closure tmp2 result_var tmp1).

(* 102-168. In the compiler: [boxable_number_kind dacc ~original_term ~arg
   ~arg_ty:boxed_number_ty ~result_var]. *)
Definition simplify_unbox_number (boxable_number_kind : K.Boxable_number.t)
    (dacc : DA.t) (original_term : Named.t) (arg : Simple.t)
    (boxed_number_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let* result_var' := Bound_var.var result_var in
  (* 105-143 *)
  let* '(shape, result_kind) :=
    match boxable_number_kind with
    | K.Boxable_number.Naked_float =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_float_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_float)
    | K.Boxable_number.Naked_float32 =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_float32_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_float32)
    | K.Boxable_number.Naked_int32 =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_int32_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_int32)
    | K.Boxable_number.Naked_int64 =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_int64_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_int64)
    | K.Boxable_number.Naked_nativeint =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_nativeint_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_nativeint)
    | K.Boxable_number.Naked_vec128 =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_vec128_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_vec128)
    | K.Boxable_number.Naked_vec256 =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_vec256_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_vec256)
    | K.Boxable_number.Naked_vec512 =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_vec512_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_vec512)
    | K.Boxable_number.Naked_mask =>
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := T.boxed_mask_alias_to result_var' tmp1 in
      ret (tmp2, K.naked_mask)
    end
  in
  (* 144-150 *)
  let* alloc_mode :=
    let! tmp1 := DA.typing_env dacc in
    T.prove_alloc_mode_of_boxed_number tmp1 boxed_number_ty
  in
  let* result :=
    Simplify_common.simplify_projection dacc original_term boxed_number_ty
      shape result_var result_kind
  in
  (* 151-168 *)
  SPR.map_dacc result
    (fun dacc =>
      (* We can only add the inverse CSE equation if we know the alloc mode
         for certain and it is [Heap]. (As per [Flambda_primitive] we don't
         currently CSE local allocations.) *)
      match alloc_mode with
      | T.Unknown
      | T.Proved (Alloc_mode.For_types.Local | Alloc_mode.For_types.Heap_or_local)
        =>
        ret dacc
      | T.Proved Alloc_mode.For_types.Heap =>
        let* alloc_region := get_my_alloc_region dacc in
        DA.map_denv dacc
          (fun denv =>
            let! tmp1 := Bound_var.name_mode result_var in
            let! tmp2 := Simple.var result_var' in
            let! tmp3 := Alloc_mode.For_allocations.heap alloc_region in
            let! tmp4 :=
              P.Eligible_for_cse.create_exn
                (P.Unary (P.Box_number boxable_number_kind tmp3) tmp2)
            in
            DE.add_cse denv tmp4 arg tmp1)
      end).

(* 170-186. In the compiler: [dacc ~original_term ~arg
   ~arg_ty:boxed_number_ty ~result_var]. *)
Definition simplify_untag_immediate (dacc : DA.t) (original_term : Named.t)
    (arg : Simple.t) (boxed_number_ty : T.t) (result_var : Bound_var.t)
    : M SPR.t :=
  let* result_var' := Bound_var.var result_var in
  let* '(shape, result_kind) :=
    let! tmp1 := T.tagged_immediate_alias_to result_var' in
    ret (tmp1, K.naked_immediate)
  in
  let* result :=
    Simplify_common.simplify_projection dacc original_term boxed_number_ty
      shape result_var result_kind
  in
  SPR.map_dacc result
    (fun dacc =>
      DA.map_denv dacc
        (fun denv =>
          let! tmp1 := Bound_var.name_mode result_var in
          let! tmp2 := Simple.var result_var' in
          let! tmp3 :=
            P.Eligible_for_cse.create_exn (P.Unary P.Tag_immediate tmp2)
          in
          DE.add_cse denv tmp3 arg tmp1)).

(* 188-206. In the compiler: [boxable_number_kind alloc_mode dacc
   ~original_term ~arg:_ ~arg_ty:naked_number_ty ~result_var]. *)
Definition simplify_box_number (boxable_number_kind : K.Boxable_number.t)
    (alloc_mode : Alloc_mode.For_allocations.t) (dacc : DA.t)
    (original_term : Named.t) (_ : Simple.t) (naked_number_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* ty :=
    let* alloc_mode := Alloc_mode.For_allocations.as_type alloc_mode in
    (* The following functions already check kinds, but we will only get
       here if the kinds are correct (see [Simplify_primitive]). *)
    match boxable_number_kind with
    | K.Boxable_number.Naked_float32 =>
      T.box_float32 naked_number_ty alloc_mode
    | K.Boxable_number.Naked_float => T.box_float naked_number_ty alloc_mode
    | K.Boxable_number.Naked_int32 => T.box_int32 naked_number_ty alloc_mode
    | K.Boxable_number.Naked_int64 => T.box_int64 naked_number_ty alloc_mode
    | K.Boxable_number.Naked_nativeint =>
      T.box_nativeint naked_number_ty alloc_mode
    | K.Boxable_number.Naked_vec128 => T.box_vec128 naked_number_ty alloc_mode
    | K.Boxable_number.Naked_vec256 => T.box_vec256 naked_number_ty alloc_mode
    | K.Boxable_number.Naked_vec512 => T.box_vec512 naked_number_ty alloc_mode
    | K.Boxable_number.Naked_mask => T.box_mask naked_number_ty alloc_mode
    end
  in
  let* dacc := DA.add_variable dacc result_var ty in
  SPR.create original_term true dacc.

(* 208-216 *)
Definition simplify_tag_immediate (dacc : DA.t) (original_term : Named.t)
    (_ : Simple.t) (naked_number_ty : T.t) (result_var : Bound_var.t)
    : M SPR.t :=
  let* ty :=
    (* The following function checks the kind, but we will only get here if
       the kind is correct (see [Simplify_primitive]). *)
    T.tag_immediate naked_number_ty
  in
  let* dacc := DA.add_variable dacc result_var ty in
  SPR.create original_term true dacc.

(* 218-235. In the compiler: [dacc ~original_term ~scrutinee ~scrutinee_ty:_
   ~result_var ~add_relation]. *)
Definition simplify_relational_primitive (dacc : DA.t)
    (original_term : Named.t) (scrutinee : Simple.t) (_ : T.t)
    (result_var : Bound_var.t)
    (add_relation : TE.t -> Name.t -> Simple.t -> M TE.t) : M SPR.t :=
  let* dacc :=
    DA.map_denv dacc
      (fun denv =>
        let* denv := DE.define_variable denv result_var K.naked_immediate in
        DE.map_typing_env denv
          (fun tenv =>
            let! tmp1 := Bound_var.var result_var in
            let! tmp2 := Name.var tmp1 in
            add_relation tenv tmp2 scrutinee))
  in
  SPR.create original_term true dacc.

(* 237-251. In the compiler: [~variant_only dacc ~original_term
   ~arg:scrutinee ~arg_ty:scrutinee_ty ~result_var]. *)
Definition simplify_is_int (variant_only : bool) (dacc : DA.t)
    (original_term : Named.t) (scrutinee : Simple.t) (scrutinee_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  if variant_only
  then
    simplify_relational_primitive dacc original_term scrutinee scrutinee_ty
      result_var TE.add_is_int_relation
  else
    let! tmp1 := DA.typing_env dacc in
    let! tmp2 := T.prove_is_int tmp1 scrutinee_ty in
    match tmp2 with
    | T.Proved b =>
      let* machine_width :=
        let! tmp1 := DA.denv dacc in
        DE.machine_width tmp1
      in
      let* ty :=
        let! tmp1 := Target_ocaml_int.bool_ machine_width b in
        T.this_naked_immediate tmp1
      in
      let* dacc := DA.add_variable dacc result_var ty in
      SPR.create original_term false dacc
    | T.Unknown =>
      SPR.create_unknown dacc result_var K.naked_immediate original_term
    end.

(* 253-282 *)
Definition simplify_get_tag (dacc : DA.t) (original_term : Named.t)
    (scrutinee : Simple.t) (scrutinee_ty : T.t) (result_var : Bound_var.t)
    : M SPR.t :=
  (* CR mshinwell: This is provisional ("for now"). [Get_tag] reads the header
     of its argument, so here it is made [Invalid] when the argument is known to
     be a tagged immediate: a constant, or a name whose type has no blocks.
     Nothing changes when the argument may be a block.

     Code using GADTs puts [Get_tag] of an immediate in branches that are never
     executed (a match on a variant with no constant constructors, in a function
     inlined where the GADT's index is a type of immediates): see
     testsuite/tests/flambda2/simplify/get_tag_of_immediate.ml. Before this the
     primitive was left in the term when the argument was a constant, and when
     its result was used in arithmetic and not in a [Switch]. The Rocq model of
     Flambda 2 (middle_end/flambda2/rocq) gives [Get_tag] of an immediate no
     meaning (its decision D5).

     This concerns the primitive only. The [Get_tag] relation that
     [TE.add_get_tag_relation] records is still recorded on names that may be
     immediates (unboxing does so, and passes tag 0 where a constant constructor
     is passed).

     The other primitives that read through their argument and are left in the
     term when it is an immediate have not been changed: [Get_header],
     [Block_set], [Block_load] of a mutable field, and the array loads and
     sets. *)
  let! tmp1 := DA.typing_env dacc in
  let! tmp2 := T.prove_is_int tmp1 scrutinee_ty in
  match tmp2 with
  | T.Proved true => SPR.create_invalid dacc
  | T.Proved false | T.Unknown =>
    simplify_relational_primitive dacc original_term scrutinee scrutinee_ty
      result_var TE.add_get_tag_relation
  end.

(* 284-296. In the compiler: [_array_kind dacc ~original_term ~arg:_
   ~arg_ty:array_ty ~result_var]. *)
Definition simplify_array_length (_array_kind : P.Array_kind_for_length.t)
    (dacc : DA.t) (original_term : Named.t) (_ : Simple.t) (array_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* result :=
    let! tmp1 := Bound_var.var result_var in
    Simple.var tmp1
  in
  (* 290-296: the arguments are in the order of the interfaces. *)
  let! tmp1 := Alloc_mode.For_types.unknown tt in
  let! tmp2 := T.alias_type_of K.value result in
  let! tmp3 := T.array_of_length Or_unknown_or_bottom.Unknown tmp2 tmp1 in
  Simplify_common.simplify_projection dacc original_term array_ty tmp3
    result_var K.value.

(* 300-321 *)
Definition simplify_string_length (dacc : DA.t) (original_term : Named.t)
    (_ : Simple.t) (str_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := DA.typing_env dacc in
  let! tmp2 := T.meet_strings tmp1 str_ty in
  match tmp2 with
  | T.Known_result str_infos =>
    let! tmp1 := String_info.Set_.is_empty str_infos in
    if tmp1
    then SPR.create_invalid dacc
    else
      let* machine_width :=
        let! tmp1 := DA.denv dacc in
        DE.machine_width tmp1
      in
      let* lengths :=
        String_info.Set_.fold
          (fun str lengths =>
            let! tmp1 := String.length str in
            let! tmp2 := Target_ocaml_int.of_int machine_width tmp1 in
            Target_ocaml_int.Set_.add tmp2 lengths)
          str_infos Target_ocaml_int.Set_.empty
      in
      let* ty := T.these_naked_immediates lengths in
      let* dacc := DA.add_variable dacc result_var ty in
      SPR.create original_term true dacc
  | T.Need_meet =>
    SPR.create_unknown dacc result_var K.naked_immediate original_term
  | T.Invalid => SPR.create_invalid dacc
  end.

(* PORT-GAP(loose): 323-344, the functor [Unary_int_arith (I :
   A.Int_number_kind)] is a module whose function [simplify] takes first
   what the functor uses of [I] (the variables of the section, in this
   order). *)
Module Unary_int_arith.
  Section I.
    Context {I_Num_t I_Num_Set_t : Type}.
    Variable I_Num_Set_is_empty : I_Num_Set_t -> M bool.
    Variable I_Num_Set_map :
      (I_Num_t -> M I_Num_t) -> I_Num_Set_t -> M I_Num_Set_t.
    Variable I_Num_swap_byte_endianness : I_Num_t -> M I_Num_t.
    Variable I_Num_not_ : I_Num_t -> M I_Num_t.
    Variable I_standard_int_or_float_kind : K.Standard_int_or_float.t.
    Variable I_unboxed_prover :
      TE.t -> T.t -> M (T.meet_shortcut I_Num_Set_t).
    Variable I_these_unboxed : I_Num_Set_t -> M T.t.

    (* 324-343 *)
    Definition simplify (op : P.unary_int_arith_op) (dacc : DA.t)
        (original_term : Named.t) (_ : Simple.t) (arg_ty : T.t)
        (result_var : Bound_var.t) : M SPR.t :=
      let! tmp1 := DA.typing_env dacc in
      let! tmp2 := I_unboxed_prover tmp1 arg_ty in
      match tmp2 with
      | T.Known_result ints =>
        (let! tmp1 := I_Num_Set_is_empty ints in
         assert_ (negb tmp1)) ;;
        let& f :=
          match op with
          | P.Swap_byte_endianness => I_Num_swap_byte_endianness
          | P.Not => I_Num_not_
          end
        in
        let* possible_results := I_Num_Set_map f ints in
        let* ty := I_these_unboxed possible_results in
        let* dacc := DA.add_variable dacc result_var ty in
        SPR.create original_term true dacc
      | T.Need_meet =>
        let* result_kind :=
          K.Standard_int_or_float.to_kind I_standard_int_or_float_kind
        in
        SPR.create_unknown dacc result_var result_kind original_term
      | T.Invalid => SPR.create_invalid dacc
      end.
  End I.
End Unary_int_arith.

(* PORT-GAP(loose): 346-353, the seven instances [Unary_int_arith
   (A.For_tagged_immediates)] and so on: each is a module whose [simplify]
   is the function applied to the operations of the argument. *)

(* 346-347 *)
Module Unary_int_arith_tagged_immediate.
  Definition simplify :=
    Unary_int_arith.simplify A.For_tagged_immediates.Num.Set_.is_empty
      A.For_tagged_immediates.Num.Set_.map
      A.For_tagged_immediates.Num.swap_byte_endianness
      A.For_tagged_immediates.Num.not_
      A.For_tagged_immediates.standard_int_or_float_kind
      A.For_tagged_immediates.unboxed_prover
      A.For_tagged_immediates.these_unboxed.
End Unary_int_arith_tagged_immediate.

(* 348 *)
Module Unary_int_arith_naked_immediate.
  Definition simplify :=
    Unary_int_arith.simplify A.For_naked_immediates.Num.Set_.is_empty
      A.For_naked_immediates.Num.Set_.map
      A.For_naked_immediates.Num.swap_byte_endianness
      A.For_naked_immediates.Num.not_
      A.For_naked_immediates.standard_int_or_float_kind
      A.For_naked_immediates.unboxed_prover
      A.For_naked_immediates.these_unboxed.
End Unary_int_arith_naked_immediate.

(* 349 *)
Module Unary_int_arith_naked_int8.
  Definition simplify :=
    Unary_int_arith.simplify A.For_int8s.Num.Set_.is_empty
      A.For_int8s.Num.Set_.map A.For_int8s.Num.swap_byte_endianness
      A.For_int8s.Num.not_ A.For_int8s.standard_int_or_float_kind
      A.For_int8s.unboxed_prover A.For_int8s.these_unboxed.
End Unary_int_arith_naked_int8.

(* 350 *)
Module Unary_int_arith_naked_int16.
  Definition simplify :=
    Unary_int_arith.simplify A.For_int16s.Num.Set_.is_empty
      A.For_int16s.Num.Set_.map A.For_int16s.Num.swap_byte_endianness
      A.For_int16s.Num.not_ A.For_int16s.standard_int_or_float_kind
      A.For_int16s.unboxed_prover A.For_int16s.these_unboxed.
End Unary_int_arith_naked_int16.

(* 351 *)
Module Unary_int_arith_naked_int32.
  Definition simplify :=
    Unary_int_arith.simplify A.For_int32s.Num.Set_.is_empty
      A.For_int32s.Num.Set_.map A.For_int32s.Num.swap_byte_endianness
      A.For_int32s.Num.not_ A.For_int32s.standard_int_or_float_kind
      A.For_int32s.unboxed_prover A.For_int32s.these_unboxed.
End Unary_int_arith_naked_int32.

(* 352 *)
Module Unary_int_arith_naked_int64.
  Definition simplify :=
    Unary_int_arith.simplify A.For_int64s.Num.Set_.is_empty
      A.For_int64s.Num.Set_.map A.For_int64s.Num.swap_byte_endianness
      A.For_int64s.Num.not_ A.For_int64s.standard_int_or_float_kind
      A.For_int64s.unboxed_prover A.For_int64s.these_unboxed.
End Unary_int_arith_naked_int64.

(* 353 *)
Module Unary_int_arith_naked_nativeint.
  Definition simplify :=
    Unary_int_arith.simplify A.For_nativeints.Num.Set_.is_empty
      A.For_nativeints.Num.Set_.map A.For_nativeints.Num.swap_byte_endianness
      A.For_nativeints.Num.not_ A.For_nativeints.standard_int_or_float_kind
      A.For_nativeints.unboxed_prover A.For_nativeints.these_unboxed.
End Unary_int_arith_naked_nativeint.

(* PORT-GAP(loose): 355-475, the functor [Make_simplify_int_conv (N :
   A.Number_kind)] is a module whose function [simplify] takes first what
   the functor uses of [N] (the variables of the section, in this order).
   [N.Num.Set.fold] is used at the type of each set of results: it is one
   variable for each (OCaml gives a function that is an argument one type
   only). *)
Module Make_simplify_int_conv.
  Section N.
    Context {N_Num_t N_Num_Set_t : Type}.
    Local Abbreviation fold_to S :=
      ((N_Num_t -> S -> M S) -> N_Num_Set_t -> S -> M S).
    Variable N_Num_Set_cardinal : N_Num_Set_t -> M int.
    Variable N_Num_Set_fold_to_immediates : fold_to Target_ocaml_int.Set_.t.
    Variable N_Num_Set_fold_to_float32s : fold_to Float32.Set_.t.
    Variable N_Num_Set_fold_to_floats : fold_to Float.Set_.t.
    Variable N_Num_Set_fold_to_int8s : fold_to Numeric_types.Int8.Set_.t.
    Variable N_Num_Set_fold_to_int16s : fold_to Numeric_types.Int16.Set_.t.
    Variable N_Num_Set_fold_to_int32s : fold_to Int32.Set_.t.
    Variable N_Num_Set_fold_to_int64s : fold_to Int64.Set_.t.
    Variable N_Num_Set_fold_to_nativeints : fold_to Targetint_32_64.Set_.t.
    Variable N_Num_to_immediate :
      N_Num_t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Variable N_Num_to_naked_float32 : N_Num_t -> M Float32.t.
    Variable N_Num_to_naked_float : N_Num_t -> M Float.t.
    Variable N_Num_to_naked_int8 : N_Num_t -> M Numeric_types.Int8.t.
    Variable N_Num_to_naked_int16 : N_Num_t -> M Numeric_types.Int16.t.
    Variable N_Num_to_naked_int32 : N_Num_t -> M Int32.t.
    Variable N_Num_to_naked_int64 : N_Num_t -> M Int64.t.
    Variable N_Num_to_naked_nativeint :
      N_Num_t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Variable N_standard_int_or_float_kind : K.Standard_int_or_float.t.
    Variable N_unboxed_prover :
      TE.t -> T.t -> M (T.meet_shortcut N_Num_Set_t).

    (* PORT-GAP(loose): 368-386, the local functor [For_kind (P : sig module
       Result_num : Container_types.S val num_to_result_num : Num.t ->
       Result_num.t val these : Result_num.Set.t -> T.t end)], whose one
       value [result] is computed when the functor is applied, is a function
       of [N.Num.Set.fold], of what it uses of [P], and of the variables of
       [simplify] that it names. *)
    Definition for_kind {P_Result_num_t P_Result_num_Set_t : Type}
        (N_Num_Set_fold : fold_to P_Result_num_Set_t)
        (P_Result_num_Set_add :
          P_Result_num_t -> P_Result_num_Set_t -> M P_Result_num_Set_t)
        (P_Result_num_Set_empty : P_Result_num_Set_t)
        (P_num_to_result_num : N_Num_t -> M P_Result_num_t)
        (P_these : P_Result_num_Set_t -> M T.t) (dacc : DA.t)
        (original_term : Named.t) (result_var : Bound_var.t)
        (is_ : N_Num_Set_t) : M SPR.t :=
      let* res_ns :=
        N_Num_Set_fold
          (fun n res_ns =>
            let! tmp1 := P_num_to_result_num n in
            P_Result_num_Set_add tmp1 res_ns)
          is_ P_Result_num_Set_empty
      in
      let* ty := P_these res_ns in
      let* dacc := DA.add_variable dacc result_var ty in
      SPR.create original_term true dacc.

    (* 356-474 *)
    Definition simplify (dst : K.Standard_int_or_float.t) (dacc : DA.t)
        (original_term : Named.t) (arg : Simple.t) (arg_ty : T.t)
        (result_var : Bound_var.t) : M SPR.t :=
      let! tmp1 :=
        K.Standard_int_or_float.equal N_standard_int_or_float_kind dst
      in
      if tmp1
      then
        let* dacc := DA.add_variable dacc result_var arg_ty in
        let! tmp1 := Named.create_simple arg in
        SPR.create tmp1 false dacc
      else
        let* proof :=
          let! tmp1 := DA.typing_env dacc in
          N_unboxed_prover tmp1 arg_ty
        in
        (* 364: [let module Num = N.Num in] *)
        match proof with
        | T.Known_result is_ =>
          (let! tmp1 := N_Num_Set_cardinal is_ in
           assert_ (tmp1 >? 0)) ;;
          let* machine_width :=
            let! tmp1 := DA.denv dacc in
            DE.machine_width tmp1
          in
          (* 388-470: each [let module M = For_kind [@inlined hint] (struct
             ... end) in M.result] is a call of [for_kind]. *)
          match dst with
          | K.Standard_int_or_float.Tagged_immediate =>
            for_kind N_Num_Set_fold_to_immediates Target_ocaml_int.Set_.add
              Target_ocaml_int.Set_.empty
              (fun t => N_Num_to_immediate t machine_width)
              T.these_tagged_immediates dacc original_term result_var is_
          | K.Standard_int_or_float.Naked_immediate =>
            for_kind N_Num_Set_fold_to_immediates Target_ocaml_int.Set_.add
              Target_ocaml_int.Set_.empty
              (fun t => N_Num_to_immediate t machine_width)
              T.these_naked_immediates dacc original_term result_var is_
          | K.Standard_int_or_float.Naked_float32 =>
            for_kind N_Num_Set_fold_to_float32s Float32.Set_.add
              Float32.Set_.empty N_Num_to_naked_float32 T.these_naked_float32s
              dacc original_term result_var is_
          | K.Standard_int_or_float.Naked_float =>
            for_kind N_Num_Set_fold_to_floats Float.Set_.add Float.Set_.empty
              N_Num_to_naked_float T.these_naked_floats dacc original_term
              result_var is_
          | K.Standard_int_or_float.Naked_int8 =>
            for_kind N_Num_Set_fold_to_int8s Numeric_types.Int8.Set_.add
              Numeric_types.Int8.Set_.empty N_Num_to_naked_int8
              T.these_naked_int8s dacc original_term result_var is_
          | K.Standard_int_or_float.Naked_int16 =>
            for_kind N_Num_Set_fold_to_int16s Numeric_types.Int16.Set_.add
              Numeric_types.Int16.Set_.empty N_Num_to_naked_int16
              T.these_naked_int16s dacc original_term result_var is_
          | K.Standard_int_or_float.Naked_int32 =>
            for_kind N_Num_Set_fold_to_int32s Int32.Set_.add Int32.Set_.empty
              N_Num_to_naked_int32 T.these_naked_int32s dacc original_term
              result_var is_
          | K.Standard_int_or_float.Naked_int64 =>
            for_kind N_Num_Set_fold_to_int64s Int64.Set_.add Int64.Set_.empty
              N_Num_to_naked_int64 T.these_naked_int64s dacc original_term
              result_var is_
          | K.Standard_int_or_float.Naked_nativeint =>
            let* machine_width :=
              let! tmp1 := DA.denv dacc in
              DE.machine_width tmp1
            in
            for_kind N_Num_Set_fold_to_nativeints Targetint_32_64.Set_.add
              Targetint_32_64.Set_.empty
              (fun n => N_Num_to_naked_nativeint n machine_width)
              T.these_naked_nativeints dacc original_term result_var is_
          end
        | T.Need_meet =>
          let* result_kind := K.Standard_int_or_float.to_kind dst in
          SPR.create_unknown dacc result_var result_kind original_term
        | T.Invalid => SPR.create_invalid dacc
        end.
  End N.
End Make_simplify_int_conv.

(* PORT-GAP(loose): 477-488, the nine instances [Make_simplify_int_conv
   (A.For_tagged_immediates)] and so on: each is a module whose [simplify]
   is the function applied to the operations of the argument
   ([N.Num.Set.fold] once for each type of result). *)

(* 477-478 *)
Module Simplify_int_conv_tagged_immediate.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_tagged_immediates.Num.Set_.cardinal
      A.For_tagged_immediates.Num.Set_.fold
      A.For_tagged_immediates.Num.Set_.fold
      A.For_tagged_immediates.Num.Set_.fold
      A.For_tagged_immediates.Num.Set_.fold
      A.For_tagged_immediates.Num.Set_.fold
      A.For_tagged_immediates.Num.Set_.fold
      A.For_tagged_immediates.Num.Set_.fold
      A.For_tagged_immediates.Num.Set_.fold
      A.For_tagged_immediates.Num.to_immediate
      A.For_tagged_immediates.Num.to_naked_float32
      A.For_tagged_immediates.Num.to_naked_float
      A.For_tagged_immediates.Num.to_naked_int8
      A.For_tagged_immediates.Num.to_naked_int16
      A.For_tagged_immediates.Num.to_naked_int32
      A.For_tagged_immediates.Num.to_naked_int64
      A.For_tagged_immediates.Num.to_naked_nativeint
      A.For_tagged_immediates.standard_int_or_float_kind
      A.For_tagged_immediates.unboxed_prover.
End Simplify_int_conv_tagged_immediate.

(* 479-480 *)
Module Simplify_int_conv_naked_immediate.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_naked_immediates.Num.Set_.cardinal
      A.For_naked_immediates.Num.Set_.fold
      A.For_naked_immediates.Num.Set_.fold
      A.For_naked_immediates.Num.Set_.fold
      A.For_naked_immediates.Num.Set_.fold
      A.For_naked_immediates.Num.Set_.fold
      A.For_naked_immediates.Num.Set_.fold
      A.For_naked_immediates.Num.Set_.fold
      A.For_naked_immediates.Num.Set_.fold
      A.For_naked_immediates.Num.to_immediate
      A.For_naked_immediates.Num.to_naked_float32
      A.For_naked_immediates.Num.to_naked_float
      A.For_naked_immediates.Num.to_naked_int8
      A.For_naked_immediates.Num.to_naked_int16
      A.For_naked_immediates.Num.to_naked_int32
      A.For_naked_immediates.Num.to_naked_int64
      A.For_naked_immediates.Num.to_naked_nativeint
      A.For_naked_immediates.standard_int_or_float_kind
      A.For_naked_immediates.unboxed_prover.
End Simplify_int_conv_naked_immediate.

(* 481 *)
Module Simplify_int_conv_naked_float.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_floats.Num.Set_.cardinal
      A.For_floats.Num.Set_.fold A.For_floats.Num.Set_.fold
      A.For_floats.Num.Set_.fold A.For_floats.Num.Set_.fold
      A.For_floats.Num.Set_.fold A.For_floats.Num.Set_.fold
      A.For_floats.Num.Set_.fold A.For_floats.Num.Set_.fold
      A.For_floats.Num.to_immediate A.For_floats.Num.to_naked_float32
      A.For_floats.Num.to_naked_float A.For_floats.Num.to_naked_int8
      A.For_floats.Num.to_naked_int16 A.For_floats.Num.to_naked_int32
      A.For_floats.Num.to_naked_int64 A.For_floats.Num.to_naked_nativeint
      A.For_floats.standard_int_or_float_kind A.For_floats.unboxed_prover.
End Simplify_int_conv_naked_float.

(* 482 *)
Module Simplify_int_conv_naked_float32.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_float32s.Num.Set_.cardinal
      A.For_float32s.Num.Set_.fold A.For_float32s.Num.Set_.fold
      A.For_float32s.Num.Set_.fold A.For_float32s.Num.Set_.fold
      A.For_float32s.Num.Set_.fold A.For_float32s.Num.Set_.fold
      A.For_float32s.Num.Set_.fold A.For_float32s.Num.Set_.fold
      A.For_float32s.Num.to_immediate A.For_float32s.Num.to_naked_float32
      A.For_float32s.Num.to_naked_float A.For_float32s.Num.to_naked_int8
      A.For_float32s.Num.to_naked_int16 A.For_float32s.Num.to_naked_int32
      A.For_float32s.Num.to_naked_int64 A.For_float32s.Num.to_naked_nativeint
      A.For_float32s.standard_int_or_float_kind
      A.For_float32s.unboxed_prover.
End Simplify_int_conv_naked_float32.

(* 483 *)
Module Simplify_int_conv_naked_int8.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_int8s.Num.Set_.cardinal
      A.For_int8s.Num.Set_.fold A.For_int8s.Num.Set_.fold
      A.For_int8s.Num.Set_.fold A.For_int8s.Num.Set_.fold
      A.For_int8s.Num.Set_.fold A.For_int8s.Num.Set_.fold
      A.For_int8s.Num.Set_.fold A.For_int8s.Num.Set_.fold
      A.For_int8s.Num.to_immediate A.For_int8s.Num.to_naked_float32
      A.For_int8s.Num.to_naked_float A.For_int8s.Num.to_naked_int8
      A.For_int8s.Num.to_naked_int16 A.For_int8s.Num.to_naked_int32
      A.For_int8s.Num.to_naked_int64 A.For_int8s.Num.to_naked_nativeint
      A.For_int8s.standard_int_or_float_kind A.For_int8s.unboxed_prover.
End Simplify_int_conv_naked_int8.

(* 484 *)
Module Simplify_int_conv_naked_int16.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_int16s.Num.Set_.cardinal
      A.For_int16s.Num.Set_.fold A.For_int16s.Num.Set_.fold
      A.For_int16s.Num.Set_.fold A.For_int16s.Num.Set_.fold
      A.For_int16s.Num.Set_.fold A.For_int16s.Num.Set_.fold
      A.For_int16s.Num.Set_.fold A.For_int16s.Num.Set_.fold
      A.For_int16s.Num.to_immediate A.For_int16s.Num.to_naked_float32
      A.For_int16s.Num.to_naked_float A.For_int16s.Num.to_naked_int8
      A.For_int16s.Num.to_naked_int16 A.For_int16s.Num.to_naked_int32
      A.For_int16s.Num.to_naked_int64 A.For_int16s.Num.to_naked_nativeint
      A.For_int16s.standard_int_or_float_kind A.For_int16s.unboxed_prover.
End Simplify_int_conv_naked_int16.

(* 485 *)
Module Simplify_int_conv_naked_int32.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_int32s.Num.Set_.cardinal
      A.For_int32s.Num.Set_.fold A.For_int32s.Num.Set_.fold
      A.For_int32s.Num.Set_.fold A.For_int32s.Num.Set_.fold
      A.For_int32s.Num.Set_.fold A.For_int32s.Num.Set_.fold
      A.For_int32s.Num.Set_.fold A.For_int32s.Num.Set_.fold
      A.For_int32s.Num.to_immediate A.For_int32s.Num.to_naked_float32
      A.For_int32s.Num.to_naked_float A.For_int32s.Num.to_naked_int8
      A.For_int32s.Num.to_naked_int16 A.For_int32s.Num.to_naked_int32
      A.For_int32s.Num.to_naked_int64 A.For_int32s.Num.to_naked_nativeint
      A.For_int32s.standard_int_or_float_kind A.For_int32s.unboxed_prover.
End Simplify_int_conv_naked_int32.

(* 486 *)
Module Simplify_int_conv_naked_int64.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_int64s.Num.Set_.cardinal
      A.For_int64s.Num.Set_.fold A.For_int64s.Num.Set_.fold
      A.For_int64s.Num.Set_.fold A.For_int64s.Num.Set_.fold
      A.For_int64s.Num.Set_.fold A.For_int64s.Num.Set_.fold
      A.For_int64s.Num.Set_.fold A.For_int64s.Num.Set_.fold
      A.For_int64s.Num.to_immediate A.For_int64s.Num.to_naked_float32
      A.For_int64s.Num.to_naked_float A.For_int64s.Num.to_naked_int8
      A.For_int64s.Num.to_naked_int16 A.For_int64s.Num.to_naked_int32
      A.For_int64s.Num.to_naked_int64 A.For_int64s.Num.to_naked_nativeint
      A.For_int64s.standard_int_or_float_kind A.For_int64s.unboxed_prover.
End Simplify_int_conv_naked_int64.

(* 487-488 *)
Module Simplify_int_conv_naked_nativeint.
  Definition simplify :=
    Make_simplify_int_conv.simplify A.For_nativeints.Num.Set_.cardinal
      A.For_nativeints.Num.Set_.fold A.For_nativeints.Num.Set_.fold
      A.For_nativeints.Num.Set_.fold A.For_nativeints.Num.Set_.fold
      A.For_nativeints.Num.Set_.fold A.For_nativeints.Num.Set_.fold
      A.For_nativeints.Num.Set_.fold A.For_nativeints.Num.Set_.fold
      A.For_nativeints.Num.to_immediate A.For_nativeints.Num.to_naked_float32
      A.For_nativeints.Num.to_naked_float A.For_nativeints.Num.to_naked_int8
      A.For_nativeints.Num.to_naked_int16 A.For_nativeints.Num.to_naked_int32
      A.For_nativeints.Num.to_naked_int64
      A.For_nativeints.Num.to_naked_nativeint
      A.For_nativeints.standard_int_or_float_kind
      A.For_nativeints.unboxed_prover.
End Simplify_int_conv_naked_nativeint.

(* 490-523 *)
Definition simplify_boolean_not (dacc : DA.t) (original_term : Named.t)
    (_ : Simple.t) (arg_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let* denv := DA.denv dacc in
  let* typing_env := DE.typing_env denv in
  let* machine_width := DE.machine_width denv in
  let* proof := T.meet_equals_tagged_immediates typing_env arg_ty in
  match proof with
  | T.Known_result imms =>
    (* 497-507 *)
    let* imms :=
      Target_ocaml_int.Set_.filter_map
        (fun imm =>
          let! tmp1 := Target_ocaml_int.zero machine_width in
          let! tmp2 := Target_ocaml_int.equal imm tmp1 in
          if tmp2
          then
            let! tmp3 := Target_ocaml_int.one machine_width in
            ret (Some tmp3)
          else
            let! tmp3 := Target_ocaml_int.one machine_width in
            let! tmp4 := Target_ocaml_int.equal imm tmp3 in
            if tmp4
            then
              let! tmp5 := Target_ocaml_int.zero machine_width in
              ret (Some tmp5)
            else ret None)
        imms
    in
    let! tmp1 := Target_ocaml_int.Set_.is_empty imms in
    if tmp1
    then SPR.create_invalid dacc
    else
      let* ty := T.these_tagged_immediates imms in
      let* dacc := DA.add_variable dacc result_var ty in
      SPR.create original_term true dacc
  | T.Need_meet =>
    (* 517-522 *)
    let* machine_width := DE.machine_width denv in
    let* ty :=
      let! tmp1 := Target_ocaml_int.all_bools machine_width in
      T.these_tagged_immediates tmp1
    in
    let* dacc := DA.add_variable dacc result_var ty in
    SPR.create original_term false dacc
  | T.Invalid => SPR.create_invalid dacc
  end.

(* PORT-GAP(loose): 525-558, the functor
   [Make_simplify_reinterpret_64_bit_word (P : sig module Src :
   Container_types.S module Dst : Container_types.S val prover : TE.t -> T.t
   -> Src.Set.t meet_shortcut val convert :
   machine_width:Target_system.Machine_width.t -> Src.t -> Dst.t val these :
   Dst.Set.t -> T.t val any_dst : T.t end)] is a module whose function
   [simplify] takes first what the functor uses of [P] (the variables of the
   section, in this order). *)
Module Make_simplify_reinterpret_64_bit_word.
  Section P.
    Context {P_Src_t P_Src_Set_t P_Dst_t P_Dst_Set_t : Type}.
    Variable P_Src_Set_fold :
      (P_Src_t -> P_Dst_Set_t -> M P_Dst_Set_t) -> P_Src_Set_t ->
      P_Dst_Set_t -> M P_Dst_Set_t.
    Variable P_Dst_Set_add : P_Dst_t -> P_Dst_Set_t -> M P_Dst_Set_t.
    Variable P_Dst_Set_empty : P_Dst_Set_t.
    Variable P_prover : TE.t -> T.t -> M (T.meet_shortcut P_Src_Set_t).
    Variable P_convert :
      Target_system.Machine_width.t -> P_Src_t -> M P_Dst_t.
    Variable P_these : P_Dst_Set_t -> M T.t.
    Variable P_any_dst : T.t.

    (* 539-557 *)
    Definition simplify (dacc : DA.t) (original_term : Named.t)
        (_ : Simple.t) (arg_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
      let* denv := DA.denv dacc in
      let* typing_env := DE.typing_env denv in
      let* machine_width := DE.machine_width denv in
      let* proof := P_prover typing_env arg_ty in
      match proof with
      | T.Known_result src =>
        let* dst :=
          P_Src_Set_fold
            (fun src dst =>
              let! tmp1 := P_convert machine_width src in
              P_Dst_Set_add tmp1 dst)
            src P_Dst_Set_empty
        in
        let* ty := P_these dst in
        let* dacc := DA.add_variable dacc result_var ty in
        SPR.create original_term true dacc
      | T.Need_meet =>
        let* dacc := DA.add_variable dacc result_var P_any_dst in
        SPR.create original_term false dacc
      | T.Invalid => SPR.create_invalid dacc
      end.
  End P.
End Make_simplify_reinterpret_64_bit_word.

(* PORT-GAP(loose): 560-572, the argument of the functor, [struct module Src
   = Int64 module Dst = Float let prover = T.meet_naked_int64s let convert
   ~machine_width:_ = Float.of_bits let these = T.these_naked_floats let
   any_dst = T.any_naked_float end], is the arguments of the function. *)
Module Simplify_reinterpret_unboxed_int64_as_unboxed_float64.
  Definition simplify :=
    Make_simplify_reinterpret_64_bit_word.simplify Int64.Set_.fold
      Float.Set_.add Float.Set_.empty T.meet_naked_int64s
      (fun (_ : Target_system.Machine_width.t) => Float.of_bits)
      T.these_naked_floats T.any_naked_float.
End Simplify_reinterpret_unboxed_int64_as_unboxed_float64.

(* PORT-GAP(loose): 574-586, as above, with [module Src = Float module Dst =
   Int64 let prover = T.meet_naked_floats let convert ~machine_width:_ =
   Float.to_bits let these = T.these_naked_int64s let any_dst =
   T.any_naked_int64]. *)
Module Simplify_reinterpret_unboxed_float64_as_unboxed_int64.
  Definition simplify :=
    Make_simplify_reinterpret_64_bit_word.simplify Float.Set_.fold
      Int64.Set_.add Int64.Set_.empty T.meet_naked_floats
      (fun (_ : Target_system.Machine_width.t) => Float.to_bits)
      T.these_naked_int64s T.any_naked_int64.
End Simplify_reinterpret_unboxed_float64_as_unboxed_int64.

(* PORT-GAP(loose): 588-604, as above, with [module Src = Int64 module Dst =
   Target_ocaml_int let prover = T.meet_naked_int64s let convert
   ~machine_width i = Target_ocaml_int.of_int64 machine_width
   (Int64.shift_right_logical i 1) let these = T.these_tagged_immediates let
   any_dst = T.any_tagged_immediate]. *)
Module Simplify_reinterpret_unboxed_int64_as_tagged_int63.
  Definition simplify :=
    Make_simplify_reinterpret_64_bit_word.simplify Int64.Set_.fold
      Target_ocaml_int.Set_.add Target_ocaml_int.Set_.empty
      T.meet_naked_int64s
      (* This primitive is logical OR with 1 on machine words, but here, we
         are working in the tagged world. As such a different computation is
         required. *)
      (fun machine_width i =>
        let! tmp1 := Int64.shift_right_logical i 1 in
        Target_ocaml_int.of_int64 machine_width tmp1)
      T.these_tagged_immediates T.any_tagged_immediate.
End Simplify_reinterpret_unboxed_int64_as_tagged_int63.

(* PORT-GAP(loose): 606-621, as above, with [module Src = Target_ocaml_int
   module Dst = Int64 let prover = T.meet_equals_tagged_immediates let
   convert ~machine_width:_ i = Int64.add (Int64.mul
   (Target_ocaml_int.to_int64 i) 2L) 1L let these = T.these_naked_int64s let
   any_dst = T.any_naked_int64]. *)
Module Simplify_reinterpret_tagged_int63_as_unboxed_int64.
  Definition simplify :=
    Make_simplify_reinterpret_64_bit_word.simplify Target_ocaml_int.Set_.fold
      Int64.Set_.add Int64.Set_.empty T.meet_equals_tagged_immediates
      (* This primitive is the identity on machine words, but as above, we
         are working in the tagged world. *)
      (fun (_ : Target_system.Machine_width.t) i =>
        let! tmp1 := Target_ocaml_int.to_int64 i in
        let! tmp2 := Int64.mul tmp1 int64_2L in
        Int64.add tmp2 int64_1L)
      T.these_naked_int64s T.any_naked_int64.
End Simplify_reinterpret_tagged_int63_as_unboxed_int64.

(* 623-637 *)
Definition simplify_reinterpret_64_bit_word
    (reinterpret : P.Reinterpret_64_bit_word.t) (dacc : DA.t)
    (original_term : Named.t) (arg : Simple.t) (arg_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  match reinterpret with
  | P.Reinterpret_64_bit_word.Unboxed_int64_as_unboxed_float64 =>
    Simplify_reinterpret_unboxed_int64_as_unboxed_float64.simplify dacc
      original_term arg arg_ty result_var
  | P.Reinterpret_64_bit_word.Unboxed_float64_as_unboxed_int64 =>
    Simplify_reinterpret_unboxed_float64_as_unboxed_int64.simplify dacc
      original_term arg arg_ty result_var
  | P.Reinterpret_64_bit_word.Unboxed_int64_as_tagged_int63 =>
    Simplify_reinterpret_unboxed_int64_as_tagged_int63.simplify dacc
      original_term arg arg_ty result_var
  | P.Reinterpret_64_bit_word.Tagged_int63_as_unboxed_int64 =>
    Simplify_reinterpret_tagged_int63_as_unboxed_int64.simplify dacc
      original_term arg arg_ty result_var
  end.

(* PORT-GAP(loose): 639-669, the functor [Make_simplify_float_arith_op (FP :
   sig module F : Numeric_types.Float_by_bit_pattern val meet :
   T.Typing_env.t -> T.t -> F.Set.t T.meet_shortcut val these : F.Set.t ->
   T.t val kind : K.t end)] is a module whose function [simplify] takes
   first what the functor uses of [FP] (the variables of the section, in
   this order). *)
Module Make_simplify_float_arith_op.
  Section FP.
    Context {FP_F_t FP_F_Set_t : Type}.
    Variable FP_F_Set_is_empty : FP_F_Set_t -> M bool.
    Variable FP_F_Set_map :
      (FP_F_t -> M FP_F_t) -> FP_F_Set_t -> M FP_F_Set_t.
    Variable FP_F_IEEE_semantics_abs : FP_F_t -> M FP_F_t.
    Variable FP_F_IEEE_semantics_neg : FP_F_t -> M FP_F_t.
    Variable FP_meet :
      T.Typing_env.t -> T.t -> M (T.meet_shortcut FP_F_Set_t).
    Variable FP_these : FP_F_Set_t -> M T.t.
    Variable FP_kind : K.t.

    (* 649-668 *)
    Definition simplify (op : P.unary_float_arith_op) (dacc : DA.t)
        (original_term : Named.t) (_ : Simple.t) (arg_ty : T.t)
        (result_var : Bound_var.t) : M SPR.t :=
      (* 651: [let module F = FP.F in] *)
      let* denv := DA.denv dacc in
      let* proof :=
        let! tmp1 := DE.typing_env denv in
        FP_meet tmp1 arg_ty
      in
      match proof with
      | T.Known_result fs =>
        (* 655: [Known_result fs when DE.propagating_float_consts denv] *)
        let! tmp1 := DE.propagating_float_consts denv in
        if tmp1
        then
          (let! tmp1 := FP_F_Set_is_empty fs in
           assert_ (negb tmp1)) ;;
          let& f :=
            match op with
            | P.Abs => FP_F_IEEE_semantics_abs
            | P.Neg => FP_F_IEEE_semantics_neg
            end
          in
          let* possible_results := FP_F_Set_map f fs in
          let* ty := FP_these possible_results in
          let* dacc := DA.add_variable dacc result_var ty in
          SPR.create original_term true dacc
        else SPR.create_unknown dacc result_var FP_kind original_term
      | T.Need_meet =>
        SPR.create_unknown dacc result_var FP_kind original_term
      | T.Invalid => SPR.create_invalid dacc
      end.
  End FP.
End Make_simplify_float_arith_op.

(* PORT-GAP(loose): 671-679, the argument of the functor, [struct module F =
   Float let meet = T.meet_naked_floats let these = T.these_naked_floats let
   kind = K.naked_float end], is the arguments of the function. *)
Module Simplify_float_arith_op.
  Definition simplify :=
    Make_simplify_float_arith_op.simplify Float.Set_.is_empty Float.Set_.map
      Float.IEEE_semantics.abs Float.IEEE_semantics.neg T.meet_naked_floats
      T.these_naked_floats K.naked_float.
End Simplify_float_arith_op.

(* PORT-GAP(loose): 681-689, as above, with [module F = Float32 let meet =
   T.meet_naked_float32s let these = T.these_naked_float32s let kind =
   K.naked_float32]. *)
Module Simplify_float32_arith_op.
  Definition simplify :=
    Make_simplify_float_arith_op.simplify Float32.Set_.is_empty
      Float32.Set_.map Float32.IEEE_semantics.abs Float32.IEEE_semantics.neg
      T.meet_naked_float32s T.these_naked_float32s K.naked_float32.
End Simplify_float32_arith_op.

(* 691 *)
Definition simplify_float_arith_op := Simplify_float_arith_op.simplify.

(* 693 *)
Definition simplify_float32_arith_op := Simplify_float32_arith_op.simplify.

(* 695-708 *)
Definition simplify_is_boxed_float (dacc : DA.t) (original_term : Named.t)
    (_ : Simple.t) (arg_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let* denv := DA.denv dacc in
  let* machine_width := DE.machine_width denv in
  let! tmp1 := DA.typing_env dacc in
  let! tmp2 := T.prove_is_or_is_not_a_boxed_float tmp1 arg_ty in
  match tmp2 with
  | T.Proved is_a_boxed_float =>
    let* imm := Target_ocaml_int.bool_ machine_width is_a_boxed_float in
    let* ty := T.this_naked_immediate imm in
    let* dacc := DA.add_variable dacc result_var ty in
    SPR.create original_term true dacc
  | T.Unknown =>
    SPR.create_unknown dacc result_var K.naked_immediate original_term
  end.

(* 710-727 *)
Definition simplify_is_flat_float_array (dacc : DA.t)
    (original_term : Named.t) (_ : Simple.t) (arg_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* denv := DA.denv dacc in
  let* machine_width := DE.machine_width denv in
  let! tmp1 := DA.typing_env dacc in
  let! tmp2 := T.meet_is_flat_float_array tmp1 arg_ty in
  match tmp2 with
  | T.Known_result is_flat_float_array =>
    let* imm := Target_ocaml_int.bool_ machine_width is_flat_float_array in
    let* ty := T.this_naked_immediate imm in
    let* dacc := DA.add_variable dacc result_var ty in
    let! tmp1 := Reg_width_const.naked_immediate imm in
    let! tmp2 := Simple.const tmp1 in
    let! tmp3 := Named.create_simple tmp2 in
    SPR.create tmp3 false dacc
  | T.Need_meet =>
    SPR.create_unknown dacc result_var K.naked_immediate original_term
  | T.Invalid => SPR.create_invalid dacc
  end.

(* 729-731. In the compiler: [dacc ~kind ~original_term ~arg:_ ~arg_ty:_
   ~result_var]. *)
Definition simplify_opaque_identity (dacc : DA.t) (kind : K.t)
    (original_term : Named.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unknown dacc result_var kind original_term.

(* 733-735 *)
Definition simplify_reinterpret_boxed_vector (dacc : DA.t)
    (original_term : Named.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unknown dacc result_var Flambda_kind.value original_term.

(* 737-742 *)
Definition simplify_end_region (dacc : DA.t) (original_term : Named.t)
    (_ : Simple.t) (_ : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let* denv := DA.denv dacc in
  let* machine_width := DE.machine_width denv in
  let* ty :=
    let! tmp1 := Target_ocaml_int.zero machine_width in
    T.this_tagged_immediate tmp1
  in
  let* dacc := DA.add_variable dacc result_var ty in
  SPR.create original_term false dacc.

(* 744-749 *)
Definition simplify_end_try_region (dacc : DA.t) (original_term : Named.t)
    (_ : Simple.t) (_ : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let* denv := DA.denv dacc in
  let* machine_width := DE.machine_width denv in
  let* ty :=
    let! tmp1 := Target_ocaml_int.zero machine_width in
    T.this_tagged_immediate tmp1
  in
  let* dacc := DA.add_variable dacc result_var ty in
  SPR.create original_term false dacc.

(* 751-753. In the compiler: [~mode:_ dacc ~original_term ~arg:_ ~arg_ty:_
   ~result_var]. *)
Definition simplify_int_as_pointer (_ : Alloc_mode.For_allocations.t)
    (dacc : DA.t) (original_term : Named.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unknown dacc result_var K.value original_term.

(* 755-757. In the compiler: [~dimension:_ dacc ~original_term ~arg:_
   ~arg_ty:_ ~result_var]. *)
Definition simplify_bigarray_length (_ : int) (dacc : DA.t)
    (original_term : Named.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unknown dacc result_var K.naked_immediate original_term.

(* 759-784. In the compiler: [~kind:_ ~source_mutability
   ~destination_mutability ~alloc_region:_ dacc ~original_term ~arg:_
   ~arg_ty ~result_var]. *)
Definition simplify_duplicate_array (_ : P.Duplicate_array_kind.t)
    (source_mutability destination_mutability : Mutability.t)
    (_ : Variable_.t) (dacc : DA.t) (original_term : Named.t) (_ : Simple.t)
    (arg_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
  (* This simplification should eliminate bounds checks on array literals. *)
  let* denv := DA.denv dacc in
  let* machine_width := DE.machine_width denv in
  match source_mutability, destination_mutability with
  | Mutability.Immutable, Mutability.Mutable =>
    let! tmp1 := DA.typing_env dacc in
    let! tmp2 := T.meet_is_immutable_array tmp1 arg_ty in
    match tmp2 with
    | T.Invalid => SPR.create_invalid dacc
    | T.Need_meet =>
      let* dacc := DA.add_variable dacc result_var T.any_value in
      SPR.create original_term false dacc
    | T.Known_result (T3 element_kind fields alloc_mode) =>
      (* 773-776: [a |> f b] is [f b a] *)
      let* length :=
        let! tmp1 := Array.length fields in
        let! tmp2 := Target_ocaml_int.of_int machine_width tmp1 in
        T.this_tagged_immediate tmp2
      in
      let* ty := T.mutable_array element_kind length alloc_mode in
      let* dacc := DA.add_variable dacc result_var ty in
      SPR.create original_term false dacc
    end
  (* PORT-GAP(loose): 780-781, the compiler's case names the nine pairs
     ([(Immutable | Immutable_unique | Mutable), (Immutable |
     Immutable_unique | Mutable)]); Rocq refuses a pattern that an earlier
     case has taken, so the eight that are left are named. *)
  | (Mutability.Immutable | Mutability.Immutable_unique | Mutability.Mutable),
    (Mutability.Immutable | Mutability.Immutable_unique)
  | (Mutability.Immutable_unique | Mutability.Mutable), Mutability.Mutable =>
    fatal_errorf2
      "Combination of mutabilities not supported for [Duplicate_array]:@ %a"
      Named.print original_term
  end.

(* 786-792. In the compiler: [~kind:_ ~alloc_region:_ dacc ~original_term
   ~arg:_ ~arg_ty ~result_var]. *)
Definition simplify_duplicate_block (_ : P.Duplicate_block_kind.t)
    (_ : Variable_.t) (dacc : DA.t) (original_term : Named.t) (_ : Simple.t)
    (arg_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
  (* Any alias in the type to the whole block will be dropped, but aliases
     inside the type (e.g. in fields) can remain. *)
  let* ty :=
    let! tmp1 := DA.typing_env dacc in
    T.remove_outermost_alias tmp1 arg_ty
  in
  let* dacc := DA.add_variable dacc result_var ty in
  SPR.create original_term false dacc.

(* 794-874. In the compiler: [~alloc_region dbg dacc ~original_term ~arg
   ~arg_ty ~result_var]. *)
Definition simplify_obj_dup (alloc_region : Variable_.t) (dbg : Debuginfo.t)
    (dacc : DA.t) (original_term : Named.t) (arg : Simple.t) (arg_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  (* This must respect the semantics of physical equality. *)
  let* typing_env := DA.typing_env dacc in
  (* PORT-GAP(loose): 798, the attribute [@inline] is not kept. *)
  let& elide_primitive :=
    fun (_ : unit) =>
    let* dacc := DA.add_variable dacc result_var arg_ty in
    let! tmp1 := Named.create_simple arg in
    SPR.create tmp1 true dacc
  in
  let! tmp1 := T.prove_is_a_boxed_or_tagged_number typing_env arg_ty in
  match tmp1 with
  | T.Proved T.Tagged_immediate
  | T.Proved (T.Boxed Alloc_mode.For_types.Heap _ _) =>
    elide_primitive tt
  | T.Proved
      (T.Boxed (Alloc_mode.For_types.Heap_or_local | Alloc_mode.For_types.Local)
         boxable_number contents_ty) =>
    (* 807-870. [TE.get_alias_then_canonical_simple_exn ~min_name_mode
       typing_env contents_ty]: the arguments are in the order of the
       interface. *)
    match_exn
      (fun _ =>
        TE.get_alias_then_canonical_simple_exn typing_env (Some NM.normal)
          None contents_ty)
      Not_found
      (fun _ =>
        (* 811-847 *)
        (* Add a projection so we have a variable bound to the contents of the
           boxed value. This means that when the contents are used directly, e.g.
           after unboxing of the boxed value, the duplicated block itself can
           become unused. This might have the effect of moving a projection
           earlier in the event that it already exists later, but this is probably
           fine: this operation isn't that common. *)
        let* contents_var :=
          let! tmp1 := T.kind contents_ty in
          Variable_.create None "obj_dup_contents" tmp1
        in
        let& contents_var_duid := Flambda_debug_uid.none in
        let* unbox_expr :=
          Named.create_prim (P.Unary (P.Unbox_number boxable_number) arg) dbg
        in
        let* contents_pat :=
          let! tmp1 :=
            Bound_var.create contents_var contents_var_duid NM.normal
          in
          Bound_pattern.singleton tmp1
        in
        let* contents_simple := Simple.var contents_var in
        let* box_expr :=
          let! tmp1 := Alloc_mode.For_allocations.heap alloc_region in
          Named.create_prim
            (P.Unary (P.Box_number boxable_number tmp1) contents_simple)
            dbg
        in
        let* result_pat := Bound_pattern.singleton result_var in
        (* 839-846. [Let.create pat named ~free_names_of_body ~body]: the
           arguments are in the order of the interface. *)
        let& wrap :=
          fun (body : Expr.t) =>
          let! tmp1 := Let.create result_pat box_expr body Or_unknown.Unknown in
          let! tmp2 := Expr.create_let tmp1 in
          let! tmp3 :=
            Let.create contents_pat unbox_expr tmp2 Or_unknown.Unknown
          in
          Expr.create_let tmp3
        in
        SPR.create_rewritten wrap)
      (fun contents =>
        (* 848-870 *)
        let& boxer :=
          match boxable_number with
          | K.Boxable_number.Naked_float => T.box_float
          | K.Boxable_number.Naked_float32 => T.box_float32
          | K.Boxable_number.Naked_int32 => T.box_int32
          | K.Boxable_number.Naked_int64 => T.box_int64
          | K.Boxable_number.Naked_nativeint => T.box_nativeint
          | K.Boxable_number.Naked_vec128 => T.box_vec128
          | K.Boxable_number.Naked_vec256 => T.box_vec256
          | K.Boxable_number.Naked_vec512 => T.box_vec512
          | K.Boxable_number.Naked_mask => T.box_mask
          end
        in
        let* ty := boxer contents_ty Alloc_mode.For_types.heap in
        let* dacc := DA.add_variable dacc result_var ty in
        let! tmp1 := Alloc_mode.For_allocations.heap alloc_region in
        let! tmp2 :=
          Named.create_prim
            (P.Unary (P.Box_number boxable_number tmp1) contents)
            dbg
        in
        SPR.create tmp2 true dacc)
  | T.Unknown =>
    let! tmp1 := T.prove_strings typing_env arg_ty in
    match tmp1 with
    | T.Proved _ => elide_primitive tt
    | T.Unknown => SPR.create_unknown dacc result_var K.value original_term
    end
  end.

(* 876-880. In the compiler: [~original_prim dacc ~original_term ~arg:_
   ~arg_ty:_ ~result_var]. *)
Definition simplify_get_header (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* PORT-GAP(loose): 882, the attribute [@inline always] is not kept. *)
(* 882-989. In the compiler: [access_kind ~field ~min_name_mode dacc
   ~original_term _dbg ~arg:block ~arg_ty:block_ty ~result_var]. *)
Definition simplify_immutable_block_load0
    (access_kind : P.Block_access_kind.t) (field : Target_ocaml_int.t)
    (min_name_mode : Name_mode.t) (dacc : DA.t) (original_term : Named.t)
    (_dbg : Debuginfo.t) (block : Simple.t) (block_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* result_kind := P.Block_access_kind.element_kind_for_load access_kind in
  let* result_var' := Bound_var.var result_var in
  let* denv := DA.denv dacc in
  let* machine_width := DE.machine_width denv in
  let* typing_env := DA.typing_env dacc in
  let! tmp1 :=
    T.meet_block_field_simple typing_env min_name_mode result_kind block_ty
      field
  in
  match tmp1 with
  | T.Invalid => SPR.create_invalid dacc
  | T.Known_result simple =>
    let* dacc :=
      let! tmp1 := T.alias_type_of result_kind simple in
      DA.add_variable dacc result_var tmp1
    in
    let! tmp1 := Named.create_simple simple in
    SPR.create tmp1 false dacc
  | T.Need_meet =>
    let* n :=
      let! tmp1 := Target_ocaml_int.one machine_width in
      Target_ocaml_int.add field tmp1
    in
    (* 904-924 *)
    let* '(tag, shape) :=
      match access_kind with
      | P.Block_access_kind.Values tag _ _ =>
        let! tmp1 := Or_unknown.map tag Tag.Scannable.to_tag in
        ret
          (tmp1,
           K.Block_shape.Scannable K.Scannable_block_shape.Value_only)
      | P.Block_access_kind.Naked_floats size =>
        let! tmp3 :=
          match size with
          | Or_unknown.Known size =>
            (* We don't expect blocks of naked floats of size zero (it
               doesn't seem that the frontend currently emits code to create
               such blocks) and so it isn't clear whether such blocks should
               have tag zero (like zero-sized naked float arrays) or another
               tag. *)
            let! tmp1 := Target_ocaml_int.zero machine_width in
            let! tmp2 := Target_ocaml_int.equal size tmp1 in
            if tmp2
            then ret Or_unknown.Unknown
            else ret (Or_unknown.Known Tag.double_array_tag)
          | Or_unknown.Unknown => ret Or_unknown.Unknown
          end
        in
        ret (tmp3, K.Block_shape.Float_record)
      | P.Block_access_kind.Mixed tag _ _ shape =>
        let! tmp1 := Or_unknown.map tag Tag.Scannable.to_tag in
        ret
          (tmp1,
           K.Block_shape.Scannable
             (K.Scannable_block_shape.Mixed_record shape))
      end
    in
    (* 925-933: the arguments are in the order of the interfaces. *)
    let* result :=
      let! tmp1 := DA.denv dacc in
      let! tmp2 := DE.machine_width tmp1 in
      let! tmp3 :=
        T.immutable_block_with_size_at_least tmp2 tag n shape result_var'
      in
      Simplify_common.simplify_projection dacc original_term block_ty tmp3
        result_var result_kind
    in
    let! tmp1 := SPR.is_invalid result in
    if tmp1
    then ret result
    else
      (* If the type contains enough information to actually build a
         primitive to make the corresponding block, then we add a CSE
         equation, to try to avoid duplicate allocations in the future. This
         should help with cases such as "Some x -> Some x". *)
      SPR.map_dacc result
        (fun dacc =>
          let! tmp1 := DA.typing_env dacc in
          let! tmp2 :=
            T.prove_unique_fully_constructed_immutable_heap_block tmp1
              block_ty
          in
          match tmp2 with
          | T.Unknown => ret dacc
          | T.Proved (T4 tag shape_from_type _size field_simples) =>
            let! tmp1 := Tag.Scannable.of_tag tag in
            match tmp1 with
            | None => ret dacc
            | Some tag =>
              (* 951-970 *)
              let* block_kind :=
                match access_kind with
                | P.Block_access_kind.Values _ _ _ =>
                  let* arity :=
                    List.map
                      (fun _ => ret K.With_subkind.any_value)
                      field_simples
                  in
                  ret (P.Block_kind.Values tag arity)
                | P.Block_access_kind.Naked_floats _ =>
                  ret P.Block_kind.Naked_floats
                | P.Block_access_kind.Mixed _ _ _ shape =>
                  (* 960-968: [Scannable (Mixed_record shape_from_type) when
                     K.Mixed_block_shape.equal shape shape_from_type] *)
                  match shape_from_type with
                  | K.Block_shape.Scannable
                      (K.Scannable_block_shape.Mixed_record shape_from_type)
                    =>
                    let! tmp1 :=
                      K.Mixed_block_shape.equal shape shape_from_type
                    in
                    if tmp1
                    then ret tt
                    else
                      fatal_error
                        "Block access kind disagrees with block shape from type"
                  | K.Block_shape.Scannable
                      K.Scannable_block_shape.Value_only
                  | K.Block_shape.Float_record =>
                    fatal_error
                      "Block access kind disagrees with block shape from type"
                  end ;;
                  ret (P.Block_kind.Mixed tag shape)
                end
              in
              (* CR alloc_regions: this uses the function's [my_alloc_region] to
                 put in the CSE. This deserves testing with zero_alloc functions
                 to figure out whether this is what we really want. *)
              let* alloc_region := get_my_alloc_region dacc in
              let* prim :=
                let! tmp1 := Alloc_mode.For_allocations.heap alloc_region in
                P.Eligible_for_cse.create
                  (P.Variadic
                     (P.Make_block block_kind Mutability.Immutable tmp1)
                     field_simples)
              in
              match prim with
              | None => ret dacc
              | Some prim =>
                DA.map_denv dacc
                  (fun denv =>
                    let! tmp1 := Bound_var.name_mode result_var in
                    DE.add_cse denv prim block tmp1)
              end
            end
          end)
  end.

(* 991-1007. In the compiler: [access_kind ~field ~min_name_mode dacc
   ~original_term ~dbg ~arg ~arg_ty ~result_var]. *)
Definition simplify_immutable_block_load (access_kind : P.Block_access_kind.t)
    (field : Target_ocaml_int.t) (min_name_mode : Name_mode.t) (dacc : DA.t)
    (original_term : Named.t) (dbg : Debuginfo.t) (arg : Simple.t)
    (arg_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let* result :=
    simplify_immutable_block_load0 access_kind field min_name_mode dacc
      original_term dbg arg arg_ty result_var
  in
  SPR.map_dacc result
    (fun dacc =>
      let* kind :=
        P.Block_access_kind.element_subkind_for_load access_kind
      in
      let& block_shape :=
        match access_kind with
        | P.Block_access_kind.Values _ _ _ =>
          K.Block_shape.Scannable K.Scannable_block_shape.Value_only
        | P.Block_access_kind.Naked_floats _ => K.Block_shape.Float_record
        | P.Block_access_kind.Mixed _ _ _ shape =>
          K.Block_shape.Scannable
            (K.Scannable_block_shape.Mixed_record shape)
        end
      in
      let! tmp1 :=
        Symbol_projection.Projection.block_load field block_shape
      in
      Simplify_common.add_symbol_projection dacc arg tmp1 result_var kind).

(* 1009-1016. In the compiler: [_access_kind ~field:_ ~original_prim dacc
   ~original_term ~dbg:_ ~arg ~arg_ty:_ ~result_var]. *)
Definition simplify_mutable_block_load
    (_access_kind : P.Block_access_kind.t) (_ : Target_ocaml_int.t)
    (original_prim : P.t) (dacc : DA.t) (original_term : Named.t)
    (_ : Debuginfo.t) (arg : Simple.t) (_ : T.t) (result_var : Bound_var.t)
    : M SPR.t :=
  let! tmp1 := Simple.is_const arg in
  if tmp1
  then SPR.create_invalid dacc
  else
    let! tmp2 := P.result_kind' original_prim in
    SPR.create_unknown dacc result_var tmp2 original_term.

(* 1018-1022 *)
Definition simplify_lazy (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1025-1028 *)
Definition simplify_is_null (dacc : DA.t) (original_term : Named.t)
    (scrutinee : Simple.t) (scrutinee_ty : T.t) (result_var : Bound_var.t)
    : M SPR.t :=
  simplify_relational_primitive dacc original_term scrutinee scrutinee_ty
    result_var TE.add_is_null_relation.

(* 1030-1034 *)
Definition simplify_peek (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1036-1106 *)
Definition simplify_unary_primitive (dacc : DA.t) (original_prim : P.t)
    (prim : P.unary_primitive) (arg : Simple.t) (arg_ty : T.t)
    (dbg : Debuginfo.t) (result_var : Bound_var.t) : M SPR.t :=
  let* min_name_mode := Bound_var.name_mode result_var in
  let* original_term := Named.create_prim original_prim dbg in
  (* 1040-1104: a function of this file with its first arguments is a value
     (no call is made until [simplifier] has all its arguments). Where the
     compiler gives by its label an argument that comes after [dacc] in the
     definition ([~dbg], [~kind]), the value is a [fun]. *)
  let& simplifier :=
    match prim with
    | P.Block_load kind (Mutability.Immutable | Mutability.Immutable_unique)
        field =>
      fun dacc original_term =>
      simplify_immutable_block_load kind field min_name_mode dacc
        original_term dbg
    | P.Block_load kind Mutability.Mutable field =>
      fun dacc original_term =>
      simplify_mutable_block_load kind field original_prim dacc original_term
        dbg
    | P.Project_value_slot project_from value_slot =>
      simplify_project_value_slot project_from value_slot min_name_mode
    | P.Project_function_slot move_from move_to =>
      simplify_project_function_slot move_from move_to min_name_mode
    | P.Unbox_number boxable_number_kind =>
      simplify_unbox_number boxable_number_kind
    | P.Box_number boxable_number_kind alloc_mode =>
      simplify_box_number boxable_number_kind alloc_mode
    | P.Tag_immediate => simplify_tag_immediate
    | P.Untag_immediate => simplify_untag_immediate
    | P.Is_int variant_only => simplify_is_int variant_only
    | P.Is_null => simplify_is_null
    | P.Get_tag => simplify_get_tag
    | P.Array_length array_kind => simplify_array_length array_kind
    | P.String_length _ => simplify_string_length
    | P.Int_arith kind op =>
      match kind with
      | K.Standard_int.Tagged_immediate =>
        Unary_int_arith_tagged_immediate.simplify op
      | K.Standard_int.Naked_immediate =>
        Unary_int_arith_naked_immediate.simplify op
      | K.Standard_int.Naked_int8 => Unary_int_arith_naked_int8.simplify op
      | K.Standard_int.Naked_int16 => Unary_int_arith_naked_int16.simplify op
      | K.Standard_int.Naked_int32 => Unary_int_arith_naked_int32.simplify op
      | K.Standard_int.Naked_int64 => Unary_int_arith_naked_int64.simplify op
      | K.Standard_int.Naked_nativeint =>
        Unary_int_arith_naked_nativeint.simplify op
      end
    | P.Float_arith P.Float64 op => simplify_float_arith_op op
    | P.Float_arith P.Float32 op => simplify_float32_arith_op op
    | P.Num_conv src dst =>
      match src with
      | K.Standard_int_or_float.Tagged_immediate =>
        Simplify_int_conv_tagged_immediate.simplify dst
      | K.Standard_int_or_float.Naked_immediate =>
        Simplify_int_conv_naked_immediate.simplify dst
      | K.Standard_int_or_float.Naked_float32 =>
        Simplify_int_conv_naked_float32.simplify dst
      | K.Standard_int_or_float.Naked_float =>
        Simplify_int_conv_naked_float.simplify dst
      | K.Standard_int_or_float.Naked_int8 =>
        Simplify_int_conv_naked_int8.simplify dst
      | K.Standard_int_or_float.Naked_int16 =>
        Simplify_int_conv_naked_int16.simplify dst
      | K.Standard_int_or_float.Naked_int32 =>
        Simplify_int_conv_naked_int32.simplify dst
      | K.Standard_int_or_float.Naked_int64 =>
        Simplify_int_conv_naked_int64.simplify dst
      | K.Standard_int_or_float.Naked_nativeint =>
        Simplify_int_conv_naked_nativeint.simplify dst
      end
    | P.Boolean_not => simplify_boolean_not
    | P.Reinterpret_64_bit_word reinterpret =>
      simplify_reinterpret_64_bit_word reinterpret
    | P.Reinterpret_boxed_vector => simplify_reinterpret_boxed_vector
    | P.Is_boxed_float => simplify_is_boxed_float
    | P.Is_flat_float_array => simplify_is_flat_float_array
    | P.Int_as_pointer mode => simplify_int_as_pointer mode
    | P.Bigarray_length dimension => simplify_bigarray_length dimension
    | P.Duplicate_array kind source_mutability destination_mutability
        alloc_region =>
      simplify_duplicate_array kind source_mutability destination_mutability
        alloc_region
    | P.Duplicate_block kind alloc_region =>
      simplify_duplicate_block kind alloc_region
    | P.Opaque_identity _ kind =>
      fun dacc => simplify_opaque_identity dacc kind
    | P.End_region _ => simplify_end_region
    | P.End_try_region _ => simplify_end_try_region
    | P.Obj_dup alloc_region => simplify_obj_dup alloc_region dbg
    | P.Get_header => simplify_get_header original_prim
    | P.Peek _ => simplify_peek original_prim
    | P.Make_lazy _ _ => simplify_lazy original_prim
    end
  in
  simplifier dacc original_term arg arg_ty result_var.
