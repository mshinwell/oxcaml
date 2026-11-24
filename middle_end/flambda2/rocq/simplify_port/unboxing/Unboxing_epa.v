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

(* This file follows middle_end/flambda2/simplify/unboxing/unboxing_epa.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the recursive functions,
   the arguments by place) is that of GUIDE.md; the Rocq form of the type
   [unboxed_arg] is that of decl/Unboxing_epa.v, and that of
   [variant_argument] is written in the same way. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Apply_cont_rewrite_id Array Bound_parameter
  Continuation_extra_params_and_args Flambda2_types Flambda_kind
  Flambda_primitive Format Function_slot List Name_mode Option Or_unknown
  Reg_width_const Simple Tag Target_ocaml_int Target_system Unboxers
  Unboxing_types Value_slot Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17 *)
(* PORT-GAP(verbatim): 21-23, the two exceptions of the file are the
   compiler's lines; they stand at the head of the extracted file, before
   the two module abbreviations of 18-19. *)
(*OCAML
open! Simplify_import

exception Invalid_apply_cont

exception Prevent_current_unboxing
OCAML*)
(* 18-19 *)
Module U := Unboxing_types.
Module Extra_param_and_args := U.Extra_param_and_args.

(* 21 *)
Parameter Invalid_apply_cont : exception unit.
Extract Inlined Constant Invalid_apply_cont =>
  "((fun () -> Invalid_apply_cont), (function Invalid_apply_cont -> Some () | _ -> None))".

(* 23 *)
Parameter Prevent_current_unboxing : exception unit.
Extract Inlined Constant Prevent_current_unboxing =>
  "((fun () -> Prevent_current_unboxing), (function Prevent_current_unboxing -> Some () | _ -> None))".

(* 25 *)
Definition prevent_current_unboxing {A : Type} (_ : unit) : M A :=
  raise_ Prevent_current_unboxing tt.

(* 27-31 *)
(* PORT-GAP(type): the type has an inline record. In Rocq it is the
   inductive type [unboxed_arg_], in the form of decl/Unboxing_epa.v (the
   field of [Added_by_wrapper_at_rewrite_use] by place); the OCaml
   definition is the compiler's text, which the directive of [unboxed_arg]
   puts at this place of the extracted file. *)
Inductive unboxed_arg_ : Type :=
| Poison : unboxed_arg_
| Available : Simple.t -> unboxed_arg_
| Generated : Variable_.t -> unboxed_arg_
| Added_by_wrapper_at_rewrite_use : int -> unboxed_arg_.
Extract Inductive unboxed_arg_ => "unboxed_arg"
  [ "Poison" "Available" "Generated"
    "(fun x__1 -> (Added_by_wrapper_at_rewrite_use { nth_arg = x__1 } : unboxed_arg))" ]
  "(fun f__1 f__2 f__3 f__4 x__0 -> match (x__0 : unboxed_arg) with Poison -> f__1 () | Available x__1 -> f__2 x__1 | Generated x__1 -> f__3 x__1 | Added_by_wrapper_at_rewrite_use { nth_arg = x__1 } -> f__4 x__1)".
Definition unboxed_arg : Type := unboxed_arg_.
Extract Constant unboxed_arg => "
  | Poison (* used for recursive calls *)
  | Available of Simple.t
  | Generated of Variable.t
  | Added_by_wrapper_at_rewrite_use of { nth_arg : int }
".

(* 33-38 *)
Definition _print_unboxed_arg (ppf : Format.formatter)
    (unboxed_arg : Unboxing_epa.unboxed_arg) : M unit :=
  match unboxed_arg with
  | Poison => Format.fprintf0 ppf "poison"
  | Available simple => Format.fprintf2 ppf "simple: %a" Simple.print simple
  | Generated v => Format.fprintf2 ppf "generated: %a" Variable_.print v
  | Added_by_wrapper_at_rewrite_use nth_arg =>
    Format.fprintf1 ppf "added_by_wrapper(%d)" nth_arg
  end.

(* 40-45 *)
Definition type_of_arg_being_unboxed (unboxed_arg : Unboxing_epa.unboxed_arg)
    : M (option T.t) :=
  match unboxed_arg with
  | Poison => ret None
  | Available simple =>
    let! tmp1 := T.alias_type_of K.value simple in
    ret (Some tmp1)
  | Generated _ =>
    let! tmp1 := T.unknown K.value in
    ret (Some tmp1)
  | Added_by_wrapper_at_rewrite_use _ => prevent_current_unboxing tt
  end.

(* 47-82 *)
Definition unbox_arg (unboxer : Unboxers.unboxer) (typing_env_at_use : TE.t)
    (arg_being_unboxed : unboxed_arg) : M (EPA.Extra_arg.t * unboxed_arg) :=
  match arg_being_unboxed with
  | Poison =>
    let* extra_arg :=
      let! tmp1 := Simple.const unboxer.(Unboxers.poison_const) in
      ret (EPA.Extra_arg.Already_in_scope tmp1)
    in
    ret (extra_arg, Poison)
  | Available arg_at_use =>
    let* arg_type := T.alias_type_of K.value arg_at_use in
    (* 58-59: [unboxer.prove_simple typing_env_at_use arg_type
       ~min_name_mode:Name_mode.normal]: the arguments are in the order of
       the type of the field. *)
    let! tmp1 :=
      unboxer.(Unboxers.prove_simple) typing_env_at_use Name_mode.normal
        arg_type
    in
    match tmp1 with
    | T.Invalid => raise_ Invalid_apply_cont tt
    | T.Known_result simple =>
      ret (EPA.Extra_arg.Already_in_scope simple, Available simple)
    | T.Need_meet =>
      let* var :=
        Variable_.create None unboxer.(Unboxers.var_name)
          unboxer.(Unboxers.var_kind)
      in
      let* prim := unboxer.(Unboxers.unboxing_prim) arg_at_use in
      let& extra_arg := EPA.Extra_arg.New_let_binding var prim in
      ret (extra_arg, Generated var)
    end
  | Generated var =>
    let* arg_at_use := Simple.var var in
    let* var :=
      Variable_.create None unboxer.(Unboxers.var_name)
        unboxer.(Unboxers.var_kind)
    in
    let* prim := unboxer.(Unboxers.unboxing_prim) arg_at_use in
    let& extra_arg := EPA.Extra_arg.New_let_binding var prim in
    ret (extra_arg, Generated var)
  | Added_by_wrapper_at_rewrite_use nth_arg =>
    let* var :=
      Variable_.create None "unboxed_field" unboxer.(Unboxers.var_kind)
    in
    ret
      ( EPA.Extra_arg.New_let_binding_with_named_args var
          (fun args =>
            let* arg_simple := List.nth args nth_arg in
            unboxer.(Unboxers.unboxing_prim) arg_simple),
        Generated var )
  end.

(* Helpers for the variant case *)
(* **************************** *)

(* 87-92 *)
(* PORT-GAP(type): the type has an inline record. In Rocq it is the
   inductive type [variant_argument_], whose constructor takes the fields by
   place; the OCaml definition is the compiler's text, which the directive
   of [variant_argument] puts at this place of the extracted file. *)
Inductive variant_argument_ : Type :=
| Not_a_constant_constructor : variant_argument_
| Maybe_constant_constructor : Simple.t -> unboxed_arg -> variant_argument_.
Extract Inductive variant_argument_ => "variant_argument"
  [ "Not_a_constant_constructor"
    "(fun (x__1, x__2) -> (Maybe_constant_constructor { is_int = x__1; arg_being_unboxed = x__2 } : variant_argument))" ]
  "(fun f__1 f__2 x__0 -> match (x__0 : variant_argument) with Not_a_constant_constructor -> f__1 () | Maybe_constant_constructor { is_int = x__1; arg_being_unboxed = x__2 } -> f__2 x__1 x__2)".
Definition variant_argument : Type := variant_argument_.
Extract Constant variant_argument => "
  | Not_a_constant_constructor
  | Maybe_constant_constructor of
      { is_int : Simple.t;
        arg_being_unboxed : unboxed_arg
      }
".

(* 94-99 *)
Definition extra_arg_for_is_int (machine_width : Target_system.Machine_width.t)
    (variant_arg : variant_argument) : M EPA.Extra_arg.t :=
  match variant_arg with
  | Maybe_constant_constructor is_int _ =>
    ret (EPA.Extra_arg.Already_in_scope is_int)
  | Not_a_constant_constructor =>
    let! tmp1 := Simple.untagged_const_false machine_width in
    ret (EPA.Extra_arg.Already_in_scope tmp1)
  end.

(* 101-119 *)
Definition extra_arg_for_ctor (typing_env_at_use : TE.t)
    (variant_arg : variant_argument) : M EPA.Extra_arg.t :=
  let* machine_width := TE.machine_width typing_env_at_use in
  match variant_arg with
  | Not_a_constant_constructor =>
    let! tmp1 := Target_ocaml_int.of_int machine_width 0 in
    let! tmp2 := Simple.untagged_const_int tmp1 in
    ret (EPA.Extra_arg.Already_in_scope tmp2)
  | Maybe_constant_constructor _ arg_being_unboxed =>
    let! tmp1 := type_of_arg_being_unboxed arg_being_unboxed in
    match tmp1 with
    | None =>
      let! tmp1 := Target_ocaml_int.of_int machine_width 0 in
      let! tmp2 := Simple.untagged_const_int tmp1 in
      ret (EPA.Extra_arg.Already_in_scope tmp2)
    | Some arg_type =>
      let! tmp1 :=
        T.meet_tagging_of_simple typing_env_at_use Name_mode.normal arg_type
      in
      match tmp1 with
      | T.Known_result simple => ret (EPA.Extra_arg.Already_in_scope simple)
      | T.Need_meet => prevent_current_unboxing tt
      | T.Invalid => raise_ Invalid_apply_cont tt
      end
    end
  end.

(* 121-162. The fields of [At_least_one] are by place, in the order of the
   type: [is_int], then [ctor]. *)
Definition extra_args_for_const_ctor_of_variant
    (const_ctors_decision : U.const_ctors_decision) (typing_env_at_use : TE.t)
    (rewrite_id : Apply_cont_rewrite_id.t) (variant_arg : variant_argument)
    : M U.const_ctors_decision :=
  let* machine_width := TE.machine_width typing_env_at_use in
  match const_ctors_decision with
  | U.Zero =>
    match variant_arg with
    | Not_a_constant_constructor => ret const_ctors_decision
    | Maybe_constant_constructor _ _ => raise_ Invalid_apply_cont tt
    end
  | U.At_least_one is_int (U.Do_not_unbox reason) =>
    let* is_int :=
      let! tmp1 := extra_arg_for_is_int machine_width variant_arg in
      Extra_param_and_args.update_param_args is_int rewrite_id tmp1
    in
    ret (U.At_least_one is_int (U.Do_not_unbox reason))
  | U.At_least_one is_int
      (U.Unbox (U.Number K.Naked_number_kind.Naked_immediate ctor)) =>
    let* is_int :=
      let! tmp1 := extra_arg_for_is_int machine_width variant_arg in
      Extra_param_and_args.update_param_args is_int rewrite_id tmp1
    in
    try_with
      (fun _ =>
        let* ctor :=
          let! tmp1 := extra_arg_for_ctor typing_env_at_use variant_arg in
          Extra_param_and_args.update_param_args ctor rewrite_id tmp1
        in
        ret
          (U.At_least_one is_int
             (U.Unbox (U.Number K.Naked_number_kind.Naked_immediate ctor))))
      Prevent_current_unboxing
      (fun _ =>
        ret
          (U.At_least_one is_int
             (U.Do_not_unbox U.Not_enough_information_at_use)))
  | U.At_least_one _
      (U.Unbox
         ( U.Unique_tag_and_size _ _ _ | U.Variant _ _ _
         | U.Closure_single_entry _ _
         | U.Number
             ( K.Naked_number_kind.Naked_float
             | K.Naked_number_kind.Naked_float32
             | K.Naked_number_kind.Naked_int32
             | K.Naked_number_kind.Naked_int64
             | K.Naked_number_kind.Naked_int8
             | K.Naked_number_kind.Naked_int16
             | K.Naked_number_kind.Naked_nativeint
             | K.Naked_number_kind.Naked_vec128
             | K.Naked_number_kind.Naked_vec256
             | K.Naked_number_kind.Naked_vec512
             | K.Naked_number_kind.Naked_mask )
             _ )) =>
    fatal_errorf0 "Bad kind for unboxing the constant constructor of a variant"
  end.

(* Helpers for the number case *)
(* *************************** *)

(* 167-173 *)
Definition compute_extra_arg_for_number (kind : K.Naked_number_kind.t)
    (unboxer : Unboxers.unboxer) (epa : Extra_param_and_args.t)
    (rewrite_id : Apply_cont_rewrite_id.t) (typing_env_at_use : TE.t)
    (arg_being_unboxed : unboxed_arg) : M U.decision_ :=
  let* '(extra_arg, _new_arg_being_unboxed) :=
    unbox_arg unboxer typing_env_at_use arg_being_unboxed
  in
  let* epa := Extra_param_and_args.update_param_args epa rewrite_id extra_arg in
  ret (U.Unbox (U.Number kind epa)).

(* Helpers for the block case *)
(* ************************** *)

(* 178-218. The fields of the inline records of [P.Block_access_kind.t] are
   by place, in the order of the type: [tag], [size], [field_kind] for
   [Values], and [tag], [size], [field_kind], [shape] for [Mixed]. The
   comment of 199-201 on the field kind of the value prefix is not copied. *)
Definition access_kind_and_poison_const {A : Type}
    (machine_width : Target_system.Machine_width.t) (tag : Tag.t)
    (shape : K.Block_shape.t) (fields : list A) (index : int)
    : M (P.Block_access_kind.t * Const.t) :=
  let* size :=
    let! tmp1 := List.length fields in
    let! tmp2 := Target_ocaml_int.of_int machine_width tmp1 in
    ret (Or_unknown.Known tmp2)
  in
  match shape with
  | K.Block_shape.Scannable K.Scannable_block_shape.Value_only =>
    let! tmp1 := Const.const_poison K.value "variant_unboxing_field" in
    let! tmp2 := Tag.Scannable.of_tag tag in
    let! tmp3 := Option.get tmp2 in
    ret
      ( P.Block_access_kind.Values (Or_unknown.Known tmp3) size
          P.Block_access_field_kind.Any_value,
        tmp1 )
  | K.Block_shape.Float_record =>
    let! tmp1 :=
      Const.const_poison K.naked_float "variant_unboxing_float_record"
    in
    ret (P.Block_access_kind.Naked_floats size, tmp1)
  | K.Block_shape.Scannable (K.Scannable_block_shape.Mixed_record shape) =>
    let* '(field_kind, const) :=
      let! tmp1 := K.Mixed_block_shape.value_prefix_size shape in
      if index <? tmp1
      then
        let! tmp2 := Const.const_zero machine_width in
        ret
          ( P.Mixed_block_access_field_kind.Value_prefix
              P.Block_access_field_kind.Any_value,
            tmp2 )
      else
        let* field_kind :=
          let* flat_suffix_index :=
            let! tmp2 := K.Mixed_block_shape.value_prefix_size shape in
            ret (index - tmp2)
          in
          assert_ (flat_suffix_index >=? 0) ;;
          (* 210: [(K.Mixed_block_shape.flat_suffix shape).(flat_suffix_index)]
             is [Array.get]. *)
          let! tmp2 := K.Mixed_block_shape.flat_suffix shape in
          Array.get tmp2 flat_suffix_index
        in
        let! tmp2 := K.Flat_suffix_element.kind field_kind in
        let! tmp3 :=
          Const.const_poison tmp2 "variant_unboxing_mixed_block_field"
        in
        ret (P.Mixed_block_access_field_kind.Flat_suffix field_kind, tmp3)
    in
    let* tag :=
      let! tmp1 := Tag.Scannable.of_tag tag in
      let! tmp2 := Option.get tmp1 in
      ret (Or_unknown.Known tmp2)
    in
    ret (P.Block_access_kind.Mixed tag size field_kind shape, const)
  end.

(* Recursive descent on decisions *)
(* ****************************** *)

(* 223-452. The record pattern [({ epa; decision; kind } : U.field_decision)]
   is the eliminator [U.match_field_decision] of decl/Unboxing_types.v, and
   the record [{ epa; decision; kind }] is its maker [U.mk_field_decision]
   (PORT-GAP(type) there). The labelled arguments are by place, in the order
   of each definition. *)
Fixpoint compute_extra_args_for_one_decision_and_use (fuel : fuel)
    (pass : U.pass) (rewrite_id : Apply_cont_rewrite_id.t)
    (typing_env_at_use : TE.t) (machine_width : Target_system.Machine_width.t)
    (arg_being_unboxed : unboxed_arg) (decision : U.decision_) {struct fuel}
    : M U.decision_ :=
  recursive! fuel in
  try_with
    (fun _ =>
      compute_extra_args_for_one_decision_and_use_aux fuel pass rewrite_id
        typing_env_at_use machine_width arg_being_unboxed decision)
    Prevent_current_unboxing
    (fun _ =>
      match pass with
      | U.Filter => ret (U.Do_not_unbox U.Not_enough_information_at_use)
      | U.Compute_all_extra_args =>
        fatal_errorf0 "This case should have been filtered out before."
      end)

(* 234-296 *)
with compute_extra_args_for_one_decision_and_use_aux (fuel : fuel)
    (pass : U.pass) (rewrite_id : Apply_cont_rewrite_id.t)
    (typing_env_at_use : TE.t) (machine_width : Target_system.Machine_width.t)
    (arg_being_unboxed : unboxed_arg) (decision : U.decision_) {struct fuel}
    : M U.decision_ :=
  recursive! fuel in
  match decision with
  | U.Do_not_unbox _ => ret decision
  | U.Unbox (U.Unique_tag_and_size tag shape fields) =>
    compute_extra_args_for_block fuel pass rewrite_id typing_env_at_use
      machine_width arg_being_unboxed tag shape fields
  | U.Unbox (U.Closure_single_entry function_slot vars_within_closure) =>
    compute_extra_args_for_closure fuel pass rewrite_id typing_env_at_use
      machine_width arg_being_unboxed function_slot vars_within_closure
  | U.Unbox (U.Variant tag const_ctors_from_decision fields_by_tag) =>
    let! tmp1 := type_of_arg_being_unboxed arg_being_unboxed in
    match tmp1 with
    | None =>
      compute_extra_args_for_variant fuel pass rewrite_id typing_env_at_use
        machine_width arg_being_unboxed tag const_ctors_from_decision
        fields_by_tag
        (Or_unknown.Known Target_ocaml_int.Set_.empty)
        Tag.Scannable.Map.empty
    | Some arg_type =>
      (* 256: [T.meet_variant_like] is written with the module's own name:
         the fields of its result are read. *)
      let! tmp1 := Flambda2_types.meet_variant_like typing_env_at_use arg_type in
      match tmp1 with
      | T.Need_meet => prevent_current_unboxing tt
      | T.Invalid => raise_ Invalid_apply_cont tt
      | T.Known_result
          {| Flambda2_types.const_ctors := const_ctors;
             Flambda2_types.non_const_ctors_with_sizes :=
               non_const_ctors_with_sizes
          |} =>
        compute_extra_args_for_variant fuel pass rewrite_id typing_env_at_use
          machine_width arg_being_unboxed tag const_ctors_from_decision
          fields_by_tag const_ctors non_const_ctors_with_sizes
      end
    end
  | U.Unbox (U.Number K.Naked_number_kind.Naked_float32 epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_float32
      Unboxers.Float32.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox (U.Number K.Naked_number_kind.Naked_float epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_float
      Unboxers.Float.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox
      (U.Number
         (K.Naked_number_kind.Naked_int8 | K.Naked_number_kind.Naked_int16)
         _epa) =>
    ret (U.Do_not_unbox U.Not_beneficial)
  | U.Unbox (U.Number K.Naked_number_kind.Naked_int32 epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_int32
      Unboxers.Int32.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox (U.Number K.Naked_number_kind.Naked_int64 epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_int64
      Unboxers.Int64.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox (U.Number K.Naked_number_kind.Naked_nativeint epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_nativeint
      Unboxers.Nativeint.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox (U.Number K.Naked_number_kind.Naked_immediate epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_immediate
      Unboxers.Immediate.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox (U.Number K.Naked_number_kind.Naked_vec128 epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_vec128
      Unboxers.Vec128.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox (U.Number K.Naked_number_kind.Naked_vec256 epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_vec256
      Unboxers.Vec256.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox (U.Number K.Naked_number_kind.Naked_vec512 epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_vec512
      Unboxers.Vec512.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  | U.Unbox (U.Number K.Naked_number_kind.Naked_mask epa) =>
    compute_extra_arg_for_number K.Naked_number_kind.Naked_mask
      Unboxers.Mask.unboxer epa rewrite_id typing_env_at_use
      arg_being_unboxed
  end

(* 298-327 *)
with compute_extra_args_for_block (fuel : fuel) (pass : U.pass)
    (rewrite_id : Apply_cont_rewrite_id.t) (typing_env_at_use : TE.t)
    (machine_width : Target_system.Machine_width.t)
    (arg_being_unboxed : unboxed_arg) (tag : Tag.t) (shape : K.Block_shape.t)
    (fields : list U.field_decision) {struct fuel} : M U.decision_ :=
  recursive! fuel in
  let* '(_, fields) :=
    let! tmp1 := Target_ocaml_int.zero machine_width in
    List.fold_left_map
      (fun field_nth field_decision =>
        U.match_field_decision field_decision
          (fun epa decision kind =>
            let* '(bak, poison_const) :=
              let! tmp2 := Target_ocaml_int.to_int field_nth in
              access_kind_and_poison_const machine_width tag shape fields tmp2
            in
            (* 309-311: [Unboxers.Field.unboxer ~poison_const bak
               ~index:field_nth] *)
            let* unboxer := Unboxers.Field.unboxer poison_const bak field_nth in
            let* '(new_extra_arg, new_arg_being_unboxed) :=
              unbox_arg unboxer typing_env_at_use arg_being_unboxed
            in
            let* epa :=
              Extra_param_and_args.update_param_args epa rewrite_id
                new_extra_arg
            in
            let* decision :=
              compute_extra_args_for_one_decision_and_use fuel pass rewrite_id
                typing_env_at_use machine_width new_arg_being_unboxed decision
            in
            let! tmp2 := Target_ocaml_int.one machine_width in
            let! tmp3 := Target_ocaml_int.add tmp2 field_nth in
            ret (tmp3, U.mk_field_decision epa decision kind)))
      tmp1 fields
  in
  ret (U.Unbox (U.Unique_tag_and_size tag shape fields))

(* 329-350 *)
with compute_extra_args_for_closure (fuel : fuel) (pass : U.pass)
    (rewrite_id : Apply_cont_rewrite_id.t) (typing_env_at_use : TE.t)
    (machine_width : Target_system.Machine_width.t)
    (arg_being_unboxed : unboxed_arg) (function_slot : Function_slot.t)
    (vars_within_closure : Value_slot.Map.t U.field_decision) {struct fuel}
    : M U.decision_ :=
  recursive! fuel in
  let* vars_within_closure :=
    Value_slot.Map.mapi
      (fun var field_decision =>
        U.match_field_decision field_decision
          (fun epa decision kind =>
            let* unboxer := Unboxers.Closure_field.unboxer function_slot var in
            let* '(new_extra_arg, new_arg_being_unboxed) :=
              unbox_arg unboxer typing_env_at_use arg_being_unboxed
            in
            let* epa :=
              Extra_param_and_args.update_param_args epa rewrite_id
                new_extra_arg
            in
            let* decision :=
              compute_extra_args_for_one_decision_and_use fuel pass rewrite_id
                typing_env_at_use machine_width new_arg_being_unboxed decision
            in
            ret (U.mk_field_decision epa decision kind)))
      vars_within_closure
  in
  ret (U.Unbox (U.Closure_single_entry function_slot vars_within_closure))

(* 352-452. The comment of 378-380 on the case where the tag is not known
   statically is not copied. *)
with compute_extra_args_for_variant (fuel : fuel) (pass : U.pass)
    (rewrite_id : Apply_cont_rewrite_id.t) (typing_env_at_use : TE.t)
    (machine_width : Target_system.Machine_width.t)
    (arg_being_unboxed : unboxed_arg)
    (tag_from_decision : Extra_param_and_args.t)
    (const_ctors_from_decision : U.const_ctors_decision)
    (fields_by_tag_from_decision :
      Tag.Scannable.Map.t (K.Block_shape.t * list U.field_decision))
    (const_ctors_at_use : Or_unknown.t Target_ocaml_int.Set_.t)
    (non_const_ctors_with_sizes_at_use :
      Tag.Scannable.Map.t (Target_ocaml_int.t * K.Block_shape.t))
    {struct fuel} : M U.decision_ :=
  recursive! fuel in
  let* are_there_const_ctors_at_use :=
    match const_ctors_at_use with
    | Or_unknown.Unknown => ret true
    | Or_unknown.Known set =>
      let! tmp1 := Target_ocaml_int.Set_.is_empty set in
      ret (negb tmp1)
    end
  in
  let* are_there_non_const_ctors_at_use :=
    let! tmp1 := Tag.Scannable.Map.is_empty non_const_ctors_with_sizes_at_use in
    ret (negb tmp1)
  in
  let* const_ctors :=
    if negb are_there_const_ctors_at_use
    then
      extra_args_for_const_ctor_of_variant const_ctors_from_decision
        typing_env_at_use rewrite_id Not_a_constant_constructor
    else
      if negb are_there_non_const_ctors_at_use
      then
        let! tmp1 := Simple.untagged_const_true machine_width in
        extra_args_for_const_ctor_of_variant const_ctors_from_decision
          typing_env_at_use rewrite_id
          (Maybe_constant_constructor tmp1 arg_being_unboxed)
      else prevent_current_unboxing tt
  in
  let* tag_at_use_site :=
    if negb are_there_non_const_ctors_at_use
    then ret Tag.Scannable.zero
    else
      let! tmp1 :=
        Tag.Scannable.Map.get_singleton non_const_ctors_with_sizes_at_use
      in
      match tmp1 with
      | None => prevent_current_unboxing tt
      | Some (tag, _) => ret tag
      end
  in
  (* 393-399: [a |> f b |> g] is [g (f b a)]. *)
  (* PORT-GAP(loose): 398, [|> fun x -> EPA.Extra_arg.Already_in_scope x] is
     the constructor applied to the value. *)
  let* tag_extra_arg :=
    let! tmp1 := Tag.Scannable.to_targetint machine_width tag_at_use_site in
    let! tmp2 := Target_ocaml_int.of_targetint machine_width tmp1 in
    let! tmp3 := Const.untagged_const_int tmp2 in
    let! tmp4 := Simple.const tmp3 in
    ret (EPA.Extra_arg.Already_in_scope tmp4)
  in
  let* tag :=
    Extra_param_and_args.update_param_args tag_from_decision rewrite_id
      tag_extra_arg
  in
  let* fields_by_tag :=
    Tag.Scannable.Map.mapi
      (fun tag_decision '(shape, block_fields) =>
        (* See doc/unboxing.md about invalid constants, poison and
           aliases. *)
        (* 410-411: the pair that the function of the fold takes apart is
           named [acc]: a name that the compiler does not have. *)
        let* '(new_fields_decisions, _) :=
          let! tmp1 := Target_ocaml_int.zero machine_width in
          List.fold_left
            (fun acc field_decision =>
              let* '(new_decisions, field_nth) := ret acc in
              U.match_field_decision field_decision
                (fun epa decision kind =>
                  let* '(bak, poison_const) :=
                    let! tmp2 := Target_ocaml_int.to_int field_nth in
                    let! tmp3 := Tag.Scannable.to_tag tag_decision in
                    access_kind_and_poison_const machine_width tmp3 shape
                      block_fields tmp2
                  in
                  let* '(new_extra_arg, new_arg_being_unboxed) :=
                    let! tmp2 :=
                      and_then are_there_non_const_ctors_at_use
                        (Tag.Scannable.equal tag_at_use_site tag_decision)
                    in
                    if tmp2
                    then
                      let* unboxer :=
                        Unboxers.Field.unboxer poison_const bak field_nth
                      in
                      unbox_arg unboxer typing_env_at_use arg_being_unboxed
                    else
                      let! tmp3 := Simple.const poison_const in
                      ret (EPA.Extra_arg.Already_in_scope tmp3, Poison)
                  in
                  let* epa :=
                    Extra_param_and_args.update_param_args epa rewrite_id
                      new_extra_arg
                  in
                  let* decision :=
                    compute_extra_args_for_one_decision_and_use fuel pass
                      rewrite_id typing_env_at_use machine_width
                      new_arg_being_unboxed decision
                  in
                  let& field_decision := U.mk_field_decision epa decision kind in
                  let& new_decisions := field_decision :: new_decisions in
                  let! tmp2 := Target_ocaml_int.one machine_width in
                  let! tmp3 := Target_ocaml_int.add tmp2 field_nth in
                  ret (new_decisions, tmp3)))
            ([], tmp1) block_fields
        in
        let! tmp1 := List.rev new_fields_decisions in
        ret (shape, tmp1))
      fields_by_tag_from_decision
  in
  ret (U.Unbox (U.Variant tag const_ctors fields_by_tag)).

(* 454-553 *)
Definition add_extra_params_and_args (extra_params_and_args : EPA.t)
    (invalids : Apply_cont_rewrite_id.Set_.t) (decision : U.decision_)
    : M EPA.t :=
  (* 455: a local [let rec] is Rocq's own [let] of a [fix]. *)
  let aux :=
    fix aux (fuel : Port_monad.fuel) (extra_params_and_args : EPA.t)
        (decision : U.decision_) {struct fuel} : M EPA.t :=
      recursive! fuel in
      match decision with
      | U.Do_not_unbox _ => ret extra_params_and_args
      | U.Unbox (U.Unique_tag_and_size _ _ fields) =>
        List.fold_left
          (fun extra_params_and_args field_decision =>
            U.match_field_decision field_decision
              (fun epa decision kind =>
                let* extra_param :=
                  BP.create epa.(Unboxing_types.Extra_param_and_args.param)
                    kind
                    epa.(Unboxing_types.Extra_param_and_args.param_debug_uid)
                in
                let* extra_params_and_args :=
                  EPA.add extra_params_and_args invalids extra_param
                    epa.(Unboxing_types.Extra_param_and_args.args)
                in
                aux fuel extra_params_and_args decision))
          extra_params_and_args fields
      | U.Unbox (U.Closure_single_entry _ vars_within_closure) =>
        Value_slot.Map.fold
          (fun _ field_decision extra_params_and_args =>
            U.match_field_decision field_decision
              (fun epa decision kind =>
                let* extra_param :=
                  BP.create epa.(Unboxing_types.Extra_param_and_args.param)
                    kind
                    epa.(Unboxing_types.Extra_param_and_args.param_debug_uid)
                in
                let* extra_params_and_args :=
                  EPA.add extra_params_and_args invalids extra_param
                    epa.(Unboxing_types.Extra_param_and_args.args)
                in
                aux fuel extra_params_and_args decision))
          vars_within_closure extra_params_and_args
      | U.Unbox (U.Variant tag const_ctors fields_by_tag) =>
        let* extra_params_and_args :=
          Tag.Scannable.Map.fold
            (fun _ '(_shape, block_fields) extra_params_and_args =>
              List.fold_left
                (fun extra_params_and_args field_decision =>
                  U.match_field_decision field_decision
                    (fun epa decision kind =>
                      let* extra_param :=
                        BP.create
                          epa.(Unboxing_types.Extra_param_and_args.param) kind
                          epa.(Unboxing_types.Extra_param_and_args.param_debug_uid)
                      in
                      let* extra_params_and_args :=
                        EPA.add extra_params_and_args invalids extra_param
                          epa.(Unboxing_types.Extra_param_and_args.args)
                      in
                      aux fuel extra_params_and_args decision))
                extra_params_and_args block_fields)
            fields_by_tag extra_params_and_args
        in
        let* extra_params_and_args :=
          match const_ctors with
          | U.Zero => ret extra_params_and_args
          | U.At_least_one is_int (U.Do_not_unbox _) =>
            let* extra_param :=
              BP.create is_int.(Unboxing_types.Extra_param_and_args.param)
                K.With_subkind.naked_immediate
                is_int.(Unboxing_types.Extra_param_and_args.param_debug_uid)
            in
            EPA.add extra_params_and_args invalids extra_param
              is_int.(Unboxing_types.Extra_param_and_args.args)
          | U.At_least_one is_int
              (U.Unbox (U.Number K.Naked_number_kind.Naked_immediate ctor)) =>
            let* extra_param :=
              BP.create is_int.(Unboxing_types.Extra_param_and_args.param)
                K.With_subkind.naked_immediate
                is_int.(Unboxing_types.Extra_param_and_args.param_debug_uid)
            in
            let* extra_params_and_args :=
              EPA.add extra_params_and_args invalids extra_param
                is_int.(Unboxing_types.Extra_param_and_args.args)
            in
            let* extra_param :=
              BP.create ctor.(Unboxing_types.Extra_param_and_args.param)
                K.With_subkind.naked_immediate
                ctor.(Unboxing_types.Extra_param_and_args.param_debug_uid)
            in
            EPA.add extra_params_and_args invalids extra_param
              ctor.(Unboxing_types.Extra_param_and_args.args)
          | U.At_least_one _
              (U.Unbox
                 ( U.Unique_tag_and_size _ _ _ | U.Variant _ _ _
                 | U.Closure_single_entry _ _
                 | U.Number
                     ( K.Naked_number_kind.Naked_float32
                     | K.Naked_number_kind.Naked_float
                     | K.Naked_number_kind.Naked_int8
                     | K.Naked_number_kind.Naked_int16
                     | K.Naked_number_kind.Naked_int32
                     | K.Naked_number_kind.Naked_int64
                     | K.Naked_number_kind.Naked_vec128
                     | K.Naked_number_kind.Naked_vec256
                     | K.Naked_number_kind.Naked_vec512
                     | K.Naked_number_kind.Naked_nativeint
                     | K.Naked_number_kind.Naked_mask )
                     _ )) =>
            fatal_errorf0
              "Trying to unbox the constant constructor of a variant with a kind other than Naked_immediate."
          end
        in
        let* extra_param :=
          BP.create tag.(Unboxing_types.Extra_param_and_args.param)
            K.With_subkind.naked_immediate
            tag.(Unboxing_types.Extra_param_and_args.param_debug_uid)
        in
        EPA.add extra_params_and_args invalids extra_param
          tag.(Unboxing_types.Extra_param_and_args.args)
      | U.Unbox (U.Number naked_number_kind epa) =>
        let* kind_with_subkind :=
          K.With_subkind.of_naked_number_kind naked_number_kind
        in
        let* extra_param :=
          BP.create epa.(Unboxing_types.Extra_param_and_args.param)
            kind_with_subkind
            epa.(Unboxing_types.Extra_param_and_args.param_debug_uid)
        in
        EPA.add extra_params_and_args invalids extra_param
          epa.(Unboxing_types.Extra_param_and_args.args)
      end
  in
  let_fuel! fuel in
  aux fuel extra_params_and_args decision.
