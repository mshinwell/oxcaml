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

(* This file follows
   middle_end/flambda2/simplify/unboxing/optimistic_unboxing_decision.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the recursive functions)
   is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Bound_name Flambda2_types
  Flambda_debug_uid Flambda_features Flambda_kind Format List Misc Name
  Name_mode Or_bottom Or_unknown Simple Tag Target_ocaml_int Unboxers
  Unboxing_types Value_slot.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda2_types.proof_of_property
   Flambda_kind.Block_shape.t Flambda_kind.Naked_number_kind.t
   Flambda_kind.Scannable_block_shape.t Flambda_kind.t Or_bottom.t
   Or_unknown.t Unboxing_types.do_not_unbox_reason
   Unboxing_types.unboxing_decision *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 18-19 *)
From SimplifyPort.abbrev.optimistic_unboxing_decision Require Import Port_abbreviations.
(*OCAML
module U = Unboxing_types
module Extra_param_and_args = U.Extra_param_and_args
OCAML*)

(* 21-22 *)
Definition pp_tag (print_tag : bool) (ppf : Format.formatter) (tag : Tag.t)
    : M unit :=
  if print_tag
  then
    let! tmp1 := Tag.to_int tag in
    Format.fprintf1 ppf "_%d" tmp1
  else ret tt.

(* Internal control knobs *)
(* 25 *)
Definition unbox_numbers : bool := true.

(* 27 *)
Definition unbox_blocks : bool := true.

(* 29 *)
Definition unbox_variants : bool := true.

(* 31 *)
Definition unbox_closures : bool := true.

(* 33-43 *)
Definition make_optimistic_const_ctor (_ : unit) : M U.const_ctors_decision :=
  let* is_int :=
    Extra_param_and_args.create "is_int" Flambda_debug_uid.none
      K.naked_immediate
  in
  let* unboxed_const_ctor :=
    Extra_param_and_args.create "unboxed_const_ctor" Flambda_debug_uid.none
      K.naked_immediate
  in
  let& ctor :=
    U.Unbox (U.Number K.Naked_number_kind.Naked_immediate unboxed_const_ctor)
  in
  ret (U.At_least_one is_int ctor).

(* 45-55 *)
Definition make_optimistic_number_decision (tenv : TE.t) (param_type : T.t)
    (decider : Unboxers.number_decider) : M (option U.decision_) :=
  let! tmp1 := decider.(Unboxers.prove_is_a_boxed_number) tenv param_type in
  match tmp1 with
  | T.Proved tt =>
    let* naked_number :=
      let! tmp1 := K.naked_number decider.(Unboxers.kind) in
      Extra_param_and_args.create decider.(Unboxers.param_name)
        Flambda_debug_uid.none tmp1
    in
    ret (Some (U.Unbox (U.Number decider.(Unboxers.kind) naked_number)))
  | T.Unknown => ret None
  end.

(* 57-58 *)
Definition decide (tenv : TE.t) (param_type : T.t)
    (deciders : list Unboxers.number_decider) : M (option U.decision_) :=
  List.find_map (make_optimistic_number_decision tenv param_type) deciders.

(* 60-70 *)
Definition deciders : list Unboxers.number_decider :=
  [ Unboxers.Immediate.decider;
    Unboxers.Float.decider;
    Unboxers.Float32.decider;
    Unboxers.Int32.decider;
    Unboxers.Int64.decider;
    Unboxers.Nativeint.decider;
    Unboxers.Vec128.decider;
    Unboxers.Vec256.decider;
    Unboxers.Vec512.decider;
    Unboxers.Mask.decider ].

(* 72-153. In the compiler: [~depth ~recursive tenv ~param_type]. *)
(* PORT-GAP(loose): 100, 109-110, 148-149, a case [p when c -> e] whose
   guard [c] is made of constants and of parameters of the function is
   written with [c] as a second scrutinee, so that the other cases are
   written once in this file; Rocq then prints [if c then e else] the other
   cases, as for the form of the guide. *)
Fixpoint make_optimistic_decision (fuel : fuel) (depth : int)
    (recursive : bool) (tenv : TE.t) (param_type : T.t) {struct fuel}
    : M U.decision_ :=
  recursive! fuel in
  (* 74-80. The parameter types will have been computed from the types of
     the continuation's arguments at the use site(s), which in turn will
     have been computed from simplified [Simple]s. As such we shouldn't need
     to canonicalise any alias again here. *)
  let* param_type_is_alias_to_symbol := T.is_alias_to_a_symbol param_type in
  (* 81-85 *)
  let* param_kind_is_not_value :=
    let! tmp1 := T.kind param_type in
    match tmp1 with
    | K.Value => ret false
    | K.Naked_number _ | K.Region | K.Rec_info => ret true
    end
  in
  if param_type_is_alias_to_symbol
  then ret (U.Do_not_unbox U.Not_beneficial)
  else
    if param_kind_is_not_value
    then ret (U.Do_not_unbox U.Not_of_kind_value)
    else
      (* 91-153 *)
      let! tmp1 := decide tenv param_type deciders in
      match tmp1 with
      | Some decision =>
        if unbox_numbers
        then ret decision
        else ret (U.Do_not_unbox U.Incomplete_parameter_type)
      | None =>
        let! tmp1 := Flambda_features.Expert.max_unboxing_depth tt in
        if depth >=? tmp1
        then ret (U.Do_not_unbox U.Max_depth_exceeded)
        else
          (* 99-153 *)
          let! tmp1 := T.prove_unique_tag_and_size tenv param_type in
          match tmp1, unbox_blocks with
          | T.Proved (T3 tag shape size), true =>
            let* fields :=
              make_optimistic_fields fuel false depth recursive tenv
                param_type tag shape size
            in
            match fields with
            | Some fields =>
              ret (U.Unbox (U.Unique_tag_and_size tag shape fields))
            | None => ret (U.Do_not_unbox U.All_fields_invalid)
            end
          | (T.Proved _ | T.Unknown), _ =>
            (* 108-153. [T.prove_variant_like], under the module's own name:
               Rocq then prints the fields of its record under that name
               too. *)
            let! tmp1 := Flambda2_types.prove_variant_like tenv param_type in
            match tmp1, unbox_variants && negb recursive with
            | T.Proved
                {| Flambda2_types.const_ctors := const_ctors;
                   Flambda2_types.non_const_ctors_with_sizes :=
                     non_const_ctors_with_sizes
                |},
              true =>
              let* tag :=
                Extra_param_and_args.create "tag" Flambda_debug_uid.none
                  K.naked_immediate
              in
              (* 115-119 *)
              let* const_ctors :=
                match const_ctors with
                | Or_unknown.Known set =>
                  let! tmp1 := Target_ocaml_int.Set_.is_empty set in
                  if tmp1 then ret U.Zero else make_optimistic_const_ctor tt
                | Or_unknown.Unknown => make_optimistic_const_ctor tt
                end
              in
              (* 120-131 *)
              let* fields_by_tag :=
                Tag.Scannable.Map.filter_map
                  (fun scannable_tag '(size, shape) =>
                    let* tag := Tag.Scannable.to_tag scannable_tag in
                    let! tmp1 :=
                      make_optimistic_fields fuel true depth recursive tenv
                        param_type tag shape size
                    in
                    match tmp1 with
                    | None => ret None
                    | Some decision => ret (Some (shape, decision))
                    end)
                  non_const_ctors_with_sizes
              in
              (* 132-142 *)
              let! tmp1 := Tag.Scannable.Map.is_empty fields_by_tag in
              if tmp1
              then ret (U.Do_not_unbox U.All_fields_invalid)
              else
                (* PORT-GAP(loose): 136-142, the compiler matches
                   [const_ctors, Tag.Scannable.Map.get_singleton
                   fields_by_tag]; here the two are exchanged, so that Rocq
                   keeps the call at the head of the match (in the
                   compiler's order Rocq prints the call inside the case
                   [Zero] only). *)
                let! tmp1 := Tag.Scannable.Map.get_singleton fields_by_tag in
                match tmp1, const_ctors with
                | Some (scannable_tag, (shape, fields)), U.Zero =>
                  let* tag := Tag.Scannable.to_tag scannable_tag in
                  ret (U.Unbox (U.Unique_tag_and_size tag shape fields))
                | _, (U.Zero | U.At_least_one _ _) =>
                  ret (U.Unbox (U.Variant tag const_ctors fields_by_tag))
                end
            | (T.Proved _ | T.Unknown), _ =>
              (* 144-153 *)
              let! tmp1 := T.prove_single_closures_entry tenv param_type in
              match tmp1, unbox_closures && negb recursive with
              | T.Proved (T4 function_slot _ closures_entry _fun_decl), true =>
                let* vars_within_closure :=
                  make_optimistic_vars_within_closure fuel depth recursive
                    tenv closures_entry
                in
                ret
                  (U.Unbox
                     (U.Closure_single_entry function_slot
                        vars_within_closure))
              | (T.Proved _ | T.Unknown), _ =>
                ret (U.Do_not_unbox U.Incomplete_parameter_type)
              end
            end
          end
      end

(* 155-208. In the compiler: [~add_tag_to_name ~depth ~recursive tenv
   param_type tag shape size]. *)
with make_optimistic_fields (fuel : fuel) (add_tag_to_name : bool)
    (depth : int) (recursive : bool) (tenv : TE.t) (param_type : T.t)
    (tag : Tag.t) (shape : K.Block_shape.t) (size : Target_ocaml_int.t)
    {struct fuel} : M (option (list U.field_decision)) :=
  recursive! fuel in
  (* 157-162 *)
  let& field_base_name :=
    match shape with
    | K.Block_shape.Scannable K.Scannable_block_shape.Value_only =>
      "unboxed_field"
    | K.Block_shape.Scannable (K.Scannable_block_shape.Mixed_record _) =>
      "unboxed_mixed_field"
    | K.Block_shape.Float_record => "unboxed_float_field"
    end
  in
  (* 163-165 *)
  let& field_name :=
    fun (n : int) =>
    Format.asprintf4 "%s%a_%d" field_base_name (pp_tag add_tag_to_name) tag n
  in
  (* 166-171 *)
  let* field_vars :=
    let! tmp3 := Target_ocaml_int.to_int size in
    List.init tmp3 (fun i =>
      let! tmp1 := K.Block_shape.element_kind shape i in
      let! tmp2 := field_name i in
      Extra_param_and_args.create tmp2 Flambda_debug_uid.none tmp1)
  in
  (* 172-176 *)
  let& type_of_var :=
    fun (index : int) (epa : Extra_param_and_args.t) =>
    let! tmp1 := Simple.var epa.(Unboxing_types.Extra_param_and_args.param) in
    let! tmp2 := K.Block_shape.element_kind shape index in
    T.alias_type_of tmp2 tmp1
  in
  let* field_types := List.mapi type_of_var field_vars in
  (* 178-186 *)
  let* tenv :=
    Misc.Stdlib.List.fold_lefti
      (fun index acc
           '({| Unboxing_types.Extra_param_and_args.param := var;
                Unboxing_types.Extra_param_and_args.param_debug_uid := _;
                Unboxing_types.Extra_param_and_args.args := _
             |}
             : Extra_param_and_args.t) =>
        let* name :=
          let! tmp1 := Name.var var in
          Bound_name.create tmp1 Name_mode.normal
        in
        let! tmp1 := K.Block_shape.element_kind shape index in
        TE.add_definition acc name tmp1)
      tenv field_vars
  in
  (* 187-191. [T.immutable_block ~is_unique:false tag ~shape ~fields
     (Alloc_mode.For_types.unknown ()) ~machine_width]: the arguments are in
     the order of the interface. *)
  let* shape :=
    let! tmp1 := Alloc_mode.For_types.unknown tt in
    let! tmp2 := TE.machine_width tenv in
    T.immutable_block tmp2 false tag shape tmp1 field_types
  in
  (* 192-208 *)
  (* PORT-GAP(loose): 198, the compiler raises again the exception that it
     caught, [raise exn]; here [Misc.Fatal_error] is raised, which is that
     exception. *)
  match_exn
    (fun _ => T.meet tenv param_type shape)
    Fatal_error
    (fun _ =>
      Format.eprintf6
        "Context is meet of type: %a@
with shape: %a@
in env: @
%a@."
        T.print param_type T.print shape TE.print tenv ;;
      raise_ Fatal_error tt)
    (fun meet_result =>
      match meet_result with
      | Or_bottom.Bottom => ret None
      | Or_bottom.Ok (_, tenv) =>
        (* 200-208 *)
        let* fields :=
          List.map2
            (fun epa var_type =>
              let* decision :=
                make_optimistic_decision fuel (depth + 1) recursive tenv
                  var_type
              in
              let! tmp1 := T.kind var_type in
              let! tmp2 := K.With_subkind.anything tmp1 in
              ret (U.mk_field_decision epa decision tmp2))
            field_vars field_types
        in
        ret (Some fields)
      end)

(* 210-228. In the compiler: [~depth ~recursive tenv closures_entry]. *)
with make_optimistic_vars_within_closure (fuel : fuel) (depth : int)
    (recursive : bool) (tenv : TE.t) (closures_entry : T.Closures_entry.t)
    {struct fuel} : M (Value_slot.Map.t U.field_decision) :=
  recursive! fuel in
  let* map := T.Closures_entry.value_slot_types closures_entry in
  Value_slot.Map.mapi
    (fun value_slot var_type =>
      let* epa :=
        let! tmp1 := Value_slot.kind value_slot in
        let! tmp2 := Value_slot.to_string value_slot in
        Extra_param_and_args.create tmp2 Flambda_debug_uid.none tmp1
      in
      let* decision :=
        make_optimistic_decision fuel (depth + 1) recursive tenv var_type
      in
      let* kind :=
        let! tmp1 := Flambda2_types.kind var_type in
        K.With_subkind.anything tmp1
      in
      ret (U.mk_field_decision epa decision kind))
    map.
