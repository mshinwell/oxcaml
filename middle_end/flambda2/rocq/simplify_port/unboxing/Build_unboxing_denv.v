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
   middle_end/flambda2/simplify/unboxing/build_unboxing_denv.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order, the fuel of the recursive function) is that of GUIDE.md.
   No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Bound_var Downwards_env
  Flambda2_types Flambda_debug_uid Flambda_kind Flambda_primitive List Misc
  Name Name_mode Or_bottom Simple Tag Unboxing_types Value_slot Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 18 *)
Module U := Unboxing_types.

(* 20-26 *)
Definition add_equation_on_var (denv : DE.t) (var : Variable_.t)
    (shape : T.t) : M DE.t :=
  let* kind := T.kind shape in
  let* var_type :=
    let! tmp1 := Simple.var var in
    T.alias_type_of kind tmp1
  in
  let! tmp1 := DE.typing_env denv in
  let! tmp2 := T.meet tmp1 var_type shape in
  match tmp2 with
  | Or_bottom.Ok (_ty, typing_env) => DE.with_typing_env denv typing_env
  | Or_bottom.Bottom =>
    fatal_errorf0 "Meet failed whereas prove and meet previously succeeded"
  end.

(* 28-32 *)
Definition denv_of_number_decision (naked_kind : K.t) (shape : T.t)
    (param_var : Variable_.t) (param_var_debug_uid : Flambda_debug_uid.t)
    (naked_var : Variable_.t) (denv : DE.t) : M DE.t :=
  let* naked_name := VB.create naked_var param_var_debug_uid Name_mode.normal in
  let* denv := DE.define_extra_variable denv naked_name naked_kind in
  add_equation_on_var denv param_var shape.

(* 34-291. In the compiler: [denv ~param_var decision]. *)
(* PORT-GAP(type): [U.field_decision] is abstract in decl/: its eliminator
   [U.match_field_decision] stands for the compiler's record patterns
   ([{ epa = { param = var; param_debug_uid; _ }; _ }]) and for its reads of
   the fields ([field.epa.param], [field.decision]). *)
Fixpoint denv_of_decision (fuel : fuel) (denv : DE.t) (param_var : Variable_.t)
    (decision : U.decision_) {struct fuel} : M DE.t :=
  recursive! fuel in
  match decision with
  | U.Do_not_unbox _ => ret denv
  (* 37-63 *)
  | U.Unbox (U.Unique_tag_and_size tag shape fields) =>
    let* denv :=
      Misc.Stdlib.List.fold_lefti
        (fun index denv (field : U.field_decision) =>
          U.match_field_decision field
            (fun '{| Unboxing_types.Extra_param_and_args.param := var;
                     Unboxing_types.Extra_param_and_args.param_debug_uid :=
                       param_debug_uid
                  |} _ _ =>
              let* v := VB.create var param_debug_uid Name_mode.normal in
              let! tmp1 := K.Block_shape.element_kind shape index in
              DE.define_extra_variable denv v tmp1))
        denv fields
    in
    (* 48-52 *)
    let& type_of_var :=
      fun (index : int) (field : U.field_decision) =>
      U.match_field_decision field (fun epa _ _ =>
        let! tmp1 :=
          Simple.var epa.(Unboxing_types.Extra_param_and_args.param)
        in
        let! tmp2 := K.Block_shape.element_kind shape index in
        T.alias_type_of tmp2 tmp1)
    in
    let* field_types := List.mapi type_of_var fields in
    (* 54-58. [T.immutable_block]: the arguments are in the order of the
       interface. *)
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := DE.machine_width denv in
      T.immutable_block tmp2 false tag shape tmp1 field_types
    in
    let* denv := add_equation_on_var denv param_var shape in
    (* 60-63 *)
    List.fold_left
      (fun denv (field : U.field_decision) =>
        U.match_field_decision field (fun epa decision _ =>
          denv_of_decision fuel denv
            epa.(Unboxing_types.Extra_param_and_args.param)
            decision))
      denv fields
  (* 64-88 *)
  | U.Unbox (U.Closure_single_entry function_slot vars_within_closure) =>
    let* denv :=
      Value_slot.Map.fold
        (fun _ (field : U.field_decision) denv =>
          U.match_field_decision field
            (fun '{| Unboxing_types.Extra_param_and_args.param := var;
                     Unboxing_types.Extra_param_and_args.param_debug_uid :=
                       param_debug_uid
                  |} _ kind =>
              let* v := VB.create var param_debug_uid Name_mode.normal in
              let! tmp1 := K.With_subkind.kind kind in
              DE.define_extra_variable denv v tmp1))
        vars_within_closure denv
    in
    (* 74-79 *)
    let* map :=
      Value_slot.Map.map
        (fun (field : U.field_decision) =>
          U.match_field_decision field
            (fun '{| Unboxing_types.Extra_param_and_args.param := var
                  |} _ kind =>
              let! tmp1 := K.With_subkind.kind kind in
              ret (var, tmp1)))
        vars_within_closure
    in
    let* shape :=
      T.closure_with_at_least_these_value_slots function_slot map
    in
    let* denv := add_equation_on_var denv param_var shape in
    (* 85-88 *)
    Value_slot.Map.fold
      (fun _ (field : U.field_decision) denv =>
        U.match_field_decision field (fun epa decision _ =>
          denv_of_decision fuel denv
            epa.(Unboxing_types.Extra_param_and_args.param)
            decision))
      vars_within_closure denv
  (* 89-197 *)
  | U.Unbox (U.Variant tag const_ctors fields_by_tag) =>
    (* Adapt the denv for the tag *)
    let* tag_v :=
      VB.create
        tag.(Unboxing_types.Extra_param_and_args.param)
        tag.(Unboxing_types.Extra_param_and_args.param_debug_uid)
        Name_mode.normal
    in
    let* denv := DE.define_extra_variable denv tag_v K.naked_immediate in
    let* denv :=
      DE.map_typing_env denv (fun tenv =>
        let! tmp1 := Simple.var param_var in
        let! tmp2 := Name.var tag.(Unboxing_types.Extra_param_and_args.param) in
        TE.add_get_tag_relation tenv tmp2 tmp1)
    in
    let* get_tag_prim :=
      let! tmp1 := Name.var param_var in
      P.Eligible_for_cse.create_get_tag tmp1
    in
    let* denv :=
      let! tmp1 := Simple.var tag.(Unboxing_types.Extra_param_and_args.param) in
      DE.add_cse denv get_tag_prim tmp1 Name_mode.normal
    in
    (* 105-128. Same thing for is_int *)
    let* denv :=
      match const_ctors with
      | U.Zero => ret denv
      | U.At_least_one is_int _ =>
        let* is_int_v :=
          VB.create
            is_int.(Unboxing_types.Extra_param_and_args.param)
            is_int.(Unboxing_types.Extra_param_and_args.param_debug_uid)
            Name_mode.normal
        in
        let* denv := DE.define_extra_variable denv is_int_v K.naked_immediate in
        let* denv :=
          DE.map_typing_env denv (fun tenv =>
            let! tmp1 := Simple.var param_var in
            let! tmp2 :=
              Name.var is_int.(Unboxing_types.Extra_param_and_args.param)
            in
            TE.add_is_int_relation tenv tmp2 tmp1)
        in
        let* is_int_prim :=
          let! tmp1 := Name.var param_var in
          P.Eligible_for_cse.create_is_int true tmp1
        in
        let* denv :=
          let! tmp1 :=
            Simple.var is_int.(Unboxing_types.Extra_param_and_args.param)
          in
          DE.add_cse denv is_int_prim tmp1 Name_mode.normal
        in
        ret denv
      end
    in
    (* 129-158 *)
    let* '(denv, const_ctors) :=
      match const_ctors with
      | U.Zero =>
        let! tmp1 := T.bottom K.naked_immediate in
        ret (denv, tmp1)
      | U.At_least_one _ (U.Do_not_unbox _) =>
        let! tmp1 := T.unknown K.naked_immediate in
        ret (denv, tmp1)
      | U.At_least_one _
          (U.Unbox (U.Number K.Naked_number_kind.Naked_immediate ctor_epa)) =>
        let* v :=
          VB.create
            ctor_epa.(Unboxing_types.Extra_param_and_args.param)
            ctor_epa.(Unboxing_types.Extra_param_and_args.param_debug_uid)
            Name_mode.normal
        in
        let* denv := DE.define_extra_variable denv v K.naked_immediate in
        let* ty :=
          let! tmp1 :=
            Simple.var ctor_epa.(Unboxing_types.Extra_param_and_args.param)
          in
          T.alias_type_of K.naked_immediate tmp1
        in
        ret (denv, ty)
      | U.At_least_one _
          (U.Unbox
             (U.Unique_tag_and_size _ _ _ | U.Variant _ _ _
             | U.Closure_single_entry _ _
             | U.Number
                 (K.Naked_number_kind.Naked_float
                 | K.Naked_number_kind.Naked_float32
                 | K.Naked_number_kind.Naked_int8
                 | K.Naked_number_kind.Naked_int16
                 | K.Naked_number_kind.Naked_int32
                 | K.Naked_number_kind.Naked_int64
                 | K.Naked_number_kind.Naked_nativeint
                 | K.Naked_number_kind.Naked_vec128
                 | K.Naked_number_kind.Naked_vec256
                 | K.Naked_number_kind.Naked_vec512
                 | K.Naked_number_kind.Naked_mask)
                 _)) =>
        fatal_errorf0
          "Variant constant constructor unboxed with a kind other than naked_immediate."
      end
    in
    (* 159-171 *)
    let* denv :=
      Tag.Scannable.Map.fold
        (fun _ '(shape, block_fields) denv =>
          Misc.Stdlib.List.fold_lefti
            (fun index denv (field : U.field_decision) =>
              U.match_field_decision field
                (fun '{| Unboxing_types.Extra_param_and_args.param := var;
                         Unboxing_types.Extra_param_and_args.param_debug_uid :=
                           param_debug_uid
                      |} _ _ =>
                  let* v := VB.create var param_debug_uid Name_mode.normal in
                  let! tmp1 := K.Block_shape.element_kind shape index in
                  DE.define_extra_variable denv v tmp1))
            denv block_fields)
        fields_by_tag denv
    in
    (* 172-183 *)
    let* non_const_ctors :=
      Tag.Scannable.Map.map
        (fun '(shape, block_fields) =>
          let! tmp3 :=
            List.mapi
              (fun i (field : U.field_decision) =>
                U.match_field_decision field (fun epa _ _ =>
                  let! tmp1 :=
                    Simple.var epa.(Unboxing_types.Extra_param_and_args.param)
                  in
                  let! tmp2 := K.Block_shape.element_kind shape i in
                  T.alias_type_of tmp2 tmp1))
              block_fields
          in
          ret (shape, tmp3))
        fields_by_tag
    in
    (* 184-188. [T.variant]: the arguments are in the order of the
       interface. *)
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      let! tmp2 := DE.machine_width denv in
      T.variant tmp2 const_ctors non_const_ctors tmp1
    in
    let* denv := add_equation_on_var denv param_var shape in
    (* 190-197. Recurse on the fields *)
    Tag.Scannable.Map.fold
      (fun _ '(_shape, block_fields) denv =>
        List.fold_left
          (fun denv (field : U.field_decision) =>
            U.match_field_decision field (fun epa decision _ =>
              denv_of_decision fuel denv
                epa.(Unboxing_types.Extra_param_and_args.param)
                decision))
          denv block_fields)
      fields_by_tag denv
  (* 198-204 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_immediate
         {| Unboxing_types.Extra_param_and_args.param := naked_immediate;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape := T.tagged_immediate_alias_to naked_immediate in
    denv_of_number_decision K.naked_immediate shape param_var param_debug_uid
      naked_immediate denv
  (* 205-213 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_float32
         {| Unboxing_types.Extra_param_and_args.param := naked_float32;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_float32_alias_to naked_float32 tmp1
    in
    denv_of_number_decision K.naked_float32 shape param_var param_debug_uid
      naked_float32 denv
  (* 214-221 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_float
         {| Unboxing_types.Extra_param_and_args.param := naked_float;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_float_alias_to naked_float tmp1
    in
    denv_of_number_decision K.naked_float shape param_var param_debug_uid
      naked_float denv
  (* 222-227 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_int8
         {| Unboxing_types.Extra_param_and_args.param := naked_int8;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let& shape := T.any_naked_int8 in
    denv_of_number_decision K.naked_int8 shape param_var param_debug_uid
      naked_int8 denv
  (* 228-233 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_int16
         {| Unboxing_types.Extra_param_and_args.param := naked_int16;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let& shape := T.any_naked_int16 in
    denv_of_number_decision K.naked_int16 shape param_var param_debug_uid
      naked_int16 denv
  (* 234-241 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_int32
         {| Unboxing_types.Extra_param_and_args.param := naked_int32;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_int32_alias_to naked_int32 tmp1
    in
    denv_of_number_decision K.naked_int32 shape param_var param_debug_uid
      naked_int32 denv
  (* 242-249 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_int64
         {| Unboxing_types.Extra_param_and_args.param := naked_int64;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_int64_alias_to naked_int64 tmp1
    in
    denv_of_number_decision K.naked_int64 shape param_var param_debug_uid
      naked_int64 denv
  (* 250-259 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_nativeint
         {| Unboxing_types.Extra_param_and_args.param := naked_nativeint;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_nativeint_alias_to naked_nativeint tmp1
    in
    denv_of_number_decision K.naked_nativeint shape param_var param_debug_uid
      naked_nativeint denv
  (* 260-267 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_vec128
         {| Unboxing_types.Extra_param_and_args.param := naked_vec128;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_vec128_alias_to naked_vec128 tmp1
    in
    denv_of_number_decision K.naked_vec128 shape param_var param_debug_uid
      naked_vec128 denv
  (* 268-275 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_vec256
         {| Unboxing_types.Extra_param_and_args.param := naked_vec256;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_vec256_alias_to naked_vec256 tmp1
    in
    denv_of_number_decision K.naked_vec256 shape param_var param_debug_uid
      naked_vec256 denv
  (* 276-283 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_vec512
         {| Unboxing_types.Extra_param_and_args.param := naked_vec512;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_vec512_alias_to naked_vec512 tmp1
    in
    denv_of_number_decision K.naked_vec512 shape param_var param_debug_uid
      naked_vec512 denv
  (* 284-291 *)
  | U.Unbox
      (U.Number K.Naked_number_kind.Naked_mask
         {| Unboxing_types.Extra_param_and_args.param := naked_mask;
            Unboxing_types.Extra_param_and_args.param_debug_uid :=
              param_debug_uid;
            Unboxing_types.Extra_param_and_args.args := _
         |}) =>
    let* shape :=
      let! tmp1 := Alloc_mode.For_types.unknown tt in
      T.boxed_mask_alias_to naked_mask tmp1
    in
    denv_of_number_decision K.naked_mask shape param_var param_debug_uid
      naked_mask denv
  end.
