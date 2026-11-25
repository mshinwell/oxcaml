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

(* This file follows middle_end/flambda2/simplify/unboxing/unboxers.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Flambda2_types Flambda_kind Flambda_primitive
  Function_slot Mutability Name_mode Reg_width_const Simple Target_ocaml_int
  Value_slot.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda_kind.Boxable_number.t
   Flambda_primitive.unary_primitive Mutability.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 19-23 *)
Record number_decider : Type :=
  { param_name : string;
    kind : K.Naked_number_kind.t;
    prove_is_a_boxed_number : TE.t -> T.t -> M (T.proof_of_property unit)
  }.

(* 25-32 *)
(* PORT-GAP(loose): 30-31, in the compiler the second argument of the field
   [prove_simple] has the label [~min_name_mode]; the type that Rocq prints
   has no label. And Rocq prints the type inside a module [Coq__1] that it
   then includes: the modules [Field] and [Closure_field] define a function
   [unboxing_prim] and then name the field [unboxing_prim], which Rocq
   writes [Coq__1.unboxing_prim]. *)
Record unboxer : Type :=
  { var_name : string;
    var_kind : Flambda_kind.t;
    poison_const : Const.t;
    unboxing_prim : Simple.t -> M P.t;
    prove_simple : TE.t -> Name_mode.t -> T.t -> M (T.meet_shortcut Simple.t)
  }.

(* 34-40 *)
Module Type Number_S.
  Parameter decider : number_decider.

  Parameter unboxing_prim : Simple.t -> M P.t.

  Parameter unboxer : unboxer.
End Number_S.

(* 42-59 *)
Module Immediate.
  (* 43-47 *)
  Definition decider : number_decider :=
    {| param_name := "naked_immediate";
       kind := K.Naked_number_kind.Naked_immediate;
       prove_is_a_boxed_number := T.prove_is_a_tagged_immediate
    |}.

  (* 49 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary P.Untag_immediate simple).

  (* 51-58 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""naked_immediate"";
      var_kind = K.naked_immediate;
      poison_const =
        Const.const_poison K.naked_immediate ""variant_unboxing_naked_immediate"";
      unboxing_prim;
      prove_simple = T.meet_tagging_of_simple
    }".
End Immediate.

(* 61-78 *)
Module Float32.
  (* 62-66 *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_float32";
       kind := K.Naked_number_kind.Naked_float32;
       prove_is_a_boxed_number := T.prove_is_a_boxed_float32
    |}.

  (* 68 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_float32) simple).

  (* 70-77 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_float32"";
      var_kind = K.naked_float32;
      poison_const =
        Const.const_poison K.naked_float32 ""variant_unboxing_float32"";
      unboxing_prim;
      prove_simple = T.meet_boxed_float32_containing_simple
    }".
End Float32.

(* 80-96 *)
Module Float.
  (* 81-85 *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_float";
       kind := K.Naked_number_kind.Naked_float;
       prove_is_a_boxed_number := T.prove_is_a_boxed_float
    |}.

  (* 87 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_float) simple).

  (* 89-95 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_float"";
      var_kind = K.naked_float;
      poison_const = Const.const_poison K.naked_float ""variant_unboxing_float"";
      unboxing_prim;
      prove_simple = T.meet_boxed_float_containing_simple
    }".
End Float.

(* 98-114 *)
Module Int32.
  (* 99-103 *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_int32";
       kind := K.Naked_number_kind.Naked_int32;
       prove_is_a_boxed_number := T.prove_is_a_boxed_int32
    |}.

  (* 105 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_int32) simple).

  (* 107-113 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_int32"";
      var_kind = K.naked_int32;
      poison_const = Const.const_poison K.naked_int32 ""variant_unboxing_int32"";
      unboxing_prim;
      prove_simple = T.meet_boxed_int32_containing_simple
    }".
End Int32.

(* 116-132 *)
Module Int64.
  (* 117-121 *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_int64";
       kind := K.Naked_number_kind.Naked_int64;
       prove_is_a_boxed_number := T.prove_is_a_boxed_int64
    |}.

  (* 123 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_int64) simple).

  (* 125-131 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_int64"";
      var_kind = K.naked_int64;
      poison_const = Const.const_poison K.naked_int64 ""variant_unboxing_int64"";
      unboxing_prim;
      prove_simple = T.meet_boxed_int64_containing_simple
    }".
End Int64.

(* 134-151 *)
Module Nativeint.
  (* 135-139 *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_nativeint";
       kind := K.Naked_number_kind.Naked_nativeint;
       prove_is_a_boxed_number := T.prove_is_a_boxed_nativeint
    |}.

  (* 141 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_nativeint) simple).

  (* 143-150 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_nativeint"";
      var_kind = K.naked_nativeint;
      poison_const =
        Const.const_poison K.naked_nativeint ""variant_unboxing_nativeint"";
      unboxing_prim;
      prove_simple = T.meet_boxed_nativeint_containing_simple
    }".
End Nativeint.

(* 153-169 *)
Module Vec128.
  (* 154-158 *)
  (* 157: the compiler writes [prove_is_a_boxed_vec128] without the name of its module. *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_vec128";
       kind := K.Naked_number_kind.Naked_vec128;
       prove_is_a_boxed_number := T.prove_is_a_boxed_vec128
    |}.

  (* 160 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_vec128) simple).

  (* 162-168 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_vec128"";
      var_kind = K.naked_vec128;
      poison_const = Const.const_poison K.naked_vec128 ""variant_unboxing_vec128"";
      unboxing_prim;
      prove_simple = T.meet_boxed_vec128_containing_simple
    }".
End Vec128.

(* 171-187 *)
Module Vec256.
  (* 172-176 *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_vec256";
       kind := K.Naked_number_kind.Naked_vec256;
       prove_is_a_boxed_number := T.prove_is_a_boxed_vec256
    |}.

  (* 178 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_vec256) simple).

  (* 180-186 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_vec256"";
      var_kind = K.naked_vec256;
      poison_const = Const.const_poison K.naked_vec256 ""variant_unxboing_vec256"";
      unboxing_prim;
      prove_simple = T.meet_boxed_vec256_containing_simple
    }".
End Vec256.

(* 189-205 *)
Module Vec512.
  (* 190-194 *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_vec512";
       kind := K.Naked_number_kind.Naked_vec512;
       prove_is_a_boxed_number := T.prove_is_a_boxed_vec512
    |}.

  (* 196 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_vec512) simple).

  (* 198-204 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_vec512"";
      var_kind = K.naked_vec512;
      poison_const = Const.const_poison K.naked_vec512 ""variant_unboxing_vec512"";
      unboxing_prim;
      prove_simple = T.meet_boxed_vec512_containing_simple
    }".
End Vec512.

(* 207-223 *)
Module Mask.
  (* 208-212 *)
  Definition decider : number_decider :=
    {| param_name := "unboxed_mask";
       kind := K.Naked_number_kind.Naked_mask;
       prove_is_a_boxed_number := T.prove_is_a_boxed_mask
    |}.

  (* 214 *)
  Definition unboxing_prim (simple : Simple.t) : M P.t :=
    ret (P.Unary (P.Unbox_number K.Boxable_number.Naked_mask) simple).

  (* 216-222 *)
  (* PORT-GAP(init): the compiler computes this record when the module
     starts ([Const.const_poison] is a call): a parameter here. Its OCaml
     text is that of the directive, which Rocq prints at this place. *)
  Parameter unboxer : unboxer.
  Extract Constant unboxer =>
    "
    { var_name = ""unboxed_mask"";
      var_kind = K.naked_mask;
      poison_const = Const.const_poison K.naked_mask ""variant_unboxing_mask"";
      unboxing_prim;
      prove_simple = T.meet_boxed_mask_containing_simple
    }".
End Mask.

(* 225-240 *)
Module Field.
  (* 226-227. In the compiler: [bak ~block ~index]. *)
  Definition unboxing_prim (bak : P.Block_access_kind.t) (block : Simple.t)
      (index : Target_ocaml_int.t) : M P.t :=
    ret (P.Unary (P.Block_load bak Mutability.Immutable index) block).

  (* 229-239. In the compiler: [~poison_const bak ~index]. *)
  Definition unboxer (poison_const : Const.t) (bak : P.Block_access_kind.t)
      (index : Target_ocaml_int.t) : M Unboxers.unboxer :=
    let! tmp1 := P.Block_access_kind.element_kind_for_load bak in
    ret
      {| var_name := "field_at_use";
         var_kind := tmp1;
         Unboxers.poison_const := poison_const;
         Unboxers.unboxing_prim :=
           fun block => unboxing_prim bak block index;
         prove_simple :=
           fun tenv min_name_mode t =>
           let! tmp1 := P.Block_access_kind.element_kind_for_load bak in
           T.meet_block_field_simple tenv min_name_mode tmp1 t index
      |}.
End Field.

(* 242-260 *)
Module Closure_field.
  (* 243-245. In the compiler: [function_slot ~closure value_slot]. *)
  Definition unboxing_prim (function_slot : Function_slot.t)
      (closure : Simple.t) (value_slot : Value_slot.t) : M P.t :=
    ret (P.Unary (P.Project_value_slot function_slot value_slot) closure).

  (* 247-259 *)
  Definition unboxer (function_slot : Function_slot.t)
      (value_slot : Value_slot.t) : M Unboxers.unboxer :=
    (* PORT-GAP(record-order): 249-253, two fields of the record have
       calls, [var_kind] and [poison_const]: they are taken in the order of
       the type, the last field first, and each is bound before the record
       is built.
       VERDICT (record_order/README.md, place 23): COMMUTE, FAILURES ORDERED.
       [Const.const_poison] alone may add to the table of constants and alone
       can fail (no identifier left). [Value_slot.kind] reads a field. The order
       chooses nothing. *)
    let* poison_const :=
      let! tmp1 := Value_slot.kind value_slot in
      Const.const_poison tmp1 "variant_unboxing_closure_field"
    in
    let* var_kind := Value_slot.kind value_slot in
    ret
      {| var_name := "closure_field_at_use";
         Unboxers.var_kind := var_kind;
         Unboxers.poison_const := poison_const;
         Unboxers.unboxing_prim :=
           fun closure => unboxing_prim function_slot closure value_slot;
         prove_simple :=
           fun tenv min_name_mode t =>
           T.meet_project_value_slot_simple tenv min_name_mode t value_slot
      |}.
End Closure_field.
