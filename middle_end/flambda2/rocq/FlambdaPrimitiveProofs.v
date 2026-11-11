(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* Proofs of the statements of FlambdaPrimitiveSpec.v, with what the
   other proofs use of the primitives: the equations of [eval_prim] by
   arity, that the equality tests decide equality, and that the integers
   of the primitives are those of rocq/. Nothing here needs review.

   [eval_prim] is opaque after this file. A proof that is not about one
   primitive goes through the three laws ([eval_prim_static_values],
   [eval_prim_kinds], [eval_prim_preserves]); one that is rewrites with
   [eval_prim_unary] or [eval_prim_binary].

   To add a primitive, add its case where a proof here goes by cases on
   the primitives: each such proof says so. No proof here names the
   constructors of [value] by their position, so one more does not break
   them. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList
  OxCamlInt OxCamlIntProofs OxCamlInt64.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaValueSpec FlambdaPrimitiveSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The equality tests                                                       *)
(* ======================================================================== *)

Lemma kind_eqb_eq (k k' : flambda_kind) : kind_eqb k k' = true <-> k = k'.
Proof.
  unfold kind_eqb. destruct (kind_eq_dec k k'); split; congruence.
Qed.

Lemma kind_eqb_refl (k : flambda_kind) : kind_eqb k k = true.
Proof. apply kind_eqb_eq. reflexivity. Qed.

Lemma prim_eqb_sound (p p' : prim) : prim_eqb p p' = true -> p = p'.
Proof. unfold prim_eqb. destruct (prim_eq_dec p p'); congruence. Qed.

Lemma prim_eqb_refl (p : prim) : prim_eqb p p = true.
Proof. unfold prim_eqb. destruct (prim_eq_dec p p); congruence. Qed.

(* ======================================================================== *)
(* The equations of [eval_prim]                                             *)
(* ======================================================================== *)

Lemma eval_prim_unary (statics : static_env) (p : unary_primitive)
    (v : value) :
  eval_prim statics (Unary p) [v] = eval_unary_primitive statics p v.
Proof. reflexivity. Qed.

Lemma eval_prim_binary (statics : static_env) (p : binary_primitive)
    (v1 v2 : value) :
  eval_prim statics (Binary p) [v1; v2] = eval_binary_primitive p v1 v2.
Proof. reflexivity. Qed.

(* A primitive that has a value was applied to as many arguments as it
   takes. (By cases on the arities.) *)
Lemma eval_prim_arity (statics : static_env) (p : prim) (vs : list value)
    (v : value) :
  eval_prim statics p vs = Some v ->
  (∃ (p' : unary_primitive) (v1 : value),
    p = Unary p' ∧ vs = [v1] ∧ eval_unary_primitive statics p' v1 = Some v)
  ∨ (∃ (p' : binary_primitive) (v1 v2 : value),
      p = Binary p' ∧ vs = [v1; v2]
      ∧ eval_binary_primitive p' v1 v2 = Some v).
Proof.
  destruct p as [p | p], vs as [ | v1 [ | v2 [ | v3 vs]]]; simpl;
    try discriminate; intros Heval.
  - left. exists p, v1. auto.
  - right. exists p, v1, v2. auto.
Qed.

(* ======================================================================== *)
(* Integers and their kinds                                                 *)
(* ======================================================================== *)

(* A value that is an integer of a kind is the constant of that integer,
   in range. *)
Lemma int_of_value_const (kind : standard_int) (v : value) (i : Z) :
  int_of_value kind v = Some i ->
  v = Value_const (const_of_int kind i)
  ∧ in_range (int_width kind) i = true.
Proof.
  destruct kind, v; simpl; try discriminate;
    (match goal with c : const |- _ => destruct c end);
    simpl; try discriminate;
    match goal with
    | |- context [if ?test then _ else _] =>
      destruct test eqn:Hrange; [ | discriminate ]
    end;
    intros [= <-]; auto.
Qed.

Lemma kind_of_const_of_int (kind : standard_int) (i : Z) :
  kind_of_const (const_of_int kind i) = kind_of_standard_int kind.
Proof. destruct kind; reflexivity. Qed.

Lemma int_of_value_kind (kind : standard_int) (v : value) (i : Z) :
  int_of_value kind v = Some i ->
  kind_of_value v = kind_of_standard_int kind.
Proof.
  intros Hint. apply int_of_value_const in Hint as [-> _]. simpl.
  apply kind_of_const_of_int.
Qed.

Lemma is_tagged_immediate_kind (v : value) :
  is_tagged_immediate v = true -> kind_of_value v = Value.
Proof.
  unfold is_tagged_immediate.
  destruct (int_of_value Standard_tagged_immediate v) as [i | ] eqn:Hint;
    [ | discriminate ].
  intros _. exact (int_of_value_kind _ _ _ Hint).
Qed.

(* ======================================================================== *)
(* The observations                                                         *)
(* ======================================================================== *)

(* An allocated value is of kind [Value]: a constant is none of a closure,
   a block, a boxed number and a string. *)
Lemma block_of_kind (statics : static_env) (v : value) :
  is_some (block_of statics v) = true -> kind_of_value v = Value.
Proof. destruct v; simpl; try discriminate; reflexivity. Qed.

Lemma is_allocated_kind (statics : static_env) (v : value) :
  is_allocated statics v = true -> kind_of_value v = Value.
Proof. destruct v; simpl; try discriminate; reflexivity. Qed.

(* An observation depends on the static environment only through what
   the value, if it is a symbol, is bound to. *)
Section Static_values.

Variables statics statics' : static_env.
Variable v : value.
Hypothesis Hsame :
  ∀ s : symbol,
    v = Value_symbol s ->
    lookup s (static_values statics) = lookup s (static_values statics').

Lemma closure_of_static_values : closure_of statics v = closure_of statics' v.
Proof.
  destruct v; simpl; try reflexivity. rewrite (Hsame _ eq_refl).
  reflexivity.
Qed.

Lemma block_of_static_values : block_of statics v = block_of statics' v.
Proof.
  destruct v; simpl; try reflexivity. rewrite (Hsame _ eq_refl).
  reflexivity.
Qed.

Lemma boxed_number_of_static_values :
  boxed_number_of statics v = boxed_number_of statics' v.
Proof.
  destruct v; simpl; try reflexivity. rewrite (Hsame _ eq_refl).
  reflexivity.
Qed.

Lemma string_of_static_values : string_of statics v = string_of statics' v.
Proof.
  destruct v; simpl; try reflexivity. rewrite (Hsame _ eq_refl).
  reflexivity.
Qed.

Lemma is_allocated_static_values :
  is_allocated statics v = is_allocated statics' v.
Proof.
  unfold is_allocated.
  rewrite closure_of_static_values, block_of_static_values,
    boxed_number_of_static_values, string_of_static_values.
  reflexivity.
Qed.

(* By cases on the unary primitives: one that reads an allocated value
   does so through an observation. *)
Lemma eval_unary_primitive_static_values (p : unary_primitive) :
  eval_unary_primitive statics p v = eval_unary_primitive statics' p v.
Proof.
  destruct p; simpl; unfold eval_is_int, eval_is_null;
    rewrite ?block_of_static_values, ?is_allocated_static_values;
    reflexivity.
Qed.

End Static_values.

Theorem eval_prim_static_values : eval_prim_static_values_statement.
Proof.
  intros statics statics' p vs Hsame.
  destruct p as [p | p], vs as [ | v1 [ | v2 [ | v3 vs]]]; simpl;
    try reflexivity.
  apply eval_unary_primitive_static_values. intros s ->.
  apply Hsame. left. reflexivity.
Qed.

(* A primitive does not look at the code. *)
Lemma eval_prim_same_static_values (statics statics' : static_env)
    (p : prim) (vs : list value) :
  static_values statics = static_values statics' ->
  eval_prim statics p vs = eval_prim statics' p vs.
Proof.
  intros Hvalues. apply eval_prim_static_values. intros s _.
  rewrite Hvalues. reflexivity.
Qed.

(* On constants, a primitive does not look at the static environment. *)
Lemma eval_prim_consts (statics statics' : static_env) (p : prim)
    (cs : list const) :
  eval_prim statics p (map Value_const cs)
  = eval_prim statics' p (map Value_const cs).
Proof.
  apply eval_prim_static_values. intros s Hin.
  apply in_map_iff in Hin as (c & Hc & _). discriminate.
Qed.

(* ======================================================================== *)
(* Kinds                                                                    *)
(* ======================================================================== *)

(* By cases on the unary primitives. *)
Lemma eval_unary_primitive_kinds (statics : static_env)
    (p : unary_primitive) (arg v : value) :
  eval_unary_primitive statics p arg = Some v ->
  kind_of_value arg = arg_kind_of_unary_primitive p
  ∧ kind_of_value v = result_kind_of_unary_primitive p.
Proof.
  destruct p as [variant_only | | | kind | | ];
    cbn [eval_unary_primitive arg_kind_of_unary_primitive
         result_kind_of_unary_primitive].
  - (* [Is_int] *)
    unfold eval_is_int.
    destruct (is_tagged_immediate arg) eqn:Htagged.
    + intros [= <-]. split; [ | reflexivity ].
      exact (is_tagged_immediate_kind arg Htagged).
    + destruct variant_only.
      * destruct (is_some (block_of statics arg)) eqn:Hblock;
          [ | discriminate ].
        intros [= <-]. split; [ | reflexivity ].
        exact (block_of_kind statics arg Hblock).
      * destruct (is_allocated statics arg) eqn:Hallocated;
          [ | discriminate ].
        intros [= <-]. split; [ | reflexivity ].
        exact (is_allocated_kind statics arg Hallocated).
  - (* [Is_null] *)
    unfold eval_is_null.
    assert (Hother :
      option_map naked_bool
        (if is_tagged_immediate arg || is_allocated statics arg
         then Some false
         else None)
      = Some v ->
      kind_of_value arg = Value ∧ kind_of_value v = naked_immediate_kind).
    { destruct (is_tagged_immediate arg) eqn:Htagged; simpl.
      - intros [= <-]. split; [ | reflexivity ].
        exact (is_tagged_immediate_kind arg Htagged).
      - destruct (is_allocated statics arg) eqn:Hallocated;
          [ | discriminate ].
        intros [= <-]. split; [ | reflexivity ].
        exact (is_allocated_kind statics arg Hallocated). }
    destruct arg; try exact Hother.
    match goal with c : const |- _ => destruct c end; try exact Hother.
    intros [= <-]. split; reflexivity.
  - (* [Get_tag] *)
    destruct (block_of statics arg) as [[tag fields] | ] eqn:Hblock;
      [ | discriminate ].
    intros [= <-]. split; [ | reflexivity ].
    apply (block_of_kind statics). rewrite Hblock. reflexivity.
  - (* [Opaque_identity] *)
    destruct (kind_eqb (kind_of_value arg) kind) eqn:Hkind;
      [ | discriminate ].
    apply kind_eqb_eq in Hkind. intros [= <-]. auto.
  - (* [Untag_immediate] *)
    destruct (int_of_value Standard_tagged_immediate arg) as [i | ] eqn:Hint;
      [ | discriminate ].
    intros [= <-]. split; [ | reflexivity ].
    exact (int_of_value_kind _ _ _ Hint).
  - (* [Tag_immediate] *)
    destruct (int_of_value Standard_naked_immediate arg) as [i | ] eqn:Hint;
      [ | discriminate ].
    intros [= <-]. split; [ | reflexivity ].
    exact (int_of_value_kind _ _ _ Hint).
Qed.

(* By cases on the binary primitives. *)
Lemma eval_binary_primitive_kinds (p : binary_primitive)
    (arg1 arg2 v : value) :
  eval_binary_primitive p arg1 arg2 = Some v ->
  kind_of_value arg1 = fst (args_kind_of_binary_primitive p)
  ∧ kind_of_value arg2 = snd (args_kind_of_binary_primitive p)
  ∧ kind_of_value v = result_kind_of_binary_primitive p.
Proof.
  destruct p as [kind op | kind behaviour]; simpl;
    (destruct (int_of_value kind arg1) as [a | ] eqn:Ha; [ | discriminate ]);
    (destruct (int_of_value kind arg2) as [b | ] eqn:Hb; [ | discriminate ]);
    rewrite (int_of_value_kind _ _ _ Ha), (int_of_value_kind _ _ _ Hb).
  - destruct (eval_int_arith (int_width kind) op a b) as [result | ];
      [ | discriminate ].
    intros [= <-]. simpl. rewrite kind_of_const_of_int. auto.
  - intros [= <-]. auto.
Qed.

Theorem eval_prim_kinds : eval_prim_kinds_statement.
Proof.
  intros statics p vs v Heval.
  destruct (eval_prim_arity statics p vs v Heval)
    as [(p' & v1 & -> & -> & Hp) | (p' & v1 & v2 & -> & -> & Hp)]; simpl.
  - apply eval_unary_primitive_kinds in Hp as [-> ->].
    rewrite kind_eqb_refl. auto.
  - apply eval_binary_primitive_kinds in Hp as (-> & -> & ->).
    rewrite !kind_eqb_refl. auto.
Qed.

(* ======================================================================== *)
(* A primitive makes its value out of its arguments                         *)
(* ======================================================================== *)

Section Preserves.

Variable P : value -> Prop.
Variable statics : static_env.
Hypothesis Hnumbers : holds_of_numbers P.
Hypothesis Hblocks : holds_of_blocks P.
Hypothesis Hstatic : holds_in_static_blocks statics P.

Lemma naked_bool_preserved (b : bool) : P (naked_bool b).
Proof. apply Hnumbers. Qed.

(* By cases on the unary primitives. *)
Lemma eval_unary_primitive_preserves (p : unary_primitive) (arg v : value) :
  P arg -> eval_unary_primitive statics p arg = Some v -> P v.
Proof.
  intros Harg.
  destruct p as [variant_only | | | kind | | ]; cbn [eval_unary_primitive].
  - destruct (eval_is_int statics variant_only arg); [ | discriminate ].
    intros [= <-]. apply naked_bool_preserved.
  - destruct (eval_is_null statics arg); [ | discriminate ].
    intros [= <-]. apply naked_bool_preserved.
  - destruct (block_of statics arg) as [[tag fields] | ]; [ | discriminate ].
    intros [= <-]. apply Hnumbers.
  - destruct (kind_eqb (kind_of_value arg) kind); [ | discriminate ].
    intros [= <-]. exact Harg.
  - destruct (int_of_value Standard_tagged_immediate arg); [ | discriminate ].
    intros [= <-]. apply Hnumbers.
  - destruct (int_of_value Standard_naked_immediate arg); [ | discriminate ].
    intros [= <-]. apply Hnumbers.
Qed.

(* By cases on the binary primitives. *)
Lemma eval_binary_primitive_preserves (p : binary_primitive)
    (arg1 arg2 v : value) :
  eval_binary_primitive p arg1 arg2 = Some v -> P v.
Proof.
  destruct p as [kind op | kind behaviour]; simpl;
    (destruct (int_of_value kind arg1) as [a | ]; [ | discriminate ]);
    (destruct (int_of_value kind arg2) as [b | ]; [ | discriminate ]).
  - destruct (eval_int_arith (int_width kind) op a b); [ | discriminate ].
    intros [= <-]. apply Hnumbers.
  - intros [= <-]. apply Hnumbers.
Qed.

End Preserves.

Theorem eval_prim_preserves : eval_prim_preserves_statement.
Proof.
  intros P statics p vs v Hnumbers Hblocks Hstatic Hargs Heval.
  destruct (eval_prim_arity statics p vs v Heval)
    as [(p' & v1 & -> & -> & Hp) | (p' & v1 & v2 & -> & -> & Hp)].
  - apply (eval_unary_primitive_preserves P statics Hnumbers p' v1 v);
      [ | exact Hp ].
    apply Hargs. left. reflexivity.
  - exact (eval_binary_primitive_preserves P Hnumbers p' v1 v2 v Hp).
Qed.

(* ======================================================================== *)
(* The integers are those of rocq/                                          *)
(* ======================================================================== *)

(* What wraps is in range, so the results of arithmetic are. *)
Lemma wrap_in_range (width z : Z) :
  1 <= width -> in_range width (wrap width z) = true.
Proof.
  intros Hwidth. unfold in_range, wrap.
  assert (Hhalf : 0 < 2 ^ (width - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdouble : 2 ^ width = 2 * 2 ^ (width - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  pose proof (Z.mod_pos_bound (z + 2 ^ (width - 1)) (2 ^ width)) as Hmod.
  apply andb_true_iff. split; [ apply Z.leb_le | apply Z.ltb_lt ]; lia.
Qed.

Lemma int_width_positive (kind : standard_int) : 1 <= int_width kind.
Proof. destruct kind; simpl; lia. Qed.

Lemma eval_int_arith_in_range (width : Z) (op : binary_int_arith_op)
    (a b result : Z) :
  1 <= width ->
  eval_int_arith width op a b = Some result ->
  in_range width result = true.
Proof.
  intros Hwidth.
  destruct op; simpl; try destruct (b =? 0); try discriminate;
    intros [= <-]; apply wrap_in_range, Hwidth.
Qed.

(* At 64 bits, the arithmetic of rocq/OxCamlInt64.v. *)
Lemma wrap_64 (z : Z) : wrap 64 z = wrap64 z.
Proof. reflexivity. Qed.

Lemma unsigned_64 (z : Z) : unsigned 64 z = unsigned64 z.
Proof. reflexivity. Qed.

Lemma in_range_64 (z : Z) : in_range 64 z = fits_int64 z.
Proof. reflexivity. Qed.

(* At 63 bits, OCaml's [int] as rocq/OxCamlInt.v has it: Rocq's [Sint63].
   Every [int] is in range, and its sums, differences and products are
   those of the primitives. *)
Lemma in_range_63 (z : Z) : in_range 63 z = fits_int z.
Proof.
  unfold in_range, fits_int. change (2 ^ (63 - 1)) with two62.
  destruct (- two62 <=? z); [ | reflexivity ]. simpl.
  destruct (Z.ltb_spec z two62), (Z.leb_spec z (two62 - 1)); try reflexivity;
    unfold two62 in *; lia.
Qed.

Lemma wrap_63 (z : Z) : wrap 63 z = Sint63.cmod z Uint63.wB.
Proof. reflexivity. Qed.

Lemma int_in_range (i : int) : in_range 63 (Sint63.to_Z i) = true.
Proof.
  rewrite in_range_63. unfold fits_int. pose proof (int_bounds i).
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma int_add (a b : int) :
  Sint63.to_Z (a + b)%sint63 = wrap 63 (Sint63.to_Z a + Sint63.to_Z b).
Proof. rewrite wrap_63. apply Sint63.add_spec. Qed.

Lemma int_sub (a b : int) :
  Sint63.to_Z (a - b)%sint63 = wrap 63 (Sint63.to_Z a - Sint63.to_Z b).
Proof. rewrite wrap_63. apply Sint63.sub_spec. Qed.

Lemma int_mul (a b : int) :
  Sint63.to_Z (a * b)%sint63 = wrap 63 (Sint63.to_Z a * Sint63.to_Z b).
Proof. rewrite wrap_63. apply Sint63.mul_spec. Qed.

(* ======================================================================== *)
(* Each primitive has a value somewhere                                     *)
(* ======================================================================== *)

(* So that no statement about a primitive holds for its having no value
   at all, and as a check of the definitions against known answers. *)

Module Examples.

Definition tagged (i : Z) : value := Value_const (Tagged_immediate i).
Definition naked (i : Z) : value := Value_const (Naked_immediate i).

Definition max_int63 : Z := 4611686018427387903.
Definition min_int63 : Z := -4611686018427387904.

Definition a_block : static_env :=
  Static_env [] [(1%positive, Static_block 3 [tagged 10; tagged 20])].

Definition int_arith (kind : standard_int) (op : binary_int_arith_op)
    (a b : value) : option value :=
  eval_prim empty_static_env (Binary (Int_arith kind op)) [a; b].

Definition int_comp (kind : standard_int)
    (behaviour : int_comparison_behaviour) (a b : value) : option value :=
  eval_prim empty_static_env (Binary (Int_comp kind behaviour)) [a; b].

Definition unary (statics : static_env) (p : unary_primitive) (v : value)
    : option value :=
  eval_prim statics (Unary p) [v].

Example add_tagged :
  int_arith Standard_tagged_immediate Add (tagged 3) (tagged 4)
  = Some (tagged 7).
Proof. reflexivity. Qed.

Example add_wraps :
  int_arith Standard_tagged_immediate Add (tagged max_int63) (tagged 1)
  = Some (tagged min_int63).
Proof. reflexivity. Qed.

Example mul_int8_wraps :
  int_arith Standard_naked_int8 Mul (Value_const (Naked_int8 100))
    (Value_const (Naked_int8 3))
  = Some (Value_const (Naked_int8 44)).
Proof. reflexivity. Qed.

Example div_truncates :
  int_arith Standard_tagged_immediate (Div Signed) (tagged (-7)) (tagged 2)
  = Some (tagged (-3)).
Proof. reflexivity. Qed.

Example mod_has_sign_of_dividend :
  int_arith Standard_tagged_immediate (Mod Signed) (tagged (-7)) (tagged 2)
  = Some (tagged (-1)).
Proof. reflexivity. Qed.

Example div_min_by_minus_one :
  int_arith Standard_tagged_immediate (Div Signed) (tagged min_int63)
    (tagged (-1))
  = Some (tagged min_int63).
Proof. reflexivity. Qed.

Example div_unsigned :
  int_arith Standard_naked_int8 (Div Unsigned)
    (Value_const (Naked_int8 (-2))) (Value_const (Naked_int8 2))
  = Some (Value_const (Naked_int8 127)).
Proof. reflexivity. Qed.

Example div_by_zero :
  int_arith Standard_tagged_immediate (Div Signed) (tagged 1) (tagged 0)
  = None.
Proof. reflexivity. Qed.

Example xor_tagged :
  int_arith Standard_tagged_immediate Xor (tagged 5) (tagged (-1))
  = Some (tagged (-6)).
Proof. reflexivity. Qed.

Example add_out_of_range :
  int_arith Standard_tagged_immediate Add (tagged (max_int63 + 1)) (tagged 0)
  = None.
Proof. reflexivity. Qed.

Example add_wrong_kind :
  int_arith Standard_tagged_immediate Add (naked 3) (tagged 4) = None.
Proof. reflexivity. Qed.

Example lt_signed :
  int_comp Standard_tagged_immediate (Yielding_bool (Int_lt Signed))
    (tagged (-1)) (tagged 0)
  = Some (naked 1).
Proof. reflexivity. Qed.

Example lt_unsigned :
  int_comp Standard_tagged_immediate (Yielding_bool (Int_lt Unsigned))
    (tagged (-1)) (tagged 0)
  = Some (naked 0).
Proof. reflexivity. Qed.

Example compare_like_functions :
  int_comp Standard_naked_int64 (Yielding_int_like_compare_functions Signed)
    (Value_const (Naked_int64 5)) (Value_const (Naked_int64 9))
  = Some (naked (-1)).
Proof. reflexivity. Qed.

Example tag_immediate :
  unary empty_static_env Tag_immediate (naked 5) = Some (tagged 5).
Proof. reflexivity. Qed.

Example untag_immediate :
  unary empty_static_env Untag_immediate (tagged 5) = Some (naked 5).
Proof. reflexivity. Qed.

Example is_int_of_immediate :
  unary empty_static_env (Is_int true) (tagged 5) = Some (naked 1).
Proof. reflexivity. Qed.

Example is_int_of_static_block :
  unary a_block (Is_int true) (Value_symbol 1%positive) = Some (naked 0).
Proof. reflexivity. Qed.

Example is_int_of_closure_of_variant :
  unary empty_static_env (Is_int true) (Value_closure 1%positive []) = None.
Proof. reflexivity. Qed.

Example is_int_of_closure :
  unary empty_static_env (Is_int false) (Value_closure 1%positive [])
  = Some (naked 0).
Proof. reflexivity. Qed.

Example is_int_of_unbound_symbol :
  unary empty_static_env (Is_int false) (Value_symbol 1%positive) = None.
Proof. reflexivity. Qed.

Example is_null_of_null :
  unary empty_static_env Is_null (Value_const Null) = Some (naked 1).
Proof. reflexivity. Qed.

Example is_null_of_immediate :
  unary empty_static_env Is_null (tagged 0) = Some (naked 0).
Proof. reflexivity. Qed.

Example get_tag_of_static_block :
  unary a_block Get_tag (Value_symbol 1%positive) = Some (naked 3).
Proof. reflexivity. Qed.

Example get_tag_of_immediate :
  unary a_block Get_tag (tagged 0) = None.
Proof. reflexivity. Qed.

(* A boxed poison is a boxed number, and allocated. *)
Definition a_boxed_poison : static_env :=
  Static_env []
    [(1%positive,
      Static_boxed_number
        (Value_const (Poison (Naked_number Kind_naked_float))))].

Example boxed_poison_is_a_boxed_number :
  boxed_number_of a_boxed_poison (Value_symbol 1%positive)
  = Some (Poison (Naked_number Kind_naked_float)).
Proof. reflexivity. Qed.

Example is_null_of_boxed_poison :
  unary a_boxed_poison Is_null (Value_symbol 1%positive) = Some (naked 0).
Proof. reflexivity. Qed.

Example opaque_identity :
  unary empty_static_env (Opaque_identity Value) (Value_symbol 1%positive)
  = Some (Value_symbol 1%positive).
Proof. reflexivity. Qed.

Example opaque_identity_wrong_kind :
  unary empty_static_env (Opaque_identity Value) (naked 1) = None.
Proof. reflexivity. Qed.

End Examples.

#[global] Opaque eval_prim.
