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

(* Proofs of the statements of FlambdaImportsSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaPrimitiveProofs
  FlambdaUnusedStaticsSpec FlambdaImportsSpec.
Import ListNotations.

Theorem expr_refines_unit_refines : expr_refines_unit_refines_statement.
Proof. intros imports source target Hrefines. apply Hrefines. Qed.

(* ======================================================================== *)
(* The static environment of the imports                                    *)
(* ======================================================================== *)

(* Three facts for the proofs that start a unit from its imports: there
   is no code in that environment, what it binds a symbol to is something
   imported, and no name occurs in it. *)
Lemma imports_statics_code (imports : list (symbol * import_class)) :
  static_code (imports_statics imports) = [].
Proof. reflexivity. Qed.

Lemma imports_statics_imported (imports : list (symbol * import_class))
    (s : symbol) (allocated : statically_allocated_value) :
  lookup s (static_values (imports_statics imports)) = Some allocated ->
  ∃ c : import_class, allocated = Static_imported c.
Proof.
  unfold imports_statics. cbn [static_values].
  induction imports as [ | [s' c] imports IH]; cbn [map lookup];
    [ discriminate | ].
  destruct (Pos.eqb s s'); [ | exact IH ].
  intros [= <-]. exists c. reflexivity.
Qed.

Lemma imports_statics_free_of (D : dropped)
    (imports : list (symbol * import_class)) :
  envs_free_of D [] [] (imports_statics imports) = true.
Proof.
  unfold envs_free_of, statics_free_of, imports_statics. simpl.
  induction imports as [ | [s c] imports IH]; [ reflexivity | exact IH ].
Qed.

(* ======================================================================== *)
(* A prefix of static bindings                                              *)
(* ======================================================================== *)

Theorem prefix_refines : prefix_refines_statement.
Proof.
  intros prefix statics statics' hp source target Heval.
  assert (Hsource :
    step (State (Let_static prefix source) [] [] statics hp)
    = Step (State source [] [] statics' hp))
    by (rewrite step_let_static, Heval; reflexivity).
  assert (Htarget :
    step (State (Let_static prefix target) [] [] statics hp)
    = Step (State target [] [] statics' hp))
    by (rewrite step_let_static, Heval; reflexivity).
  split; intros Hrefines.
  - apply (refines_trans _ _ _
      (equivalent_refines _ _
         (equivalent_sym _ _ (step_equivalent _ _ Hsource)))).
    apply (refines_trans _ _ _ Hrefines).
    apply equivalent_refines, step_equivalent, Htarget.
  - exact (refines_step _ _ _ _ Hsource Htarget Hrefines).
Qed.

(* ======================================================================== *)
(* What a primitive does with an imported symbol                            *)
(* ======================================================================== *)

Lemma identity_not_allocated (statics : static_env) (v : value)
    (s : symbol) :
  identity_of statics v = Some s -> is_allocated statics v = false.
Proof.
  intros Hs. destruct (is_allocated statics v) eqn:Hallocated;
    [ | reflexivity ].
  unfold identity_of in Hs.
  rewrite (is_allocated_not_imported statics v Hallocated) in Hs.
  discriminate.
Qed.

Lemma identity_is_imported (statics : static_env) (v : value) (s : symbol) :
  identity_of statics v = Some s -> is_imported statics v = true.
Proof.
  intros Hs. apply identity_of_imported in Hs. unfold is_imported.
  rewrite Hs. reflexivity.
Qed.

Theorem phys_equal_identities : phys_equal_identities_statement.
Proof.
  intros statics s1 s2 Hs1 Hs2. unfold eval_phys_equal.
  rewrite !int_of_value_symbol, Hs1, Hs2. reflexivity.
Qed.

Theorem phys_equal_imported_immediate
  : phys_equal_imported_immediate_statement.
Proof.
  intros statics s v Hs Hv. unfold eval_phys_equal.
  unfold is_tagged_immediate in Hv.
  rewrite !int_of_value_symbol, Hs.
  destruct (int_of_value Standard_tagged_immediate v) as [i | ];
    [ | discriminate ].
  rewrite orb_true_r. split; reflexivity.
Qed.

Theorem phys_equal_identity_other : phys_equal_identity_other_statement.
Proof.
  intros statics s v Hs Hv. unfold eval_phys_equal.
  rewrite !int_of_value_symbol, Hs.
  assert (Hnone : identity_of statics v = None).
  { destruct Hv as [Hv | [_ Hv]]; [ | exact Hv ].
    unfold identity_of.
    rewrite (is_allocated_not_imported statics v Hv). reflexivity. }
  assert (Hother : is_allocated statics v || is_imported statics v = true).
  { destruct Hv as [Hv | [Hv _]]; rewrite Hv;
      [ reflexivity | apply orb_true_r ]. }
  assert (Hint : int_of_value Standard_tagged_immediate v = None).
  { destruct (int_of_value Standard_tagged_immediate v) as [i | ] eqn:Hint;
      [ | reflexivity ].
    exfalso. destruct Hv as [Hv | [Hv _]].
    - destruct v; simpl in Hint, Hv; discriminate.
    - unfold is_imported in Hv.
      destruct v; simpl in Hint, Hv; discriminate. }
  rewrite Hint, Hnone, Hother. split; reflexivity.
Qed.

Theorem phys_equal_data_import : phys_equal_data_import_statement.
Proof.
  intros statics s v Hs Hv Hnone. unfold eval_phys_equal.
  unfold is_tagged_immediate in Hv.
  assert (Hdata : identity_of statics (Value_symbol s) = None).
  { unfold identity_of. rewrite Hs. reflexivity. }
  rewrite !int_of_value_symbol, Hdata, Hnone.
  destruct (int_of_value Standard_tagged_immediate v) as [i | ];
    [ discriminate | ].
  split; reflexivity.
Qed.

Theorem imported_not_read : imported_not_read_statement.
Proof.
  split.
  - intros statics p v result Himported.
    unfold is_imported in Himported.
    destruct (imported_of statics v) as [[s c] | ] eqn:Hs;
      [ | discriminate ].
    apply imported_of_symbol in Hs as [-> Hs].
    destruct p as [[tag size field_kind] mut field | variant_only | | |
                  length_kind | | kind | kind op | src dst | | kind | kind | |
                  | reinterpret];
      cbn [eval_unary_primitive];
      unfold eval_block_load, eval_is_int, eval_is_null, is_tagged_immediate,
        is_allocated, eval_reinterpret_64_bit_word;
      try destruct reinterpret;
      rewrite ?int_of_value_symbol;
      cbn [block_of closure_of boxed_number_of string_of array_of
           bound_if_symbol partial_application_of kind_of_value];
      rewrite ?Hs; simpl;
      try discriminate.
    + destruct variant_only; discriminate.
    + destruct kind; simpl; try discriminate.
      intros [= <-]. split; reflexivity.
  - intros statics p v1 v2 result Himported.
    destruct p as [array_kind load_kind mut | width | op | kind op | kind op
                  | kind behaviour];
      cbn [eval_binary_primitive]; [ | | intros _; eauto | | | ];
      intros Heval; exfalso;
      destruct Himported as [Himported | Himported];
      unfold is_imported in Himported;
      (destruct (imported_of statics _) as [[s c] | ] eqn:Hs;
         [ | discriminate ]);
      apply imported_of_symbol in Hs as [-> Hs];
      revert Heval;
      unfold eval_string_load, array_loaded, array_index;
      rewrite ?int_of_value_symbol;
      cbn [string_of array_of]; rewrite ?Hs;
      try discriminate.
    + destruct (array_of statics v1); discriminate.
    + destruct (string_of statics v1); discriminate.
    + destruct (int_of_value kind v1); discriminate.
    + destruct (int_of_value kind v1); discriminate.
    + destruct (int_of_value kind v1); discriminate.
Qed.

(* ======================================================================== *)
(* The examples                                                             *)
(* ======================================================================== *)

Theorem catches_by_name : catches_by_name_statement.
Proof.
  unfold catches_by_name_statement. split; [ | split ].
  - exists 10%nat. vm_compute. reflexivity.
  - exists 10%nat. vm_compute. reflexivity.
  - exists 12%nat. vm_compute. reflexivity.
Qed.

Theorem catches_with_argument : catches_with_argument_statement.
Proof.
  unfold catches_with_argument_statement. split.
  - exists 12%nat. vm_compute. reflexivity.
  - exists 12%nat. vm_compute. reflexivity.
Qed.
