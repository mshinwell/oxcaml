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


(* Proofs of the statements of FlambdaJoinEnvSpec.v. Nothing in this
   file needs to be reviewed. *)

From Stdlib Require Import ZArith List Bool PeanoNat.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesProofs
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvInvariantProofs FlambdaJoinEnv FlambdaJoinSpec
  FlambdaJoinEnvSpec.
Import ListNotations.

(* ======================================================================== *)
(* The instance: what its environments hold                                 *)
(* ======================================================================== *)

Definition source_entries : Keyed.finite_map name _ :=
  Eval vm_compute in Typing_env.names_to_types Witness.source_env.

Definition use_entries : Keyed.finite_map name _ :=
  Eval vm_compute in Typing_env.names_to_types Witness.use_env.

Lemma source_names_to_types :
  Typing_env.names_to_types Witness.source_env = source_entries.
Proof. vm_compute. reflexivity. Qed.

Lemma use_names_to_types :
  Typing_env.names_to_types Witness.use_env = use_entries.
Proof. vm_compute. reflexivity. Qed.

Definition use_null_entries : Keyed.finite_map name _ :=
  Eval vm_compute in Typing_env.names_to_types Witness.use_env_null.

Lemma use_null_names_to_types :
  Typing_env.names_to_types Witness.use_env_null = use_null_entries.
Proof. vm_compute. reflexivity. Qed.

(* A use of the instance is one of its two use environments. *)
Lemma witness_use_at (index : Index.t) (use : Typing_env.t) :
  use_at Witness.inputs index use ->
  use = Witness.use_env ∨ use = Witness.use_env_null.
Proof.
  intros [id Hnth]. cbn in Hnth.
  destruct index as [ | [ | index]]; cbn in Hnth.
  - injection Hnth as _ <-. left. reflexivity.
  - injection Hnth as _ <-. right. reflexivity.
  - destruct index; discriminate.
Qed.

(* The stand-in for the join of types recognises one type. *)
Lemma is_type_of_x_eq (t : flambda_type) :
  Witness.is_type_of_x t = true -> t = Witness.type_of_x.
Proof.
  destruct t as [ty | ty | k ty | ty | ty]; try discriminate.
  destruct ty as [ | d | ]; try discriminate.
  destruct d as [head | s]; try discriminate.
  destruct head as [non_null is_null].
  destruct non_null; try discriminate.
  destruct is_null as [ | is_null]; try discriminate.
  destruct is_null as [r' | ]; try discriminate.
  cbn. destruct r'; intros Heq; try discriminate. reflexivity.
Qed.

Lemma is_type_of_x_null_eq (t : flambda_type) :
  Witness.is_type_of_x_null t = true -> t = Witness.type_of_x_null.
Proof.
  destruct t as [ty | ty | k ty | ty | ty]; try discriminate.
  destruct ty as [ | d | ]; try discriminate.
  destruct d as [head | s]; try discriminate.
  destruct head as [non_null is_null].
  destruct non_null; try discriminate.
  destruct is_null as [ | is_null]; try discriminate.
  destruct is_null as [r' | ]; try discriminate.
  cbn. destruct r'; intros Heq; try discriminate. reflexivity.
Qed.

Theorem witness_join_of_types_upper_bound
  : witness_join_of_types_upper_bound_statement.
Proof.
  intros s s' ts ty index t_index statics valuation valuation' v Hjoin Hin
    Hr Hsatisfied.
  unfold Witness.join_of_types in Hjoin.
  destruct ts as [ | binding ts]; [ discriminate | ].
  destruct (forallb _ (binding :: ts)) eqn:Hall; [ | discriminate ].
  injection Hjoin as <- <-. split; [ reflexivity | ].
  rewrite forallb_forall in Hall. specialize (Hall _ Hin). cbn in Hall.
  apply orb_true_iff in Hall. destruct Hall as [Hall | Hall].
  - apply is_type_of_x_eq in Hall. subst t_index.
    unfold Witness.type_of_x in *.
    rewrite type_satisfied_value in *. cbn in *.
    rewrite head_of_kind_value_satisfied_eq in *.
    unfold variable_is in *. rewrite Hr. exact Hsatisfied.
  - apply is_type_of_x_null_eq in Hall. subst t_index.
    unfold Witness.type_of_x, Witness.type_of_x_null in *.
    rewrite type_satisfied_value in *. cbn in *.
    rewrite head_of_kind_value_satisfied_eq in *.
    unfold variable_is in *. rewrite Hr.
    destruct Hsatisfied as [Hnull | [_ [[] _]]]. left. exact Hnull.
Qed.

(* ======================================================================== *)
(* The inputs of the instance                                               *)
(* ======================================================================== *)

Lemma source_invariant : typing_env_invariant Witness.source_env.
Proof.
  apply add_variable_definition_invariant; [ | reflexivity ].
  apply add_variable_definition_invariant; [ | reflexivity ].
  exact create_invariant.
Qed.

Lemma use_invariant : typing_env_invariant Witness.use_env.
Proof.
  apply replace_equation_invariant.
  - apply increment_scope_invariant. exact source_invariant.
  - reflexivity.
  - intros y [<- | []]. reflexivity.
  - intros ty' binding_time_and_mode Hlookup. vm_compute in Hlookup.
    injection Hlookup as <- _. reflexivity.
  - intros alias Halias. discriminate.
  - left. reflexivity.
Qed.

Lemma use_null_invariant : typing_env_invariant Witness.use_env_null.
Proof.
  apply replace_equation_invariant.
  - apply increment_scope_invariant. exact source_invariant.
  - reflexivity.
  - intros y [<- | []]. reflexivity.
  - intros ty' binding_time_and_mode Hlookup. vm_compute in Hlookup.
    injection Hlookup as <- _. reflexivity.
  - intros alias Halias. discriminate.
  - left. reflexivity.
Qed.

(* What an environment of the instance has for a name: the cases of a
   lookup in its entries. *)
Ltac entries_cases Hlookup n :=
  destruct n as [y | sym]; cbn [Keyed.lookup name_eqb fst snd] in Hlookup;
  [ destruct (Pos.eqb y 2%positive) eqn:Hx;
    [ apply Pos.eqb_eq in Hx; subst y
    | destruct (Pos.eqb y 1%positive) eqn:Hr;
      [ apply Pos.eqb_eq in Hr; subst y | ] ]
  | ].

Lemma source_no_bottom_types : no_bottom_types Witness.source_env.
Proof.
  intros _ n ty binding_time_and_mode Hlookup.
  rewrite source_names_to_types in Hlookup. unfold source_entries in Hlookup.
  entries_cases Hlookup n; try discriminate;
    injection Hlookup as <- _; reflexivity.
Qed.

Lemma use_no_bottom_types : no_bottom_types Witness.use_env.
Proof.
  intros _ n ty binding_time_and_mode Hlookup.
  rewrite use_names_to_types in Hlookup. unfold use_entries in Hlookup.
  entries_cases Hlookup n; try discriminate;
    injection Hlookup as <- _; reflexivity.
Qed.

Lemma use_kinded : typing_env_kinded Witness.use_env.
Proof.
  intros n ty binding_time_and_mode Hlookup.
  rewrite use_names_to_types in Hlookup. unfold use_entries in Hlookup.
  entries_cases Hlookup n; try discriminate; injection Hlookup as <- _.
  - intros simple kind [Heq | []]. injection Heq as <- <-.
    eexists. vm_compute. reflexivity.
  - intros simple kind [].
Qed.

Lemma use_null_no_bottom_types : no_bottom_types Witness.use_env_null.
Proof.
  intros _ n ty binding_time_and_mode Hlookup.
  rewrite use_null_names_to_types in Hlookup.
  unfold use_null_entries in Hlookup.
  entries_cases Hlookup n; try discriminate;
    injection Hlookup as <- _; reflexivity.
Qed.

Lemma use_null_kinded : typing_env_kinded Witness.use_env_null.
Proof.
  intros n ty binding_time_and_mode Hlookup.
  rewrite use_null_names_to_types in Hlookup.
  unfold use_null_entries in Hlookup.
  entries_cases Hlookup n; try discriminate; injection Hlookup as <- _.
  - intros simple kind [Heq | []]. injection Heq as <- <-.
    eexists. vm_compute. reflexivity.
  - intros simple kind [].
Qed.

Theorem witness_inputs_well_formed : witness_inputs_well_formed_statement.
Proof.
  split; [ split; [ | split; [ | split; [ | split ] ] ] | ].
  - split; [ exact source_invariant | ].
    intros index use Huse.
    destruct (witness_use_at _ _ Huse); subst use;
      [ exact use_invariant | exact use_null_invariant ].
  - split; [ exact source_no_bottom_types | ].
    intros index use Huse.
    destruct (witness_use_at _ _ Huse); subst use;
      [ exact use_no_bottom_types | exact use_null_no_bottom_types ].
  - intros index use Huse _.
    destruct (witness_use_at _ _ Huse); subst use;
      eexists; vm_compute; reflexivity.
  - intros index use sym Huse Hdefined.
    destruct (witness_use_at _ _ Huse); subst use; discriminate.
  - split.
    + intros y Hknown. unfold knows, Typing_env.mem in Hknown.
      change (source Witness.inputs) with Witness.source_env in Hknown.
      rewrite source_names_to_types in Hknown.
      unfold source_entries in Hknown.
      cbn [Keyed.lookup name_eqb fst snd] in Hknown.
      destruct (Pos.eqb y 2%positive) eqn:Hx;
        [ apply Pos.eqb_eq in Hx; subst y; reflexivity | ].
      destruct (Pos.eqb y 1%positive) eqn:Hr;
        [ apply Pos.eqb_eq in Hr; subst y; reflexivity | discriminate ].
    + intros index use y Huse Hknown.
      unfold knows, Typing_env.mem in Hknown.
      destruct (witness_use_at _ _ Huse); subst use;
        [ rewrite use_names_to_types in Hknown; unfold use_entries in Hknown
        | rewrite use_null_names_to_types in Hknown;
          unfold use_null_entries in Hknown ];
        cbn [Keyed.lookup name_eqb fst snd] in Hknown;
        (destruct (Pos.eqb y 2%positive) eqn:Hx;
           [ apply Pos.eqb_eq in Hx; subst y; reflexivity | ]);
        (destruct (Pos.eqb y 1%positive) eqn:Hr;
           [ apply Pos.eqb_eq in Hr; subst y; reflexivity | discriminate ]).
  - intros index use Huse.
    destruct (witness_use_at _ _ Huse); subst use;
      [ exact use_kinded | exact use_null_kinded ].
Qed.

(* ======================================================================== *)
(* The run of the instance                                                  *)
(* ======================================================================== *)

Lemma source_aliases : Typing_env.aliases Witness.source_env = Aliases.empty.
Proof. reflexivity. Qed.

Lemma use_aliases : Typing_env.aliases Witness.use_env = Aliases.empty.
Proof. reflexivity. Qed.

Theorem witness_run_satisfies : witness_run_satisfies_statement.
Proof.
  intros statics. split.
  - split; [ reflexivity | ]. split.
    + intros n ty binding_time_and_mode v Hlookup Hvalue.
      rewrite use_names_to_types in Hlookup. unfold use_entries in Hlookup.
      entries_cases Hlookup n; try discriminate.
      injection Hlookup as <- _. injection Hvalue as <-.
      right. rewrite type_satisfied_naked_immediate. reflexivity.
    + rewrite use_aliases. apply empty_respected.
  - split; [ reflexivity | ]. split.
    + intros n ty binding_time_and_mode v Hlookup Hvalue.
      rewrite source_names_to_types in Hlookup.
      unfold source_entries in Hlookup.
      entries_cases Hlookup n; try discriminate.
      injection Hlookup as <- _. injection Hvalue as <-.
      right. rewrite type_satisfied_naked_immediate. reflexivity.
    + rewrite source_aliases. apply empty_respected.
Qed.

(* ======================================================================== *)
(* What the join answers for the instance                                   *)
(* ======================================================================== *)

Definition witness_target : Typing_env.t :=
  Eval vm_compute in
    match Witness.join [Witness.r; Witness.x] Witness.inputs with
    | Some (target, _) => target
    | None => Typing_env.create
    end.

Definition witness_analysis : Analysis.t unit :=
  Eval vm_compute in
    match Witness.join [Witness.r; Witness.x] Witness.inputs with
    | Some (_, analysis) => analysis
    | None => Analysis.empty
    end.

Lemma witness_join_result :
  Witness.join [Witness.r; Witness.x] Witness.inputs
  = Some (witness_target, witness_analysis).
Proof. vm_compute. reflexivity. Qed.

Theorem witness_use_not_admitted : witness_use_not_admitted_statement.
Proof.
  exists witness_target, witness_analysis.
  split; [ exact witness_join_result | ]. split; [ | split ].
  - intros Hadmits.
    destruct (witness_run_satisfies (Static_env [] [])) as [Huse Hsource].
    destruct (Hadmits _ _ Huse Hsource)
      as [valuation' [[_ [Htypes _]] [Hagrees _]]].
    assert (Hr : value_of_name valuation' (Name_var Witness.r)
                 = Some (Value_const (Naked_immediate 0))).
    { cbn. rewrite (Hagrees Witness.r eq_refl). reflexivity. }
    assert (Hx : lookup Witness.x valuation' = None).
    { rewrite (Hagrees Witness.x eq_refl). reflexivity. }
    destruct (Htypes (Name_var Witness.r) _ _ _ eq_refl Hr)
      as [[[] _] | Hsatisfied].
    rewrite type_satisfied_naked_immediate in Hsatisfied.
    destruct Hsatisfied as [i [_ [_ Hrelations]]].
    destruct
      (Hrelations Relation.Is_null (Name_var Witness.x) (or_introl eq_refl))
      as [w [Hw _]].
    cbn in Hw. rewrite Hx in Hw. discriminate.
  - intros Hscrutinees.
    destruct
      (Hscrutinees Witness.r Witness.x Relation.Is_null _ _ eq_refl
         (or_introl eq_refl) (or_introl (ex_intro _ _ eq_refl)))
      as [[v Hv] | [simples [kind [simple [v [Hdefinition _]]]]]];
      discriminate.
  - intros Hjoined.
    destruct (Hjoined Witness.x eq_refl) as [v Hv]; [ | discriminate ].
    intros index use Huse _.
    destruct (witness_use_at _ _ Huse); subst use;
      eexists; eexists; split; vm_compute; reflexivity.
Qed.

Theorem transcribed_join_not_strict : transcribed_join_not_strict_statement.
Proof.
  intros Hsound.
  destruct witness_inputs_well_formed as [Hwell_formed Hkinded].
  destruct witness_use_not_admitted
    as [target [analysis [Hjoin [Hnot_admitted _]]]].
  destruct (Hsound _ _ _ _ Hwell_formed Hkinded Hjoin)
    as [_ [_ [_ [_ [_ Hadmits]]]]].
  apply Hnot_admitted. apply (Hadmits 0 Witness.use_env).
  exists tt. reflexivity.
Qed.
