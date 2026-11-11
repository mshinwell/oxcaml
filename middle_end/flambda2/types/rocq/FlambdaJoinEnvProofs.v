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
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaMapProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesProofs
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvProofs
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs
  FlambdaJoinEnv FlambdaJoinSpec FlambdaJoinEnvSpec.
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

(* ======================================================================== *)
(* Where the rounds record a relation                                       *)
(* ======================================================================== *)

Lemma recorded_add (relations : Join_env.inverse_relations)
    (var result : variable) (relation relation' : Relation.t)
    (scrutinee scrutinee' : name) :
  relation_recorded
    (Join_env.add_to_inverse_relations relations var relation' scrutinee')
    result relation scrutinee ->
  relation_recorded relations result relation scrutinee
  ∨ scrutinee = scrutinee'.
Proof.
  intros [recorded [Hlookup Hin]].
  unfold Join_env.add_to_inverse_relations in Hlookup.
  cbn [lookup] in Hlookup.
  destruct (Pos.eqb result var) eqn:Heq.
  - apply Pos.eqb_eq in Heq. subst var. injection Hlookup as <-.
    destruct Hin as [Hhead | Hin].
    + injection Hhead as _ <-. right. reflexivity.
    + destruct (lookup result relations) as [existing | ] eqn:Hexisting.
      * left. exists existing. split; [ exact Hexisting | exact Hin ].
      * destruct Hin.
  - left. exists recorded. split; assumption.
Qed.

Theorem recovered_relations_on_name : recovered_relations_on_name_statement.
Proof.
  intros relations relations' n ty ty' result relation scrutinee Hrecover
    Hrecorded.
  unfold Join_env.recover_inverse_relations in Hrecover.
  repeat
    (match type of Hrecover with
     | context [match ?e with _ => _ end] => destruct e eqn:?
     end; try discriminate);
    injection Hrecover as _ <-;
    first
      [ left; exact Hrecorded
      | exact (recorded_add _ _ _ _ _ _ _ Hrecorded) ].
Qed.

Lemma keeps_definitions_refl (s : Join_env.t) : keeps_definitions s s.
Proof.
  split; [ intros index; reflexivity | intros x definition H; exact H ].
Qed.

Lemma keeps_definitions_trans (s1 s2 s3 : Join_env.t) :
  keeps_definitions s1 s2 -> keeps_definitions s2 s3 ->
  keeps_definitions s1 s3.
Proof.
  intros [Henvs Hdefs] [Henvs' Hdefs']. split.
  - intros index. rewrite Henvs'. apply Henvs.
  - intros x definition H. apply Hdefs'. apply Hdefs. exact H.
Qed.

Lemma add_equation_keeps (s s' : Join_env.t) (x : variable)
    (ty : flambda_type) :
  Join_env.add_equation_in_target_env s x ty = Some s' ->
  keeps_definitions s s'.
Proof.
  unfold Join_env.add_equation_in_target_env.
  destruct (is_bound x (Join_env.types_in_target_env s)); [ discriminate | ].
  intros H. injection H as <-. split; [ intros index; reflexivity | ].
  intros y definition Hy. exact Hy.
Qed.

Lemma recorded_where_chosen_same (choices : Join_env.choices)
    (s s' : Join_env.t) (relations : Join_env.inverse_relations) :
  recorded_where_chosen choices s s' relations relations.
Proof. intros result relation scrutinee H. left. exact H. Qed.

Lemma recorded_where_chosen_trans (choices : Join_env.choices)
    (s1 s2 s3 : Join_env.t)
    (relations1 relations2 relations3 : Join_env.inverse_relations) :
  keeps_definitions s1 s2 ->
  keeps_definitions s2 s3 ->
  recorded_where_chosen choices s1 s2 relations1 relations2 ->
  recorded_where_chosen choices s2 s3 relations2 relations3 ->
  recorded_where_chosen choices s1 s3 relations1 relations3.
Proof.
  intros H12 H23 Hfirst Hsecond result relation scrutinee Hrecorded.
  destruct (Hsecond _ _ _ Hrecorded)
    as [Hrecorded2 | [x [types [s0 [Heq [Hbefore [Hafter Htest]]]]]]].
  - destruct (Hfirst _ _ _ Hrecorded2)
      as [Hrecorded1 | [x [types [s0 [Heq [Hbefore [Hafter Htest]]]]]]].
    + left. exact Hrecorded1.
    + right. exists x, types, s0. split; [ exact Heq | ].
      split; [ exact Hbefore | ]. split; [ | exact Htest ].
      exact (keeps_definitions_trans _ _ _ Hafter H23).
  - right. exists x, types, s0. split; [ exact Heq | ].
    split; [ | split; [ exact Hafter | exact Htest ] ].
    exact (keeps_definitions_trans _ _ _ H12 Hbefore).
Qed.

Theorem round_records_where_chosen : round_records_where_chosen_statement.
Proof.
  intros choices jt s s' equations relations relations' Hjt Hround.
  unfold Join_env.n_way_join_round in Hround.
  match type of Hround with
  | List.fold_left ?f _ _ = _ => set (step := f) in Hround
  end.
  assert (Hnone : ∀ bindings, List.fold_left step bindings None = None).
  { induction bindings as [ | binding bindings IH];
      [ reflexivity | exact IH ]. }
  revert relations s Hround. generalize (compact equations) as bindings.
  induction bindings as [ | [var types] bindings IH];
    intros relations s Hround.
  - cbn in Hround. injection Hround as <- <-.
    split; [ apply keeps_definitions_refl | apply recorded_where_chosen_same ].
  - cbn [List.fold_left] in Hround.
    destruct (step (Some (relations, s)) (var, types))
      as [[relations1 s1] | ] eqn:Hstep;
      [ | rewrite Hnone in Hround; discriminate ].
    destruct (IH _ _ Hround) as [Hkeeps Hchosen].
    assert (Hfirst :
              keeps_definitions s s1
              ∧ recorded_where_chosen choices s s1 relations relations1).
    { unfold step in Hstep. cbn [fst snd] in Hstep.
      destruct (jt s (Index.bindings types)) as [[joined s0] | ] eqn:Hjoin;
        [ | discriminate ].
      pose proof (Hjt _ _ _ _ Hjoin) as Hkeeps0.
      destruct joined as [ty | ].
      - destruct (Join_env.recover_relations_on choices s0 var types)
          eqn:Htest.
        + destruct (Join_env.recover_inverse_relations relations
                      (Name_var var) ty)
            as [[ty' relations0] | ] eqn:Hrecover; [ | discriminate ].
          destruct (Join_env.add_equation_in_target_env s0 var ty')
            as [s2 | ] eqn:Hadd; [ | discriminate ].
          injection Hstep as <- <-.
          pose proof (add_equation_keeps _ _ _ _ Hadd) as Hkeeps2.
          split; [ exact (keeps_definitions_trans _ _ _ Hkeeps0 Hkeeps2) | ].
          intros result relation scrutinee Hrecorded.
          destruct (recovered_relations_on_name _ _ _ _ _ _ _ _ Hrecover
                      Hrecorded) as [Hbefore | ->].
          * left. exact Hbefore.
          * right. exists var, types, s0. split; [ reflexivity | ].
            split; [ exact Hkeeps0 | ]. split; [ exact Hkeeps2 | exact Htest ].
        + destruct (Join_env.add_equation_in_target_env s0 var ty)
            as [s2 | ] eqn:Hadd; [ | discriminate ].
          injection Hstep as <- <-.
          pose proof (add_equation_keeps _ _ _ _ Hadd) as Hkeeps2.
          split; [ exact (keeps_definitions_trans _ _ _ Hkeeps0 Hkeeps2) | ].
          apply recorded_where_chosen_same.
      - injection Hstep as <- <-. split; [ exact Hkeeps0 | ].
        apply recorded_where_chosen_same. }
    destruct Hfirst as [Hkeeps1 Hchosen1].
    split; [ exact (keeps_definitions_trans _ _ _ Hkeeps1 Hkeeps) | ].
    exact (recorded_where_chosen_trans _ _ _ _ _ _ _ Hkeeps1 Hkeeps Hchosen1
             Hchosen).
Qed.

Theorem delayed_equations_record_where_chosen
  : delayed_equations_record_where_chosen_statement.
Proof.
  intros fuel choices jt s s' equations relations relations' Hjt.
  revert s equations relations.
  induction fuel as [ | fuel IH]; intros s equations relations Hloop;
    [ discriminate | ].
  cbn [Join_env.n_way_join_delayed_equations] in Hloop.
  destruct (Keyed.is_empty equations).
  - injection Hloop as <- <-.
    split; [ apply keeps_definitions_refl | apply recorded_where_chosen_same ].
  - destruct (Join_env.n_way_join_round choices jt s equations relations)
      as [[relations1 s1] | ] eqn:Hround; [ | discriminate ].
    destruct (round_records_where_chosen _ _ _ _ _ _ _ Hjt Hround)
      as [Hkeeps1 Hchosen1].
    destruct (IH _ _ _ Hloop) as [Hkeeps Hchosen].
    split; [ exact (keeps_definitions_trans _ _ _ Hkeeps1 Hkeeps) | ].
    exact (recorded_where_chosen_trans _ _ _ _ _ _ _ Hkeeps1 Hkeeps Hchosen1
             Hchosen).
Qed.

Theorem loop_records_where_chosen : loop_records_where_chosen_statement.
Proof.
  intros depth p fuel choices jt s s' existentials relations relations' Hjt.
  revert s existentials relations.
  induction depth as [ | depth IH]; intros s existentials relations Hloop.
  - injection Hloop as <- <-.
    split; [ apply keeps_definitions_refl | apply recorded_where_chosen_same ].
  - cbn [Join_env.n_way_join_loop] in Hloop.
    destruct (Keyed.is_empty existentials).
    + injection Hloop as <- <-.
      split;
        [ apply keeps_definitions_refl | apply recorded_where_chosen_same ].
    + destruct (Join_env.equations_of_existentials p s (compact existentials))
        as [equations | ]; [ | discriminate ].
      destruct
        (Join_env.n_way_join_delayed_equations fuel choices jt s relations
           equations)
        as [[relations1 s1] | ] eqn:Hrounds; [ | discriminate ].
      destruct
        (delayed_equations_record_where_chosen _ _ _ _ _ _ _ _ Hjt Hrounds)
        as [Hkeeps1 Hchosen1].
      destruct (IH _ _ _ Hloop) as [Hkeeps Hchosen].
      split; [ exact (keeps_definitions_trans _ _ _ Hkeeps1 Hkeeps) | ].
      exact (recorded_where_chosen_trans _ _ _ _ _ _ _ Hkeeps1 Hkeeps Hchosen1
               Hchosen).
Qed.

(* ======================================================================== *)
(* The repaired test                                                        *)
(* ======================================================================== *)

Lemma index_equal_decides : decides_equality Index.equal.
Proof. intros index index'. apply Nat.eqb_eq. Qed.

(* An index that has a joined environment is among the keys. *)
Lemma joined_env_key (envs : Joined_envs.t) (index : Index.t)
    (tenv : Typing_env.t) :
  Joined_envs.get_nth_joined_env envs index = Some tenv ->
  index ∈ Joined_envs.keys envs.
Proof.
  unfold Joined_envs.get_nth_joined_env, Joined_envs.keys. intros Hnth.
  apply (keyed_among_in _ Index.equal index_equal_decides).
  rewrite (keyed_among_domain _ Index.equal index_equal_decides).
  apply keyed_is_bound_lookup.
  destruct (Keyed.lookup Index.equal index envs) as [binding | ];
    [ | discriminate ].
  exists binding. reflexivity.
Qed.

Theorem repaired_test_gives_values : repaired_test_gives_values_statement.
Proof.
  intros s x types index tenv exempt statics valuation Htest Hindex
    Hsatisfied Hbound.
  cbn in Htest. apply andb_true_iff in Htest. destruct Htest as [_ Htest].
  unfold Join_env.in_terms_in_all_joined_envs in Htest.
  rewrite forallb_forall in Htest.
  unfold Join_env.joined_env in Hindex.
  specialize (Htest index (joined_env_key _ _ _ Hindex)).
  rewrite Hindex in Htest.
  destruct (Join_env.stands_for s index x) as [simple | ] eqn:Hstands;
    [ | discriminate ].
  unfold Join_env.has_alias_in_terms in Htest.
  destruct (Typing_env.get_canonical_simple_exn tenv (Some Name_mode.normal)
              None simple) as [[canonical | ] | ] eqn:Hcanonical;
    try discriminate.
  assert (Hvalue : ∃ v : value, eval_simple valuation simple = Some v).
  { rewrite <- (get_canonical_simple_satisfied _ _ _ _ _ _ _ _ Hsatisfied
                  Hcanonical).
    destruct canonical as [y | sym | c].
    - exact (Hbound y Htest).
    - eexists. reflexivity.
    - eexists. reflexivity. }
  destruct Hvalue as [v Hv].
  unfold Join_env.stands_for in Hstands.
  destruct (lookup x (Join_env.definitions_of_existentials s))
    as [[simples kind] | ] eqn:Hdefinition.
  - right. exists simples, kind, simple, v.
    split; [ exact Hdefinition | split; [ exact Hstands | exact Hv ] ].
  - injection Hstands as <-. left. exists v. exact Hv.
Qed.

(* A variable that has a value by the definitions of a state has one by
   those of a later state. *)
Lemma has_value_at_use_keeps (s s' : Join_env.t) (index : Index.t)
    (valuation : env) (x : variable) :
  keeps_definitions s s' ->
  has_value_at_use (Join_env.definitions_of_existentials s) index valuation x
  ->
  has_value_at_use (Join_env.definitions_of_existentials s') index valuation
    x.
Proof.
  intros [_ Hdefinitions]
    [Hvalue | [simples [kind [simple [v [Hdefinition [Hfind Hv]]]]]]].
  - left. exact Hvalue.
  - right. exists simples, kind, simple, v.
    split; [ exact (Hdefinitions _ _ Hdefinition) | ].
    split; [ exact Hfind | exact Hv ].
Qed.

Theorem repaired_rounds_scrutinees_have_values
  : repaired_rounds_scrutinees_have_values_statement.
Proof.
  intros depth p fuel jt s s1 s2 equations existentials relations1 relations2
    result relation scrutinee index tenv exempt statics valuation Hjt
    Hrounds Hloop Hrecorded Hindex Hsatisfied Hbound.
  destruct (delayed_equations_record_where_chosen _ _ _ _ _ _ _ _ Hjt Hrounds)
    as [Hkeeps1 Hchosen1].
  destruct (loop_records_where_chosen _ _ _ _ _ _ _ _ _ _ Hjt Hloop)
    as [Hkeeps2 Hchosen2].
  pose proof (recorded_where_chosen_trans _ _ _ _ _ _ _ Hkeeps1 Hkeeps2
                Hchosen1 Hchosen2) as Hchosen.
  destruct (Hchosen _ _ _ Hrecorded)
    as [[recorded [Hlookup _]]
       | [x [types [s0 [Heq [Hbefore [Hafter Htest]]]]]]];
    [ discriminate | ].
  exists x. split; [ exact Heq | ].
  apply (has_value_at_use_keeps s0 s2 _ _ _ Hafter).
  apply (repaired_test_gives_values s0 x types index tenv exempt statics
           valuation Htest); try assumption.
  destruct Hbefore as [Henvs _]. rewrite Henvs. exact Hindex.
Qed.

(* ======================================================================== *)
(* The repaired join on the instance                                        *)
(* ======================================================================== *)

Definition repaired_target : Typing_env.t :=
  Eval vm_compute in
    match Witness.repaired_join [Witness.r; Witness.x] Witness.inputs with
    | Some (target, _) => target
    | None => Typing_env.create
    end.

Definition repaired_analysis : Analysis.t unit :=
  Eval vm_compute in
    match Witness.repaired_join [Witness.r; Witness.x] Witness.inputs with
    | Some (_, analysis) => analysis
    | None => Analysis.empty
    end.

Lemma repaired_join_result :
  Witness.repaired_join [Witness.r; Witness.x] Witness.inputs
  = Some (repaired_target, repaired_analysis).
Proof. vm_compute. reflexivity. Qed.

Definition repaired_entries : Keyed.finite_map name _ :=
  Eval vm_compute in Typing_env.names_to_types repaired_target.

Lemma repaired_names_to_types :
  Typing_env.names_to_types repaired_target = repaired_entries.
Proof. vm_compute. reflexivity. Qed.

Theorem witness_repaired_join_admits : witness_repaired_join_admits_statement.
Proof.
  exists repaired_target, repaired_analysis.
  split; [ exact repaired_join_result | ].
  intros index use Huse statics valuation [_ [Htypes _]] _.
  exists valuation.
  split;
    [ | split;
        [ intros y _; reflexivity
        | split;
          [ intros y _; reflexivity
          | split; intros y simples kind simple v Hlookup; discriminate ] ] ].
  split; [ reflexivity | ]. split; [ | apply empty_respected ].
  intros n ty binding_time_and_mode v Hlookup Hvalue.
  rewrite repaired_names_to_types in Hlookup.
  unfold repaired_entries in Hlookup.
  entries_cases Hlookup n; try discriminate; injection Hlookup as <- _;
    right.
  - destruct (witness_use_at _ _ Huse); subst use;
      destruct (Htypes (Name_var 2%positive) _ _ v eq_refl Hvalue)
        as [[[] _] | Hsatisfied].
    + exact Hsatisfied.
    + rewrite type_satisfied_value in *. cbn in *.
      rewrite head_of_kind_value_satisfied_eq in *.
      destruct Hsatisfied as [Hnull | [_ [[] _]]]. left. exact Hnull.
  - destruct (witness_use_at _ _ Huse); subst use;
      destruct (Htypes (Name_var 1%positive) _ _ v eq_refl Hvalue)
        as [[[] _] | Hsatisfied];
      exact Hsatisfied.
Qed.
