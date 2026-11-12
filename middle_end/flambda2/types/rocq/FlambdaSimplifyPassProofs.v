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


(* Proofs of the statements of FlambdaSimplifyPassSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaMapProofs FlambdaValueSpec FlambdaPrimitiveModel
  FlambdaPrimitiveSpec FlambdaPrimitiveProofs FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaWellFormedSpec FlambdaWellFormedProofs.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaTypeWellFormedSpec FlambdaTypeWellFormedProofs FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesProofs
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvProofs
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs
  FlambdaTypingEnvOperationsSpec FlambdaTypingEnvOperationsProofs
  FlambdaTypingEnvKindedSpec FlambdaTypingEnvKindedProofs
  FlambdaTypingEnvRefinementSpec FlambdaTypingEnvRefinementProofs
  FlambdaProvers FlambdaProversSpec FlambdaProversProofs
  FlambdaSimplifyPrimitivesSpec FlambdaSimplifyPrimitivesProofs
  FlambdaSimplifyProjectionsSpec FlambdaSimplifyProjectionsProofs
  FlambdaSimplifyBoxingSpec FlambdaSimplifyBoxingProofs
  FlambdaSimplifyArithSpec FlambdaSimplifyArithProofs FlambdaSimplifyPassSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* A [Simple] of the term                                                   *)
(* ======================================================================== *)

Lemma simplify_simple_answer (tenv : Typing_env.t) (s canonical : simple)
    (ty : flambda_type) :
  simplify_simple tenv s = Some (ty, canonical) ->
  argument_type tenv s ty ∧ canonical_in_terms tenv s canonical.
Proof.
  unfold simplify_simple.
  destruct (Typing_env.mem_simple (Some Name_mode.normal) tenv s) eqn:Hmem;
    [ | discriminate ].
  destruct (Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) s)
    as [[[ty' canonical'] | ] | ] eqn:Htype; try discriminate.
  intros [= <- <-].
  split; (split; [ exact Hmem | eexists; exact Htype ]).
Qed.

Lemma simplify_simples_answers (tenv : Typing_env.t) (args : list simple) :
  ∀ answers : list (flambda_type * simple),
    simplify_simples tenv args = Some answers ->
    Forall2 (argument_type tenv) args (map fst answers)
    ∧ Forall2 (canonical_in_terms tenv) args (map snd answers).
Proof.
  induction args as [ | arg args IH]; intros answers; simpl.
  - intros [= <-]. split; apply Forall2_nil.
  - destruct (simplify_simple tenv arg) as [[ty canonical] | ] eqn:Harg;
      [ | discriminate ].
    destruct (simplify_simples tenv args) as [answers' | ];
      [ | discriminate ].
    intros [= <-].
    destruct (simplify_simple_answer tenv arg canonical ty Harg)
      as [Hty Hcanonical].
    destruct (IH answers' eq_refl) as [Htys Hcanonicals].
    split; apply Forall2_cons; assumption.
Qed.

(* ======================================================================== *)
(* What an outcome says                                                     *)
(* ======================================================================== *)

Definition outcome_sound (tenv : Typing_env.t) (d : named) (o : outcome)
    : Prop :=
  match o with
  | Becomes_invalid =>
    ∀ (x : variable) (declared : flambda_kind) (body : expr),
      expr_equivalent_under tenv (Let x declared d body) Invalid
  | Becomes_simple s =>
    ∀ (x : variable) (declared : flambda_kind) (body : expr),
      expr_refines_under tenv (Let x declared d body)
        (Let x declared (Simple s) body)
  | Stays_with_type ty =>
    ∀ (statics : static_env) (vars : env) (v : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars d = Some v ->
      type_satisfied statics vars v ty
  | Stays_with_kind kind =>
    ∀ (statics : static_env) (vars : env) (v : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars d = Some v ->
      kind_of_value v = kind
  | Not_known => True
  end.

Lemma of_bool_shortcut_sound (tenv : Typing_env.t) (d : named)
    (answer : option (Meet_shortcut.t bool)) (otherwise : outcome) :
  (∀ (x : variable) (declared : flambda_kind) (body : expr),
    match answer with
    | Some (Meet_shortcut.Known_result b) =>
      expr_refines_under tenv (Let x declared d body)
        (Let x declared
           (Simple (Const (Naked_immediate (if b then 1 else 0)))) body)
    | Some Meet_shortcut.Invalid =>
      expr_equivalent_under tenv (Let x declared d body) Invalid
    | Some Meet_shortcut.Need_meet | None => True
    end) ->
  outcome_sound tenv d otherwise ->
  outcome_sound tenv d (of_bool_shortcut answer otherwise).
Proof.
  intros Hanswer Hotherwise.
  destruct answer as [[b | | ] | ]; simpl; try exact Hotherwise;
    exact Hanswer.
Qed.

Lemma of_simple_shortcut_sound (tenv : Typing_env.t) (d : named)
    (answer : option (Meet_shortcut.t simple)) (otherwise : outcome) :
  (∀ (x : variable) (declared : flambda_kind) (body : expr),
    match answer with
    | Some (Meet_shortcut.Known_result s) =>
      expr_refines_under tenv (Let x declared d body)
        (Let x declared (Simple s) body)
    | Some Meet_shortcut.Invalid =>
      expr_equivalent_under tenv (Let x declared d body) Invalid
    | Some Meet_shortcut.Need_meet | None => True
    end) ->
  outcome_sound tenv d otherwise ->
  outcome_sound tenv d (of_simple_shortcut answer otherwise).
Proof.
  intros Hanswer Hotherwise.
  destruct answer as [[s | | ] | ]; simpl; try exact Hotherwise;
    exact Hanswer.
Qed.

(* The value of a primitive is of its result kind. *)
Lemma prim_kind_sound (tenv : Typing_env.t) (p : prim) (args : list simple) :
  outcome_sound tenv (Prim p args) (Stays_with_kind (prim_result_kind p)).
Proof.
  intros statics vars v _ Hnamed. cbn [eval_named] in Hnamed.
  destruct (eval_simples vars args) as [vs | ]; [ | discriminate ].
  exact (proj2 (eval_prim_kinds statics p vs v Hnamed)).
Qed.

(* ======================================================================== *)
(* Unary primitives                                                         *)
(* ======================================================================== *)

Lemma simplify_unary_sound (tenv : Typing_env.t) (p : unary_primitive)
    (arg : simple) (ty : flambda_type) :
  argument_type tenv arg ty ->
  outcome_sound tenv (Prim (Unary p) [arg]) (simplify_unary tenv p arg ty).
Proof.
  intros Hty.
  assert (Hterms : simple_in_terms tenv arg).
  { intros x ->. exact (proj1 Hty). }
  pose proof (prim_kind_sound tenv (Unary p) [arg]) as Hunknown.
  (* By cases on the primitive, with no names given to what it holds:
     a primitive that has no line of its own in [simplify_unary]
     closes by [Hunknown]. *)
  destruct p; cbn [simplify_unary]; try exact Hunknown.
  - (* [Block_load] *)
    match goal with
    | |- context [Block_load ?kind ?mut ?field] =>
      destruct mut; try exact Hunknown;
        (apply of_simple_shortcut_sound; [ | exact Hunknown ]);
        intros x declared body;
        refine (let_block_load tenv x declared kind _ field arg ty
                  body _ Hty);
        discriminate
    end.
  - (* [Is_int] *)
    match goal with
    | |- context [Is_int ?variant_only] => destruct variant_only
    end.
    + apply of_bool_shortcut_sound; [ | exact Hunknown ].
      intros x declared body.
      exact (let_is_int_variant_only tenv x declared arg ty body Hty).
    + destruct (Provers.prove_is_int tenv ty) as [[b | ] | ] eqn:Hprove;
        try exact Hunknown.
      intros x declared body.
      exact (let_is_int_proved tenv x declared arg ty b body Hty
               Hprove).
  - (* [Is_null] *)
    apply of_bool_shortcut_sound; [ | exact Hunknown ].
    intros x declared body.
    exact (let_is_null tenv x declared arg ty body Hty).
  - (* [Get_tag] *)
    destruct (Provers.prove_is_int tenv ty) as [[[ | ] | ] | ] eqn:Hint.
    + intros x declared body.
      exact (let_get_tag_of_immediate tenv x declared arg ty body Hty
               Hint).
    + destruct (Provers.prove_get_tag tenv ty)
        as [[[ | tag [ | tag' tags]] | ] | ] eqn:Htag;
        try exact Hunknown.
      intros x declared body.
      refine (let_get_tag_proved tenv x declared arg ty [tag] tag
                body Hty Htag _).
      intros tag' [<- | []]. reflexivity.
    + destruct (Provers.prove_get_tag tenv ty)
        as [[[ | tag [ | tag' tags]] | ] | ] eqn:Htag;
        try exact Hunknown.
      intros x declared body.
      refine (let_get_tag_proved tenv x declared arg ty [tag] tag
                body Hty Htag _).
      intros tag' [<- | []]. reflexivity.
    + destruct (Provers.prove_get_tag tenv ty)
        as [[[ | tag [ | tag' tags]] | ] | ] eqn:Htag;
        try exact Hunknown.
      intros x declared body.
      refine (let_get_tag_proved tenv x declared arg ty [tag] tag
                body Hty Htag _).
      intros tag' [<- | []]. reflexivity.
  - (* [Unbox_number] *)
    apply of_simple_shortcut_sound; [ | exact Hunknown ].
    intros x declared body.
    exact (let_unbox_number tenv x declared _ arg body Hterms).
  - (* [Box_number] *)
    intros statics vars v Hsat Hnamed.
    exact (box_number_typed tenv statics vars _ arg ty v
             (env_satisfies_strictly_env_satisfies tenv statics vars Hsat)
             Hty Hnamed).
  - (* [Untag_immediate] *)
    destruct (types_well_formed_b tenv) eqn:Hwf; [ | exact Hunknown ].
    apply of_simple_shortcut_sound; [ | exact Hunknown ].
    intros x declared body.
    exact (let_untag_immediate tenv x declared arg body Hterms
             (proj1 (types_well_formed_b_iff tenv) Hwf)).
  - (* [Tag_immediate] *)
    intros statics vars v Hsat Hnamed.
    exact (tag_immediate_typed tenv statics vars arg ty v
             (env_satisfies_strictly_env_satisfies tenv statics vars Hsat)
             Hty Hnamed).
Qed.

(* ======================================================================== *)
(* The arithmetic of tagged immediates                                      *)
(* ======================================================================== *)

(* The tables for one side known: what they answer is right of the
   operation on a number in range. *)
Lemma op_rhs_unknown_sound (op : binary_int_arith_op) (lhs j r : Z) :
  in_range tagged_width j = true ->
  eval_int_arith tagged_width op lhs j = Some r ->
  match op_rhs_unknown op lhs with
  | Exactly result => r = result
  | The_other_side => r = j
  | No_result => False
  | Cannot_simplify => True
  end.
Proof.
  intros Hrange.
  destruct (int_arith_identities Standard_tagged_immediate j Hrange)
    as (Hadd0l & Hadd0r & Hsub0 & Hmul0l & Hmul0r & Hmul1l & Hmul1r & Handm1l
        & Handm1r & Hand0l & Hand0r & Horm1l & Horm1r & Hor0l & Hor0r
        & Hxor0l & Hxor0r & Hdivmod & Hmodm1).
  unfold op_rhs_unknown, symmetric_op_one_side_unknown, tagged_width.
  destruct op; try (intros _; exact I);
    repeat match goal with
           | |- context [?a =? ?b] => destruct (Z.eqb_spec a b) as [-> | _]
           end;
    try (intros _; exact I); congruence.
Qed.

Lemma op_lhs_unknown_sound (op : binary_int_arith_op) (rhs j r : Z) :
  in_range tagged_width j = true ->
  eval_int_arith tagged_width op j rhs = Some r ->
  match op_lhs_unknown op rhs with
  | Exactly result => r = result
  | The_other_side => r = j
  | No_result => False
  | Cannot_simplify => True
  end.
Proof.
  intros Hrange.
  destruct (int_arith_identities Standard_tagged_immediate j Hrange)
    as (Hadd0l & Hadd0r & Hsub0 & Hmul0l & Hmul0r & Hmul1l & Hmul1r & Handm1l
        & Handm1r & Hand0l & Hand0r & Horm1l & Horm1r & Hor0l & Hor0r
        & Hxor0l & Hxor0r & Hdivmod & Hmodm1).
  unfold op_lhs_unknown, symmetric_op_one_side_unknown, tagged_width.
  destruct op as [ | | | s | s | | | ];
    try (destruct (Hdivmod s) as (Hdiv0 & Hmod0 & Hdiv1 & Hmod1));
    try destruct s;
    repeat match goal with
           | |- context [?a =? ?b] => destruct (Z.eqb_spec a b) as [-> | _]
           end;
    try (intros _; exact I); congruence.
Qed.

Lemma one_side_results_in (table : Z -> one_side_outcome) (nums : list Z) :
  ∀ results : list possible_result,
    one_side_results table nums = Some results ->
    ∀ i : Z,
      i ∈ nums ->
      match table i with
      | Exactly result => Result_exactly result ∈ results
      | The_other_side => Result_other_side ∈ results
      | No_result => True
      | Cannot_simplify => False
      end.
Proof.
  induction nums as [ | n nums IH]; intros results; simpl.
  - intros _ i [].
  - destruct (one_side_results table nums) as [results' | ];
      [ | discriminate ].
    intros Hresults i [<- | Hin].
    + destruct (table n); try discriminate; try exact I;
        injection Hresults as <-; left; reflexivity.
    + specialize (IH results' eq_refl i Hin).
      destruct (table n); try discriminate; injection Hresults as <-;
        destruct (table i); try exact I; try contradiction;
        first [ exact IH | right; exact IH ].
Qed.

Lemma exact_results_in (results : list possible_result) (r : Z) :
  Result_exactly r ∈ results -> r ∈ exact_results results.
Proof.
  induction results as [ | [i | ] results IH]; simpl.
  - intros [].
  - intros [[= <-] | Hin]; [ left; reflexivity | right; exact (IH Hin) ].
  - intros [[=] | Hin]. exact (IH Hin).
Qed.

Lemma well_formed_input_b_sound (tenv : Typing_env.t) (ty : flambda_type) :
  well_formed_input_b tenv ty = true -> well_formed_input tenv ty.
Proof.
  unfold well_formed_input_b. intros Hwf. apply andb_true_iff in Hwf.
  destruct Hwf as [Htenv Hty].
  split; [ exact (proj1 (types_well_formed_b_iff tenv) Htenv) | exact Hty ].
Qed.

Section Int_arith.

Variable tenv : Typing_env.t.
Variable op : binary_int_arith_op.
Variables arg1 arg2 : simple.
Variables ty1 ty2 : flambda_type.
Hypothesis Hty1 : argument_type tenv arg1 ty1.
Hypothesis Hty2 : argument_type tenv arg2 ty2.

Let arith : named :=
  Prim (Binary (Int_arith Standard_tagged_immediate op)) [arg1; arg2].

Lemma int_arith_tagged_any :
  outcome_sound tenv arith (Stays_with_type any_tagged_immediate).
Proof.
  intros statics vars v Hsat Hnamed. unfold arith in Hnamed.
  simpl in Hnamed.
  destruct (eval_simple vars arg1) as [v1 | ]; [ | discriminate ].
  destruct (eval_simple vars arg2) as [v2 | ]; [ | discriminate ].
  change (eval_prim statics
            (Binary (Int_arith Standard_tagged_immediate op)) [v1; v2]
          = Some v) in Hnamed.
  destruct (int_arith_tagged_defined statics op v1 v2 v Hnamed)
    as [i1 [i2 [result [_ [_ [_ [_ [_ ->]]]]]]]].
  apply any_tagged_immediate_satisfied. exists result. reflexivity.
Qed.

Hypothesis Hwf1 : well_formed_input tenv ty1.
Hypothesis Hwf2 : well_formed_input tenv ty2.

Lemma check_possible_results_sound (first : bool)
    (results : list possible_result) :
  (∀ i1 i2 r : Z,
    possible_tagged_immediate tenv ty1 i1 ->
    possible_tagged_immediate tenv ty2 i2 ->
    eval_int_arith tagged_width op i1 i2 = Some r ->
    Result_exactly r ∈ results
    ∨ (Result_other_side ∈ results ∧ r = if first then i1 else i2)) ->
  outcome_sound tenv arith
    (check_possible_results results (if first then arg1 else arg2)).
Proof.
  intros Hresults.
  assert (Hvalue :
    ∀ (statics : static_env) (vars : env) (v : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars arith = Some v ->
      ∃ i1 i2 r : Z,
        possible_tagged_immediate tenv ty1 i1
        ∧ possible_tagged_immediate tenv ty2 i2
        ∧ eval_simple vars arg1 = Some (Value_const (Tagged_immediate i1))
        ∧ eval_simple vars arg2 = Some (Value_const (Tagged_immediate i2))
        ∧ eval_int_arith tagged_width op i1 i2 = Some r
        ∧ v = Value_const (Tagged_immediate r)).
  { intros statics vars v Hsat Hnamed.
    exact (int_arith_tagged_possible tenv statics vars op arg1 arg2 ty1 ty2
             v Hsat Hty1 Hty2 Hwf1 Hwf2 Hnamed). }
  unfold check_possible_results.
  destruct results as [ | result rest].
  - intros x declared body. apply let_no_value.
    intros statics vars v Hsat Hnamed.
    destruct (Hvalue statics vars v Hsat Hnamed)
      as (i1 & i2 & r & Hi1 & Hi2 & _ & _ & Heval & _).
    destruct (Hresults i1 i2 r Hi1 Hi2 Heval) as [[] | [[] _]].
  - destruct (forallb (possible_result_eqb result) rest) eqn:Hsame.
    + assert (Hall :
        ∀ r' : possible_result, r' ∈ result :: rest -> r' = result).
      { intros r' [<- | Hin]; [ reflexivity | ].
        rewrite forallb_forall in Hsame. specialize (Hsame r' Hin).
        destruct result, r'; simpl in Hsame; try discriminate;
          [ apply Z.eqb_eq in Hsame; subst; reflexivity | reflexivity ]. }
      destruct result as [i | ].
      * intros x declared body. apply let_constant.
        intros statics vars v Hsat Hnamed.
        destruct (Hvalue statics vars v Hsat Hnamed)
          as (i1 & i2 & r & Hi1 & Hi2 & _ & _ & Heval & ->).
        destruct (Hresults i1 i2 r Hi1 Hi2 Heval) as [Hin | [Hin _]].
        -- injection (Hall _ Hin) as ->. reflexivity.
        -- discriminate (Hall _ Hin).
      * intros x declared body. apply let_simple.
        intros statics vars v Hsat Hnamed.
        destruct (Hvalue statics vars v Hsat Hnamed)
          as (i1 & i2 & r & Hi1 & Hi2 & Hv1 & Hv2 & Heval & ->).
        destruct (Hresults i1 i2 r Hi1 Hi2 Heval) as [Hin | [_ ->]].
        -- discriminate (Hall _ Hin).
        -- destruct first; assumption.
    + destruct (forallb
                  (fun r =>
                     match r with
                     | Result_exactly _ => true
                     | Result_other_side => false
                     end)
                  (result :: rest)) eqn:Hexact.
      * intros statics vars v Hsat Hnamed.
        destruct (Hvalue statics vars v Hsat Hnamed)
          as (i1 & i2 & r & Hi1 & Hi2 & _ & _ & Heval & ->).
        apply these_tagged_immediates_satisfied. exists r.
        split; [ reflexivity | ].
        destruct (Hresults i1 i2 r Hi1 Hi2 Heval) as [Hin | [Hin _]].
        -- exact (exact_results_in _ _ Hin).
        -- rewrite forallb_forall in Hexact. discriminate (Hexact _ Hin).
      * exact int_arith_tagged_any.
Qed.

End Int_arith.

Lemma simplify_int_arith_tagged_sound (tenv : Typing_env.t)
    (op : binary_int_arith_op) (arg1 arg2 : simple) (ty1 ty2 : flambda_type) :
  argument_type tenv arg1 ty1 ->
  argument_type tenv arg2 ty2 ->
  outcome_sound tenv
    (Prim (Binary (Int_arith Standard_tagged_immediate op)) [arg1; arg2])
    (simplify_int_arith_tagged tenv op arg1 ty1 arg2 ty2).
Proof.
  intros Hty1 Hty2. unfold simplify_int_arith_tagged.
  pose proof (int_arith_tagged_any tenv op arg1 arg2) as Hunknown.
  destruct (well_formed_input_b tenv ty1 && well_formed_input_b tenv ty2)
    eqn:Hwf; [ | exact Hunknown ].
  apply andb_true_iff in Hwf. destruct Hwf as [Hwf1 Hwf2].
  apply well_formed_input_b_sound in Hwf1, Hwf2.
  pose proof (check_possible_results_sound tenv op arg1 arg2 ty1 ty2
                Hty1 Hty2 Hwf1 Hwf2) as Hcheck.
  (* Where a prover answers [Invalid] there is no number. *)
  assert (Hinvalid :
    (∀ i1 i2 : Z,
      possible_tagged_immediate tenv ty1 i1 ->
      possible_tagged_immediate tenv ty2 i2 ->
      False) ->
    outcome_sound tenv
      (Prim (Binary (Int_arith Standard_tagged_immediate op)) [arg1; arg2])
      Becomes_invalid).
  { intros Hnone x declared body. apply let_no_value.
    intros statics vars v Hsat Hnamed.
    destruct (int_arith_tagged_possible tenv statics vars op arg1 arg2 ty1
                ty2 v Hsat Hty1 Hty2 Hwf1 Hwf2 Hnamed)
      as (i1 & i2 & r & Hi1 & Hi2 & _).
    exact (Hnone i1 i2 Hi1 Hi2). }
  unfold possible_tagged_immediate in Hcheck, Hinvalid.
  destruct (Provers.meet_equals_tagged_immediates tenv ty1)
    as [[nums1 | | ] | ],
    (Provers.meet_equals_tagged_immediates tenv ty2) as [[nums2 | | ] | ];
    try exact Hunknown;
    try (apply Hinvalid; intros i1 i2 [_ H1] [_ H2];
         first [ exact H1 | exact H2 ]).
  - (* Both are known. *)
    destruct ((max_num_possible_results <? length nums1)%nat
              || (max_num_possible_results <? length nums2)%nat);
      [ exact Hunknown | ].
    apply (Hcheck true). intros i1 i2 r [_ H1] [_ H2] Heval. left.
    unfold both_sides_results. apply in_flat_map. exists i1.
    split; [ exact H1 | ]. apply in_flat_map. exists i2.
    split; [ exact H2 | ]. rewrite Heval. left. reflexivity.
  - (* The first is known; the second needs a meet. *)
    destruct (one_side_results (op_rhs_unknown op) nums1) as [results | ]
      eqn:Hresults; [ | exact Hunknown ].
    apply (Hcheck false). intros i1 i2 r [_ H1] [Hrange2 _] Heval.
    pose proof (one_side_results_in _ _ _ Hresults i1 H1) as Hin.
    pose proof (op_rhs_unknown_sound op i1 i2 r Hrange2 Heval) as Htable.
    destruct (op_rhs_unknown op i1) as [result | | | ];
      [ left; subst; exact Hin | right; split; [ exact Hin | exact Htable ]
      | contradiction | contradiction ].
  - (* The first is known; the second stops. *)
    destruct (one_side_results (op_rhs_unknown op) nums1) as [results | ]
      eqn:Hresults; [ | exact Hunknown ].
    apply (Hcheck false). intros i1 i2 r [_ H1] [Hrange2 _] Heval.
    pose proof (one_side_results_in _ _ _ Hresults i1 H1) as Hin.
    pose proof (op_rhs_unknown_sound op i1 i2 r Hrange2 Heval) as Htable.
    destruct (op_rhs_unknown op i1) as [result | | | ];
      [ left; subst; exact Hin | right; split; [ exact Hin | exact Htable ]
      | contradiction | contradiction ].
  - (* The second is known; the first needs a meet. *)
    destruct (one_side_results (op_lhs_unknown op) nums2) as [results | ]
      eqn:Hresults; [ | exact Hunknown ].
    apply (Hcheck true). intros i1 i2 r [Hrange1 _] [_ H2] Heval.
    pose proof (one_side_results_in _ _ _ Hresults i2 H2) as Hin.
    pose proof (op_lhs_unknown_sound op i2 i1 r Hrange1 Heval) as Htable.
    destruct (op_lhs_unknown op i2) as [result | | | ];
      [ left; subst; exact Hin | right; split; [ exact Hin | exact Htable ]
      | contradiction | contradiction ].
  - (* The second is known; the first stops. *)
    destruct (one_side_results (op_lhs_unknown op) nums2) as [results | ]
      eqn:Hresults; [ | exact Hunknown ].
    apply (Hcheck true). intros i1 i2 r [Hrange1 _] [_ H2] Heval.
    pose proof (one_side_results_in _ _ _ Hresults i2 H2) as Hin.
    pose proof (op_lhs_unknown_sound op i2 i1 r Hrange1 Heval) as Htable.
    destruct (op_lhs_unknown op i2) as [result | | | ];
      [ left; subst; exact Hin | right; split; [ exact Hin | exact Htable ]
      | contradiction | contradiction ].
Qed.

Lemma simplify_int_comp_tagged_sound (tenv : Typing_env.t)
    (behaviour : int_comparison_behaviour) (arg1 arg2 : simple)
    (ty1 ty2 : flambda_type) :
  argument_type tenv arg1 ty1 ->
  argument_type tenv arg2 ty2 ->
  outcome_sound tenv
    (Prim (Binary (Int_comp Standard_tagged_immediate behaviour))
       [arg1; arg2])
    (simplify_int_comp_tagged tenv behaviour ty1 ty2).
Proof.
  intros Hty1 Hty2. unfold simplify_int_comp_tagged.
  pose proof (prim_kind_sound tenv
                (Binary (Int_comp Standard_tagged_immediate behaviour))
                [arg1; arg2]) as Hunknown.
  destruct (well_formed_input_b tenv ty1 && well_formed_input_b tenv ty2)
    eqn:Hwf; [ | exact Hunknown ].
  apply andb_true_iff in Hwf. destruct Hwf as [Hwf1 Hwf2].
  apply well_formed_input_b_sound in Hwf1, Hwf2.
  pose proof (fun x declared body =>
                let_int_comp_tagged tenv x declared behaviour arg1
                  arg2 ty1 ty2 body Hty1 Hty2 Hwf1 Hwf2) as Hlaw.
  cbv zeta in Hlaw. revert Hlaw.
  destruct (Provers.meet_equals_tagged_immediates tenv ty1)
    as [[nums1 | | ] | ],
    (Provers.meet_equals_tagged_immediates tenv ty2) as [[nums2 | | ] | ];
    intros Hlaw; try exact Hunknown; try exact Hlaw.
  match goal with
  | |- context [match ?results with _ => _ end] =>
    destruct results as [ | result rest] eqn:Hresults
  end; [ exact Hunknown | ].
  destruct (forallb (Z.eqb result) rest) eqn:Hsame; [ | exact Hunknown ].
  intros x declared body. apply (Hlaw x declared body result).
  intros i1 i2 Hi1 Hi2.
  assert (Hin :
    eval_int_comp tagged_width behaviour i1 i2 ∈ result :: rest).
  { rewrite <- Hresults. apply in_flat_map. exists i1.
    split; [ exact Hi1 | ]. apply in_map. exact Hi2. }
  destruct Hin as [Hfirst | Hin]; [ symmetry; exact Hfirst | ].
  rewrite forallb_forall in Hsame. symmetry. apply Z.eqb_eq.
  exact (Hsame _ Hin).
Qed.

Lemma simplify_binary_sound (tenv : Typing_env.t) (p : binary_primitive)
    (arg1 arg2 : simple) (ty1 ty2 : flambda_type) :
  argument_type tenv arg1 ty1 ->
  argument_type tenv arg2 ty2 ->
  outcome_sound tenv (Prim (Binary p) [arg1; arg2])
    (simplify_binary tenv p arg1 ty1 arg2 ty2).
Proof.
  intros Hty1 Hty2.
  destruct p; try exact (prim_kind_sound tenv _ [arg1; arg2]);
    match goal with
    | |- context [Int_arith ?kind _] => destruct kind
    | |- context [Int_comp ?kind _] => destruct kind
    end;
    try exact (prim_kind_sound tenv _ [arg1; arg2]).
  - exact (simplify_int_arith_tagged_sound tenv _ arg1 arg2 ty1 ty2
             Hty1 Hty2).
  - exact (simplify_int_comp_tagged_sound tenv _ arg1 arg2 ty1 ty2
             Hty1 Hty2).
Qed.

Lemma simplify_variadic_sound (tenv : Typing_env.t) (p : variadic_primitive)
    (args : list simple) (tys : list flambda_type) :
  Forall2 (argument_type tenv) args tys ->
  outcome_sound tenv (Prim (Variadic p) args) (simplify_variadic p tys).
Proof.
  intros Htys. destruct p as [[tag]]. simpl.
  destruct (tag <? no_scan_tag) eqn:Htag.
  - intros statics vars v Hsat Hnamed.
    exact (make_block_typed tenv statics vars tag args tys v
             (env_satisfies_strictly_env_satisfies tenv statics vars Hsat)
             Htys (proj1 (Z.ltb_lt _ _) Htag) Hnamed).
  - exact (prim_kind_sound tenv
             (Variadic (Make_block (Block_kind_values tag))) args).
Qed.

(* ======================================================================== *)
(* A defining expression                                                    *)
(* ======================================================================== *)

Lemma expr_refines_under_refl (tenv : Typing_env.t) (e : expr) :
  expr_refines_under tenv e e.
Proof. intros vars conts statics _. apply refines_refl. Qed.

(* The closure that a projection of a function slot answers is of the
   kind value. *)
Lemma project_function_slot_kind (statics : static_env)
    (move_from move_to : function_slot) (v r : value) :
  project_function_slot statics move_from move_to v = Some r ->
  kind_of_value r = Value.
Proof.
  unfold project_function_slot.
  repeat match goal with
         | |- context [match ?e with _ => _ end] =>
           destruct e; try discriminate
         end;
    intros [= <-]; reflexivity.
Qed.

Lemma simplify_named_sound (tenv : Typing_env.t) (d : named) :
  outcome_sound tenv d (simplify_named tenv d).
Proof.
  destruct d
    as [s | p args | code value_slots | slot function_decls value_slots
        | slot closure | project_from slot closure
        | move_from move_to closure];
    cbn [simplify_named].
  - intros x declared body. apply expr_refines_under_refl.
  - destruct (simplify_simples tenv args) as [answers | ] eqn:Hargs;
      [ | exact I ].
    destruct (simplify_simples_answers tenv args answers Hargs)
      as [Htys _].
    destruct (prim_args_well_kinded p
                (map FlambdaTypeGrammar.kind (map fst answers)))
      eqn:Hkinds.
    + (* By cases on the family of the primitive; a family that is not
         one of the three named here is left as it is. *)
      destruct p;
        [ destruct args as [ | arg [ | arg' args]]; try exact I;
          destruct (map fst answers) as [ | ty [ | ty' tys]]; try exact I;
          inversion Htys as [ | ? ? ? ? Hty _]; subst;
          exact (simplify_unary_sound tenv _ arg ty Hty)
        | destruct args as [ | arg1 [ | arg2 [ | arg3 args]]]; try exact I;
          destruct (map fst answers) as [ | ty1 [ | ty2 [ | ty3 tys]]];
          try exact I;
          inversion Htys as [ | ? ? ? ? Hty1 Hrest]; subst;
          inversion Hrest as [ | ? ? ? ? Hty2 _]; subst;
          exact (simplify_binary_sound tenv _ arg1 arg2 ty1 ty2 Hty1
                   Hty2)
        | match goal with
          | |- outcome_sound _ (Prim (Variadic ?q) _) ?answer =>
            replace answer with (simplify_variadic q (map fst answers))
              by (destruct args; destruct (map fst answers); reflexivity)
          end;
          exact (simplify_variadic_sound tenv _ args (map fst answers) Htys)
        | .. ];
        destruct args; destruct (map fst answers); exact I.
    + intros x declared body.
      exact (let_prim_kind_mismatch tenv x declared p args (map fst answers)
               body Htys Hkinds).
  - intros statics vars v _ Hnamed. simpl in Hnamed.
    destruct (eval_value_slots vars value_slots); [ | discriminate ].
    injection Hnamed as <-. reflexivity.
  - intros statics vars v _ Hnamed. simpl in Hnamed.
    destruct (lookup slot function_decls); [ | discriminate ].
    simpl in Hnamed.
    destruct (eval_value_slots vars value_slots); [ | discriminate ].
    injection Hnamed as <-. reflexivity.
  - exact I.
  - exact I.
  - destruct (simplify_simple tenv closure) as [[ty canonical] | ]
      eqn:Hclosure; [ | exact I ].
    destruct (simplify_simple_answer tenv closure canonical ty Hclosure)
      as [Hty _].
    apply of_simple_shortcut_sound.
    + intros x declared body.
      exact (let_project_function_slot tenv x declared move_from
               move_to closure ty body Hty).
    + intros statics vars v _ Hnamed. simpl in Hnamed.
      destruct (eval_simple vars closure) as [w | ]; [ | discriminate ].
      exact (project_function_slot_kind statics move_from move_to w v
               Hnamed).
Qed.

(* The arguments of a primitive may be replaced by their canonical
   elements. *)
Lemma canonical_named_equivalent (tenv : Typing_env.t) (x : variable)
    (declared : flambda_kind) (d : named) (body : expr) :
  expr_equivalent_under tenv (Let x declared d body)
    (Let x declared (canonical_named tenv d) body).
Proof.
  assert (Hrefl :
    expr_equivalent_under tenv (Let x declared d body)
      (Let x declared d body)).
  { intros vars conts statics _. apply equivalent_refl. }
  destruct d as [s | p args | | | | | ]; try exact Hrefl.
  cbn [canonical_named].
  destruct (simplify_simples tenv args) as [answers | ] eqn:Hargs;
    [ | exact Hrefl ].
  apply let_prim_canonical.
  exact (proj2 (simplify_simples_answers tenv args answers Hargs)).
Qed.

(* ======================================================================== *)
(* A [Let]                                                                  *)
(* ======================================================================== *)

Lemma simple_in_terms_b_sound (tenv : Typing_env.t) (s : simple) :
  simple_in_terms_b tenv s = true -> simple_in_terms tenv s.
Proof. intros Hb x ->. exact Hb. Qed.

Lemma simple_of_kind_b_sound (tenv : Typing_env.t) (s : simple)
    (kind : flambda_kind) :
  simple_of_kind_b tenv s kind = true -> simple_of_kind tenv s kind.
Proof.
  destruct s as [x | sym | c]; simpl.
  - destruct (Typing_env.find tenv (Name_var x) (Some kind)) as [ty | ];
      [ | discriminate ].
    intros _. exists ty. reflexivity.
  - destruct (Typing_env.find tenv (Name_symbol sym) (Some kind))
      as [ty | ]; [ | discriminate ].
    intros _. exists ty. reflexivity.
  - intros Hkind. exact (proj1 (kind_eqb_eq _ _) Hkind).
Qed.

Lemma bind_simple_sound (tenv tenv' : Typing_env.t) (x : variable)
    (s : simple) (d' : named) :
  typing_env_well_formed tenv = true ->
  Typing_env.mem None tenv (Name_var x) = false ->
  bind_simple tenv x s = Step_let d' tenv' ->
  ∀ (declared : flambda_kind) (body body' : expr),
    expr_refines_under tenv' body body' ->
    expr_refines_under tenv (Let x declared (Simple s) body)
      (Let x declared d' body').
Proof.
  intros Hwf Hfresh. unfold bind_simple.
  destruct (simplify_simple tenv s) as [[ty canonical] | ] eqn:Hs;
    [ | discriminate ].
  destruct (simplify_simple_answer tenv s canonical ty Hs)
    as [_ Hcanonical].
  destruct (simple_in_terms_b tenv canonical
            && simple_of_kind_b tenv canonical (FlambdaTypeGrammar.kind ty))
    eqn:Htests; [ | discriminate ].
  apply andb_true_iff in Htests. destruct Htests as [Hterms Hkind].
  destruct (Typing_env.add_alias _ _ _) as [[ | result | ] | ] eqn:Hadd;
    try discriminate.
  intros [= <- <-] declared body body' Hbody.
  eapply expr_refines_under_trans.
  - apply expr_equivalent_under_refines.
    exact (let_simple_canonical tenv x declared s canonical body Hcanonical).
  - exact (let_simple_refines_under tenv x declared canonical body body'
             (FlambdaTypeGrammar.kind ty) result Hwf Hfresh
             (simple_in_terms_b_sound tenv canonical Hterms)
             (simple_of_kind_b_sound tenv canonical _ Hkind) Hadd Hbody).
Qed.

Lemma simplify_let_sound (tenv : Typing_env.t) (x : variable) (d : named) :
  match simplify_let tenv x d with
  | Step_invalid =>
    ∀ (declared : flambda_kind) (body : expr),
      expr_equivalent_under tenv (Let x declared d body) Invalid
  | Step_let d' tenv' =>
    ∀ (declared : flambda_kind) (body body' : expr),
      expr_refines_under tenv' body body' ->
      expr_refines_under tenv (Let x declared d body)
        (Let x declared d' body')
  | Step_stop => True
  end.
Proof.
  unfold simplify_let.
  destruct (typing_env_well_formed tenv
            && negb (Typing_env.mem None tenv (Name_var x))) eqn:Htests;
    [ | exact I ].
  apply andb_true_iff in Htests. destruct Htests as [Hwf Hfresh].
  apply negb_true_iff in Hfresh.
  pose proof (simplify_named_sound tenv d) as Hsound.
  destruct (simplify_named tenv d) as [ | s | ty | kind | ]; simpl in Hsound.
  - intros declared body. exact (Hsound x declared body).
  - destruct (bind_simple tenv x s) as [ | d' tenv' | ] eqn:Hbind;
      try exact I.
    + (* [bind_simple] does not answer [Step_invalid]. *)
      exfalso. revert Hbind. unfold bind_simple.
      repeat match goal with
             | |- context [match ?e with _ => _ end] =>
               destruct e; try discriminate
             end.
    + intros declared body body' Hbody.
      eapply expr_refines_under_trans; [ exact (Hsound x declared body) | ].
      exact (bind_simple_sound tenv tenv' x s d' Hwf Hfresh Hbind declared
               body body' Hbody).
  - destruct (type_in_scope_b tenv ty) eqn:Hscope; [ | exact I ].
    intros declared body body' Hbody.
    eapply expr_refines_under_trans;
      [ | apply expr_equivalent_under_refines;
          exact (canonical_named_equivalent tenv x declared d body') ].
    apply (let_typed_refines_under tenv x declared d body body' ty Hwf
             Hfresh);
      [ | exact Hsound | exact Hbody ].
    intros y Hy. unfold type_in_scope_b in Hscope.
    rewrite forallb_forall in Hscope. exact (Hscope y Hy).
  - intros declared body body' Hbody.
    eapply expr_refines_under_trans;
      [ | apply expr_equivalent_under_refines;
          exact (canonical_named_equivalent tenv x declared d body') ].
    exact (let_refines_under tenv x declared d body body' kind Hwf Hfresh
             Hsound Hbody).
  - exact I.
Qed.

(* ======================================================================== *)
(* The other expressions                                                    *)
(* ======================================================================== *)

Lemma simplify_apply_cont_equivalent (tenv : Typing_env.t) (ac : apply_cont) :
  expr_equivalent_under tenv (Apply_cont ac)
    (Apply_cont (simplify_apply_cont tenv ac)).
Proof.
  unfold simplify_apply_cont.
  destruct (simplify_simples tenv (ac_args ac)) as [answers | ] eqn:Hargs.
  - destruct ac as [k args action]. simpl in *.
    apply apply_cont_canonical.
    exact (proj2 (simplify_simples_answers tenv args answers Hargs)).
  - intros vars conts statics _. apply equivalent_refl.
Qed.

Lemma simplify_switch_refines (tenv : Typing_env.t) (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  expr_refines_under tenv (Switch scrutinee arms)
    (simplify_switch tenv scrutinee arms).
Proof.
  unfold simplify_switch.
  destruct (simplify_simple tenv scrutinee) as [[ty canonical] | ]
    eqn:Hscrutinee; [ | apply expr_refines_under_refl ].
  destruct canonical as [x | sym | c]; try apply expr_refines_under_refl.
  destruct c; try apply expr_refines_under_refl.
  destruct (find_arm _ arms) as [ac | ] eqn:Harm;
    [ | apply expr_refines_under_refl ].
  destruct (simplify_simple_answer tenv scrutinee _ ty Hscrutinee)
    as [_ Hcanonical].
  eapply expr_refines_under_trans; apply expr_equivalent_under_refines.
  - exact (switch_known tenv scrutinee _ arms ac Hcanonical Harm).
  - apply simplify_apply_cont_equivalent.
Qed.

(* Under a [Let_static] the body runs with the same variables, in a
   static environment that has grown, and the symbols that it binds
   are defined. *)
Lemma add_symbol_definitions_env_satisfies_strictly (tenv : Typing_env.t)
    (syms : list symbol) (statics : static_env) (vars : env) :
  env_satisfies_strictly tenv statics vars ->
  env_satisfies_strictly (Typing_env.add_symbol_definitions tenv syms)
    statics vars.
Proof.
  intros [Hbound [valuation [Hsatisfied Hagrees]]].
  split; [ exact Hbound | ]. exists valuation.
  split; [ | exact Hagrees ].
  clear Hbound Hagrees. induction syms as [ | sym syms IH].
  - destruct tenv. exact Hsatisfied.
  - exact (proj2 (add_symbol_definition_satisfied _ statics valuation
                    (Typing_env.add_symbol_definitions tenv syms) sym) IH).
Qed.

Lemma let_static_body_refines_under (tenv : Typing_env.t)
    (bindings : list static_binding) (body body' : expr) :
  expr_refines_under
    (Typing_env.add_symbol_definitions tenv (bound_symbols bindings)) body
    body' ->
  expr_refines_under tenv (Let_static bindings body)
    (Let_static bindings body').
Proof.
  intros Hbody vars conts statics Hsat.
  destruct (eval_static_bindings vars bindings statics) as [statics' | ]
    eqn:Hbindings.
  - assert (Hstep :
      ∀ b : expr,
        step (State (Let_static bindings b) vars conts statics)
        = Step (State b vars conts statics')).
    { intros b. rewrite step_let_static, Hbindings. reflexivity. }
    eapply refines_step; [ apply Hstep | apply Hstep | ].
    apply Hbody. apply add_symbol_definitions_env_satisfies_strictly.
    refine (env_satisfies_strictly_statics_extend tenv statics statics' vars
              _ Hsat).
    exact (step_extends_statics _ _ (Hstep body)).
  - apply step_undefined_refines. rewrite step_let_static, Hbindings.
    reflexivity.
Qed.

(* ======================================================================== *)
(* A term                                                                   *)
(* ======================================================================== *)

Theorem simplify_expr_refines_under : simplify_expr_refines_under_statement.
Proof.
  intros tenv e. revert tenv.
  induction e
    as [x declared d body IH | bindings body IH | k handler body IH
        | handlers body IH | ap | ac | scrutinee arms | ];
    intros tenv; cbn [simplify_expr].
  - pose proof (simplify_let_sound tenv x d) as Hlet.
    destruct (simplify_let tenv x d) as [ | d' tenv' | ].
    + apply expr_equivalent_under_refines. exact (Hlet declared body).
    + exact (Hlet declared body (simplify_expr tenv' body) (IH tenv')).
    + apply expr_refines_under_refl.
  - apply let_static_body_refines_under. apply IH.
  - apply let_cont_body_refines_under. apply IH.
  - apply let_cont_recursive_body_refines_under. apply IH.
  - apply expr_refines_under_refl.
  - apply expr_equivalent_under_refines. apply simplify_apply_cont_equivalent.
  - apply simplify_switch_refines.
  - apply expr_refines_under_refl.
Qed.

Theorem simplify_by_types_refines : simplify_by_types_refines_statement.
Proof.
  intros e. apply expr_refines_under_create.
  exact (simplify_expr_refines_under Typing_env.create e).
Qed.

(* ======================================================================== *)
(* Examples                                                                 *)
(* ======================================================================== *)

Theorem example_pass_add_constants : example_pass_add_constants_statement.
Proof. intros k. vm_compute. reflexivity. Qed.

Theorem example_pass_is_int : example_pass_is_int_statement.
Proof. intros k0 k1. vm_compute. reflexivity. Qed.

Theorem example_pass_second_of_pair : example_pass_second_of_pair_statement.
Proof. intros k. vm_compute. reflexivity. Qed.

Theorem example_pass_add_zero : example_pass_add_zero_statement.
Proof. intros k. vm_compute. reflexivity. Qed.

Theorem example_pass_unbox_of_box : example_pass_unbox_of_box_statement.
Proof. intros k. vm_compute. reflexivity. Qed.

Theorem example_pass_untag_of_tag : example_pass_untag_of_tag_statement.
Proof. intros k. vm_compute. reflexivity. Qed.

Theorem example_pass_under_binders : example_pass_under_binders_statement.
Proof. intros k k'. vm_compute. reflexivity. Qed.
