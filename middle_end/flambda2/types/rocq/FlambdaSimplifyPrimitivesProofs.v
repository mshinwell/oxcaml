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


(* Proofs of the statements of FlambdaSimplifyPrimitivesSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaMapProofs FlambdaValueSpec FlambdaPrimitiveModel
  FlambdaPrimitiveSpec FlambdaPrimitiveProofs FlambdaSemanticsSpec
  FlambdaSemanticsProofs.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaTypeWellFormedSpec FlambdaTypeWellFormedProofs FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesProofs
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvProofs
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs
  FlambdaTypingEnvExamplesSpec FlambdaTypingEnvRefinementSpec
  FlambdaTypingEnvRefinementProofs FlambdaProvers
  FlambdaProversSpec FlambdaProversProofs FlambdaSimplifyPrimitivesSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The type of an argument                                                  *)
(* ======================================================================== *)

Theorem argument_type_satisfied : argument_type_satisfied_statement.
Proof.
  intros tenv statics vars arg ty v [Hbound [valuation [Hsatisfied Hagrees]]]
    [Hmem [canonical Htype]] Heval.
  exists valuation. split; [ exact Hsatisfied | ].
  split; [ exact Hagrees | ].
  apply (proj2 (type_simple_in_term_satisfied (fun _ => False) statics
                  valuation tenv (Some Name_mode.normal) arg canonical ty
                  Hsatisfied Htype)).
  rewrite (agrees_eval_simple tenv valuation vars arg Hagrees);
    [ exact Heval | ].
  intros x ->. exact Hmem.
Qed.

(* ======================================================================== *)
(* The type of an argument, computed                                        *)
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

Lemma well_formed_input_b_sound (tenv : Typing_env.t) (ty : flambda_type) :
  well_formed_input_b tenv ty = true -> well_formed_input tenv ty.
Proof.
  unfold well_formed_input_b. intros Hwf. apply andb_true_iff in Hwf.
  destruct Hwf as [Htenv Hty].
  split; [ exact (proj1 (types_well_formed_b_iff tenv) Htenv) | exact Hty ].
Qed.

(* ======================================================================== *)
(* The arguments, and the two conclusions                                   *)
(* ======================================================================== *)

Theorem let_prim_canonical : let_prim_canonical_statement.
Proof.
  intros tenv x declared p args args' body Hargs vars conts statics Hsat.
  apply let_equivalent_step; [ | intros v _; apply equivalent_refl ].
  simpl.
  rewrite (canonical_in_terms_simples tenv statics vars args args' Hsat
             Hargs).
  reflexivity.
Qed.

Theorem let_constant : let_constant_statement.
Proof.
  intros tenv x declared d c body Hknown vars conts statics Hsat.
  destruct (eval_named statics vars d) as [v | ] eqn:Hd.
  - pose proof (Hknown statics vars v Hsat Hd) as ->.
    eapply refines_step;
      [ rewrite step_let, Hd; reflexivity | rewrite step_let; reflexivity
      | apply refines_refl ].
  - apply step_undefined_refines. rewrite step_let, Hd. reflexivity.
Qed.

Theorem let_invalid : let_invalid_statement.
Proof.
  intros tenv x declared d body Hnone vars conts statics Hsat.
  apply step_eq_equivalent.
  rewrite step_let, (Hnone statics vars Hsat), step_invalid. reflexivity.
Qed.

(* The values of arguments that have values. *)
Lemma eval_simples_values (vars : env) (args : list simple) :
  ∀ vs : list value,
    eval_simples vars args = Some vs ->
    Forall2 (fun arg v => eval_simple vars arg = Some v) args vs.
Proof.
  induction args as [ | arg args IH]; intros vs; simpl.
  - intros [= <-]. apply Forall2_nil.
  - destruct (eval_simple vars arg) as [v | ] eqn:Hv; [ | discriminate ].
    destruct (eval_simples vars args) as [vs' | ]; [ | discriminate ].
    intros [= <-]. apply Forall2_cons; [ exact Hv | exact (IH vs' eq_refl) ].
Qed.

Theorem let_prim_kind_mismatch : let_prim_kind_mismatch_statement.
Proof.
  intros tenv x declared p args tys body Htys Hkinds.
  apply let_invalid. intros statics vars Hsat.
  destruct (eval_named statics vars (Prim p args)) as [r | ] eqn:Hnamed;
    [ exfalso | reflexivity ].
  cbn [eval_named] in Hnamed.
  destruct (eval_simples vars args) as [vs | ] eqn:Hvs; [ | discriminate ].
  destruct (eval_prim_kinds statics p vs r Hnamed) as [Hwell _].
  assert (Hsame :
    map kind_of_value vs = map FlambdaTypeGrammar.kind tys).
  { pose proof (eval_simples_values vars args vs Hvs) as Hvalues.
    clear Hvs Hnamed Hwell Hkinds. revert vs Hvalues.
    induction Htys as [ | arg ty args tys Hty Htys IH]; intros vs Hvalues;
      inversion Hvalues as [ | arg' v args' vs' Hv Hrest]; subst;
      [ reflexivity | ].
    simpl. f_equal; [ | exact (IH vs' Hrest) ].
    destruct (argument_type_satisfied tenv statics vars arg ty v Hsat Hty
                Hv) as [valuation [_ [_ Htyped]]].
    exact (type_satisfied_kind statics valuation v ty Htyped). }
  rewrite Hsame in Hwell. congruence.
Qed.

(* ======================================================================== *)
(* A primitive applied in a state that satisfies the environment            *)
(* ======================================================================== *)

(* A unary primitive that has a value was applied to the value of its
   argument. *)
Lemma unary_prim_value (statics : static_env) (vars : env)
    (p : unary_primitive) (arg : simple) (r : value) :
  eval_named statics vars (Prim (Unary p) [arg]) = Some r ->
  ∃ v : value,
    eval_simple vars arg = Some v ∧ eval_prim statics (Unary p) [v] = Some r.
Proof.
  simpl. destruct (eval_simple vars arg) as [v | ]; [ | discriminate ].
  intros Hprim. exists v. split; [ reflexivity | exact Hprim ].
Qed.

(* So to the value of an argument that has the type of the argument. *)
Lemma unary_prim_typed (tenv : Typing_env.t) (statics : static_env)
    (vars : env) (p : unary_primitive) (arg : simple) (ty : flambda_type)
    (r : value) :
  env_satisfies_strictly tenv statics vars ->
  argument_type tenv arg ty ->
  eval_named statics vars (Prim (Unary p) [arg]) = Some r ->
  ∃ (valuation : env) (v : value),
    typing_env_satisfied_strictly statics valuation tenv
    ∧ type_satisfied statics valuation v ty
    ∧ eval_prim statics (Unary p) [v] = Some r.
Proof.
  intros Hsat Hty Hnamed.
  destruct (unary_prim_value statics vars p arg r Hnamed) as [v [Hv Hprim]].
  destruct (argument_type_satisfied tenv statics vars arg ty v Hsat Hty Hv)
    as [valuation [Hsatisfied [_ Htyped]]].
  exists valuation, v.
  split; [ exact Hsatisfied | ]. split; [ exact Htyped | exact Hprim ].
Qed.

(* Two answers about one value are the same. *)
Lemma is_int_is_unique (b b' : bool) (v : value) :
  is_int_is b v -> is_int_is b' v -> b = b'.
Proof. destruct b, b'; simpl; intros H H'; try reflexivity; contradiction. Qed.

Lemma is_null_is_unique (b b' : bool) (v : value) :
  is_null_is b v -> is_null_is b' v -> b = b'.
Proof. destruct b, b'; simpl; intros H H'; try reflexivity; contradiction. Qed.

Lemma naked_bool_const (b : bool) :
  naked_bool b = Value_const (Naked_immediate (if b then 1 else 0)).
Proof. reflexivity. Qed.

(* ======================================================================== *)
(* [Is_int] and [Get_tag], through [Provers.prove_is_int]                   *)
(* ======================================================================== *)

Theorem let_is_int_proved : let_is_int_proved_statement.
Proof.
  intros tenv x declared arg ty b body Hty Hprove.
  apply let_constant. intros statics vars r Hsat Hnamed.
  destruct (unary_prim_typed tenv statics vars _ arg ty r Hsat Hty Hnamed)
    as [valuation [v [Hsatisfied [Htyped Hprim]]]].
  rewrite <- naked_bool_const.
  exact (prove_is_int_is_int statics valuation tenv ty b v r
           Hsatisfied Htyped Hprove Hprim).
Qed.

Theorem let_get_tag_of_immediate : let_get_tag_of_immediate_statement.
Proof.
  intros tenv x declared arg ty body Hty Hprove.
  apply let_invalid. intros statics vars Hsat.
  destruct (eval_named statics vars (Prim (Unary Get_tag) [arg]))
    as [r | ] eqn:Hnamed; [ exfalso | reflexivity ].
  destruct (unary_prim_typed tenv statics vars _ arg ty r Hsat Hty Hnamed)
    as [valuation [v [Hsatisfied [Htyped Hprim]]]].
  rewrite (prove_is_int_get_tag statics valuation tenv ty v
             Hsatisfied Htyped Hprove) in Hprim.
  discriminate.
Qed.

(* ======================================================================== *)
(* The relational primitives                                                *)
(* ======================================================================== *)

Theorem is_int_relation_type : is_int_relation_type_statement.
Proof.
  intros statics valuation scrutinee w r Hw Hprim.
  destruct (is_int_defined statics true w r Hprim)
    as [Hvariants [b [-> Hb]]].
  apply is_int_for_scrutinee_satisfied.
  exists (if b then 1 else 0), w.
  split; [ apply naked_bool_const | ]. split; [ exact Hw | ].
  destruct b; simpl in Hb.
  - left. split; [ exact Hb | reflexivity ].
  - right. split; [ | reflexivity ].
    destruct (Hvariants eq_refl) as [Himmediate | Hblock];
      [ contradiction | exact Hblock ].
Qed.

Theorem is_null_relation_type : is_null_relation_type_statement.
Proof.
  intros statics valuation scrutinee w r Hw Hprim.
  destruct (is_null_defined statics w r Hprim) as [Hkind [b [-> Hb]]].
  apply is_null_for_scrutinee_satisfied.
  exists (if b then 1 else 0), w.
  split; [ apply naked_bool_const | ]. split; [ exact Hw | ].
  destruct b; simpl in Hb.
  - left. split; [ exact Hb | reflexivity ].
  - right. split; [ exact Hkind | ]. split; [ exact Hb | reflexivity ].
Qed.

Theorem get_tag_relation_type : get_tag_relation_type_statement.
Proof.
  intros statics valuation block w r Hw Hprim Htag.
  destruct (get_tag_defined statics w r Hprim) as [tag [fields [Hblock ->]]].
  apply get_tag_for_block_satisfied.
  exists tag, w. split; [ reflexivity | ]. split; [ exact Hw | ].
  right. split; [ exists fields; exact Hblock | ].
  exact (Htag tag fields Hblock).
Qed.

Theorem let_is_int_variant_only : let_is_int_variant_only_statement.
Proof.
  intros tenv x declared arg ty body Hty.
  (* What the answer says of the value of the argument. *)
  assert (Hsound :
    ∀ (statics : static_env) (vars : env) (r : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars (Prim (Unary (Is_int true)) [arg]) = Some r ->
      match Provers.meet_is_int_variant_only tenv ty with
      | Some (Meet_shortcut.Known_result b) => r = naked_bool b
      | Some Meet_shortcut.Invalid => False
      | Some Meet_shortcut.Need_meet | None => True
      end).
  { intros statics vars r Hsat Hnamed.
    destruct (unary_prim_typed tenv statics vars _ arg ty r Hsat Hty Hnamed)
      as [valuation [v [Hsatisfied [Htyped Hprim]]]].
    destruct (is_int_defined statics true v r Hprim)
      as [Hvariants [b' [-> Hb']]].
    pose proof (meet_is_int_variant_only_sound statics valuation tenv
                  ty v Hsatisfied I Htyped (Hvariants eq_refl)) as Hanswer.
    destruct (Provers.meet_is_int_variant_only tenv ty) as [[b | | ] | ];
      try exact I; [ | exact Hanswer ].
    rewrite (is_int_is_unique b b' v Hanswer Hb'). reflexivity. }
  destruct (Provers.meet_is_int_variant_only tenv ty) as [[b | | ] | ];
    try exact I.
  - apply let_constant. intros statics vars r Hsat Hnamed.
    rewrite <- naked_bool_const. exact (Hsound statics vars r Hsat Hnamed).
  - apply let_invalid. intros statics vars Hsat.
    destruct (eval_named statics vars (Prim (Unary (Is_int true)) [arg]))
      as [r | ] eqn:Hnamed; [ exfalso | reflexivity ].
    exact (Hsound statics vars r Hsat Hnamed).
Qed.

Theorem let_get_tag_proved : let_get_tag_proved_statement.
Proof.
  intros tenv x declared arg ty tags tag body Hty Hprove Htags.
  apply let_constant. intros statics vars r Hsat Hnamed.
  destruct (unary_prim_typed tenv statics vars _ arg ty r Hsat Hty Hnamed)
    as [valuation [v [Hsatisfied [Htyped Hprim]]]].
  destruct (get_tag_defined statics v r Hprim)
    as [tag' [fields' [Hblock' ->]]].
  destruct (prove_get_tag_sound statics valuation tenv ty tags v
              Hsatisfied I Htyped Hprove)
    as [tag'' [fields'' [Hblock'' Hin]]].
  rewrite Hblock' in Hblock''. injection Hblock'' as -> _.
  rewrite (Htags tag'' Hin). reflexivity.
Qed.

Theorem let_is_null : let_is_null_statement.
Proof.
  intros tenv x declared arg ty body Hty.
  assert (Hsound :
    ∀ (statics : static_env) (vars : env) (r : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars (Prim (Unary Is_null) [arg]) = Some r ->
      match Provers.meet_is_null tenv ty with
      | Some (Meet_shortcut.Known_result b) => r = naked_bool b
      | Some Meet_shortcut.Invalid => False
      | Some Meet_shortcut.Need_meet | None => True
      end).
  { intros statics vars r Hsat Hnamed.
    destruct (unary_prim_typed tenv statics vars _ arg ty r Hsat Hty Hnamed)
      as [valuation [v [Hsatisfied [Htyped Hprim]]]].
    destruct (is_null_defined statics v r Hprim) as [Hkind [b' [-> Hb']]].
    pose proof (meet_is_null_sound statics valuation tenv ty v
                  Hsatisfied I Htyped Hkind) as Hanswer.
    destruct (Provers.meet_is_null tenv ty) as [[b | | ] | ];
      try exact I; [ | exact Hanswer ].
    rewrite (is_null_is_unique b b' v Hanswer Hb'). reflexivity. }
  destruct (Provers.meet_is_null tenv ty) as [[b | | ] | ]; try exact I.
  - apply let_constant. intros statics vars r Hsat Hnamed.
    rewrite <- naked_bool_const. exact (Hsound statics vars r Hsat Hnamed).
  - apply let_invalid. intros statics vars Hsat.
    destruct (eval_named statics vars (Prim (Unary Is_null) [arg]))
      as [r | ] eqn:Hnamed; [ exfalso | reflexivity ].
    exact (Hsound statics vars r Hsat Hnamed).
Qed.

(* ======================================================================== *)
(* A comparison of tagged immediates                                        *)
(* ======================================================================== *)

(* A comparison of tagged immediates that has a value was applied to
   two tagged immediates, and its value is the comparison of their
   numbers. *)
Lemma int_comp_tagged_defined (statics : static_env)
    (behaviour : int_comparison_behaviour) (v1 v2 r : value) :
  eval_prim statics (Binary (Int_comp Standard_tagged_immediate behaviour))
    [v1; v2]
  = Some r ->
  ∃ i1 i2 : Z,
    v1 = Value_const (Tagged_immediate i1)
    ∧ v2 = Value_const (Tagged_immediate i2)
    ∧ r
      = Value_const
          (Naked_immediate
             (eval_int_comp (int_width Standard_tagged_immediate) behaviour
                i1 i2)).
Proof.
  cbn [eval_prim eval_binary_primitive].
  destruct (int_of_value Standard_tagged_immediate v1) as [a | ] eqn:Ha;
    [ | discriminate ].
  destruct (int_of_value Standard_tagged_immediate v2) as [b | ] eqn:Hb;
    [ | discriminate ].
  intros [= <-].
  assert (Hint :
    ∀ (v : value) (i : Z),
      int_of_value Standard_tagged_immediate v = Some i ->
      v = Value_const (Tagged_immediate i)).
  { intros v i Hv. exact (proj1 (int_of_value_const _ _ _ Hv)). }
  exists a, b.
  split; [ exact (Hint v1 a Ha) | ]. split; [ exact (Hint v2 b Hb) | ].
  reflexivity.
Qed.

Theorem let_int_comp_tagged : let_int_comp_tagged_statement.
Proof.
  intros tenv x declared behaviour arg1 arg2 ty1 ty2 body Hty1 Hty2
    Hwf1 Hwf2 comparison.
  (* What the answers say of the values of the arguments. *)
  assert (Hsound :
    ∀ (statics : static_env) (vars : env) (r : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars comparison = Some r ->
      ∃ i1 i2 : Z,
        r
        = Value_const
            (Naked_immediate
               (eval_int_comp (int_width Standard_tagged_immediate)
                  behaviour i1 i2))
        ∧ match Provers.meet_equals_tagged_immediates tenv ty1 with
          | Some (Meet_shortcut.Known_result imms1) => i1 ∈ imms1
          | Some Meet_shortcut.Invalid => False
          | Some Meet_shortcut.Need_meet | None => True
          end
        ∧ match Provers.meet_equals_tagged_immediates tenv ty2 with
          | Some (Meet_shortcut.Known_result imms2) => i2 ∈ imms2
          | Some Meet_shortcut.Invalid => False
          | Some Meet_shortcut.Need_meet | None => True
          end).
  { intros statics vars r Hsat Hnamed. unfold comparison in Hnamed.
    simpl in Hnamed.
    destruct (eval_simple vars arg1) as [v1 | ] eqn:Hv1; [ | discriminate ].
    destruct (eval_simple vars arg2) as [v2 | ] eqn:Hv2; [ | discriminate ].
    change (eval_prim statics
              (Binary (Int_comp Standard_tagged_immediate behaviour))
              [v1; v2]
            = Some r) in Hnamed.
    destruct (int_comp_tagged_defined statics behaviour v1 v2 r Hnamed)
      as [i1 [i2 [-> [-> ->]]]].
    exists i1, i2. split; [ reflexivity | ].
    (* The answer about one argument. *)
    assert (Hone :
      ∀ (arg : simple) (ty : flambda_type) (i : Z),
        argument_type tenv arg ty ->
        well_formed_input tenv ty ->
        eval_simple vars arg = Some (Value_const (Tagged_immediate i)) ->
        match Provers.meet_equals_tagged_immediates tenv ty with
        | Some (Meet_shortcut.Known_result imms) => i ∈ imms
        | Some Meet_shortcut.Invalid => False
        | Some Meet_shortcut.Need_meet | None => True
        end).
    { intros arg ty i Hty Hwf Hv.
      destruct (argument_type_satisfied tenv statics vars arg ty _ Hsat Hty
                  Hv) as [valuation [Hsatisfied [_ Htyped]]].
      pose proof (meet_equals_tagged_immediates_sound statics
                    valuation tenv ty _ Hsatisfied Hwf Htyped
                    (ex_intro _ i eq_refl)) as Hanswer.
      destruct (Provers.meet_equals_tagged_immediates tenv ty)
        as [[imms | | ] | ]; try exact I; [ | exact Hanswer ].
      destruct Hanswer as [j [[= <-] Hin]]. exact Hin. }
    split;
      [ exact (Hone arg1 ty1 i1 Hty1 Hwf1 Hv1)
      | exact (Hone arg2 ty2 i2 Hty2 Hwf2 Hv2) ]. }
  assert (Hinvalid :
    (∀ (statics : static_env) (vars : env) (r : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars comparison = Some r ->
      False) ->
    expr_equivalent_under tenv (Let x declared comparison body) Invalid).
  { intros Hnone. apply let_invalid. intros statics vars Hsat.
    destruct (eval_named statics vars comparison) as [r | ] eqn:Hnamed;
      [ exfalso; exact (Hnone statics vars r Hsat Hnamed) | reflexivity ]. }
  destruct (Provers.meet_equals_tagged_immediates tenv ty1)
    as [[imms1 | | ] | ],
    (Provers.meet_equals_tagged_immediates tenv ty2) as [[imms2 | | ] | ];
    try exact I;
    try (apply Hinvalid; intros statics vars r Hsat Hnamed;
         destruct (Hsound statics vars r Hsat Hnamed)
           as [i1 [i2 [_ [H1 H2]]]];
         first [ exact H1 | exact H2 ]).
  intros result Hresult.
  apply let_constant. intros statics vars r Hsat Hnamed.
  destruct (Hsound statics vars r Hsat Hnamed) as [i1 [i2 [-> [H1 H2]]]].
  rewrite (Hresult i1 i2 H1 H2). reflexivity.
Qed.

(* ======================================================================== *)
(* Physical equality                                                        *)
(* ======================================================================== *)

(* The value of an argument has the type of the argument under any
   valuation that satisfies the environment and agrees with the
   machine: the two arguments of a primitive under the same one. *)
Lemma argument_type_in_valuation (tenv : Typing_env.t)
    (statics : static_env) (valuation vars : env) (arg : simple)
    (ty : flambda_type) (v : value) :
  typing_env_satisfied_strictly statics valuation tenv ->
  agrees_in_terms tenv valuation vars ->
  argument_type tenv arg ty ->
  eval_simple vars arg = Some v ->
  type_satisfied statics valuation v ty.
Proof.
  intros Hsatisfied Hagrees [Hmem [canonical Htype]] Heval.
  apply (proj2 (type_simple_in_term_satisfied (fun _ => False) statics
                  valuation tenv (Some Name_mode.normal) arg canonical ty
                  Hsatisfied Htype)).
  rewrite (agrees_eval_simple tenv valuation vars arg Hagrees);
    [ exact Heval | ].
  intros x ->. exact Hmem.
Qed.

Theorem let_phys_equal : let_phys_equal_statement.
Proof.
  intros tenv x declared op arg1 arg2 ty1 ty2 b body Hty1 Hty2 Hwf1 Hwf2
    Hprove result.
  apply let_constant.
  intros statics vars r [_ [valuation [Hsatisfied Hagrees]]] Hnamed.
  simpl in Hnamed.
  destruct (eval_simple vars arg1) as [v1 | ] eqn:Hv1; [ | discriminate ].
  destruct (eval_simple vars arg2) as [v2 | ] eqn:Hv2; [ | discriminate ].
  change (eval_prim statics (Binary (Phys_equal op)) [v1; v2] = Some r)
    in Hnamed.
  rewrite <- naked_bool_const.
  exact (prove_physical_equality_phys_equal statics valuation tenv ty1 ty2
           b op v1 v2 r Hsatisfied Hwf1 Hwf2
           (argument_type_in_valuation tenv statics valuation vars arg1 ty1
              v1 Hsatisfied Hagrees Hty1 Hv1)
           (argument_type_in_valuation tenv statics valuation vars arg2 ty2
              v2 Hsatisfied Hagrees Hty2 Hv2)
           Hprove Hnamed).
Qed.

(* ======================================================================== *)
(* Examples                                                                 *)
(* ======================================================================== *)

(* What the environment answers for an argument is computed. *)
Ltac argument_computed :=
  split; [ vm_compute; reflexivity | eexists; vm_compute; reflexivity ].

(* The first [Let] of the two examples: [x] is made equal to the
   constant. *)
Ltac example_first_let :=
  apply expr_refines_under_create;
  eapply (let_simple_refines_under Typing_env.create example_x Value
            (Const (Tagged_immediate 5)) _ _ Value);
  [ reflexivity | reflexivity | intros ? [=] | reflexivity
  | vm_compute; reflexivity | ].

(* Their end: [i] is made equal to 1, and the [Switch] is its arm. *)
Ltac example_switch_arm :=
  eapply (let_simple_refines_under _ example_i
            (Naked_number Kind_naked_immediate) (Const (Naked_immediate 1))
            _ _ (Naked_number Kind_naked_immediate));
  [ vm_compute; reflexivity | vm_compute; reflexivity | intros ? [=]
  | reflexivity | vm_compute; reflexivity
  | apply expr_equivalent_under_refines;
    apply (switch_known _ (Var example_i) 1);
    [ canonical_computed | reflexivity ] ].

Theorem example_is_int : example_is_int_statement.
Proof.
  intros k0 k1. example_first_let.
  eapply expr_refines_under_trans.
  - eapply (let_is_int_proved _ example_i _ (Var example_x) _ true);
      [ argument_computed | vm_compute; reflexivity ].
  - example_switch_arm.
Qed.

(* The types of an environment that is computed are well formed. *)
Ltac well_formed_input_computed :=
  split; [ | vm_compute; reflexivity ];
  apply (proj1 (types_well_formed_b_iff _)); vm_compute; reflexivity.

Theorem example_int_comp : example_int_comp_statement.
Proof.
  intros k0 k1. example_first_let.
  eapply expr_refines_under_trans.
  - match goal with
    | |- expr_refines_under ?tenv (Let _ _ _ ?body) _ =>
      pose proof (let_int_comp_tagged tenv example_i
                    (Naked_number Kind_naked_immediate)
                    (Yielding_bool (Int_lt Signed)) (Var example_x)
                    (Const (Tagged_immediate 7))
                    (alias_type_of Value (Const (Tagged_immediate 5)))
                    (alias_type_of Value (Const (Tagged_immediate 7))) body)
        as Hcomparison
    end.
    cbv zeta in Hcomparison.
    repeat match type of Hcomparison with
           | context [Provers.meet_equals_tagged_immediates ?tenv ?ty] =>
             let answer :=
               eval vm_compute in
                 (Provers.meet_equals_tagged_immediates tenv ty)
             in
             replace (Provers.meet_equals_tagged_immediates tenv ty)
               with answer in Hcomparison by (vm_compute; reflexivity)
           end.
    cbv beta iota in Hcomparison.
    refine (Hcomparison _ _ _ _ 1 _);
      [ argument_computed | argument_computed | well_formed_input_computed
      | well_formed_input_computed | ].
    intros i1 i2 [<- | []] [<- | []]. reflexivity.
  - example_switch_arm.
Qed.
