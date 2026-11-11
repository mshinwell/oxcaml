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


(* Proofs of the statements of FlambdaTypingEnvOperationsSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaWellFormedSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec
  FlambdaEnvAliasesProofs FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvProofs FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvInvariantProofs FlambdaTypingEnvOperationsSpec.
Import ListNotations.

(* ======================================================================== *)
(* Scopes and symbols                                                       *)
(* ======================================================================== *)

Theorem increment_scope_satisfied : increment_scope_satisfied_statement.
Proof.
  intros exempt statics valuation tenv.
  split; exact (fun Hsatisfied => Hsatisfied).
Qed.

Theorem closure_env_satisfied : closure_env_satisfied_statement.
Proof.
  intros exempt statics valuation tenv.
  split; exact (fun Hsatisfied => Hsatisfied).
Qed.

Theorem add_symbol_definition_satisfied
    : add_symbol_definition_satisfied_statement.
Proof.
  intros exempt statics valuation tenv sym.
  split; exact (fun Hsatisfied => Hsatisfied).
Qed.

Theorem increment_scope_env_satisfies_strictly
    : increment_scope_env_satisfies_strictly_statement.
Proof.
  intros tenv statics vars. split; exact (fun Hsatisfies => Hsatisfies).
Qed.

(* ======================================================================== *)
(* Defining a variable                                                      *)
(* ======================================================================== *)

Theorem add_variable_definition_satisfied
    : add_variable_definition_satisfied_statement.
Proof.
  intros exempt statics valuation tenv var kind name_mode
    [Hbottom [Htypes Hrespected]] Hkind.
  split; [ exact Hbottom | ]. split; [ | exact Hrespected ].
  intros n ty btm v Hlookup Hvalue.
  rewrite add_variable_definition_lookup in Hlookup.
  destruct (keyed_eqb_spec name_eqb name_eqb_eq n (Name_var var))
    as [Heq | Hne].
  - subst n. injection Hlookup as <- <-. right.
    apply (proj2 (unknown_satisfied statics valuation v kind)).
    exact (Hkind v Hvalue).
  - exact (Htypes n ty btm v Hlookup Hvalue).
Qed.

Theorem add_variable_definition_satisfied_bind
    : add_variable_definition_satisfied_bind_statement.
Proof.
  intros exempt statics valuation tenv var kind name_mode v Hsatisfied
    Hnot_mentioned Hkind.
  apply add_variable_definition_satisfied.
  - apply (satisfied_but_coincide exempt statics valuation
             ((var, v) :: valuation) tenv); [ | exact Hsatisfied ].
    intros x Hmentions. symmetry. apply lookup_other.
    intros ->. exact (Hnot_mentioned Hmentions).
  - intros v' Hlookup. rewrite lookup_head in Hlookup.
    injection Hlookup as <-. exact Hkind.
Qed.

Theorem well_formed_not_mentioned : well_formed_not_mentioned_statement.
Proof.
  intros tenv var Hwf Hfresh Hmentions.
  apply typing_env_well_formed_iff in Hwf.
  destruct Hwf
    as [[_ [_ [_ [Hclosed _]]]] [_ [Hconsistent [_ [Hknown _]]]]].
  pose proof (mem_fresh_lookup tenv var Hfresh) as Hnone.
  destruct Hmentions
    as [[ty [btm Hlookup]] | [[n [ty [btm [Hlookup Hin]]]] | Hmention]].
  - congruence.
  - pose proof (Hclosed n ty btm var Hlookup Hin) as Hbound.
    rewrite <- mem_var_is_bound in Hbound. congruence.
  - pose proof (mentioned_known tenv (Name_var var) Hconsistent Hknown
                  Hmention).
    congruence.
Qed.

Theorem add_variable_definition_satisfied_inv
    : add_variable_definition_satisfied_inv_statement.
Proof.
  intros exempt statics valuation tenv var kind name_mode Hfresh
    [Hbottom [Htypes Hrespected]].
  apply mem_fresh_lookup in Hfresh.
  split; [ exact Hbottom | ]. split; [ | exact Hrespected ].
  intros n ty btm v Hlookup Hvalue.
  apply (Htypes n ty btm v); [ | exact Hvalue ].
  rewrite add_variable_definition_lookup.
  destruct (keyed_eqb_spec name_eqb name_eqb_eq n (Name_var var))
    as [-> | Hne]; [ congruence | exact Hlookup ].
Qed.

Theorem add_variable_definition_mentions
    : add_variable_definition_mentions_statement.
Proof.
  intros tenv var kind name_mode x Hmentions.
  destruct (Pos.eq_dec x var) as [-> | Hne]; [ left; reflexivity | right ].
  destruct Hmentions
    as [[ty [btm Hlookup]] | [[n [ty [btm [Hlookup Hin]]]] | Hmention]].
  - left. rewrite add_variable_definition_lookup in Hlookup.
    destruct (keyed_eqb_spec name_eqb name_eqb_eq (Name_var x)
                (Name_var var)) as [Heq | _]; [ congruence | ].
    exists ty, btm. exact Hlookup.
  - rewrite add_variable_definition_lookup in Hlookup.
    destruct (keyed_eqb_spec name_eqb name_eqb_eq n (Name_var var))
      as [-> | _].
    + injection Hlookup as <- <-. rewrite free_variables_unknown in Hin.
      destruct Hin.
    + right. left. exists n, ty, btm. split; [ exact Hlookup | exact Hin ].
  - right. right. exact Hmention.
Qed.

Theorem add_definitions_of_params_satisfied_bind
    : add_definitions_of_params_satisfied_bind_statement.
Proof.
  intros exempt statics valuation valuation' tenv params.
  revert valuation tenv.
  induction params as [ | [x kind] params IH];
    intros valuation tenv vs Hsatisfied Hdistinct Hfresh Hkinds Hbind.
  - inversion Hkinds; subst. simpl in Hbind. injection Hbind as <-.
    exact Hsatisfied.
  - inversion Hkinds as [ | param v params' vs' Hkind Hrest]; subst.
    simpl in Hbind.
    change (negb (among x (map fst params)) && distinct (map fst params)
            = true) in Hdistinct.
    apply andb_true_iff in Hdistinct. destruct Hdistinct as [Hx Hdistinct].
    apply negb_true_iff in Hx.
    apply (IH ((x, v) :: valuation)
             (Typing_env.add_variable_definition tenv x kind
                Name_mode.normal) vs').
    + apply add_variable_definition_satisfied_bind;
        [ exact Hsatisfied | | exact Hkind ].
      apply Hfresh. left. reflexivity.
    + exact Hdistinct.
    + intros y Hin Hmentions.
      apply add_variable_definition_mentions in Hmentions.
      destruct Hmentions as [-> | Hmentions].
      * apply among_In in Hin. congruence.
      * exact (Hfresh y (or_intror Hin) Hmentions).
    + exact Hrest.
    + exact Hbind.
Qed.

(* ======================================================================== *)
(* A new type for a name                                                    *)
(* ======================================================================== *)

(* What [replace_equation] does to the types of the names: nothing for
   a variable that is not bound, and otherwise an entry for the name. *)
Lemma replace_equation_names_to_types (tenv : Typing_env.t) (n : name)
    (ty : flambda_type) :
  Typing_env.names_to_types (Typing_env.replace_equation tenv n ty)
  = match n with
    | Name_var _ =>
      match Keyed.lookup name_eqb n (Typing_env.names_to_types tenv) with
      | Some (_, binding_time_and_mode) =>
        (n, (ty, binding_time_and_mode)) :: Typing_env.names_to_types tenv
      | None => Typing_env.names_to_types tenv
      end
    | Name_symbol _ =>
      (n,
       (ty,
        Binding_time.With_name_mode.create Binding_time.symbols
          Name_mode.normal))
      :: Typing_env.names_to_types tenv
    end.
Proof.
  destruct n as [x | s]; [ | reflexivity ].
  unfold Typing_env.replace_equation, Typing_env.names_to_types,
    Typing_env.with_current_level.
  cbn [Typing_env.just_after_level].
  unfold Cached_level.replace_variable_binding.
  destruct (Keyed.lookup name_eqb (Name_var x)
              (Cached_level.names_to_types (Typing_env.just_after_level tenv)))
    as [[ty0 btm0] | ]; reflexivity.
Qed.

Lemma replace_equation_aliases (tenv : Typing_env.t) (n : name)
    (ty : flambda_type) :
  Typing_env.aliases (Typing_env.replace_equation tenv n ty)
  = Typing_env.aliases tenv.
Proof.
  destruct n as [x | s]; [ | reflexivity ].
  unfold Typing_env.replace_equation, Typing_env.aliases,
    Typing_env.with_current_level.
  cbn [Typing_env.just_after_level].
  unfold Cached_level.replace_variable_binding.
  destruct (Keyed.lookup name_eqb (Name_var x)
              (Cached_level.names_to_types (Typing_env.just_after_level tenv)))
    as [[ty0 btm0] | ]; reflexivity.
Qed.

(* An entry afterwards is the new one of the name, or one that was
   there. *)
Lemma replace_equation_lookup_cases (tenv : Typing_env.t) (n : name)
    (ty : flambda_type) (m : name) (ty1 : flambda_type)
    (btm1 : Binding_time.With_name_mode.t) :
  Keyed.lookup name_eqb m
    (Typing_env.names_to_types (Typing_env.replace_equation tenv n ty))
  = Some (ty1, btm1) ->
  (m = n ∧ ty1 = ty)
  ∨ Keyed.lookup name_eqb m (Typing_env.names_to_types tenv)
    = Some (ty1, btm1).
Proof.
  rewrite replace_equation_names_to_types.
  assert (Hcons :
    ∀ btm : Binding_time.With_name_mode.t,
      Keyed.lookup name_eqb m
        ((n, (ty, btm)) :: Typing_env.names_to_types tenv)
      = Some (ty1, btm1) ->
      (m = n ∧ ty1 = ty)
      ∨ Keyed.lookup name_eqb m (Typing_env.names_to_types tenv)
        = Some (ty1, btm1)).
  { intros btm. rewrite keyed_lookup_cons.
    destruct (keyed_eqb_spec name_eqb name_eqb_eq m n) as [Heq | Hne].
    - intros [= <- _]. left. split; [ exact Heq | reflexivity ].
    - intros Hlookup. right. exact Hlookup. }
  destruct n as [x | s]; [ | apply Hcons ].
  destruct (Keyed.lookup name_eqb (Name_var x)
              (Typing_env.names_to_types tenv)) as [[ty0 btm0] | ];
    [ apply Hcons | intros Hlookup; right; exact Hlookup ].
Qed.

Theorem replace_equation_frame : replace_equation_frame_statement.
Proof.
  intros tenv n ty. cbv zeta.
  repeat (split; [ reflexivity | ]).
  split; [ apply add_or_replace_equation_defined_vars | ].
  split; [ apply add_or_replace_equation_binding_times | ].
  repeat (split; [ reflexivity | ]).
  apply replace_equation_aliases.
Qed.

Theorem replace_equation_lookup_other
    : replace_equation_lookup_other_statement.
Proof.
  intros tenv n m ty Hne.
  rewrite replace_equation_names_to_types.
  destruct n as [x | s].
  - destruct (Keyed.lookup name_eqb (Name_var x)
                (Typing_env.names_to_types tenv)) as [[ty0 btm0] | ];
      [ | reflexivity ].
    apply (keyed_lookup_other name_eqb name_eqb_eq). exact Hne.
  - apply (keyed_lookup_other name_eqb name_eqb_eq). exact Hne.
Qed.

Theorem replace_equation_lookup : replace_equation_lookup_statement.
Proof.
  intros tenv n ty. rewrite replace_equation_names_to_types.
  destruct n as [x | s].
  - destruct (Keyed.lookup name_eqb (Name_var x)
                (Typing_env.names_to_types tenv))
      as [[ty0 btm0] | ] eqn:Hlookup.
    + apply (keyed_lookup_head name_eqb name_eqb_eq).
    + exact Hlookup.
  - apply (keyed_lookup_head name_eqb name_eqb_eq).
Qed.

Theorem replace_equation_satisfied : replace_equation_satisfied_statement.
Proof.
  intros exempt statics valuation tenv n ty [Hbottom [Htypes Hrespected]]
    Hty.
  split; [ exact Hbottom | ]. split.
  - intros m ty1 btm1 v Hlookup Hvalue.
    destruct (replace_equation_lookup_cases tenv n ty m ty1 btm1 Hlookup)
      as [[-> ->] | Hold].
    + exact (Hty v Hvalue).
    + exact (Htypes m ty1 btm1 v Hold Hvalue).
  - rewrite replace_equation_aliases. exact Hrespected.
Qed.

Theorem replace_equation_satisfied_inv
    : replace_equation_satisfied_inv_statement.
Proof.
  intros exempt statics valuation tenv n ty Hold
    [Hbottom [Htypes Hrespected]].
  split; [ exact Hbottom | ]. split.
  - intros m ty1 btm1 v Hlookup Hvalue.
    destruct (keyed_eqb_spec name_eqb name_eqb_eq m n) as [-> | Hne].
    + exact (Hold ty1 btm1 v Hlookup Hvalue).
    + apply (Htypes m ty1 btm1 v); [ | exact Hvalue ].
      rewrite (replace_equation_lookup_other tenv n m ty Hne).
      exact Hlookup.
  - rewrite replace_equation_aliases in Hrespected. exact Hrespected.
Qed.

(* ======================================================================== *)
(* Two canonical elements made aliases                                      *)
(* ======================================================================== *)

Theorem add_alias_satisfied : add_alias_satisfied_statement.
Proof.
  intros exempt statics valuation tenv c1 c2 result
    [Hbottom [Htypes Hrespected]] Hadd Hsame.
  destruct (add_alias_some tenv c1 c2 result Hadd) as [added [Hadded ->]].
  split; [ exact Hbottom | ]. split; [ exact Htypes | ].
  exact (add_respected _ _ _ _ c1 c2 added valuation Hadded Hrespected
           Hsame).
Qed.

Theorem add_alias_frame : add_alias_frame_statement.
Proof.
  intros tenv c1 c2 result Hadd. cbv zeta.
  unfold Typing_env.add_alias, Typing_env.aliases_add in Hadd.
  destruct (Aliases.add (Typing_env.binding_time_resolver tenv)
              (Typing_env.names_to_types tenv) (Typing_env.aliases tenv) c1
              c2) as [[added | ] | ] eqn:Hadded; try discriminate.
  injection Hadd as <-.
  split; [ | repeat split ].
  exists added. repeat split.
Qed.

Theorem add_alias_bottom : add_alias_bottom_statement.
Proof.
  intros valuation tenv c1 c2.
  unfold Typing_env.add_alias, Typing_env.aliases_add.
  destruct (Aliases.add _ _ _ c1 c2) as [[added | ] | ] eqn:Hadd;
    try discriminate.
  intros _. apply (proj1 (add_bottom _ _ _ _ c1 c2)) in Hadd.
  destruct Hadd as [k1 [k2 [-> [-> Hne]]]].
  simpl. intros [= Heq]. exact (Hne Heq).
Qed.

(* ======================================================================== *)
(* The machine and the static environment                                   *)
(* ======================================================================== *)

Theorem satisfied_but_statics_extend
    : satisfied_but_statics_extend_statement.
Proof.
  intros exempt statics statics' valuation tenv Hextend
    [Hbottom [Htypes Hrespected]].
  split; [ exact Hbottom | ]. split; [ | exact Hrespected ].
  intros n ty btm v Hlookup Hvalue.
  destruct (Htypes n ty btm v Hlookup Hvalue) as [Hexempt | Hty];
    [ left; exact Hexempt | right ].
  exact (type_satisfied_statics_extend statics statics' valuation v ty
           Hextend Hty).
Qed.

Theorem env_satisfies_strictly_statics_extend
    : env_satisfies_strictly_statics_extend_statement.
Proof.
  intros tenv statics statics' vars Hextend
    [Hbound [valuation [Hsatisfied Hagrees]]].
  split; [ exact Hbound | ]. exists valuation.
  split; [ | exact Hagrees ].
  exact (satisfied_but_statics_extend _ statics statics' valuation tenv
           Hextend Hsatisfied).
Qed.

(* A variable that is not bound is not in scope. *)
Lemma not_bound_not_in_scope (tenv : Typing_env.t) (x y : variable) :
  Typing_env.mem None tenv (Name_var x) = false ->
  in_scope_in_terms tenv y ->
  y <> x.
Proof.
  intros Hfresh Hscope ->. apply mem_fresh_lookup in Hfresh.
  apply in_scope_in_terms_lookup in Hscope.
  destruct Hscope as [ty [btm [Hlookup _]]]. congruence.
Qed.

Theorem env_satisfies_strictly_bind : env_satisfies_strictly_bind_statement.
Proof.
  intros tenv statics vars x v Hfresh.
  apply env_satisfies_strictly_coincide.
  intros y Hscope. symmetry. apply lookup_other.
  exact (not_bound_not_in_scope tenv x y Hfresh Hscope).
Qed.

Theorem env_satisfies_bind : env_satisfies_bind_statement.
Proof.
  intros tenv statics vars x v Hfresh.
  apply env_satisfies_coincide.
  intros y Hscope. symmetry. apply lookup_other.
  exact (not_bound_not_in_scope tenv x y Hfresh Hscope).
Qed.
