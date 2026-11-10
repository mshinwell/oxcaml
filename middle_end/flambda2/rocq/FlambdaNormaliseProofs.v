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

(* Proofs of the statements of FlambdaNormaliseSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Bool Arith.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaContextSpec FlambdaContextProofs FlambdaApplySpec
  FlambdaApplyProofs FlambdaNormaliseSpec.
Import ListNotations.

(* ======================================================================== *)
(* Names in scope                                                           *)
(* ======================================================================== *)

Lemma name_in_In (name : positive) (names : list positive) :
  name_in name names = true -> name ∈ names.
Proof.
  unfold name_in. intros Hin. apply existsb_exists in Hin.
  destruct Hin as (name' & Hin & Heq). apply Pos.eqb_eq in Heq.
  subst name'. exact Hin.
Qed.

Lemma simple_in_scope_sound (vs : list variable) (s : simple) (x : variable) :
  simple_in_scope vs s = true -> var_free_in_simple x s -> x ∈ vs.
Proof.
  destruct s as [y | sym | c]; simpl; try contradiction.
  intros Hin ->. apply name_in_In, Hin.
Qed.

Lemma simples_in_scope_sound (vs : list variable) (args : list simple)
    (x : variable) :
  simples_in_scope vs args = true -> var_free_in_simples x args -> x ∈ vs.
Proof.
  unfold simples_in_scope, var_free_in_simples. intros Hscope Hfree.
  apply Exists_exists in Hfree. destruct Hfree as (s & Hin & Hfree).
  rewrite forallb_forall in Hscope.
  exact (simple_in_scope_sound vs s x (Hscope s Hin) Hfree).
Qed.

Lemma value_slots_in_scope_sound (vs : list variable)
    (slots : list (value_slot * simple)) (x : variable) :
  forallb (fun slot => simple_in_scope vs (snd slot)) slots = true ->
  Exists (fun slot => var_free_in_simple x (snd slot)) slots ->
  x ∈ vs.
Proof.
  intros Hscope Hfree.
  apply Exists_exists in Hfree. destruct Hfree as (slot & Hin & Hfree).
  rewrite forallb_forall in Hscope.
  exact (simple_in_scope_sound vs (snd slot) x (Hscope slot Hin) Hfree).
Qed.

Lemma named_in_scope_sound (vs : list variable) (d : named) (x : variable) :
  named_in_scope vs d = true -> var_free_in_named x d -> x ∈ vs.
Proof.
  destruct d as [s | p args | code slots | slot closure]; simpl.
  - apply simple_in_scope_sound.
  - apply simples_in_scope_sound.
  - apply value_slots_in_scope_sound.
  - apply simple_in_scope_sound.
Qed.

Lemma static_binding_in_scope_sound (vs : list variable)
    (binding : static_binding) (x : variable) :
  static_binding_in_scope vs binding = true ->
  var_free_in_static_binding x binding ->
  x ∈ vs.
Proof.
  destruct binding
    as [id c | id | sym [code slots | tag fields | s | bytes]];
    simpl; try contradiction.
  - apply value_slots_in_scope_sound.
  - apply simples_in_scope_sound.
  - apply simple_in_scope_sound.
Qed.

Lemma lookup_none_not_in {A : Type} (name : positive)
    (bindings : list (positive * A)) :
  lookup name bindings = None -> name ∉ map fst bindings.
Proof.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ auto | ].
  destruct (Pos.eqb_spec name bound) as [-> | Hne]; [ discriminate | ].
  intros Hlookup [Heq | Hin]; [ congruence | exact (IH Hlookup Hin) ].
Qed.

(* What the check means: the free names of the expression are among those
   given. *)
Fixpoint expr_in_scope_sound (e : expr) :
  ∀ (vs : list variable) (ks : list continuation),
    expr_in_scope vs ks e = true ->
    (∀ x : variable, var_free_in_expr x e -> x ∈ vs)
    ∧ (∀ k : continuation, cont_free_in_expr k e -> k ∈ ks)
with handler_in_scope_sound (h : continuation_handler) :
  ∀ (vs : list variable) (ks : list continuation),
    handler_in_scope vs ks h = true ->
    (∀ x : variable, var_free_in_handler x h -> x ∈ vs)
    ∧ (∀ k : continuation, cont_free_in_handler k h -> k ∈ ks).
Proof.
  - destruct e
      as [ y d body | bindings body | k' h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros vs ks Hscope; simpl in Hscope.
    + (* Let *)
      apply andb_true_iff in Hscope as [Hd Hbody].
      destruct (expr_in_scope_sound body _ _ Hbody) as [Hvars Hconts].
      split; [ | exact Hconts ].
      intros x [Hx | [Hne Hx]];
        [ exact (named_in_scope_sound vs d x Hd Hx) | ].
      destruct (Hvars x Hx) as [Heq | Hin]; [ congruence | exact Hin ].
    + (* Let_static *)
      apply andb_true_iff in Hscope as [Hbindings Hbody].
      destruct (expr_in_scope_sound body _ _ Hbody) as [Hvars Hconts].
      split; [ | exact Hconts ].
      intros x [Hx | Hx]; [ | exact (Hvars x Hx) ].
      apply Exists_exists in Hx. destruct Hx as (binding & Hin & Hx).
      rewrite forallb_forall in Hbindings.
      exact (static_binding_in_scope_sound vs binding x
        (Hbindings binding Hin) Hx).
    + (* Let_cont_non_recursive *)
      apply andb_true_iff in Hscope as [Hh Hbody].
      destruct (handler_in_scope_sound h _ _ Hh) as [Hvars_h Hconts_h].
      destruct (expr_in_scope_sound body _ _ Hbody) as [Hvars Hconts].
      split.
      * intros x [Hx | Hx]; [ exact (Hvars_h x Hx) | exact (Hvars x Hx) ].
      * intros k [Hk | [Hne Hk]]; [ exact (Hconts_h k Hk) | ].
        destruct (Hconts k Hk) as [Heq | Hin]; [ congruence | exact Hin ].
    + (* Let_cont_recursive *)
      apply andb_true_iff in Hscope as [Hhandlers Hbody].
      destruct (expr_in_scope_sound body _ _ Hbody) as [Hvars Hconts].
      assert (Hin_handlers :
        (∀ x : variable,
          any_handler (var_free_in_handler x) handlers -> x ∈ vs)
        ∧ (∀ k : continuation,
            any_handler (cont_free_in_handler k) handlers ->
            k ∈ map fst handlers ++ ks)).
      { revert Hhandlers. generalize (map fst handlers ++ ks) as ks'.
        intros ks'. clear Hbody Hvars Hconts.
        induction handlers as [ | [k0 h] handlers IH]; simpl;
          [ intros _; split; intros ? [] | ].
        intros Hhandlers. apply andb_true_iff in Hhandlers as [Hh Hrest].
        destruct (handler_in_scope_sound h _ _ Hh) as [Hvars_h Hconts_h].
        destruct (IH Hrest) as [Hvars_rest Hconts_rest].
        split.
        - intros x [Hx | Hx];
            [ exact (Hvars_h x Hx) | exact (Hvars_rest x Hx) ].
        - intros k [Hk | Hk];
            [ exact (Hconts_h k Hk) | exact (Hconts_rest k Hk) ]. }
      destruct Hin_handlers as [Hvars_h Hconts_h].
      split.
      * intros x [Hx | Hx]; [ exact (Hvars_h x Hx) | exact (Hvars x Hx) ].
      * intros k [Hunbound Hk].
        assert (Hin : k ∈ map fst handlers ++ ks)
          by (destruct Hk as [Hk | Hk];
              [ exact (Hconts_h k Hk) | exact (Hconts k Hk) ]).
        apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [ | exact Hin ].
        destruct (lookup_none_not_in k handlers Hunbound Hin).
    + (* Apply *)
      apply andb_true_iff in Hscope as [Hscope Hexn].
      apply andb_true_iff in Hscope as [Hscope Hreturn].
      apply andb_true_iff in Hscope as [Hcallee Hargs].
      split.
      * intros x [Hx | Hx];
          [ exact (simple_in_scope_sound vs _ x Hcallee Hx)
          | exact (simples_in_scope_sound vs _ x Hargs Hx) ].
      * intros k [-> | ->]; apply name_in_In; assumption.
    + (* Apply_cont *)
      unfold apply_cont_in_scope in Hscope.
      apply andb_true_iff in Hscope as [Hk Hargs].
      split.
      * intros x Hx. exact (simples_in_scope_sound vs _ x Hargs Hx).
      * intros k ->. apply name_in_In, Hk.
    + (* Switch *)
      apply andb_true_iff in Hscope as [Hscrutinee Harms].
      rewrite forallb_forall in Harms.
      split.
      * intros x [Hx | Hx];
          [ exact (simple_in_scope_sound vs _ x Hscrutinee Hx) | ].
        apply Exists_exists in Hx. destruct Hx as (arm & Hin & Hx).
        specialize (Harms arm Hin). unfold apply_cont_in_scope in Harms.
        apply andb_true_iff in Harms as [_ Hargs].
        exact (simples_in_scope_sound vs _ x Hargs Hx).
      * intros k Hk. apply Exists_exists in Hk.
        destruct Hk as (arm & Hin & ->).
        specialize (Harms arm Hin). unfold apply_cont_in_scope in Harms.
        apply andb_true_iff in Harms as [Hk _]. apply name_in_In, Hk.
    + (* Invalid *)
      split; intros ? [].
  - destruct h as [params handler]. intros vs ks Hscope. simpl in Hscope.
    destruct (expr_in_scope_sound handler _ _ Hscope) as [Hvars Hconts].
    split; [ | exact Hconts ].
    intros x [Hnotin Hx]. destruct (in_app_or _ _ _ (Hvars x Hx)); tauto.
Qed.

(* ======================================================================== *)
(* Inlining direct calls of known code                                      *)
(* ======================================================================== *)

Lemma var_in_simples_sound (x : variable) (args : list simple) :
  var_free_in_simples x args -> var_in_simples x args = true.
Proof.
  unfold var_free_in_simples, var_in_simples. intros Hfree.
  apply Exists_exists in Hfree. destruct Hfree as (s & Hin & Hfree).
  apply existsb_exists. exists s. split; [ exact Hin | ].
  destruct s as [y | sym | c]; simpl in Hfree; try contradiction.
  subst y. apply Pos.eqb_refl.
Qed.

(* [inline_renaming] sends the continuations of the code to those of the
   call, and fixes the variables. *)
Lemma inline_renaming_spec (ret exn k k_exn : continuation) :
  ret <> exn ->
  k <> k_exn ->
  (∀ x : variable, rename_variable (inline_renaming ret exn k k_exn) x = x)
  ∧ rename_continuation (inline_renaming ret exn k k_exn) ret = k
  ∧ rename_continuation (inline_renaming ret exn k k_exn) exn = k_exn.
Proof.
  intros Hcode Hcall. split; [ reflexivity | ].
  unfold rename_continuation, inline_renaming. simpl. split.
  - assert (Hk : swap ret k ret = k)
      by (unfold swap; rewrite Pos.eqb_refl; reflexivity).
    rewrite Hk. unfold swap at 1.
    destruct (Pos.eqb_spec k (swap ret k exn)) as [Heq | _].
    + rewrite <- Hk in Heq at 1. apply swap_injective in Heq.
      contradiction.
    + destruct (Pos.eqb_spec k k_exn); [ contradiction | reflexivity ].
  - unfold swap at 1. rewrite Pos.eqb_refl. reflexivity.
Qed.

Lemma inlinable_b_sound (ap : apply_expr) (c : code) :
  inlinable_b ap c = true ->
  inlinable ap c
    (inline_renaming (code_return_continuation c) (code_exn_continuation c)
       (ap_continuation ap) (ap_exn_continuation ap)).
Proof.
  unfold inlinable_b. intros Hb.
  apply andb_true_iff in Hb as [Hb Harity].
  apply andb_true_iff in Hb as [Hb Hparams].
  apply andb_true_iff in Hb as [Hb Hmy_closure].
  apply andb_true_iff in Hb as [Hb Hcall].
  apply andb_true_iff in Hb as [Hscope Hcode].
  apply negb_true_iff, Pos.eqb_neq in Hcode.
  apply negb_true_iff, Pos.eqb_neq in Hcall.
  destruct (expr_in_scope_sound _ _ _ Hscope) as [Hvars Hconts].
  destruct (inline_renaming_spec _ _ _ _ Hcode Hcall)
    as (Hfix & Hret & Hexn).
  unfold inlinable.
  refine
    (conj _ (conj _ (conj Hfix (conj Hret (conj Hexn (conj _ (conj _ _))))))).
  - intros x Hx. destruct (Hvars x Hx) as [<- | Hin]; auto.
  - intros k Hk. destruct (Hconts k Hk) as [<- | [<- | []]]; auto.
  - intros Hfree. apply var_in_simples_sound in Hfree.
    apply negb_true_iff in Hmy_closure. congruence.
  - intros param Hin Hfree. apply var_in_simples_sound in Hfree.
    rewrite forallb_forall in Hparams. specialize (Hparams param Hin).
    apply negb_true_iff in Hparams. congruence.
  - apply Nat.eqb_eq, Harity.
Qed.

(* The static environment binds the code that is known. *)
Definition statics_know (known : list (code_id * code))
    (statics : static_env) : Prop :=
  ∀ (id : code_id) (c : code),
    lookup id known = Some c -> lookup id (static_code statics) = Some c.

Lemma eval_static_bindings_know (vars : env)
    (bindings : list static_binding) :
  ∀ (known : list (code_id * code)) (statics extended : static_env),
    statics_know known statics ->
    eval_static_bindings vars bindings statics = Some extended ->
    statics_know (codes_of bindings known) extended.
Proof.
  induction bindings as [ | binding bindings IH];
    intros known statics extended Hknow; simpl.
  - intros [= <-]. exact Hknow.
  - destruct binding as [id c | id | sym const].
    + apply IH. intros id' c'. simpl.
      destruct (Pos.eqb id' id); [ auto | apply Hknow ].
    + apply IH, Hknow.
    + destruct (eval_static_const vars const) as [allocated | ]; simpl;
        [ | discriminate ].
      apply IH. exact Hknow.
Qed.

Lemma inline_apply_refines (known : list (code_id * code)) (ap : apply_expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  statics_know known statics ->
  refines (State (Apply ap) vars conts statics)
    (State (inline_apply known ap) vars conts statics).
Proof.
  intros Hknow. unfold inline_apply.
  destruct (ap_call_kind ap) as [called | ] eqn:Hkind; [ | apply refines_refl ].
  destruct (lookup called known) as [c | ] eqn:Hlookup;
    [ | apply refines_refl ].
  destruct (inlinable_b ap c) eqn:Hinlinable; [ | apply refines_refl ].
  exact (inline ap called c _ vars conts statics Hkind
    (Hknow called c Hlookup) (inlinable_b_sound ap c Hinlinable)).
Qed.

(* Down the bodies, with the static environment binding what is known. *)
Lemma inline_calls_refines_knowing (e : expr) :
  ∀ (known : list (code_id * code)) (vars : env) (conts : cont_env)
    (statics : static_env),
    statics_know known statics ->
    refines (State e vars conts statics)
      (State (inline_calls known e) vars conts statics).
Proof.
  induction e
    as [ x d body IH | bindings body IH | k h body IH | handlers body IH
       | ap | ac | scrutinee arms | ];
    intros known vars conts statics Hknow; simpl;
    try apply refines_refl.
  - destruct (eval_named statics vars d) as [v | ] eqn:Hd.
    + eapply refines_step;
        [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity
        | apply IH, Hknow ].
    + apply goes_wrong_refines. exists 1. simpl. rewrite Hd. reflexivity.
  - destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hbindings.
    + eapply refines_step;
        [ simpl; rewrite Hbindings; reflexivity
        | simpl; rewrite Hbindings; reflexivity | ].
      apply IH.
      exact (eval_static_bindings_know vars bindings known statics extended
        Hknow Hbindings).
    + apply goes_wrong_refines. exists 1. simpl. rewrite Hbindings.
      reflexivity.
  - eapply refines_step; [ reflexivity | reflexivity | apply IH, Hknow ].
  - eapply refines_step; [ reflexivity | reflexivity | apply IH, Hknow ].
  - apply inline_apply_refines, Hknow.
Qed.

Theorem inline_calls_refines : inline_calls_refines_statement.
Proof.
  intros e vars conts statics. apply inline_calls_refines_knowing.
  intros id c Hlookup. discriminate Hlookup.
Qed.

(* ======================================================================== *)
(* Removing unused [Let]s                                                   *)
(* ======================================================================== *)

Lemma var_in_simple_sound (x : variable) (s : simple) :
  var_free_in_simple x s -> var_in_simple x s = true.
Proof.
  destruct s as [y | sym | c]; simpl; try contradiction.
  intros ->. apply Pos.eqb_refl.
Qed.

Lemma var_in_value_slots_sound (x : variable)
    (slots : list (value_slot * simple)) :
  Exists (fun slot => var_free_in_simple x (snd slot)) slots ->
  var_in_value_slots x slots = true.
Proof.
  intros Hfree. apply Exists_exists in Hfree.
  destruct Hfree as (slot & Hin & Hfree). apply existsb_exists.
  exists slot. split; [ exact Hin | apply var_in_simple_sound, Hfree ].
Qed.

Lemma var_in_named_sound (x : variable) (d : named) :
  var_free_in_named x d -> var_in_named x d = true.
Proof.
  destruct d as [s | p args | code slots | slot closure]; simpl.
  - apply var_in_simple_sound.
  - apply var_in_simples_sound.
  - apply var_in_value_slots_sound.
  - apply var_in_simple_sound.
Qed.

Lemma var_in_static_binding_sound (x : variable) (binding : static_binding) :
  var_free_in_static_binding x binding ->
  var_in_static_binding x binding = true.
Proof.
  destruct binding
    as [id c | id | sym [code slots | tag fields | s | bytes]];
    simpl; try contradiction.
  - apply var_in_value_slots_sound.
  - apply var_in_simples_sound.
  - apply var_in_simple_sound.
Qed.

Lemma name_in_complete (name : positive) (names : list positive) :
  name ∈ names -> name_in name names = true.
Proof.
  intros Hin. apply existsb_exists. exists name.
  split; [ exact Hin | apply Pos.eqb_refl ].
Qed.

(* The test says yes of every variable that is free. *)
Fixpoint var_free_b_sound (x : variable) (e : expr) {struct e} :
  var_free_in_expr x e -> var_free_b x e = true
with var_free_in_handler_b_sound (x : variable) (h : continuation_handler)
    {struct h} :
  var_free_in_handler x h -> var_free_in_handler_b x h = true.
Proof.
  - destruct e
      as [ y d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl.
    + intros [Hx | [Hne Hx]]; apply orb_true_iff;
        [ left; apply var_in_named_sound, Hx | right ].
      apply andb_true_iff. split.
      * apply negb_true_iff, Pos.eqb_neq, Hne.
      * apply (var_free_b_sound x body), Hx.
    + intros [Hx | Hx]; apply orb_true_iff;
        [ left | right; apply (var_free_b_sound x body), Hx ].
      apply Exists_exists in Hx. destruct Hx as (binding & Hin & Hx).
      apply existsb_exists. exists binding.
      split; [ exact Hin | apply var_in_static_binding_sound, Hx ].
    + intros [Hx | Hx]; apply orb_true_iff;
        [ left; apply (var_free_in_handler_b_sound x h), Hx
        | right; apply (var_free_b_sound x body), Hx ].
    + intros [Hx | Hx]; apply orb_true_iff;
        [ left | right; apply (var_free_b_sound x body), Hx ].
      induction handlers as [ | [k h] handlers IH]; simpl in Hx |- *;
        [ contradiction | ].
      apply orb_true_iff. destruct Hx as [Hx | Hx];
        [ left; apply (var_free_in_handler_b_sound x h), Hx
        | right; exact (IH Hx) ].
    + intros [Hx | Hx]; apply orb_true_iff;
        [ left; apply var_in_simple_sound, Hx
        | right; apply var_in_simples_sound, Hx ].
    + apply var_in_simples_sound.
    + intros [Hx | Hx]; apply orb_true_iff;
        [ left; apply var_in_simple_sound, Hx | right ].
      apply Exists_exists in Hx. destruct Hx as (arm & Hin & Hx).
      apply existsb_exists. exists arm.
      split; [ exact Hin | apply var_in_simples_sound, Hx ].
    + contradiction.
  - destruct h as [params handler]. simpl. intros [Hnotin Hx].
    apply andb_true_iff. split.
    + apply negb_true_iff. destruct (name_in x params) eqn:Hin;
        [ | reflexivity ].
      apply name_in_In in Hin. contradiction.
    + apply (var_free_b_sound x handler), Hx.
Qed.

Lemma expr_refines_trans (e e' e'' : expr) :
  expr_refines e e' -> expr_refines e' e'' -> expr_refines e e''.
Proof.
  intros H H' vars conts statics.
  exact (refines_trans _ _ _ (H vars conts statics) (H' vars conts statics)).
Qed.

Lemma expr_refines_refl (e : expr) : expr_refines e e.
Proof. intros vars conts statics. apply refines_refl. Qed.

(* Each layer is a context around what the induction gives; a [Let] whose
   variable the test finds unused then goes. *)
Fixpoint remove_unused_lets_refines_aux (e : expr) :
  expr_refines e (remove_unused_lets e)
with remove_unused_lets_in_handler_refines (h : continuation_handler) :
  ∀ (k : continuation) (body : expr),
    expr_refines (Let_cont_non_recursive k h body)
      (Let_cont_non_recursive k (remove_unused_lets_in_handler h) body).
Proof.
  - destruct e
      as [ x d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try apply expr_refines_refl.
    + pose proof (plug_refines (Let_body x d Hole) _ _
        (remove_unused_lets_refines_aux body)) as Hbody.
      simpl in Hbody.
      destruct (var_free_b x (remove_unused_lets body)) eqn:Hfree;
        [ exact Hbody | ].
      apply (expr_refines_trans _ _ _ Hbody), unused_let.
      intros Hx. apply var_free_b_sound in Hx. congruence.
    + exact (plug_refines (Let_static_body bindings Hole) _ _
        (remove_unused_lets_refines_aux body)).
    + apply (expr_refines_trans _ _ _
        (remove_unused_lets_in_handler_refines h k body)).
      exact (plug_refines
        (Let_cont_non_recursive_body k (remove_unused_lets_in_handler h)
           Hole)
        _ _ (remove_unused_lets_refines_aux body)).
    + exact (plug_refines (Let_cont_recursive_body handlers Hole) _ _
        (remove_unused_lets_refines_aux body)).
  - destruct h as [params handler]. intros k body. simpl.
    exact (plug_refines (Let_cont_non_recursive_handler k params Hole body)
      _ _ (remove_unused_lets_refines_aux handler)).
Qed.

Theorem remove_unused_lets_refines : remove_unused_lets_refines_statement.
Proof. exact remove_unused_lets_refines_aux. Qed.
