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
  FlambdaWellFormedSpec
  FlambdaSemanticsProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaControlFlowSpec FlambdaControlFlowProofs FlambdaContextSpec
  FlambdaContextProofs FlambdaApplySpec FlambdaApplyProofs
  FlambdaStaticSpec FlambdaStaticProofs FlambdaNormaliseSpec.
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
  apply andb_true_iff in Hb as [Hb Hstatic].
  apply negb_true_iff in Hstatic.
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
    (conj _
       (conj _
          (conj Hfix
             (conj Hret (conj Hexn (conj _ (conj _ (conj _ Hstatic)))))))).
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
    + destruct (lookup id (static_code statics)); [ discriminate | ].
      apply IH. intros id' c'. simpl.
      destruct (Pos.eqb id' id); [ auto | apply Hknow ].
    + apply IH, Hknow.
    + destruct (lookup sym (static_values statics)); [ discriminate | ].
      destruct (eval_static_const vars const) as [allocated | ]; simpl;
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

Lemma statics_know_extend (known : list (code_id * code))
    (statics statics' : static_env) :
  statics_know known statics -> statics_extend statics statics' ->
  statics_know known statics'.
Proof. intros Hknow [Hcode _] id c Hid. apply Hcode, Hknow, Hid. Qed.

(* Handlers that refine each other's counterparts where they run, in the
   two forms that FlambdaContextProofs.related_envs_refines asks for. *)
Definition handlers_refine (ok : static_env -> Prop) (vars : env)
    (handlers handlers' : list (continuation * continuation_handler))
    : Prop :=
  handlers_related (handler_refines_where ok) vars handlers handlers'
  ∧ handlers_related
      (fun params def_vars target source =>
         handler_refines_where ok params def_vars source target)
      vars handlers' handlers.

(* Inlining leaves what binds something static as it is: what is inlined
   binds nothing. *)
Lemma let_params_binds_statics (params : list variable) :
  ∀ (args : list simple) (body : expr),
    binds_statics (let_params params args body) = binds_statics body.
Proof.
  induction params as [ | param params IH]; intros [ | arg args] body; simpl;
    auto.
Qed.

Lemma inlined_body_binds_statics (c : code) (r : renaming) (ap : apply_expr) :
  binds_statics (inlined_body c r ap) = binds_statics (code_body c).
Proof.
  unfold inlined_body. simpl. rewrite let_params_binds_statics.
  apply rename_binds_statics.
Qed.

Lemma inlinable_b_binds_statics (ap : apply_expr) (c : code) :
  inlinable_b ap c = true -> binds_statics (code_body c) = false.
Proof.
  unfold inlinable_b. intros Hb. apply andb_true_iff in Hb as [_ Hstatic].
  apply negb_true_iff, Hstatic.
Qed.

Lemma inline_apply_binds_statics (known : list (code_id * code))
    (ap : apply_expr) :
  binds_statics (inline_apply known ap) = false.
Proof.
  unfold inline_apply.
  destruct (ap_call_kind ap) as [called | ]; [ | reflexivity ].
  destruct (lookup called known) as [c | ]; [ | reflexivity ].
  destruct (inlinable_b ap c) eqn:Hinlinable; [ | reflexivity ].
  rewrite inlined_body_binds_statics.
  exact (inlinable_b_binds_statics ap c Hinlinable).
Qed.

Fixpoint inline_calls_binds_statics (e : expr) :
  ∀ known : list (code_id * code),
    binds_statics (inline_calls known e) = binds_statics e.
Proof.
  destruct e
    as [ x d body | bindings body | k h body | handlers body
       | ap | ac | scrutinee arms | ];
    intros known; simpl; try reflexivity.
  - apply inline_calls_binds_statics.
  - rewrite inline_calls_binds_statics. reflexivity.
  - destruct h as [params handler]. simpl.
    rewrite !inline_calls_binds_statics. reflexivity.
  - rewrite inline_calls_binds_statics. f_equal.
    induction handlers as [ | [k [params handler]] handlers IH]; simpl;
      [ reflexivity | ].
    rewrite inline_calls_binds_statics, IH. reflexivity.
  - apply inline_apply_binds_statics.
Qed.

Lemma inline_calls_handlers_bind_statics (known : list (code_id * code))
    (handlers : list (continuation * continuation_handler)) :
  handlers_bind_statics
    (map (fun '(k, h) => (k, inline_calls_in_handler known h)) handlers)
  = handlers_bind_statics handlers.
Proof.
  unfold handlers_bind_statics.
  induction handlers as [ | [k [params handler]] handlers IH]; simpl;
    [ reflexivity | ].
  rewrite inline_calls_binds_statics, IH. reflexivity.
Qed.

(* Down the term, with the static environment binding what is known: at
   once in a body, and from then on in a handler. *)
Fixpoint inline_calls_refines_knowing (e : expr) :
  ∀ (known : list (code_id * code)) (vars : env) (conts : cont_env)
    (statics : static_env),
    statics_know known statics ->
    refines (State e vars conts statics)
      (State (inline_calls known e) vars conts statics).
Proof.
  - destruct e
      as [ x d body | bindings body | k h body | handlers body
         | ap | ac | scrutinee arms | ];
      intros known vars conts statics Hknow; simpl;
      try apply refines_refl.
    + destruct (eval_named statics vars d) as [v | ] eqn:Hd.
      * eapply refines_step;
          [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity
          | apply inline_calls_refines_knowing, Hknow ].
      * apply goes_wrong_refines. exists 1. simpl. rewrite Hd. reflexivity.
    + destruct (eval_static_bindings vars bindings statics) as [extended | ]
        eqn:Hbindings.
      * eapply refines_step;
          [ simpl; rewrite Hbindings; reflexivity
          | simpl; rewrite Hbindings; reflexivity | ].
        apply inline_calls_refines_knowing.
        exact (eval_static_bindings_know vars bindings known statics extended
          Hknow Hbindings).
      * apply goes_wrong_refines. exists 1. simpl. rewrite Hbindings.
        reflexivity.
    + destruct h as [params handler]. simpl.
      apply (refines_trans _
        (State
           (Let_cont_non_recursive k
              (Handler params (inline_calls known handler)) body)
           vars conts statics)).
      * apply (let_cont_handler_refines_where (statics_know known)
          (statics_know_extend known)); [ exact Hknow | ].
        intros vs handler_vars conts' statics' Hknow' _.
        apply inline_calls_refines_knowing, Hknow'.
      * eapply refines_step;
          [ reflexivity | reflexivity
          | apply inline_calls_refines_knowing, Hknow ].
    + apply (refines_trans _
        (State
           (Let_cont_recursive
              (map (fun '(k, h) => (k, inline_calls_in_handler known h))
                 handlers)
              body)
           vars conts statics)).
      * assert (Hhandlers :
          handlers_refine (statics_know known) vars handlers
            (map (fun '(k, h) => (k, inline_calls_in_handler known h))
               handlers)).
        { induction handlers as [ | [k [params handler]] handlers IH]; simpl.
          - split; apply Forall2_nil.
          - destruct IH as [Hforwards Hbackwards].
            split; (apply Forall2_cons; [ | assumption ]);
              (split; [ reflexivity | ]); apply Handler_related;
              intros vs handler_vars conts' statics' Hknow' _;
              apply inline_calls_refines_knowing, Hknow'. }
        destruct Hhandlers as [Hforwards Hbackwards].
        apply (let_cont_recursive_handlers_refine_where (statics_know known)
          (statics_know_extend known));
          try assumption.
        symmetry. apply inline_calls_handlers_bind_statics.
      * apply let_cont_recursive_refines_step; [ reflexivity | intros _ ].
        apply inline_calls_refines_knowing, Hknow.
    + apply inline_apply_refines, Hknow.
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
    + pose proof (plug_refines (Let_body x d Hole) _ _ (not_many _)
        (remove_unused_lets_refines_aux body)) as Hbody.
      simpl in Hbody.
      destruct
        (var_free_b x (remove_unused_lets body) || negb (named_may_go d))
        eqn:Hkeep; [ exact Hbody | ].
      apply orb_false_iff in Hkeep as [Hfree _].
      apply (expr_refines_trans _ _ _ Hbody), unused_let.
      intros Hx. apply var_free_b_sound in Hx. congruence.
    + exact (plug_refines (Let_static_body bindings Hole) _ _ (not_many _)
        (remove_unused_lets_refines_aux body)).
    + apply (expr_refines_trans _ _ _
        (remove_unused_lets_in_handler_refines h k body)).
      exact (plug_refines
        (Let_cont_non_recursive_body k (remove_unused_lets_in_handler h)
           Hole)
        _ _ (not_many _) (remove_unused_lets_refines_aux body)).
    + exact (plug_refines (Let_cont_recursive_body handlers Hole)
          _ _ (not_many _)
        (remove_unused_lets_refines_aux body)).
  - destruct h as [params handler]. intros k body. simpl.
    exact (plug_refines (Let_cont_non_recursive_handler k params Hole body)
      _ _ (not_many _) (remove_unused_lets_refines_aux handler)).
Qed.

Theorem remove_unused_lets_refines : remove_unused_lets_refines_statement.
Proof. exact remove_unused_lets_refines_aux. Qed.

(* ======================================================================== *)
(* A continuation applied once, at the end of its scope                     *)
(* ======================================================================== *)

Lemma bind_params_defined (params : list variable) :
  ∀ (vs : list value) (vars vars' bound : env),
    bind_params params vs vars = Some bound ->
    ∃ bound' : env, bind_params params vs vars' = Some bound'.
Proof.
  induction params as [ | p params IH]; intros [ | v vs] vars vars' bound;
    simpl; try discriminate; [ eauto | ].
  apply IH.
Qed.

(* Binding the same parameters under environments that agree at a variable
   gives environments that agree at it; and at every parameter. *)
Lemma bind_params_agree (params : list variable) :
  ∀ (vs : list value) (vars vars' bound bound' : env),
    bind_params params vs vars = Some bound ->
    bind_params params vs vars' = Some bound' ->
    ∀ x : variable,
      x ∈ params ∨ lookup x vars' = lookup x vars ->
      lookup x bound' = lookup x bound.
Proof.
  induction params as [ | p params IH];
    intros [ | v vs] vars vars' bound bound'; simpl; try discriminate.
  - intros [= <-] [= <-] x [[] | Hagree]. exact Hagree.
  - intros Hbind Hbind' x Hx. apply (IH vs _ _ _ _ Hbind Hbind'). simpl.
    destruct (Pos.eqb_spec x p) as [-> | Hne]; [ right; reflexivity | ].
    destruct Hx as [[Heq | Hin] | Hagree];
      [ congruence | left; exact Hin | right; exact Hagree ].
Qed.

(* The body under the binding of [k], against the body with the handler in
   place: the [Let]s run alike; then the one applies [k] and the other
   binds the parameters and goes on, to the handler under environments
   that agree on its free variables. *)
Lemma inline_cont_at_tail_refines (k : continuation) (params : list variable)
    (handler : expr) (body : expr) :
  ∀ inlined : expr,
    inline_cont_at_tail k params handler body = Some inlined ->
    ∀ (vars def_vars : env) (conts : cont_env) (statics : static_env),
      (∀ x : variable,
        var_free_in_handler x (Handler params handler) ->
        lookup x vars = lookup x def_vars) ->
      refines
        (State body vars
           ((k, Closure (Handler params handler) def_vars conts []) :: conts)
           statics)
        (State inlined vars conts statics).
Proof.
  induction body
    as [ x d body IH | bindings body IH | k' h body IH | handlers body IH
       | ap | ac | scrutinee arms | ];
    intros inlined Heq vars def_vars conts statics Hagree; simpl in Heq;
    try discriminate.
  - (* Let *)
    match type of Heq with
    | context [if ?free then _ else _] => destruct free eqn:Hfree
    end;
      [ discriminate | ].
    change (var_free_in_handler_b x (Handler params handler) = false)
      in Hfree.
    destruct (inline_cont_at_tail k params handler body) as [body' | ];
      [ | discriminate ].
    simpl in Heq. injection Heq as <-.
    destruct (eval_named statics vars d) as [v | ] eqn:Hd.
    + eapply refines_step;
        [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity | ].
      apply (IH body' eq_refl). intros y Hy. simpl.
      destruct (Pos.eqb_spec y x) as [-> | _]; [ | exact (Hagree y Hy) ].
      apply var_free_in_handler_b_sound in Hy. congruence.
    + apply goes_wrong_refines. exists 1. simpl. rewrite Hd. reflexivity.
  - (* Let_static *)
    destruct (inline_cont_at_tail k params handler body) as [body' | ];
      [ | discriminate ].
    simpl in Heq. injection Heq as <-.
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hbindings.
    + eapply refines_step;
        [ simpl; rewrite Hbindings; reflexivity
        | simpl; rewrite Hbindings; reflexivity | ].
      exact (IH body' eq_refl vars def_vars conts extended Hagree).
    + apply goes_wrong_refines. exists 1. simpl. rewrite Hbindings.
      reflexivity.
  - (* Apply_cont *)
    destruct
      (Pos.eqb (ac_continuation ac) k
       && Nat.eqb (length params) (length (ac_args ac))
       && forallb (fun param => negb (var_in_simples param (ac_args ac)))
            params)
      eqn:Hcheck; [ | discriminate ].
    injection Heq as <-.
    apply andb_true_iff in Hcheck as [Hcheck Hcapture].
    apply andb_true_iff in Hcheck as [Hk _]. apply Pos.eqb_eq in Hk.
    assert (Hwrong :
      step
        (State (Apply_cont ac) vars
           ((k, Closure (Handler params handler) def_vars conts []) :: conts)
           statics)
      = Undefined ->
      refines
        (State (Apply_cont ac) vars
           ((k, Closure (Handler params handler) def_vars conts []) :: conts)
           statics)
        (State (let_params params (ac_args ac) handler) vars conts statics)).
    { intros Hstep. apply goes_wrong_refines. exists 1. unfold run.
      rewrite Hstep. reflexivity. }
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hargs;
      [ | apply Hwrong; simpl; rewrite Hargs; reflexivity ].
    destruct (bind_params params vs def_vars) as [handler_vars | ] eqn:Hbind;
      [ | apply Hwrong; simpl; rewrite Hargs, Hk;
          unfold apply_continuation, resolve; simpl; rewrite Pos.eqb_refl;
          simpl; rewrite Hbind; reflexivity ].
    destruct (bind_params_defined params vs def_vars vars handler_vars Hbind)
      as [bound Hbound].
    destruct (let_params_run params (ac_args ac) vs vars bound handler conts
                statics Hargs)
      as [n Hrun]; [ | exact Hbound | ].
    { intros param Hin Hfree. apply var_in_simples_sound in Hfree.
      rewrite forallb_forall in Hcapture. specialize (Hcapture param Hin).
      apply negb_true_iff in Hcapture. congruence. }
    apply equivalent_refines.
    apply (equivalent_trans _ (State handler handler_vars conts statics)).
    { apply step_equivalent. simpl. rewrite Hargs, Hk.
      unfold apply_continuation, resolve. simpl. rewrite Pos.eqb_refl.
      simpl. rewrite Hbind. reflexivity. }
    apply (equivalent_trans _ (State handler bound conts statics)).
    { apply coincide_equivalent.
      - intros x Hx.
        apply (bind_params_agree params vs def_vars vars handler_vars bound
          Hbind Hbound).
        destruct (in_dec Pos.eq_dec x params) as [Hin | Hnotin];
          [ left; exact Hin | right ].
        apply Hagree. split; assumption.
      - intros k' _. apply (conts_agree_same identity_renaming). reflexivity. }
    apply equivalent_sym, (equivalent_of_run n 0). exact Hrun.
Qed.

(* Each layer is a context around what the induction gives; then the
   handler goes into the body where that ends by applying it. *)
Fixpoint inline_tail_conts_refines_aux (e : expr) :
  expr_refines e (inline_tail_conts e).
Proof.
  destruct e
    as [ x d body | bindings body | k [params handler] body | handlers body
       | ap | ac | scrutinee arms | ];
    simpl; try apply expr_refines_refl.
  - exact (plug_refines (Let_body x d Hole) _ _ (not_many _)
      (inline_tail_conts_refines_aux body)).
  - exact (plug_refines (Let_static_body bindings Hole) _ _ (not_many _)
      (inline_tail_conts_refines_aux body)).
  - assert (Hlayers :
      expr_refines (Let_cont_non_recursive k (Handler params handler) body)
        (Let_cont_non_recursive k
           (Handler params (inline_tail_conts handler))
           (inline_tail_conts body))).
    { apply (expr_refines_trans _
        (Let_cont_non_recursive k
           (Handler params (inline_tail_conts handler)) body)).
      - exact (plug_refines
          (Let_cont_non_recursive_handler k params Hole body) _ _ (not_many _)
          (inline_tail_conts_refines_aux handler)).
      - exact (plug_refines
          (Let_cont_non_recursive_body k
             (Handler params (inline_tail_conts handler)) Hole)
          _ _ (not_many _) (inline_tail_conts_refines_aux body)). }
    destruct
      (inline_cont_at_tail k params (inline_tail_conts handler)
         (inline_tail_conts body))
      as [inlined | ] eqn:Hinline; [ | exact Hlayers ].
    apply (expr_refines_trans _ _ _ Hlayers). intros vars conts statics.
    eapply refines_trans;
      [ apply equivalent_refines, step_equivalent; reflexivity | ].
    apply (inline_cont_at_tail_refines k params _ _ inlined Hinline).
    intros x _. reflexivity.
  - exact (plug_refines (Let_cont_recursive_body handlers Hole) _ _ (not_many _)
      (inline_tail_conts_refines_aux body)).
Qed.

Theorem inline_tail_conts_refines : inline_tail_conts_refines_statement.
Proof. exact inline_tail_conts_refines_aux. Qed.

(* ======================================================================== *)
(* Bindings of deleted code                                                 *)
(* ======================================================================== *)

Lemma expr_equivalent_trans (e e' e'' : expr) :
  expr_equivalent e e' -> expr_equivalent e' e'' -> expr_equivalent e e''.
Proof.
  intros H H' vars conts statics.
  exact (equivalent_trans _ _ _ (H vars conts statics)
    (H' vars conts statics)).
Qed.

Lemma eval_static_bindings_filter (vars : env)
    (bindings : list static_binding) :
  ∀ statics : static_env,
    eval_static_bindings vars (filter binds_something bindings) statics
    = eval_static_bindings vars bindings statics.
Proof.
  induction bindings as [ | binding bindings IH]; intros statics;
    [ reflexivity | ].
  destruct binding as [id c | id | sym const]; simpl.
  - destruct (lookup id (static_code statics)); [ reflexivity | apply IH ].
  - apply IH.
  - destruct (lookup sym (static_values statics)); [ reflexivity | ].
    destruct (eval_static_const vars const); simpl;
      [ apply IH | reflexivity ].
Qed.

(* A group and the group without its bindings of deleted code, the
   [Let_static] itself going if nothing is left. *)
Lemma let_static_if_any_equivalent (bindings : list static_binding)
    (body : expr) :
  expr_equivalent (Let_static bindings body)
    (let_static_if_any (filter binds_something bindings) body).
Proof.
  intros vars conts statics.
  destruct (filter binds_something bindings) as [ | binding kept] eqn:Hkept;
    simpl.
  - apply step_equivalent. simpl.
    rewrite <- (eval_static_bindings_filter vars bindings statics), Hkept.
    reflexivity.
  - apply (equivalent_of_run 1 1). simpl.
    rewrite <- (eval_static_bindings_filter vars bindings statics), Hkept.
    reflexivity.
Qed.

Fixpoint drop_deleted_code_equivalent_aux (e : expr) :
  expr_equivalent e (drop_deleted_code e).
Proof.
  destruct e
    as [ x d body | bindings body | k [params handler] body | handlers body
       | ap | ac | scrutinee arms | ];
    simpl; try (intros vars conts statics; apply equivalent_refl).
  - exact (plug_equivalent (Let_body x d Hole) _ _ (not_many _)
      (drop_deleted_code_equivalent_aux body)).
  - apply (expr_equivalent_trans _
      (Let_static bindings (drop_deleted_code body))).
    + exact (plug_equivalent (Let_static_body bindings Hole) _ _ (not_many _)
        (drop_deleted_code_equivalent_aux body)).
    + apply let_static_if_any_equivalent.
  - apply (expr_equivalent_trans _
      (Let_cont_non_recursive k
         (Handler params (drop_deleted_code handler)) body)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_handler k params Hole body) _ _ (not_many _)
        (drop_deleted_code_equivalent_aux handler)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_body k
           (Handler params (drop_deleted_code handler)) Hole)
        _ _ (not_many _) (drop_deleted_code_equivalent_aux body)).
  - exact (plug_equivalent (Let_cont_recursive_body handlers Hole)
        _ _ (not_many _)
      (drop_deleted_code_equivalent_aux body)).
Qed.

Theorem drop_deleted_code_equivalent : drop_deleted_code_equivalent_statement.
Proof. exact drop_deleted_code_equivalent_aux. Qed.

(* ======================================================================== *)
(* Folding constants                                                        *)
(* ======================================================================== *)

Lemma consts_of_simples_eval (vars : env) (args : list simple) :
  ∀ cs : list const,
    consts_of_simples args = Some cs ->
    eval_simples vars args = Some (map Value_const cs).
Proof.
  induction args as [ | [x | sym | c] args IH]; intros cs; simpl;
    try discriminate.
  - intros [= <-]. reflexivity.
  - destruct (consts_of_simples args) as [cs' | ]; [ | discriminate ].
    simpl. intros [= <-]. rewrite (IH cs' eq_refl). reflexivity.
Qed.

(* The value is the one the primitive has. *)
Lemma fold_named_sound (statics : static_env) (vars : env) (d : named) :
  eval_named statics vars (fold_named d) = eval_named statics vars d.
Proof.
  destruct d as [s | p args | code slots | slot closure]; simpl;
    try reflexivity.
  destruct (prim_may_fold p); [ | reflexivity ].
  destruct (consts_of_simples args) as [cs | ] eqn:Hconsts; [ | reflexivity ].
  destruct (eval_prim p (map Value_const cs)) as [[c | code slots | sym] | ]
    eqn:Hprim;
    try reflexivity.
  simpl. rewrite (consts_of_simples_eval vars args cs Hconsts). simpl.
  rewrite Hprim. reflexivity.
Qed.

Lemma fold_switch_equivalent (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  expr_equivalent (Switch scrutinee arms) (fold_switch scrutinee arms).
Proof.
  unfold fold_switch.
  destruct scrutinee as [x | sym | [i | | | | | | | | | | | | | | ]];
    try (intros vars conts statics; apply equivalent_refl).
  destruct (find_arm i arms) as [ac | ] eqn:Hfind;
    [ | intros vars conts statics; apply equivalent_refl ].
  exact (switch_const i arms ac Hfind).
Qed.

Fixpoint fold_constants_equivalent_aux (e : expr) :
  expr_equivalent e (fold_constants e).
Proof.
  destruct e
    as [ x d body | bindings body | k [params handler] body | handlers body
       | ap | ac | scrutinee arms | ];
    simpl; try (intros vars conts statics; apply equivalent_refl).
  - apply (expr_equivalent_trans _ (Let x (fold_named d) body)).
    + intros vars conts statics. apply (equivalent_of_run 1 1). simpl.
      rewrite fold_named_sound. reflexivity.
    + exact (plug_equivalent (Let_body x (fold_named d) Hole) _ _ (not_many _)
        (fold_constants_equivalent_aux body)).
  - exact (plug_equivalent (Let_static_body bindings Hole) _ _ (not_many _)
      (fold_constants_equivalent_aux body)).
  - apply (expr_equivalent_trans _
      (Let_cont_non_recursive k (Handler params (fold_constants handler))
         body)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_handler k params Hole body) _ _ (not_many _)
        (fold_constants_equivalent_aux handler)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_body k
           (Handler params (fold_constants handler)) Hole)
        _ _ (not_many _) (fold_constants_equivalent_aux body)).
  - exact (plug_equivalent (Let_cont_recursive_body handlers Hole)
        _ _ (not_many _)
      (fold_constants_equivalent_aux body)).
  - apply fold_switch_equivalent.
Qed.

Theorem fold_constants_equivalent : fold_constants_equivalent_statement.
Proof. exact fold_constants_equivalent_aux. Qed.

(* ======================================================================== *)
(* Removing unused [Let]s whose defining expression always has a value     *)
(* ======================================================================== *)

(* The defining expression has a value, so the [Let] takes its step; the
   body does not look at the variable. *)
Lemma unused_total_let (x : variable) (d : named) (body : expr) :
  named_is_total d = true ->
  ~ var_free_in_expr x body ->
  expr_equivalent (Let x d body) body.
Proof.
  intros Htotal Hunused vars conts statics.
  assert (Hvalue : ∃ v : value, eval_named statics vars d = Some v).
  { destruct d as [[y | sym | c] | p args | code slots | slot closure];
      simpl in Htotal; try discriminate; simpl; eauto. }
  destruct Hvalue as [v Hd].
  apply (equivalent_trans _ (State body ((x, v) :: vars) conts statics));
    [ apply step_equivalent; simpl; rewrite Hd; reflexivity | ].
  apply coincide_equivalent.
  - intros y Hy. simpl.
    destruct (Pos.eqb_spec y x) as [-> | _]; [ contradiction | reflexivity ].
  - intros k _. apply (conts_agree_same identity_renaming). reflexivity.
Qed.

Fixpoint remove_unused_total_lets_equivalent_aux (e : expr) :
  expr_equivalent e (remove_unused_total_lets e).
Proof.
  destruct e
    as [ x d body | bindings body | k [params handler] body | handlers body
       | ap | ac | scrutinee arms | ];
    simpl; try (intros vars conts statics; apply equivalent_refl).
  - pose proof (plug_equivalent (Let_body x d Hole) _ _ (not_many _)
      (remove_unused_total_lets_equivalent_aux body)) as Hbody.
    simpl in Hbody.
    destruct
      (named_is_total d && negb (var_free_b x (remove_unused_total_lets body)))
      eqn:Hremove; [ | exact Hbody ].
    apply andb_true_iff in Hremove as [Htotal Hunused].
    apply negb_true_iff in Hunused.
    apply (expr_equivalent_trans _ _ _ Hbody), unused_total_let;
      [ exact Htotal | ].
    intros Hx. apply var_free_b_sound in Hx. congruence.
  - exact (plug_equivalent (Let_static_body bindings Hole) _ _ (not_many _)
      (remove_unused_total_lets_equivalent_aux body)).
  - apply (expr_equivalent_trans _
      (Let_cont_non_recursive k
         (Handler params (remove_unused_total_lets handler)) body)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_handler k params Hole body) _ _ (not_many _)
        (remove_unused_total_lets_equivalent_aux handler)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_body k
           (Handler params (remove_unused_total_lets handler)) Hole)
        _ _ (not_many _) (remove_unused_total_lets_equivalent_aux body)).
  - exact (plug_equivalent (Let_cont_recursive_body handlers Hole)
        _ _ (not_many _)
      (remove_unused_total_lets_equivalent_aux body)).
Qed.

Theorem remove_unused_total_lets_equivalent :
  remove_unused_total_lets_equivalent_statement.
Proof. exact remove_unused_total_lets_equivalent_aux. Qed.

(* ======================================================================== *)
(* Removing unused [Let]s whose defining expression has a value in scope   *)
(* ======================================================================== *)

Definition all_bound (vs : list variable) (vars : env) : Prop :=
  ∀ x : variable, x ∈ vs -> ∃ v : value, lookup x vars = Some v.

(* Equivalence under the environments that bind the variables given. *)
Definition expr_equivalent_bound (vs : list variable) (e e' : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env),
    all_bound vs vars ->
    equivalent (State e vars conts statics) (State e' vars conts statics).

Lemma all_bound_cons (vs : list variable) (vars : env) (x : variable)
    (v : value) :
  all_bound vs vars -> all_bound (x :: vs) ((x, v) :: vars).
Proof.
  intros Hbound y Hin. simpl.
  destruct (Pos.eqb_spec y x) as [-> | Hne]; [ eauto | ].
  destruct Hin as [Heq | Hin]; [ congruence | exact (Hbound y Hin) ].
Qed.

Lemma simple_in_scope_defined (vs : list variable) (vars : env) (s : simple) :
  all_bound vs vars ->
  simple_in_scope vs s = true ->
  ∃ v : value, eval_simple vars s = Some v.
Proof.
  intros Hbound. destruct s as [x | sym | c]; simpl; eauto.
  intros Hin. apply Hbound, name_in_In, Hin.
Qed.

Lemma value_slots_defined (vs : list variable) (vars : env)
    (slots : list (value_slot * simple)) :
  all_bound vs vars ->
  forallb (fun slot => simple_in_scope vs (snd slot)) slots = true ->
  ∃ evaluated : list (value_slot * value),
    eval_value_slots vars slots = Some evaluated.
Proof.
  intros Hbound. induction slots as [ | [slot s] slots IH]; simpl; [ eauto | ].
  intros Hscope. apply andb_true_iff in Hscope as [Hs Hslots].
  destruct (simple_in_scope_defined vs vars s Hbound Hs) as [v ->].
  destruct (IH Hslots) as [evaluated ->]. simpl. eauto.
Qed.

Lemma named_defined_sound (vs : list variable) (vars : env)
    (statics : static_env) (d : named) :
  all_bound vs vars ->
  named_defined vs d = true ->
  ∃ v : value, eval_named statics vars d = Some v.
Proof.
  intros Hbound. destruct d as [s | p args | code slots | slot closure];
    simpl; try discriminate.
  - apply simple_in_scope_defined, Hbound.
  - intros Hslots.
    destruct (value_slots_defined vs vars slots Hbound Hslots)
      as [evaluated ->].
    simpl. eauto.
Qed.

Lemma let_equivalent_bound (vs : list variable) (x : variable) (d : named)
    (body body' : expr) :
  expr_equivalent_bound (x :: vs) body body' ->
  expr_equivalent_bound vs (Let x d body) (Let x d body').
Proof.
  intros Hbody vars conts statics Hbound.
  destruct (eval_named statics vars d) as [v | ] eqn:Hd.
  - eapply equivalent_step;
      [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity | ].
    apply Hbody, all_bound_cons, Hbound.
  - apply (equivalent_of_run 1 1). simpl. rewrite Hd. reflexivity.
Qed.

(* The defining expression has a value, so the [Let] takes its step; the
   body does not look at the variable. *)
Lemma unused_defined_let (vs : list variable) (x : variable) (d : named)
    (body : expr) :
  named_defined vs d = true ->
  ~ var_free_in_expr x body ->
  expr_equivalent_bound vs (Let x d body) body.
Proof.
  intros Hdefined Hunused vars conts statics Hbound.
  destruct (named_defined_sound vs vars statics d Hbound Hdefined) as [v Hd].
  apply (equivalent_trans _ (State body ((x, v) :: vars) conts statics));
    [ apply step_equivalent; simpl; rewrite Hd; reflexivity | ].
  apply coincide_equivalent.
  - intros y Hy. simpl.
    destruct (Pos.eqb_spec y x) as [-> | _]; [ contradiction | reflexivity ].
  - intros k _. apply (conts_agree_same identity_renaming). reflexivity.
Qed.

Lemma let_cont_handler_equivalent_bound (vs : list variable)
    (k : continuation) (params : list variable)
    (handler handler' body : expr) :
  expr_equivalent_bound (params ++ vs) handler handler' ->
  expr_equivalent_bound vs
    (Let_cont_non_recursive k (Handler params handler) body)
    (Let_cont_non_recursive k (Handler params handler') body).
Proof.
  intros Hhandler vars conts statics Hbound.
  assert (Hruns :
    ∀ (values : list value) (handler_vars : env),
      bind_params params values vars = Some handler_vars ->
      all_bound (params ++ vs) handler_vars).
  { intros values handler_vars Hbind x Hin.
    apply (bind_params_bound params values vars handler_vars x Hbind).
    apply in_app_or in Hin. destruct Hin as [Hin | Hin];
      [ left; exact Hin | right; exact (Hbound x Hin) ]. }
  apply refines_antisymmetric; apply let_cont_handler_refines_at;
    intros values handler_vars conts' statics' Hbind;
    apply equivalent_refines; [ | apply equivalent_sym ];
    apply Hhandler, (Hruns values handler_vars Hbind).
Qed.

Lemma expr_equivalent_bound_trans (vs : list variable) (e e' e'' : expr) :
  expr_equivalent_bound vs e e' -> expr_equivalent_bound vs e' e'' ->
  expr_equivalent_bound vs e e''.
Proof.
  intros H H' vars conts statics Hbound.
  exact (equivalent_trans _ _ _ (H vars conts statics Hbound)
    (H' vars conts statics Hbound)).
Qed.

Fixpoint remove_unused_defined_lets_equivalent_bound (e : expr) :
  ∀ vs : list variable,
    expr_equivalent_bound vs e (remove_unused_defined_lets vs e).
Proof.
  destruct e
    as [ x d body | bindings body | k [params handler] body | handlers body
       | ap | ac | scrutinee arms | ];
    intros vs; simpl;
    try (intros vars conts statics _; apply equivalent_refl).
  - pose proof (let_equivalent_bound vs x d _ _
      (remove_unused_defined_lets_equivalent_bound body (x :: vs)))
      as Hbody.
    destruct
      (named_defined vs d
       && negb (var_free_b x (remove_unused_defined_lets (x :: vs) body)))
      eqn:Hremove; [ | exact Hbody ].
    apply andb_true_iff in Hremove as [Hdefined Hunused].
    apply negb_true_iff in Hunused.
    apply (expr_equivalent_bound_trans vs _ _ _ Hbody), unused_defined_let;
      [ exact Hdefined | ].
    intros Hx. apply var_free_b_sound in Hx. congruence.
  - intros vars conts statics Hbound.
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hbindings.
    + eapply equivalent_step;
        [ simpl; rewrite Hbindings; reflexivity
        | simpl; rewrite Hbindings; reflexivity | ].
      apply (remove_unused_defined_lets_equivalent_bound body vs), Hbound.
    + apply (equivalent_of_run 1 1). simpl. rewrite Hbindings. reflexivity.
  - apply (expr_equivalent_bound_trans vs _
      (Let_cont_non_recursive k
         (Handler params
            (remove_unused_defined_lets (params ++ vs) handler))
         body)).
    + apply let_cont_handler_equivalent_bound,
        remove_unused_defined_lets_equivalent_bound.
    + intros vars conts statics Hbound.
      eapply equivalent_step; [ reflexivity | reflexivity | ].
      apply (remove_unused_defined_lets_equivalent_bound body vs), Hbound.
  - intros vars conts statics Hbound.
    apply let_cont_recursive_equivalent_step; [ reflexivity | intros _ ].
    apply (remove_unused_defined_lets_equivalent_bound body vs), Hbound.
Qed.

Theorem remove_unused_defined_lets_equivalent :
  remove_unused_defined_lets_equivalent_statement.
Proof.
  intros e vars conts statics.
  apply (remove_unused_defined_lets_equivalent_bound e []). intros x [].
Qed.

(* ======================================================================== *)
(* Inlining calls of symbols known to be closures                           *)
(* ======================================================================== *)

(* The static environment binds the symbols known to be closures to
   closures of the code known. *)
Definition statics_know_symbols (known : list (symbol * option code_id))
    (statics : static_env) : Prop :=
  ∀ (s : symbol) (code : code_id),
    lookup s known = Some (Some code) ->
    ∃ slots : list (value_slot * value),
      lookup s (static_values statics) = Some (Static_closure code slots).

Lemma eval_static_bindings_know_symbols (vars : env)
    (bindings : list static_binding) :
  ∀ (known : list (symbol * option code_id)) (statics extended : static_env),
    statics_know_symbols known statics ->
    eval_static_bindings vars bindings statics = Some extended ->
    statics_know_symbols (symbols_of bindings known) extended.
Proof.
  induction bindings as [ | binding bindings IH];
    intros known statics extended Hknow; simpl.
  - intros [= <-]. exact Hknow.
  - destruct binding
      as [id c | id | sym [code slots | tag fields | contents | bytes]];
      simpl.
    + destruct (lookup id (static_code statics)); [ discriminate | ].
      apply IH. exact Hknow.
    + apply IH, Hknow.
    + destruct (lookup sym (static_values statics)); [ discriminate | ].
      destruct (eval_value_slots vars slots) as [evaluated | ]; simpl;
        [ | discriminate ].
      apply IH. intros s code'. simpl.
      destruct (Pos.eqb s sym); [ intros [= <-]; eauto | apply Hknow ].
    + destruct (lookup sym (static_values statics)); [ discriminate | ].
      destruct (eval_simples vars fields) as [vs | ]; simpl;
        [ | discriminate ].
      apply IH. intros s code'. simpl.
      destruct (Pos.eqb s sym); [ discriminate | apply Hknow ].
    + destruct (lookup sym (static_values statics)); [ discriminate | ].
      destruct (eval_simple vars contents) as [v | ]; simpl;
        [ | discriminate ].
      apply IH. intros s code'. simpl.
      destruct (Pos.eqb s sym); [ discriminate | apply Hknow ].
    + destruct (lookup sym (static_values statics)); [ discriminate | ].
      apply IH. intros s code'. simpl.
      destruct (Pos.eqb s sym); [ discriminate | apply Hknow ].
Qed.

Lemma inline_known_apply_equivalent (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (ap : apply_expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  statics_know known_code statics ->
  statics_know_symbols known_symbols statics ->
  equivalent (State (Apply ap) vars conts statics)
    (State (inline_known_apply known_code known_symbols ap) vars conts
       statics).
Proof.
  intros Hcode Hsymbols. unfold inline_known_apply.
  destruct (ap_callee ap) as [x | s | const] eqn:Hcallee;
    try apply equivalent_refl.
  destruct (ap_call_kind ap) as [called | ] eqn:Hkind;
    [ | apply equivalent_refl ].
  destruct (lookup s known_symbols) as [[code | ] | ] eqn:Hs;
    try apply equivalent_refl.
  destruct (lookup called known_code) as [c | ] eqn:Hc;
    [ | apply equivalent_refl ].
  destruct (Pos.eqb code called && inlinable_b ap c) eqn:Hcheck;
    [ | apply equivalent_refl ].
  apply andb_true_iff in Hcheck as [Hsame Hinlinable].
  apply Pos.eqb_eq in Hsame. subst code.
  destruct (Hsymbols s called Hs) as [slots Hlookup].
  apply (inline_equivalent ap called c _ (Value_symbol s) slots);
    [ exact Hkind | rewrite Hcallee; reflexivity
    | simpl; rewrite Hlookup; reflexivity | exact (Hcode called c Hc)
    | exact (inlinable_b_sound ap c Hinlinable) ].
Qed.

Definition statics_know_both (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (statics : static_env)
    : Prop :=
  statics_know known_code statics
  ∧ statics_know_symbols known_symbols statics.

Lemma statics_know_both_extend (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id))
    (statics statics' : static_env) :
  statics_know_both known_code known_symbols statics ->
  statics_extend statics statics' ->
  statics_know_both known_code known_symbols statics'.
Proof.
  intros [Hcode Hsymbols] Hextend. split.
  - exact (statics_know_extend known_code statics statics' Hcode Hextend).
  - intros s code Hs. destruct (Hsymbols s code Hs) as [slots Hlookup].
    exists slots. apply (proj2 Hextend), Hlookup.
Qed.

Lemma inline_known_apply_binds_statics
    (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (ap : apply_expr) :
  binds_statics (inline_known_apply known_code known_symbols ap) = false.
Proof.
  unfold inline_known_apply.
  destruct (ap_callee ap) as [x | s | const]; try reflexivity.
  destruct (ap_call_kind ap) as [called | ]; try reflexivity.
  destruct (lookup s known_symbols) as [[code | ] | ]; try reflexivity.
  destruct (lookup called known_code) as [c | ]; try reflexivity.
  destruct (Pos.eqb code called && inlinable_b ap c) eqn:Hcheck;
    [ | reflexivity ].
  apply andb_true_iff in Hcheck as [_ Hinlinable].
  rewrite inlined_body_binds_statics.
  exact (inlinable_b_binds_statics ap c Hinlinable).
Qed.

Fixpoint inline_known_calls_binds_statics (e : expr) :
  ∀ (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)),
    binds_statics (inline_known_calls known_code known_symbols e)
    = binds_statics e.
Proof.
  destruct e
    as [ x d body | bindings body | k h body | handlers body
       | ap | ac | scrutinee arms | ];
    intros known_code known_symbols; simpl; try reflexivity.
  - apply inline_known_calls_binds_statics.
  - rewrite inline_known_calls_binds_statics. reflexivity.
  - destruct h as [params handler]. simpl.
    rewrite !inline_known_calls_binds_statics. reflexivity.
  - rewrite inline_known_calls_binds_statics. f_equal.
    induction handlers as [ | [k [params handler]] handlers IH]; simpl;
      [ reflexivity | ].
    rewrite inline_known_calls_binds_statics, IH. reflexivity.
  - apply inline_known_apply_binds_statics.
Qed.

Lemma inline_known_calls_handlers_bind_statics
    (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id))
    (handlers : list (continuation * continuation_handler)) :
  handlers_bind_statics
    (map
       (fun '(k, h) =>
          (k, inline_known_calls_in_handler known_code known_symbols h))
       handlers)
  = handlers_bind_statics handlers.
Proof.
  unfold handlers_bind_statics.
  induction handlers as [ | [k [params handler]] handlers IH]; simpl;
    [ reflexivity | ].
  rewrite inline_known_calls_binds_statics, IH. reflexivity.
Qed.

Fixpoint inline_known_calls_equivalent_knowing (e : expr) :
  ∀ (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (vars : env)
    (conts : cont_env) (statics : static_env),
    statics_know known_code statics ->
    statics_know_symbols known_symbols statics ->
    equivalent (State e vars conts statics)
      (State (inline_known_calls known_code known_symbols e) vars conts
         statics).
Proof.
  - destruct e
      as [ x d body | bindings body | k h body | handlers body
         | ap | ac | scrutinee arms | ];
      intros known_code known_symbols vars conts statics Hcode Hsymbols;
      simpl; try apply equivalent_refl.
    + destruct (eval_named statics vars d) as [v | ] eqn:Hd.
      * eapply equivalent_step;
          [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity
          | apply inline_known_calls_equivalent_knowing; assumption ].
      * apply (equivalent_of_run 1 1). simpl. rewrite Hd. reflexivity.
    + destruct (eval_static_bindings vars bindings statics) as [extended | ]
        eqn:Hbindings.
      * eapply equivalent_step;
          [ simpl; rewrite Hbindings; reflexivity
          | simpl; rewrite Hbindings; reflexivity | ].
        apply inline_known_calls_equivalent_knowing.
        -- exact (eval_static_bindings_know vars bindings known_code statics
             extended Hcode Hbindings).
        -- exact (eval_static_bindings_know_symbols vars bindings
             known_symbols statics extended Hsymbols Hbindings).
      * apply (equivalent_of_run 1 1). simpl. rewrite Hbindings.
        reflexivity.
    + destruct h as [params handler]. simpl.
      apply (equivalent_trans _
        (State
           (Let_cont_non_recursive k
              (Handler params
                 (inline_known_calls known_code known_symbols handler))
              body)
           vars conts statics)).
      * apply refines_antisymmetric;
          apply (let_cont_handler_refines_where
            (statics_know_both known_code known_symbols)
            (statics_know_both_extend known_code known_symbols));
          try (split; assumption);
          intros vs handler_vars conts' statics' [Hcode' Hsymbols'] _;
          apply equivalent_refines; [ | apply equivalent_sym ];
          apply inline_known_calls_equivalent_knowing; assumption.
      * eapply equivalent_step;
          [ reflexivity | reflexivity
          | apply inline_known_calls_equivalent_knowing; assumption ].
    + apply (equivalent_trans _
        (State
           (Let_cont_recursive
              (map
                 (fun '(k, h) =>
                    (k,
                     inline_known_calls_in_handler known_code known_symbols
                       h))
                 handlers)
              body)
           vars conts statics)).
      * assert (Hhandlers :
          let handlers' :=
            map
              (fun '(k, h) =>
                 (k,
                  inline_known_calls_in_handler known_code known_symbols h))
              handlers
          in
          handlers_refine (statics_know_both known_code known_symbols) vars
            handlers handlers'
          ∧ handlers_refine (statics_know_both known_code known_symbols)
              vars handlers' handlers).
        { induction handlers as [ | [k [params handler]] handlers IH]; simpl.
          - repeat split; apply Forall2_nil.
          - destruct IH as [[Hforwards Hbackwards] [Hforwards' Hbackwards']].
            repeat split; (apply Forall2_cons; [ | assumption ]);
              (split; [ reflexivity | ]); apply Handler_related;
              intros vs handler_vars conts' statics' [Hcode' Hsymbols'] _;
              try (apply equivalent_refines,
                     inline_known_calls_equivalent_knowing; assumption);
              apply equivalent_refines, equivalent_sym,
                inline_known_calls_equivalent_knowing; assumption. }
        destruct Hhandlers
          as [[Hforwards Hbackwards] [Hforwards' Hbackwards']].
        apply refines_antisymmetric;
          apply (let_cont_recursive_handlers_refine_where
            (statics_know_both known_code known_symbols)
            (statics_know_both_extend known_code known_symbols));
          try assumption; try (split; assumption);
          first
            [ apply inline_known_calls_handlers_bind_statics
            | symmetry; apply inline_known_calls_handlers_bind_statics ].
      * apply let_cont_recursive_equivalent_step; [ reflexivity | intros _ ].
        apply inline_known_calls_equivalent_knowing; assumption.
    + apply inline_known_apply_equivalent; assumption.
Qed.

Theorem inline_known_calls_equivalent :
  inline_known_calls_equivalent_statement.
Proof.
  intros e vars conts statics. apply inline_known_calls_equivalent_knowing.
  - intros id c Hlookup. discriminate Hlookup.
  - intros s code Hlookup. discriminate Hlookup.
Qed.

(* ======================================================================== *)
(* Groups of static bindings                                                *)
(* ======================================================================== *)

(* A binding of a symbol may be made after bindings of code that came
   after it: code and symbols go to different parts of the static
   environment. *)
Lemma eval_static_bindings_symbol_later (vars : env) (sym : symbol)
    (const : static_const) (codes rest : list static_binding) :
  forallb binds_code codes = true ->
  ∀ statics : static_env,
    eval_static_bindings vars (codes ++ Bind_symbol sym const :: rest) statics
    = eval_static_bindings vars (Bind_symbol sym const :: codes ++ rest)
        statics.
Proof.
  induction codes as [ | binding codes IH]; intros Hcodes statics;
    [ reflexivity | ].
  simpl in Hcodes. apply andb_true_iff in Hcodes as [Hbinding Hcodes].
  destruct binding as [id c | id | sym' const']; simpl in Hbinding;
    try discriminate.
  - change
      (match lookup id (static_code statics) with
       | Some _ => None
       | None =>
         eval_static_bindings vars (codes ++ Bind_symbol sym const :: rest)
           (Static_env ((id, c) :: static_code statics)
              (static_values statics))
       end
       = eval_static_bindings vars
           (Bind_symbol sym const :: Bind_code id c :: codes ++ rest)
           statics).
    rewrite (IH Hcodes). simpl.
    destruct (lookup id (static_code statics)),
      (lookup sym (static_values statics)),
      (eval_static_const vars const); reflexivity.
  - change
      (eval_static_bindings vars (codes ++ Bind_symbol sym const :: rest)
         statics
       = eval_static_bindings vars
           (Bind_symbol sym const :: Bind_deleted_code id :: codes ++ rest)
           statics).
    rewrite (IH Hcodes). simpl.
    destruct (lookup sym (static_values statics)),
      (eval_static_const vars const); reflexivity.
Qed.

Lemma filter_binds_code (bindings : list static_binding) :
  forallb binds_code (filter binds_code bindings) = true.
Proof.
  induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
  destruct (binds_code binding) eqn:Hcode; simpl; [ rewrite Hcode | ];
    exact IH.
Qed.

Lemma eval_static_bindings_code_first (vars : env)
    (bindings : list static_binding) :
  ∀ statics : static_env,
    eval_static_bindings vars (code_first bindings) statics
    = eval_static_bindings vars bindings statics.
Proof.
  unfold code_first.
  induction bindings as [ | binding bindings IH]; intros statics;
    [ reflexivity | ].
  destruct binding as [id c | id | sym const]; simpl.
  - destruct (lookup id (static_code statics)); [ reflexivity | apply IH ].
  - apply IH.
  - rewrite (eval_static_bindings_symbol_later vars sym const _ _
      (filter_binds_code bindings)).
    simpl. destruct (lookup sym (static_values statics)); [ reflexivity | ].
    destruct (eval_static_const vars const); simpl;
      [ apply IH | reflexivity ].
Qed.

Lemma code_first_equivalent (bindings : list static_binding) (body : expr) :
  expr_equivalent (Let_static bindings body)
    (Let_static (code_first bindings) body).
Proof.
  intros vars conts statics. apply (equivalent_of_run 1 1). simpl.
  rewrite eval_static_bindings_code_first. reflexivity.
Qed.

Fixpoint merge_statics_equivalent_aux (e : expr) :
  expr_equivalent e (merge_statics e).
Proof.
  destruct e
    as [ x d body | bindings body | k [params handler] body | handlers body
       | ap | ac | scrutinee arms | ];
    simpl; try (intros vars conts statics; apply equivalent_refl).
  - exact (plug_equivalent (Let_body x d Hole) _ _ (not_many _)
      (merge_statics_equivalent_aux body)).
  - pose proof (plug_equivalent (Let_static_body bindings Hole) _ _ (not_many _)
      (merge_statics_equivalent_aux body)) as Hbody.
    simpl in Hbody.
    destruct (merge_statics body)
      as [ x d body' | bindings' body' | k h body' | handlers body' | ap
         | ac | scrutinee arms | ];
      try (apply (expr_equivalent_trans _ _ _ Hbody), code_first_equivalent).
    apply (expr_equivalent_trans _ _ _ Hbody).
    apply (expr_equivalent_trans _
      (Let_static (bindings ++ bindings') body')).
    + intros vars conts statics.
      apply equivalent_sym, let_static_split.
    + apply code_first_equivalent.
  - apply (expr_equivalent_trans _
      (Let_cont_non_recursive k (Handler params (merge_statics handler))
         body)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_handler k params Hole body) _ _ (not_many _)
        (merge_statics_equivalent_aux handler)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_body k
           (Handler params (merge_statics handler)) Hole)
        _ _ (not_many _) (merge_statics_equivalent_aux body)).
  - exact (plug_equivalent (Let_cont_recursive_body handlers Hole)
        _ _ (not_many _)
      (merge_statics_equivalent_aux body)).
Qed.

Theorem merge_statics_equivalent : merge_statics_equivalent_statement.
Proof. exact merge_statics_equivalent_aux. Qed.

(* ======================================================================== *)
(* Switches whose arms are all the same                                     *)
(* ======================================================================== *)

Lemma collapse_switch_refines (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  expr_refines (Switch scrutinee arms) (collapse_switch scrutinee arms).
Proof.
  unfold collapse_switch.
  destruct arms as [ | [i ac] others]; [ apply expr_refines_refl | ].
  destruct
    (forallb
       (fun arm => if apply_cont_eq_dec (snd arm) ac then true else false)
       others)
    eqn:Hsame; [ | apply expr_refines_refl ].
  apply switch_same_arms. intros j arm [[= _ <-] | Hin]; [ reflexivity | ].
  rewrite forallb_forall in Hsame. specialize (Hsame (j, arm) Hin).
  simpl in Hsame.
  destruct (apply_cont_eq_dec arm ac); [ assumption | discriminate ].
Qed.

Fixpoint collapse_switches_refines_aux (e : expr) :
  expr_refines e (collapse_switches e).
Proof.
  destruct e
    as [ x d body | bindings body | k [params handler] body | handlers body
       | ap | ac | scrutinee arms | ];
    simpl; try apply expr_refines_refl.
  - exact (plug_refines (Let_body x d Hole) _ _ (not_many _)
      (collapse_switches_refines_aux body)).
  - exact (plug_refines (Let_static_body bindings Hole) _ _ (not_many _)
      (collapse_switches_refines_aux body)).
  - apply (expr_refines_trans _
      (Let_cont_non_recursive k (Handler params (collapse_switches handler))
         body)).
    + exact (plug_refines
        (Let_cont_non_recursive_handler k params Hole body) _ _ (not_many _)
        (collapse_switches_refines_aux handler)).
    + exact (plug_refines
        (Let_cont_non_recursive_body k
           (Handler params (collapse_switches handler)) Hole)
        _ _ (not_many _) (collapse_switches_refines_aux body)).
  - exact (plug_refines (Let_cont_recursive_body handlers Hole) _ _ (not_many _)
      (collapse_switches_refines_aux body)).
  - apply collapse_switch_refines.
Qed.

Theorem collapse_switches_refines : collapse_switches_refines_statement.
Proof. exact collapse_switches_refines_aux. Qed.
