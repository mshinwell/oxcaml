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

(* Proofs of the statements of FlambdaNominalSpec.v. Nothing here needs
   review.

   All of them come from one fact ([renamed_equivalent]): a state and its
   renaming, under environments that agree on the free names along the
   renaming, are equivalent. The two run in step with each other, so this
   is a bisimulation (FlambdaSemanticsProofs.bisimulation_equivalent). A
   continuation closure is related to its renaming by a renaming of its
   own ([closure_renamed]), since it was made under other environments. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaNominalSpec.
Import ListNotations.

(* ======================================================================== *)
(* Permutations                                                             *)
(* ======================================================================== *)

Lemma swap_injective (a b x y : positive) : swap a b x = swap a b y -> x = y.
Proof.
  unfold swap.
  destruct (Pos.eqb_spec x a), (Pos.eqb_spec x b), (Pos.eqb_spec y a),
    (Pos.eqb_spec y b); congruence.
Qed.

Lemma permute_injective (p : permutation) (x y : positive) :
  permute p x = permute p y -> x = y.
Proof.
  induction p as [ | [a b] p IH]; simpl; [ auto | ].
  intros Heq. apply IH, (swap_injective a b), Heq.
Qed.

Lemma permute_eqb (p : permutation) (x y : positive) :
  Pos.eqb (permute p x) (permute p y) = Pos.eqb x y.
Proof.
  destruct (Pos.eqb_spec x y) as [-> | Hne]; [ apply Pos.eqb_refl | ].
  apply Pos.eqb_neq. intros Heq. apply Hne, (permute_injective p), Heq.
Qed.

Lemma rename_variable_eqb (r : renaming) (x y : variable) :
  Pos.eqb (rename_variable r x) (rename_variable r y) = Pos.eqb x y.
Proof. apply permute_eqb. Qed.

Lemma rename_continuation_eqb (r : renaming) (k k' : continuation) :
  Pos.eqb (rename_continuation r k) (rename_continuation r k') = Pos.eqb k k'.
Proof. apply permute_eqb. Qed.

(* ======================================================================== *)
(* The identity renaming                                                    *)
(* ======================================================================== *)

Lemma rename_simple_id (s : simple) : rename_simple identity_renaming s = s.
Proof. destruct s; reflexivity. Qed.

Lemma rename_simples_id (args : list simple) :
  map (rename_simple identity_renaming) args = args.
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite rename_simple_id, IH. reflexivity.
Qed.

Lemma rename_named_id (d : named) : rename_named identity_renaming d = d.
Proof.
  destruct d; simpl; [ rewrite rename_simple_id | rewrite rename_simples_id ];
    reflexivity.
Qed.

Lemma rename_apply_cont_id (ac : apply_cont) :
  rename_apply_cont identity_renaming ac = ac.
Proof.
  destruct ac. unfold rename_apply_cont. simpl.
  rewrite rename_simples_id. reflexivity.
Qed.

(* By induction on the expression, its handlers included. *)
Fixpoint rename_expr_id (e : expr) : rename_expr identity_renaming e = e
with rename_handler_id (h : continuation_handler) :
  rename_handler identity_renaming h = h.
Proof.
  - destruct e
      as [x d body | k h body | handlers body | ac | scrutinee arms | ];
      simpl.
    + rewrite rename_named_id, rename_expr_id. reflexivity.
    + rewrite rename_handler_id, rename_expr_id. reflexivity.
    + rewrite rename_expr_id. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite rename_handler_id, IH. reflexivity.
    + rewrite rename_apply_cont_id. reflexivity.
    + rewrite rename_simple_id. f_equal.
      induction arms as [ | [i ac] arms IH]; simpl; [ reflexivity | ].
      rewrite rename_apply_cont_id, IH. reflexivity.
    + reflexivity.
  - destruct h as [params handler]. simpl. rewrite rename_expr_id. f_equal.
    induction params as [ | x params IH]; simpl; [ reflexivity | ].
    rewrite IH. reflexivity.
Qed.

(* ======================================================================== *)
(* Lookups and evaluation under a renaming                                  *)
(* ======================================================================== *)

Lemma lookup_rename_handlers (r : renaming) (k : continuation)
    (handlers : list (continuation * continuation_handler)) :
  lookup (rename_continuation r k) (rename_handlers r handlers)
  = option_map (rename_handler r) (lookup k handlers).
Proof.
  induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
  rewrite rename_continuation_eqb.
  destruct (Pos.eqb k k'); [ reflexivity | exact IH ].
Qed.

Lemma lookup_any_handler {A : Type} (P : A -> Prop) (k : continuation)
    (handlers : list (continuation * A)) (h : A) :
  lookup k handlers = Some h -> P h -> any_handler P handlers.
Proof.
  induction handlers as [ | [k' h'] handlers IH]; simpl; [ discriminate | ].
  destruct (Pos.eqb k k').
  - intros [= ->] Hh. left. exact Hh.
  - intros Hlookup Hh. right. exact (IH Hlookup Hh).
Qed.

Lemma eval_simple_renamed (r : renaming) (s : simple) (vars vars' : env) :
  (∀ x : variable,
    var_free_in_simple x s ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  eval_simple vars' (rename_simple r s) = eval_simple vars s.
Proof.
  intros Hvars. destruct s as [x | c]; simpl; [ | reflexivity ].
  apply Hvars. reflexivity.
Qed.

Lemma eval_simples_renamed (r : renaming) (args : list simple)
    (vars vars' : env) :
  (∀ x : variable,
    var_free_in_simples x args ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  eval_simples vars' (map (rename_simple r) args) = eval_simples vars args.
Proof.
  induction args as [ | s args IH]; intros Hvars; simpl; [ reflexivity | ].
  rewrite (eval_simple_renamed r s vars vars'), IH; [ reflexivity | | ];
    intros x Hx; apply Hvars; [ apply Exists_cons_tl | apply Exists_cons_hd ];
    exact Hx.
Qed.

Lemma eval_named_renamed (r : renaming) (d : named) (vars vars' : env) :
  (∀ x : variable,
    var_free_in_named x d ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  eval_named vars' (rename_named r d) = eval_named vars d.
Proof.
  intros Hvars. destruct d as [s | p args]; simpl.
  - apply eval_simple_renamed, Hvars.
  - rewrite (eval_simples_renamed r args vars vars' Hvars). reflexivity.
Qed.

(* Binding renamed parameters: both fail or both succeed, and then the
   environments agree at a variable that is a parameter or at which they
   agreed. *)
Lemma bind_params_renamed (r : renaming) (params : list variable) :
  ∀ (vs : list value) (vars vars' : env),
    match
      bind_params params vs vars,
      bind_params (map (rename_variable r) params) vs vars'
    with
    | Some bound, Some bound' =>
      ∀ x : variable,
        x ∈ params ∨ lookup (rename_variable r x) vars' = lookup x vars ->
        lookup (rename_variable r x) bound' = lookup x bound
    | None, None => True
    | _, _ => False
    end.
Proof.
  induction params as [ | p params IH]; intros [ | v vs] vars vars'; simpl;
    try exact I.
  - intros x [[] | Hagree]. exact Hagree.
  - specialize (IH vs ((p, v) :: vars) ((rename_variable r p, v) :: vars')).
    destruct (bind_params params vs ((p, v) :: vars)),
      (bind_params (map (rename_variable r) params) vs
         ((rename_variable r p, v) :: vars'));
      try contradiction; try exact I.
    intros x Hx. apply IH. simpl. rewrite rename_variable_eqb.
    destruct (Pos.eqb_spec x p) as [-> | Hne]; [ right; reflexivity | ].
    destruct Hx as [[Heq | Hin] | Hagree];
      [ congruence | left; exact Hin | right; exact Hagree ].
Qed.

Lemma find_arm_renamed (r : renaming) (i : Z) (arms : list (Z * apply_cont)) :
  find_arm i (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  = option_map (rename_apply_cont r) (find_arm i arms).
Proof.
  induction arms as [ | [discriminant ac] arms IH]; simpl; [ reflexivity | ].
  destruct (Z.eqb i discriminant); [ reflexivity | exact IH ].
Qed.

(* ======================================================================== *)
(* A state and its renaming                                                 *)
(* ======================================================================== *)

(* A closure and its renaming, under environments that agree along the
   renaming on the free names of the closure: those of its handler and of
   the handlers defined with it, except, for the continuations, the ones
   they define. (The warning silenced is about induction schemes, which
   nothing uses.) *)
#[local] Set Warnings "-register-all".
Inductive closure_renamed : cont_value -> cont_value -> Prop :=
  | Closure_same (c : cont_value) : closure_renamed c c
  | Closure_renamed (r : renaming) (h : continuation_handler)
      (vars vars' : env) (conts conts' : cont_env)
      (recursive : list (continuation * continuation_handler)) :
    (∀ x : variable,
      var_free_in_handler x h
      ∨ any_handler (var_free_in_handler x) recursive ->
      lookup (rename_variable r x) vars' = lookup x vars) ->
    (∀ (k : continuation) (c : cont_value),
      lookup k recursive = None ->
      cont_free_in_handler k h
      ∨ any_handler (cont_free_in_handler k) recursive ->
      lookup k conts = Some c ->
      ∃ c' : cont_value,
        lookup (rename_continuation r k) conts' = Some c'
        ∧ closure_renamed c c') ->
    (∀ k : continuation,
      lookup k recursive = None ->
      cont_free_in_handler k h
      ∨ any_handler (cont_free_in_handler k) recursive ->
      lookup k conts = None ->
      lookup (rename_continuation r k) conts' = None
      ∧ rename_continuation r k = k) ->
    closure_renamed (Closure h vars conts recursive)
      (Closure (rename_handler r h) vars' conts' (rename_handlers r recursive)).

(* Two continuation environments agree at [k] along [r]: both bind it, to a
   closure and its renaming, or neither does, and then [r] fixes it, as it
   is observed. *)
Definition conts_agree_at (r : renaming) (k : continuation)
    (conts conts' : cont_env) : Prop :=
  match lookup k conts with
  | Some c =>
    ∃ c' : cont_value,
      lookup (rename_continuation r k) conts' = Some c' ∧ closure_renamed c c'
  | None =>
    lookup (rename_continuation r k) conts' = None
    ∧ rename_continuation r k = k
  end.

Inductive state_renamed : state -> state -> Prop :=
  | State_same (s : state) : state_renamed s s
  | State_renamed (r : renaming) (e : expr) (vars vars' : env)
      (conts conts' : cont_env) :
    (∀ x : variable,
      var_free_in_expr x e ->
      lookup (rename_variable r x) vars' = lookup x vars) ->
    (∀ k : continuation,
      cont_free_in_expr k e -> conts_agree_at r k conts conts') ->
    state_renamed (State e vars conts) (State (rename_expr r e) vars' conts').

(* [Closure_renamed] with the two premises about continuations, one for
   those bound and one for those not, put as [conts_agree_at]; and back. *)
Lemma closure_renamed_intro (r : renaming) (h : continuation_handler)
    (vars vars' : env) (conts conts' : cont_env)
    (recursive : list (continuation * continuation_handler)) :
  (∀ x : variable,
    var_free_in_handler x h
    ∨ any_handler (var_free_in_handler x) recursive ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  (∀ k : continuation,
    lookup k recursive = None ->
    cont_free_in_handler k h
    ∨ any_handler (cont_free_in_handler k) recursive ->
    conts_agree_at r k conts conts') ->
  closure_renamed (Closure h vars conts recursive)
    (Closure (rename_handler r h) vars' conts'
       (rename_handlers r recursive)).
Proof.
  intros Hvars Hconts. apply Closure_renamed; [ exact Hvars | | ].
  - intros k c Hunbound Hk Hlookup.
    specialize (Hconts k Hunbound Hk). unfold conts_agree_at in Hconts.
    rewrite Hlookup in Hconts. exact Hconts.
  - intros k Hunbound Hk Hlookup.
    specialize (Hconts k Hunbound Hk). unfold conts_agree_at in Hconts.
    rewrite Hlookup in Hconts. exact Hconts.
Qed.

Lemma conts_agree_of_clauses (r : renaming) (k : continuation)
    (conts conts' : cont_env) :
  (∀ c : cont_value,
    lookup k conts = Some c ->
    ∃ c' : cont_value,
      lookup (rename_continuation r k) conts' = Some c'
      ∧ closure_renamed c c')
  ->
  (lookup k conts = None ->
   lookup (rename_continuation r k) conts' = None
   ∧ rename_continuation r k = k) ->
  conts_agree_at r k conts conts'.
Proof.
  intros Hbound Hunbound. unfold conts_agree_at.
  destruct (lookup k conts) as [c | ];
    [ apply Hbound | apply Hunbound ]; reflexivity.
Qed.

(* One environment agrees with itself at a continuation the renaming
   fixes. *)
Lemma conts_agree_same (r : renaming) (k : continuation) (conts : cont_env) :
  rename_continuation r k = k -> conts_agree_at r k conts conts.
Proof.
  intros Hfix. unfold conts_agree_at. rewrite Hfix.
  destruct (lookup k conts) as [c | ]; [ | auto ].
  exists c. split; [ reflexivity | apply Closure_same ].
Qed.

(* Agreement at [k] once the closures of a recursive [Let_cont] and of its
   renaming are added: by the closures of the handler of [k], if it has
   one, and by the environments underneath if not. *)
Lemma rec_closures_agree (r : renaming) (k : continuation)
    (handlers : list (continuation * continuation_handler))
    (vars vars' : env) (conts conts' : cont_env) :
  (∀ h : continuation_handler,
    lookup k handlers = Some h ->
    closure_renamed (Closure h vars conts handlers)
      (Closure (rename_handler r h) vars' conts'
         (rename_handlers r handlers))) ->
  (lookup k handlers = None -> conts_agree_at r k conts conts') ->
  conts_agree_at r k (rec_closures handlers vars conts ++ conts)
    (rec_closures (rename_handlers r handlers) vars' conts' ++ conts').
Proof.
  intros Hbound Hunbound. unfold conts_agree_at.
  rewrite !lookup_rec_closures_app, lookup_rename_handlers.
  destruct (lookup k handlers) as [h | ]; simpl.
  - eexists. split; [ reflexivity | ]. apply Hbound. reflexivity.
  - apply Hunbound. reflexivity.
Qed.

(* Applying a continuation and its renaming to the same values. *)
Lemma apply_continuation_renamed (r : renaming) (k : continuation)
    (vs : list value) (conts conts' : cont_env) :
  conts_agree_at r k conts conts' ->
  result_related state_renamed (apply_continuation k vs conts)
    (apply_continuation (rename_continuation r k) vs conts').
Proof.
  unfold conts_agree_at, apply_continuation.
  destruct (lookup k conts) as [c | ].
  - intros (c' & -> & Hclosure).
    destruct Hclosure
      as [[[params handler] vars conts0 recursive]
         | r' [params handler] vars vars' conts0 conts0' recursive
             Hvars Hclosures Hexits].
    + destruct (bind_params params vs vars); simpl;
        [ apply State_same | exact I ].
    + assert (Hconts :
        ∀ k' : continuation,
          lookup k' recursive = None ->
          cont_free_in_handler k' (Handler params handler)
          ∨ any_handler (cont_free_in_handler k') recursive ->
          conts_agree_at r' k' conts0 conts0').
      { intros k' Hnone Hk'. apply conts_agree_of_clauses.
        - intros c0 Hlookup. exact (Hclosures k' c0 Hnone Hk' Hlookup).
        - intros Hlookup. exact (Hexits k' Hnone Hk' Hlookup). }
      simpl.
      pose proof (bind_params_renamed r' params vs vars vars') as Hbind.
      destruct (bind_params params vs vars),
        (bind_params (map (rename_variable r') params) vs vars');
        try contradiction; simpl; [ | exact I ].
      apply State_renamed.
      * intros x Hx. apply Hbind.
        destruct (in_dec Pos.eq_dec x params) as [Hin | Hnotin];
          [ left; exact Hin | right ].
        apply Hvars. left. split; assumption.
      * intros k' Hk'. apply rec_closures_agree.
        -- intros h Hlookup. apply closure_renamed_intro.
           ++ intros x [Hx | Hx]; apply Hvars; right;
                [ exact (lookup_any_handler _ _ _ _ Hlookup Hx) | exact Hx ].
           ++ intros k'' Hunbound [Hk'' | Hk'']; apply Hconts;
                try exact Hunbound; right;
                [ exact (lookup_any_handler _ _ _ _ Hlookup Hk'')
                | exact Hk'' ].
        -- intros Hunbound. apply Hconts; [ exact Hunbound | ].
           left. exact Hk'.
  - intros [-> ->]. simpl. auto.
Qed.

(* A state and its renaming step alike. *)
Lemma renamed_step (s s' : state) :
  state_renamed s s' -> result_related state_renamed (step s) (step s').
Proof.
  intros [s0 | r e vars vars' conts conts' Hvars Hconts].
  - apply result_related_refl, State_same.
  - destruct e
      as [x d body | k h body | handlers body | ac | scrutinee arms | ];
      simpl.
    + (* Let *)
      rewrite (eval_named_renamed r d vars vars');
        [ | intros y Hy; apply Hvars; left; exact Hy ].
      destruct (eval_named vars d) as [v | ]; simpl; [ | exact I ].
      apply State_renamed.
      * intros y Hy. simpl. rewrite rename_variable_eqb.
        destruct (Pos.eqb_spec y x) as [-> | Hne]; [ reflexivity | ].
        apply Hvars. right. split; assumption.
      * intros k Hk. apply Hconts. exact Hk.
    + (* Let_cont_non_recursive *)
      apply State_renamed.
      * intros y Hy. apply Hvars. right. exact Hy.
      * intros k' Hk'. unfold conts_agree_at. simpl.
        rewrite rename_continuation_eqb.
        destruct (Pos.eqb_spec k' k) as [-> | Hne].
        -- eexists. split; [ reflexivity | ].
           apply (closure_renamed_intro r h vars vars' conts conts' []).
           ++ intros x [Hx | []]. apply Hvars. left. exact Hx.
           ++ intros k'' _ [Hk'' | []]. apply Hconts. left. exact Hk''.
        -- apply Hconts. right. split; assumption.
    + (* Let_cont_recursive *)
      apply State_renamed.
      * intros y Hy. apply Hvars. right. exact Hy.
      * intros k Hk. apply rec_closures_agree.
        -- intros h Hlookup. apply closure_renamed_intro.
           ++ intros x [Hx | Hx]; apply Hvars; left;
                [ exact (lookup_any_handler _ _ _ _ Hlookup Hx) | exact Hx ].
           ++ intros k' Hunbound Hk'. apply Hconts.
              split; [ exact Hunbound | ]. left.
              destruct Hk' as [Hk' | Hk'];
                [ exact (lookup_any_handler _ _ _ _ Hlookup Hk')
                | exact Hk' ].
        -- intros Hunbound. apply Hconts.
           split; [ exact Hunbound | right; exact Hk ].
    + (* Apply_cont *)
      rewrite (eval_simples_renamed r (ac_args ac) vars vars');
        [ | intros y Hy; apply Hvars; exact Hy ].
      destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | exact I ].
      apply apply_continuation_renamed, Hconts. reflexivity.
    + (* Switch *)
      rewrite (eval_simple_renamed r scrutinee vars vars');
        [ | intros y Hy; apply Hvars; left; exact Hy ].
      destruct (eval_simple vars scrutinee) as [[[i | i]] | ]; try exact I.
      rewrite find_arm_renamed.
      destruct (find_arm i arms) as [ac | ] eqn:Hfind; simpl; [ | exact I ].
      apply find_arm_in in Hfind.
      apply (State_renamed r (Apply_cont ac)).
      * intros y Hy. apply Hvars. right. apply Exists_exists.
        exists (i, ac). split; [ exact Hfind | exact Hy ].
      * intros k Hk. apply Hconts. apply Exists_exists.
        exists (i, ac). split; [ exact Hfind | exact Hk ].
    + exact I.
Qed.

Theorem renamed_equivalent (s s' : state) :
  state_renamed s s' -> equivalent s s'.
Proof. apply (bisimulation_equivalent state_renamed renamed_step). Qed.

(* The case of no renaming: one expression under environments that agree
   on its free names. *)
Lemma coincide_equivalent (e : expr) (vars vars' : env)
    (conts conts' : cont_env) :
  (∀ x : variable, var_free_in_expr x e -> lookup x vars' = lookup x vars) ->
  (∀ k : continuation,
    cont_free_in_expr k e -> conts_agree_at identity_renaming k conts conts')
  ->
  equivalent (State e vars conts) (State e vars' conts').
Proof.
  intros Hvars Hconts. apply renamed_equivalent.
  pose proof (State_renamed identity_renaming e vars vars' conts conts'
    Hvars Hconts) as Hrenamed.
  rewrite rename_expr_id in Hrenamed. exact Hrenamed.
Qed.

(* Both sides take a step, to states that are equivalent. *)
Lemma equivalent_step (s s' t t' : state) :
  step s = Step s' -> step t = Step t' -> equivalent s' t' -> equivalent s t.
Proof.
  intros Hs Ht Hequiv.
  apply (equivalent_trans s s'); [ apply step_equivalent, Hs | ].
  apply (equivalent_trans s' t'); [ exact Hequiv | ].
  apply equivalent_sym, step_equivalent, Ht.
Qed.

(* ======================================================================== *)
(* Binders are name abstractions                                            *)
(* ======================================================================== *)

Theorem rename_let : rename_let_statement.
Proof.
  intros r x d body Hvars Hconts vars conts.
  destruct (eval_named vars d) as [v | ] eqn:Hd.
  - eapply equivalent_step;
      [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity | ].
    apply renamed_equivalent, State_renamed.
    + intros y Hy. simpl.
      destruct (Pos.eqb_spec y x) as [-> | Hne];
        [ rewrite Pos.eqb_refl; reflexivity | ].
      rewrite (Hvars y Hne Hy).
      destruct (Pos.eqb_spec y (rename_variable r x)) as [Heq | _];
        [ | reflexivity ].
      rewrite <- (Hvars y Hne Hy) in Heq.
      apply permute_injective in Heq. contradiction.
    + intros k Hk. apply conts_agree_same, Hconts, Hk.
  - apply (equivalent_of_run 1 1). simpl. rewrite Hd. reflexivity.
Qed.

Theorem freshen_let : freshen_let_statement.
Proof.
  intros x fresh d body Hfresh.
  pose proof (rename_let (Renaming [(x, fresh)] []) x d body) as Hrename.
  replace (rename_variable (Renaming [(x, fresh)] []) x) with fresh
    in Hrename
    by (unfold rename_variable, swap; simpl; unfold swap;
        rewrite Pos.eqb_refl; reflexivity).
  apply Hrename.
  - intros y Hne Hy. unfold rename_variable. simpl. unfold swap.
    destruct (Pos.eqb_spec y x); [ contradiction | ].
    destruct (Pos.eqb_spec y fresh) as [-> | _]; [ contradiction | ].
    reflexivity.
  - intros k _. reflexivity.
Qed.

Theorem rename_let_cont : rename_let_cont_statement.
Proof.
  intros r k h body Hvars Hconts vars conts.
  eapply equivalent_step; [ reflexivity | reflexivity | ].
  apply renamed_equivalent, State_renamed.
  - intros y Hy. rewrite (Hvars y Hy). reflexivity.
  - intros k' Hk'. unfold conts_agree_at. simpl.
    rewrite rename_continuation_eqb.
    destruct (Pos.eqb_spec k' k) as [-> | Hne].
    + eexists. split; [ reflexivity | apply Closure_same ].
    + apply (conts_agree_same r k' conts), Hconts; assumption.
Qed.

Theorem rename_handler : rename_handler_statement.
Proof.
  intros r k params handler body Hvars Hconts vars conts.
  eapply equivalent_step; [ reflexivity | reflexivity | ].
  apply coincide_equivalent; [ reflexivity | ].
  intros k' _. unfold conts_agree_at. simpl.
  change (rename_continuation identity_renaming k') with k'.
  destruct (Pos.eqb k' k).
  - eexists. split; [ reflexivity | ].
    apply (closure_renamed_intro r (Handler params handler) vars vars conts
      conts []).
    + intros x [[Hnotin Hx] | []]. rewrite (Hvars x Hnotin Hx). reflexivity.
    + intros k'' _ [Hk'' | []]. apply conts_agree_same, Hconts, Hk''.
  - apply (conts_agree_same identity_renaming k' conts). reflexivity.
Qed.

Theorem rename_let_cont_recursive : rename_let_cont_recursive_statement.
Proof.
  intros r handlers body Hvars Hconts vars conts.
  eapply equivalent_step; [ reflexivity | reflexivity | ].
  apply renamed_equivalent, State_renamed.
  - intros y Hy. rewrite (Hvars y); [ reflexivity | right; exact Hy ].
  - intros k Hk. apply rec_closures_agree.
    + intros h Hlookup. apply closure_renamed_intro.
      * intros x Hx. rewrite (Hvars x); [ reflexivity | ]. left.
        destruct Hx as [Hx | Hx];
          [ exact (lookup_any_handler _ _ _ _ Hlookup Hx) | exact Hx ].
      * intros k' Hunbound Hk'. apply conts_agree_same, Hconts.
        split; [ exact Hunbound | ]. left.
        destruct Hk' as [Hk' | Hk'];
          [ exact (lookup_any_handler _ _ _ _ Hlookup Hk') | exact Hk' ].
    + intros Hunbound. apply conts_agree_same, Hconts.
      split; [ exact Hunbound | right; exact Hk ].
Qed.

(* ======================================================================== *)
(* Bindings that are not used                                               *)
(* ======================================================================== *)

Theorem unused_let : unused_let_statement.
Proof.
  intros x d body Hunused vars conts.
  destruct (eval_named vars d) as [v | ] eqn:Hd.
  - apply equivalent_refines.
    apply (equivalent_trans _ (State body ((x, v) :: vars) conts));
      [ apply step_equivalent; simpl; rewrite Hd; reflexivity | ].
    apply coincide_equivalent.
    + intros y Hy. simpl.
      destruct (Pos.eqb_spec y x) as [-> | _]; [ contradiction | ].
      reflexivity.
    + intros k _. apply (conts_agree_same identity_renaming). reflexivity.
  - apply goes_wrong_refines. exists 1. simpl. rewrite Hd. reflexivity.
Qed.

Theorem unused_let_cont : unused_let_cont_statement.
Proof.
  intros k h body Hunused vars conts.
  eapply equivalent_trans; [ apply step_equivalent; reflexivity | ].
  apply coincide_equivalent; [ reflexivity | ].
  intros k' Hk'. unfold conts_agree_at.
  change (rename_continuation identity_renaming k') with k'. simpl.
  destruct (Pos.eqb_spec k' k) as [-> | _]; [ contradiction | ].
  apply (conts_agree_same identity_renaming k' conts). reflexivity.
Qed.

Theorem unused_let_cont_recursive : unused_let_cont_recursive_statement.
Proof.
  intros handlers body Hunused vars conts.
  eapply equivalent_trans; [ apply step_equivalent; reflexivity | ].
  apply coincide_equivalent; [ reflexivity | ].
  intros k Hk. unfold conts_agree_at.
  change (rename_continuation identity_renaming k) with k.
  rewrite lookup_rec_closures_app, (Hunused k Hk).
  apply (conts_agree_same identity_renaming k conts). reflexivity.
Qed.
