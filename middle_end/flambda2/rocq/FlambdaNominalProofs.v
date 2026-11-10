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

Lemma rename_value_slots_id (slots : list (value_slot * simple)) :
  map (fun slot => (fst slot, rename_simple identity_renaming (snd slot)))
    slots
  = slots.
Proof.
  induction slots as [ | [slot s] slots IH]; simpl; [ reflexivity | ].
  rewrite rename_simple_id, IH. reflexivity.
Qed.

Lemma rename_named_id (d : named) : rename_named identity_renaming d = d.
Proof.
  destruct d as [s | p args | code slots | slot closure]; simpl;
    rewrite ?rename_simple_id, ?rename_simples_id, ?rename_value_slots_id;
    reflexivity.
Qed.

Lemma rename_static_binding_id (binding : static_binding) :
  rename_static_binding identity_renaming binding = binding.
Proof.
  destruct binding as [id c | id | sym [code slots | tag fields | s | bytes]];
    simpl;
    rewrite ?rename_simple_id, ?rename_simples_id, ?rename_value_slots_id;
    reflexivity.
Qed.

Lemma rename_apply_id (ap : apply_expr) :
  rename_apply identity_renaming ap = ap.
Proof.
  destruct ap. unfold rename_apply. simpl.
  rewrite rename_simple_id, rename_simples_id. reflexivity.
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
      as [ x d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl.
    + rewrite rename_named_id, rename_expr_id. reflexivity.
    + rewrite rename_expr_id. f_equal.
      induction bindings as [ | binding bindings IH]; simpl;
        [ reflexivity | ].
      rewrite rename_static_binding_id, IH. reflexivity.
    + rewrite rename_handler_id, rename_expr_id. reflexivity.
    + rewrite rename_expr_id. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite rename_handler_id, IH. reflexivity.
    + rewrite rename_apply_id. reflexivity.
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
  intros Hvars. destruct s as [x | sym | c]; simpl; try reflexivity.
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

Lemma eval_value_slots_renamed (r : renaming)
    (slots : list (value_slot * simple)) (vars vars' : env) :
  (∀ x : variable,
    Exists (fun slot => var_free_in_simple x (snd slot)) slots ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  eval_value_slots vars'
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = eval_value_slots vars slots.
Proof.
  induction slots as [ | [slot s] slots IH]; intros Hvars; simpl;
    [ reflexivity | ].
  rewrite (eval_simple_renamed r s vars vars'), IH; [ reflexivity | | ];
    intros x Hx; apply Hvars; [ apply Exists_cons_tl | apply Exists_cons_hd ];
    exact Hx.
Qed.

Lemma eval_named_renamed (r : renaming) (d : named) (vars vars' : env)
    (statics : static_env) :
  (∀ x : variable,
    var_free_in_named x d ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  eval_named statics vars' (rename_named r d) = eval_named statics vars d.
Proof.
  intros Hvars. destruct d as [s | p args | code slots | slot closure]; simpl.
  - apply eval_simple_renamed, Hvars.
  - rewrite (eval_simples_renamed r args vars vars' Hvars). reflexivity.
  - rewrite (eval_value_slots_renamed r slots vars vars' Hvars). reflexivity.
  - rewrite (eval_simple_renamed r closure vars vars' Hvars). reflexivity.
Qed.

Lemma eval_static_const_renamed (r : renaming) (const : static_const)
    (vars vars' : env) :
  (∀ x : variable,
    var_free_in_static_const x const ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  eval_static_const vars' (rename_static_const r const)
  = eval_static_const vars const.
Proof.
  intros Hvars. destruct const as [code slots | tag fields | s | bytes]; simpl.
  - rewrite (eval_value_slots_renamed r slots vars vars' Hvars). reflexivity.
  - rewrite (eval_simples_renamed r fields vars vars' Hvars). reflexivity.
  - rewrite (eval_simple_renamed r s vars vars' Hvars). reflexivity.
  - reflexivity.
Qed.

Lemma eval_static_bindings_renamed (r : renaming)
    (bindings : list static_binding) (vars vars' : env) :
  (∀ x : variable,
    Exists (var_free_in_static_binding x) bindings ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  ∀ statics : static_env,
    eval_static_bindings vars' (map (rename_static_binding r) bindings)
      statics
    = eval_static_bindings vars bindings statics.
Proof.
  induction bindings as [ | binding bindings IH]; intros Hvars statics;
    [ reflexivity | ].
  assert (Hrest :
    ∀ x : variable,
      Exists (var_free_in_static_binding x) bindings ->
      lookup (rename_variable r x) vars' = lookup x vars).
  { intros x Hx. apply Hvars. apply Exists_cons_tl. exact Hx. }
  destruct binding as [id c | id | sym const]; simpl;
    [ apply IH, Hrest | apply IH, Hrest | ].
  rewrite (eval_static_const_renamed r const vars vars').
  - destruct (eval_static_const vars const); simpl;
      [ apply IH, Hrest | reflexivity ].
  - intros x Hx. apply Hvars. apply Exists_cons_hd. exact Hx.
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

(* What relates a handler [h] of a closure to its renaming by [r], given
   the environments of the two closures and the handlers defined with
   them: the variable environments agree along [r] on the free variables
   of [h]; a free continuation of [h] that the group does not define is not
   defined by the other group either, and what it stands for in the one
   environment and what [r] sends it to stands for in the other are
   related by [C]; and one that the group defines, with a handler [hk], is
   sent by [r] to one the other group defines with [hk] renamed by the
   renaming chosen for it. *)
Definition handler_agrees (C : cont_value -> cont_value -> Prop)
    (choice : continuation -> renaming) (r : renaming)
    (h : continuation_handler) (vars vars' : env) (conts conts' : cont_env)
    (recursive recursive' : list (continuation * continuation_handler))
    : Prop :=
  (∀ x : variable,
    var_free_in_handler x h ->
    lookup (rename_variable r x) vars' = lookup x vars)
  ∧ (∀ k : continuation,
      cont_free_in_handler k h ->
      lookup k recursive = None ->
      lookup (rename_continuation r k) recursive' = None
      ∧ C (resolve k conts) (resolve (rename_continuation r k) conts'))
  ∧ (∀ (k : continuation) (hk : continuation_handler),
      cont_free_in_handler k h ->
      lookup k recursive = Some hk ->
      lookup (rename_continuation r k) recursive'
      = Some (rename_handler (choice k) hk)).

(* A continuation and its renaming: the same, which covers a way out; or
   two closures, of a handler and its renaming. Each handler of a
   recursive group may have been renamed by a renaming of its own,
   [choice] of its continuation. (The warning silenced is about induction
   schemes, which nothing uses.) *)
#[local] Set Warnings "-register-all".
Inductive closure_renamed : cont_value -> cont_value -> Prop :=
  | Closure_same (c : cont_value) : closure_renamed c c
  | Closure_renamed (choice : continuation -> renaming) (r : renaming)
      (h : continuation_handler) (vars vars' : env) (conts conts' : cont_env)
      (recursive recursive' : list (continuation * continuation_handler)) :
    handler_agrees closure_renamed choice r h vars vars' conts conts'
      recursive recursive' ->
    (∀ (j : continuation) (hj : continuation_handler),
      lookup j recursive = Some hj ->
      handler_agrees closure_renamed choice (choice j) hj vars vars' conts
        conts' recursive recursive') ->
    closure_renamed (Closure h vars conts recursive)
      (Closure (rename_handler r h) vars' conts' recursive').

(* Two continuation environments agree at [k] along [r]: what [k] stands
   for in the one and what [r] sends it to stands for in the other are a
   continuation and its renaming. If neither binds it, [r] fixes it, as it
   is observed. *)
Definition conts_agree_at (r : renaming) (k : continuation)
    (conts conts' : cont_env) : Prop :=
  closure_renamed (resolve k conts)
    (resolve (rename_continuation r k) conts').

Inductive state_renamed : state -> state -> Prop :=
  | State_same (s : state) : state_renamed s s
  | State_renamed (r : renaming) (e : expr) (vars vars' : env)
      (conts conts' : cont_env) (statics : static_env) :
    (∀ x : variable,
      var_free_in_expr x e ->
      lookup (rename_variable r x) vars' = lookup x vars) ->
    (∀ k : continuation,
      cont_free_in_expr k e -> conts_agree_at r k conts conts') ->
    state_renamed (State e vars conts statics)
      (State (rename_expr r e) vars' conts' statics).

(* One environment agrees with itself at a continuation the renaming
   fixes. *)
Lemma conts_agree_same (r : renaming) (k : continuation) (conts : cont_env) :
  rename_continuation r k = k -> conts_agree_at r k conts conts.
Proof.
  intros Hfix. unfold conts_agree_at. rewrite Hfix. apply Closure_same.
Qed.

(* The environments in which the handlers of two groups run, their own
   closures included, agree at the free continuations of a handler that
   agrees. *)
Lemma group_conts_agree (choice : continuation -> renaming) (r : renaming)
    (h : continuation_handler) (vars vars' : env) (conts conts' : cont_env)
    (recursive recursive' : list (continuation * continuation_handler)) :
  handler_agrees closure_renamed choice r h vars vars' conts conts'
    recursive recursive' ->
  (∀ (j : continuation) (hj : continuation_handler),
    lookup j recursive = Some hj ->
    handler_agrees closure_renamed choice (choice j) hj vars vars' conts
      conts' recursive recursive') ->
  ∀ k : continuation,
    cont_free_in_handler k h ->
    conts_agree_at r k (rec_closures recursive vars conts ++ conts)
      (rec_closures recursive' vars' conts' ++ conts').
Proof.
  intros (_ & Hunbound & Hbound) Hgroup k Hk. unfold conts_agree_at, resolve.
  rewrite !lookup_rec_closures_app.
  destruct (lookup k recursive) as [hk | ] eqn:Hlookup.
  - rewrite (Hbound k hk Hk Hlookup).
    apply (Closure_renamed choice (choice k));
      [ exact (Hgroup k hk Hlookup) | exact Hgroup ].
  - destruct (Hunbound k Hk Hlookup) as [Hnone Hagree].
    rewrite Hnone. exact Hagree.
Qed.

(* A closure that is not recursive and its renaming. *)
Lemma closure_renamed_non_recursive (r : renaming) (h : continuation_handler)
    (vars vars' : env) (conts conts' : cont_env) :
  (∀ x : variable,
    var_free_in_handler x h ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  (∀ k : continuation,
    cont_free_in_handler k h -> conts_agree_at r k conts conts') ->
  closure_renamed (Closure h vars conts [])
    (Closure (rename_handler r h) vars' conts' []).
Proof.
  intros Hvars Hconts. apply (Closure_renamed (fun _ => r) r).
  - split; [ exact Hvars | ]. split.
    + intros k Hk _. split; [ reflexivity | exact (Hconts k Hk) ].
    + intros k hk _ Hlookup. discriminate Hlookup.
  - intros j hj Hlookup. discriminate Hlookup.
Qed.

(* A recursive group and its renaming by one renaming throughout: every
   handler agrees. *)
Lemma uniform_group_agrees (r : renaming)
    (handlers : list (continuation * continuation_handler))
    (vars vars' : env) (conts conts' : cont_env) :
  (∀ x : variable,
    any_handler (var_free_in_handler x) handlers ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  (∀ k : continuation,
    lookup k handlers = None ->
    any_handler (cont_free_in_handler k) handlers ->
    conts_agree_at r k conts conts') ->
  ∀ (j : continuation) (hj : continuation_handler),
    lookup j handlers = Some hj ->
    handler_agrees closure_renamed (fun _ => r) r hj vars vars' conts conts'
      handlers (rename_handlers r handlers).
Proof.
  intros Hvars Hconts j hj Hlookup. split; [ | split ].
  - intros x Hx. apply Hvars. exact (lookup_any_handler _ _ _ _ Hlookup Hx).
  - intros k Hk Hnone.
    split; [ rewrite lookup_rename_handlers, Hnone; reflexivity | ].
    apply Hconts; [ exact Hnone | ].
    exact (lookup_any_handler _ _ _ _ Hlookup Hk).
  - intros k hk _ Hk. rewrite lookup_rename_handlers, Hk. reflexivity.
Qed.

(* Agreement at [k] once the closures of such a group and of its renaming
   are added. *)
Lemma uniform_rec_conts_agree (r : renaming)
    (handlers : list (continuation * continuation_handler))
    (vars vars' : env) (conts conts' : cont_env) :
  (∀ x : variable,
    any_handler (var_free_in_handler x) handlers ->
    lookup (rename_variable r x) vars' = lookup x vars) ->
  (∀ k : continuation,
    lookup k handlers = None ->
    any_handler (cont_free_in_handler k) handlers ->
    conts_agree_at r k conts conts') ->
  ∀ k : continuation,
    (lookup k handlers = None -> conts_agree_at r k conts conts') ->
    conts_agree_at r k (rec_closures handlers vars conts ++ conts)
      (rec_closures (rename_handlers r handlers) vars' conts' ++ conts').
Proof.
  intros Hvars Hconts k Hunbound. unfold conts_agree_at, resolve.
  rewrite !lookup_rec_closures_app, lookup_rename_handlers.
  destruct (lookup k handlers) as [hk | ] eqn:Hlookup; simpl.
  - apply (Closure_renamed (fun _ => r) r).
    + exact (uniform_group_agrees r handlers vars vars' conts conts' Hvars
        Hconts k hk Hlookup).
    + exact (uniform_group_agrees r handlers vars vars' conts conts' Hvars
        Hconts).
  - apply Hunbound. reflexivity.
Qed.

(* Applying a continuation and its renaming to the same values. *)
Lemma apply_cont_value_renamed (c c' : cont_value) (vs : list value)
    (statics : static_env) :
  closure_renamed c c' ->
  result_related state_renamed (apply_cont_value c vs statics)
    (apply_cont_value c' vs statics).
Proof.
  intros
    [[[params handler] vars conts0 recursive | exit]
    | choice r' [params handler] vars vars' conts0 conts0' recursive
        recursive' Hh Hgroup];
    simpl.
  - destruct (bind_params params vs vars); simpl;
      [ apply State_same | exact I ].
  - auto.
  - pose proof (bind_params_renamed r' params vs vars vars') as Hbind.
    destruct (bind_params params vs vars),
      (bind_params (map (rename_variable r') params) vs vars');
      try contradiction; simpl; [ | exact I ].
    apply State_renamed.
    + intros x Hx. apply Hbind.
      destruct (in_dec Pos.eq_dec x params) as [Hin | Hnotin];
        [ left; exact Hin | right ].
      apply (proj1 Hh). split; assumption.
    + intros k' Hk'.
      exact (group_conts_agree _ _ _ _ _ _ _ _ _ Hh Hgroup k' Hk').
Qed.

(* One expression under environments that agree on its free names is a
   state and its renaming by the identity. *)
Lemma state_renamed_identity (e : expr) (vars vars' : env)
    (conts conts' : cont_env) (statics : static_env) :
  (∀ x : variable, var_free_in_expr x e -> lookup x vars' = lookup x vars) ->
  (∀ k : continuation,
    cont_free_in_expr k e -> conts_agree_at identity_renaming k conts conts')
  ->
  state_renamed (State e vars conts statics) (State e vars' conts' statics).
Proof.
  intros Hvars Hconts.
  pose proof (State_renamed identity_renaming e vars vars' conts conts'
    statics Hvars Hconts) as Hrenamed.
  rewrite rename_expr_id in Hrenamed. exact Hrenamed.
Qed.

(* A state and its renaming step alike. *)
Lemma renamed_step (s s' : state) :
  state_renamed s s' -> result_related state_renamed (step s) (step s').
Proof.
  intros [s0 | r e vars vars' conts conts' statics Hvars Hconts].
  - apply result_related_refl, State_same.
  - destruct e
      as [ x d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl.
    + (* Let *)
      rewrite (eval_named_renamed r d vars vars' statics);
        [ | intros y Hy; apply Hvars; left; exact Hy ].
      destruct (eval_named statics vars d) as [v | ]; simpl; [ | exact I ].
      apply State_renamed.
      * intros y Hy. simpl. rewrite rename_variable_eqb.
        destruct (Pos.eqb_spec y x) as [-> | Hne]; [ reflexivity | ].
        apply Hvars. right. split; assumption.
      * intros k Hk. apply Hconts. exact Hk.
    + (* Let_static: the same static environment *)
      rewrite (eval_static_bindings_renamed r bindings vars vars');
        [ | intros y Hy; apply Hvars; left; exact Hy ].
      destruct (eval_static_bindings vars bindings statics) as [statics' | ];
        simpl; [ | exact I ].
      apply State_renamed.
      * intros y Hy. apply Hvars. right. exact Hy.
      * intros k Hk. apply Hconts. exact Hk.
    + (* Let_cont_non_recursive *)
      apply State_renamed.
      * intros y Hy. apply Hvars. right. exact Hy.
      * intros k' Hk'. unfold conts_agree_at, resolve. simpl.
        rewrite rename_continuation_eqb.
        destruct (Pos.eqb_spec k' k) as [-> | Hne].
        -- apply closure_renamed_non_recursive.
           ++ intros x Hx. apply Hvars. left. exact Hx.
           ++ intros k'' Hk''. apply Hconts. left. exact Hk''.
        -- exact (Hconts k' (or_intror (conj Hne Hk'))).
    + (* Let_cont_recursive *)
      apply State_renamed.
      * intros y Hy. apply Hvars. right. exact Hy.
      * intros k Hk. apply uniform_rec_conts_agree.
        -- intros x Hx. apply Hvars. left. exact Hx.
        -- intros k' Hunbound Hk'. apply Hconts.
           split; [ exact Hunbound | left; exact Hk' ].
        -- intros Hunbound. apply Hconts.
           split; [ exact Hunbound | right; exact Hk ].
    + (* Apply: the same call, as code is not renamed, returning to a
         continuation and its renaming *)
      rewrite (eval_simple_renamed r (ap_callee ap) vars vars');
        [ | intros y Hy; apply Hvars; left; exact Hy ].
      rewrite (eval_simples_renamed r (ap_args ap) vars vars');
        [ | intros y Hy; apply Hvars; right; exact Hy ].
      destruct (eval_simple vars (ap_callee ap)) as [closure | ];
        [ | exact I ].
      destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | exact I ].
      destruct (call_function_cases closure (ap_call_kind ap) vs statics)
        as [Hundefined | (body & callee_vars & ret & exn & Hcall)].
      * rewrite !Hundefined. exact I.
      * rewrite !Hcall. simpl.
        apply state_renamed_identity; [ reflexivity | ].
        intros k _. unfold conts_agree_at, resolve.
        change (rename_continuation identity_renaming k) with k. simpl.
        destruct (Pos.eqb k ret);
          [ exact (Hconts (ap_continuation ap) (or_introl eq_refl)) | ].
        destruct (Pos.eqb k exn);
          [ exact (Hconts (ap_exn_continuation ap) (or_intror eq_refl)) | ].
        apply Closure_same.
    + (* Apply_cont *)
      rewrite (eval_simples_renamed r (ac_args ac) vars vars');
        [ | intros y Hy; apply Hvars; exact Hy ].
      destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | exact I ].
      apply apply_cont_value_renamed, Hconts. reflexivity.
    + (* Switch *)
      rewrite (eval_simple_renamed r scrutinee vars vars');
        [ | intros y Hy; apply Hvars; left; exact Hy ].
      destruct (eval_simple vars scrutinee) as [v | ]; [ | exact I ].
      destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
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
    (conts conts' : cont_env) (statics : static_env) :
  (∀ x : variable, var_free_in_expr x e -> lookup x vars' = lookup x vars) ->
  (∀ k : continuation,
    cont_free_in_expr k e -> conts_agree_at identity_renaming k conts conts')
  ->
  equivalent (State e vars conts statics) (State e vars' conts' statics).
Proof.
  intros Hvars Hconts.
  apply renamed_equivalent, state_renamed_identity; assumption.
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
  intros r x d body Hvars Hconts vars conts statics.
  destruct (eval_named statics vars d) as [v | ] eqn:Hd.
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
  intros r k h body Hvars Hconts vars conts statics.
  eapply equivalent_step; [ reflexivity | reflexivity | ].
  apply renamed_equivalent, State_renamed.
  - intros y Hy. rewrite (Hvars y Hy). reflexivity.
  - intros k' Hk'. unfold conts_agree_at, resolve. simpl.
    rewrite rename_continuation_eqb.
    destruct (Pos.eqb_spec k' k) as [-> | Hne]; [ apply Closure_same | ].
    exact (conts_agree_same r k' conts (Hconts k' Hne Hk')).
Qed.

Theorem rename_handler_params : rename_handler_params_statement.
Proof.
  intros r k params handler body Hvars Hconts vars conts statics.
  eapply equivalent_step; [ reflexivity | reflexivity | ].
  apply coincide_equivalent; [ reflexivity | ].
  intros k' _. unfold conts_agree_at, resolve.
  change (rename_continuation identity_renaming k') with k'. simpl.
  destruct (Pos.eqb k' k).
  - apply (closure_renamed_non_recursive r (Handler params handler) vars vars
      conts conts).
    + intros x [Hnotin Hx]. rewrite (Hvars x Hnotin Hx). reflexivity.
    + intros k'' Hk''. apply conts_agree_same, Hconts, Hk''.
  - exact (conts_agree_same identity_renaming k' conts eq_refl).
Qed.

Theorem rename_let_cont_recursive : rename_let_cont_recursive_statement.
Proof.
  intros r handlers body Hvars Hconts vars conts statics.
  eapply equivalent_step; [ reflexivity | reflexivity | ].
  apply renamed_equivalent, State_renamed.
  - intros y Hy. rewrite (Hvars y); [ reflexivity | right; exact Hy ].
  - intros k Hk. apply uniform_rec_conts_agree.
    + intros x Hx. rewrite (Hvars x); [ reflexivity | left; exact Hx ].
    + intros k' Hunbound Hk'. apply conts_agree_same, Hconts.
      split; [ exact Hunbound | left; exact Hk' ].
    + intros Hunbound. apply conts_agree_same, Hconts.
      split; [ exact Hunbound | right; exact Hk ].
Qed.

Lemma lookup_app {A : Type} (name : positive)
    (bindings bindings' : list (positive * A)) :
  lookup name (bindings ++ bindings')
  = match lookup name bindings with
    | Some a => Some a
    | None => lookup name bindings'
    end.
Proof.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ reflexivity | ].
  destruct (Pos.eqb name bound); [ reflexivity | exact IH ].
Qed.

(* The parameters of one handler of a recursive group: that handler is
   renamed by [r] and the others are left as they are. *)
Theorem rename_recursive_handler_params :
  rename_recursive_handler_params_statement.
Proof.
  intros r before k params handler after body Hvars Hconts vars conts statics.
  set (h := Handler params handler).
  set (handlers := before ++ (k, h) :: after).
  set (handlers' := before ++ (k, rename_handler r h) :: after).
  set (choice := fun j : continuation =>
    match lookup j before with
    | Some _ => identity_renaming
    | None => if Pos.eqb j k then r else identity_renaming
    end).
  (* The handler of a continuation in the two groups. *)
  assert (Hbound :
    ∀ (j : continuation) (hj : continuation_handler),
      lookup j handlers = Some hj ->
      lookup j handlers' = Some (rename_handler (choice j) hj)).
  { intros j hj. subst handlers handlers' choice. simpl.
    rewrite !lookup_app. destruct (lookup j before) as [h0 | ].
    - intros [= ->]. rewrite rename_handler_id. reflexivity.
    - simpl. destruct (Pos.eqb j k).
      + intros [= <-]. reflexivity.
      + intros ->. rewrite rename_handler_id. reflexivity. }
  assert (Hunbound :
    ∀ j : continuation,
      lookup j handlers = None -> lookup j handlers' = None).
  { intros j. subst handlers handlers'. rewrite !lookup_app.
    destruct (lookup j before); [ discriminate | ]. simpl.
    destruct (Pos.eqb j k); [ discriminate | auto ]. }
  (* The renaming chosen for a handler fixes its free names. *)
  assert (Hfix :
    ∀ (j : continuation) (hj : continuation_handler),
      lookup j handlers = Some hj ->
      (∀ x : variable,
        var_free_in_handler x hj -> rename_variable (choice j) x = x)
      ∧ (∀ k' : continuation,
          cont_free_in_handler k' hj ->
          rename_continuation (choice j) k' = k')).
  { intros j hj. subst handlers choice. simpl. rewrite lookup_app.
    destruct (lookup j before) as [h0 | ]; [ intros _; split; reflexivity | ].
    simpl. destruct (Pos.eqb j k); [ | intros _; split; reflexivity ].
    intros [= <-]. split.
    - intros x [Hnotin Hx]. exact (Hvars x Hnotin Hx).
    - intros k' Hk'. exact (Hconts k' Hk'). }
  assert (Hgroup :
    ∀ (j : continuation) (hj : continuation_handler),
      lookup j handlers = Some hj ->
      handler_agrees closure_renamed choice (choice j) hj vars vars conts
        conts handlers handlers').
  { intros j hj Hlookup. destruct (Hfix j hj Hlookup) as [Hfixv Hfixk].
    split; [ | split ].
    - intros x Hx. rewrite (Hfixv x Hx). reflexivity.
    - intros k' Hk' Hnone. rewrite (Hfixk k' Hk').
      split; [ exact (Hunbound k' Hnone) | apply Closure_same ].
    - intros k' hk Hk' Hlookup'. rewrite (Hfixk k' Hk').
      exact (Hbound k' hk Hlookup'). }
  eapply equivalent_step; [ reflexivity | reflexivity | ].
  apply coincide_equivalent; [ reflexivity | ].
  intros k' _. unfold conts_agree_at, resolve.
  change (rename_continuation identity_renaming k') with k'.
  rewrite !lookup_rec_closures_app.
  destruct (lookup k' handlers) as [hk | ] eqn:Hlookup.
  - rewrite (Hbound k' hk Hlookup).
    apply (Closure_renamed choice (choice k'));
      [ exact (Hgroup k' hk Hlookup) | exact Hgroup ].
  - rewrite (Hunbound k' Hlookup).
    exact (conts_agree_same identity_renaming k' conts eq_refl).
Qed.

(* ======================================================================== *)
(* Bindings that are not used                                               *)
(* ======================================================================== *)

Theorem unused_let : unused_let_statement.
Proof.
  intros x d body Hunused vars conts statics.
  destruct (eval_named statics vars d) as [v | ] eqn:Hd.
  - apply equivalent_refines.
    apply (equivalent_trans _ (State body ((x, v) :: vars) conts statics));
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
  intros k h body Hunused vars conts statics.
  eapply equivalent_trans; [ apply step_equivalent; reflexivity | ].
  apply coincide_equivalent; [ reflexivity | ].
  intros k' Hk'. unfold conts_agree_at, resolve.
  change (rename_continuation identity_renaming k') with k'. simpl.
  destruct (Pos.eqb_spec k' k) as [-> | _]; [ contradiction | ].
  exact (conts_agree_same identity_renaming k' conts eq_refl).
Qed.

Theorem unused_let_cont_recursive : unused_let_cont_recursive_statement.
Proof.
  intros handlers body Hunused vars conts statics.
  eapply equivalent_trans; [ apply step_equivalent; reflexivity | ].
  apply coincide_equivalent; [ reflexivity | ].
  intros k Hk. unfold conts_agree_at, resolve.
  change (rename_continuation identity_renaming k) with k.
  rewrite lookup_rec_closures_app, (Hunused k Hk).
  exact (conts_agree_same identity_renaming k conts eq_refl).
Qed.
