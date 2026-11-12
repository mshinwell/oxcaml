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


(* Proofs of the statements of FlambdaStaticsScopeSpec.v. Nothing here
   needs review.

   Each rewrite is shown to give a term that keeps the scope of the
   term it is given (FlambdaScopedProofs.scoped), by recursion on the
   term with the lemmas of that file for each construct. A group whose
   bindings are permuted has the same closed code and the same free
   names; a group with bindings removed has no more of either. *)

From Stdlib Require Import ZArith List Bool Permutation.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaBindersSpec
  FlambdaNormaliseSpec FlambdaUnusedStaticsSpec FlambdaStaticsOrderSpec
  FlambdaMyClosureSpec FlambdaLiftSpec FlambdaUnusedSlotsSpec
  FlambdaKnownSymbolsSpec FlambdaValidateSpec
  FlambdaValidatorEquivarianceSpec FlambdaScopedProofs
  FlambdaKeepsScopeProofs FlambdaStaticsScopeSpec.
Import ListNotations.

(* ======================================================================== *)
(* Groups of bindings, and a [Let] added                                    *)
(* ======================================================================== *)

(* The same bindings in another order. *)
Lemma scoped_bindings_permutation (bindings bindings' : list static_binding) :
  Permutation bindings bindings' -> scoped_bindings bindings bindings'.
Proof.
  intros Hperm Hclosed.
  assert (Hin : ∀ binding : static_binding,
            In binding bindings' -> In binding bindings).
  { intros binding. apply Permutation_in, Permutation_sym, Hperm. }
  split; [ | split ].
  - apply forallb_forall. intros binding Hbinding.
    exact (proj1 (forallb_forall _ _) Hclosed binding (Hin binding Hbinding)).
  - intros x Hx. apply in_flat_map in Hx. destruct Hx as (binding & Hb & Hx).
    apply in_flat_map. exists binding. split; [ apply Hin, Hb | exact Hx ].
  - intros k Hk. apply in_flat_map in Hk. destruct Hk as (binding & Hb & Hk).
    apply in_flat_map. exists binding. split; [ apply Hin, Hb | exact Hk ].
Qed.

(* A binding removed from the front. *)
Lemma scoped_bindings_drop (binding : static_binding)
    (bindings bindings' : list static_binding) :
  scoped_bindings bindings bindings' ->
  scoped_bindings (binding :: bindings) bindings'.
Proof.
  intros Hbindings Hclosed. cbn [forallb flat_map] in Hclosed |- *.
  apply andb_true_iff in Hclosed. destruct Hclosed as [_ Hrest].
  destruct (Hbindings Hrest) as (Hrest' & Hv & Hk).
  split; [ exact Hrest' | split; apply incl_appr; assumption ].
Qed.

(* A symbol bound to a constant with no more variables. *)
Lemma scoped_bindings_cons_symbol (s : symbol) (const const' : static_const)
    (bindings bindings' : list static_binding) :
  incl (free_variables_of_static_const const')
    (free_variables_of_static_const const) ->
  scoped_bindings bindings bindings' ->
  scoped_bindings (Bind_symbol s const :: bindings)
    (Bind_symbol s const' :: bindings').
Proof.
  intros Hconst Hbindings Hclosed. cbn [forallb flat_map] in Hclosed |- *.
  apply andb_true_iff in Hclosed. destruct Hclosed as [_ Hrest].
  destruct (Hbindings Hrest) as (Hrest' & Hv & Hk).
  scope. rewrite Hrest'.
  split; [ reflexivity | ].
  split; (apply incl_app_app; [ | assumption ]);
    [ exact Hconst | apply incl_refl ].
Qed.

(* A [Let] of something with no variable put before a term. *)
Lemma scoped_let_closed (x : variable) (kind : flambda_kind) (d : named)
    (body : expr) :
  free_variables_of_named d = [] -> scoped body (Let x kind d body).
Proof.
  intros Hd Hclosed. scope. rewrite Hd.
  split; [ exact Hclosed | split; [ | apply incl_refl ] ].
  intros y Hy. apply in_without in Hy. exact (proj1 Hy).
Qed.

(* ======================================================================== *)
(* The removal of static bindings                                           *)
(* ======================================================================== *)

Fixpoint erase_expr_scoped (D : dropped) (e : expr) {struct e} :
  scoped e (erase_expr D e)
with erase_handler_scoped (D : dropped) (h : continuation_handler)
    {struct h} :
  scoped_handler h (erase_handler D h)
with erase_code_scoped (D : dropped) (c : code) {struct c} :
  scoped_code c (erase_code D c).
Proof.
  - destruct e as [x kind d body | bindings body | k h body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [erase_expr]; try apply scoped_refl.
    + apply scoped_let; [ apply incl_refl | apply erase_expr_scoped ].
    + apply scoped_let_static; [ | apply erase_expr_scoped ].
      induction bindings as [ | binding bindings IH]; cbn [keep_map];
        [ apply scoped_bindings_nil | ].
      destruct (binding_kept D binding);
        [ | apply scoped_bindings_drop, IH ].
      destruct binding as [id c | id | sym const]; cbn [erase_binding].
      * apply scoped_bindings_cons_code;
          [ apply erase_code_scoped | exact IH ].
      * apply scoped_bindings_cons_same, IH.
      * apply scoped_bindings_cons_same, IH.
    + apply scoped_let_cont;
        [ apply erase_handler_scoped | apply erase_expr_scoped ].
    + apply scoped_let_cont_recursive; [ | | apply erase_expr_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons; [ apply erase_handler_scoped | exact IH ].
  - destruct h as [params metadata handler]. cbn [erase_handler].
    apply scoped_handler_intro, erase_expr_scoped.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [erase_code]. apply scoped_code_intro, erase_expr_scoped.
Qed.

Theorem erase_expr_keeps_scope : erase_expr_keeps_scope_statement.
Proof.
  intros D. apply keeps_scope_intro. intros e. apply erase_expr_scoped.
Qed.

Theorem without_statics_keeps_scope : without_statics_keeps_scope_statement.
Proof.
  intros unused. apply keeps_scope_intro. intros e.
  unfold without_statics, drop_statics.
  destruct (expr_avoids unused e); [ | apply scoped_refl ].
  eapply scoped_trans; [ apply erase_expr_scoped | ].
  eapply scoped_trans;
    [ apply drop_deleted_code_scoped | apply merge_statics_scoped ].
Qed.

(* ======================================================================== *)
(* The order of static bindings                                             *)
(* ======================================================================== *)

Lemma to_front_permutation (is_it : static_binding -> bool)
    (bindings : list static_binding) :
  Permutation bindings (to_front is_it bindings).
Proof.
  induction bindings as [ | binding rest IH]; cbn [to_front];
    [ apply perm_nil | ].
  destruct (is_it binding); [ apply Permutation_refl | ].
  destruct (to_front is_it rest) as [ | found rest'];
    [ apply Permutation_refl | ].
  destruct (is_it found); [ | apply Permutation_refl ].
  eapply perm_trans; [ apply perm_skip, IH | apply perm_swap ].
Qed.

Lemma order_as_permutation (pattern bindings : list static_binding) :
  Permutation bindings (order_as pattern bindings).
Proof.
  unfold order_as.
  induction pattern as [ | named pattern IH]; cbn [fold_right];
    [ apply Permutation_refl | ].
  eapply perm_trans; [ exact IH | apply to_front_permutation ].
Qed.

Fixpoint order_statics_as_scoped (e : expr) :
  ∀ pattern : expr, scoped e (order_statics_as pattern e).
Proof.
  intros pattern.
  destruct e as [x kind d body | bindings body | k h body | handlers body
                | ap | ac | scrutinee arms | ];
    try apply scoped_refl.
  - destruct pattern; cbn [order_statics_as]; try apply scoped_refl.
    apply scoped_let; [ apply incl_refl | apply order_statics_as_scoped ].
  - destruct pattern as [ | pattern_bindings pattern | | | | | | ];
      cbn [order_statics_as]; try apply scoped_refl.
    apply scoped_let_static; [ | apply order_statics_as_scoped ].
    apply scoped_bindings_permutation, order_as_permutation.
  - destruct h as [params metadata handler].
    destruct pattern as [ | | pattern_k pattern_h pattern | | | | | ];
      cbn [order_statics_as]; try apply scoped_refl.
    destruct pattern_h as [pattern_params pattern_metadata pattern_handler].
    apply scoped_let_cont; [ | apply order_statics_as_scoped ].
    apply scoped_handler_intro, order_statics_as_scoped.
  - destruct pattern; cbn [order_statics_as]; try apply scoped_refl.
    apply scoped_let_cont_recursive; [ reflexivity | | ].
    + apply scoped_handlers_refl.
    + apply order_statics_as_scoped.
Qed.

Theorem order_statics_as_keeps_scope : order_statics_as_keeps_scope_statement.
Proof.
  intros pattern. apply keeps_scope_intro. intros e.
  apply order_statics_as_scoped.
Qed.

(* ======================================================================== *)
(* The lifting                                                              *)
(* ======================================================================== *)

(* What a group of bindings that stands for a defining expression is
   asked: no code, no variable but those of the expression. *)
Definition stands_for (bindings : list static_binding) (d : named) : Prop :=
  forallb binding_code_closed bindings = true
  ∧ incl (flat_map free_variables_of_binding bindings)
      (free_variables_of_named d)
  ∧ flat_map free_continuations_of_binding bindings = [].

(* The bindings of the closures of a set: each binds a symbol to the
   set, with its value slots. *)
Lemma closure_bindings_stand_for (all l : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) (slot : function_slot) :
  stands_for
    (map
       (fun '(slot, s) =>
          Bind_symbol s
            (Static_const_closure_of_set slot all function_decls value_slots))
       l)
    (Closure_of_set slot function_decls value_slots).
Proof.
  unfold stands_for.
  induction l as [ | [slot' s] l IH]; cbn [map forallb flat_map].
  - split; [ reflexivity | split; [ apply incl_nil_l | reflexivity ] ].
  - destruct IH as (Hclosed & Hv & Hk). scope.
    cbn [free_variables_of_static_const free_variables_of_named] in Hv |- *.
    rewrite Hclosed, Hk.
    split; [ reflexivity | split; [ | reflexivity ] ].
    apply incl_app; [ apply incl_refl | exact Hv ].
Qed.

Lemma lift_named_stands_for (target : lift_to) (d : named)
    (bindings : list static_binding) (s : symbol) :
  lift_named target d = Some (bindings, s) -> stands_for bindings d.
Proof.
  unfold lift_named. intros Hlift.
  repeat
    match type of Hlift with
    | match ?x with _ => _ end = Some _ =>
      destruct x eqn:?; try discriminate Hlift
    | (if ?c then _ else _) = Some _ =>
      destruct c eqn:?; try discriminate Hlift
    end;
    injection Hlift as <- <-;
    try apply closure_bindings_stand_for;
    unfold stands_for; cbn [forallb flat_map]; scope;
    cbn [free_variables_of_static_const free_variables_of_named
         free_variables_of_simples flat_map];
    rewrite ?app_nil_r;
    (split; [ reflexivity | split; [ apply incl_refl | reflexivity ] ]).
Qed.

(* A [Let] lifted: a group that stands for its defining expression, and
   a [Let] of a symbol. *)
Lemma scoped_let_lifted (x : variable) (kind : flambda_kind) (d : named)
    (bindings : list static_binding) (s : symbol) (body body' : expr) :
  stands_for bindings d ->
  scoped body body' ->
  scoped (Let x kind d body)
    (Let_static bindings (Let x kind (Simple (Symbol s)) body')).
Proof.
  intros (Hclosed_b & Hv_b & Hk_b) Hbody Hclosed. scope_in Hclosed. scope.
  destruct (Hbody Hclosed) as (Hclosed' & Hv & Hk).
  rewrite Hclosed_b, Hclosed', Hk_b.
  split; [ reflexivity | split; [ | exact Hk ] ].
  apply incl_app_app; [ exact Hv_b | ].
  cbn [free_variables_of_named free_variables_of_simple app].
  apply incl_without, Hv.
Qed.

Fixpoint lift_expr_scoped (lets : list (path * lift_to)) (e : expr)
    {struct e} :
  ∀ at_path : path, scoped e (lift_expr lets at_path e)
with lift_handler_scoped (lets : list (path * lift_to))
    (h : continuation_handler) {struct h} :
  ∀ at_path : path, scoped_handler h (lift_handler lets at_path h).
Proof.
  - intros at_path.
    destruct e as [x kind d body | bindings body | k h body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [lift_expr]; try apply scoped_refl.
    + destruct (lookup at_path lets) as [target | ];
        [ | apply scoped_let; [ apply incl_refl | apply lift_expr_scoped ] ].
      destruct (lift_named target d) as [[bindings s] | ] eqn:Hlift;
        [ | apply scoped_let; [ apply incl_refl | apply lift_expr_scoped ] ].
      apply scoped_let_lifted;
        [ exact (lift_named_stands_for _ _ _ _ Hlift)
        | apply lift_expr_scoped ].
    + apply scoped_let_static;
        [ apply scoped_bindings_refl | apply lift_expr_scoped ].
    + apply scoped_let_cont;
        [ apply lift_handler_scoped | apply lift_expr_scoped ].
    + apply scoped_let_cont_recursive; [ reflexivity | | ].
      * apply scoped_handlers_refl.
      * apply lift_expr_scoped.
  - intros at_path. destruct h as [params metadata handler].
    cbn [lift_handler]. apply scoped_handler_intro, lift_expr_scoped.
Qed.

Theorem lift_expr_keeps_scope : lift_expr_keeps_scope_statement.
Proof.
  intros lets at_path. apply keeps_scope_intro. intros e.
  apply lift_expr_scoped.
Qed.

Fixpoint bind_my_closures_scoped (known : list (code_id * symbol)) (e : expr)
    {struct e} :
  scoped e (bind_my_closures known e)
with bind_my_closures_in_handler_scoped (known : list (code_id * symbol))
    (h : continuation_handler) {struct h} :
  scoped_handler h (bind_my_closures_in_handler known h)
with bind_my_closure_scoped (known : list (code_id * symbol)) (id : code_id)
    (c : code) {struct c} :
  scoped_code c (bind_my_closure known id c).
Proof.
  - destruct e as [x kind d body | bindings body | k h body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [bind_my_closures]; try apply scoped_refl.
    + apply scoped_let; [ apply incl_refl | apply bind_my_closures_scoped ].
    + apply scoped_let_static; [ | apply bind_my_closures_scoped ].
      induction bindings as [ | binding bindings IH]; cbn [map];
        [ apply scoped_bindings_nil | ].
      destruct binding as [id c | id | sym const];
        cbn [bind_my_closures_in_binding].
      * apply scoped_bindings_cons_code;
          [ apply bind_my_closure_scoped | exact IH ].
      * apply scoped_bindings_cons_same, IH.
      * apply scoped_bindings_cons_same, IH.
    + apply scoped_let_cont;
        [ apply bind_my_closures_in_handler_scoped
        | apply bind_my_closures_scoped ].
    + apply scoped_let_cont_recursive; [ | | apply bind_my_closures_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply bind_my_closures_in_handler_scoped | exact IH ].
  - destruct h as [params metadata handler].
    cbn [bind_my_closures_in_handler].
    apply scoped_handler_intro, bind_my_closures_scoped.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [bind_my_closure].
    destruct (lookup id known) as [s | ];
      [ | apply scoped_code_intro, bind_my_closures_scoped ].
    destruct (among my_closure params);
      [ apply scoped_code_intro, bind_my_closures_scoped | ].
    apply scoped_code_intro.
    eapply scoped_trans;
      [ apply bind_my_closures_scoped | apply scoped_let_closed; reflexivity ].
Qed.

Theorem bind_my_closures_keeps_scope : bind_my_closures_keeps_scope_statement.
Proof.
  intros known. apply keeps_scope_intro. intros e.
  apply bind_my_closures_scoped.
Qed.

Theorem with_lifting_keeps_scope : with_lifting_keeps_scope_statement.
Proof.
  intros L. apply keeps_scope_intro. intros e.
  unfold with_lifting, lift_unit. cbv zeta.
  match goal with
  | |- scoped _ (match (if ?c then _ else _) with _ => _ end) => destruct c
  end;
    [ | apply scoped_refl ].
  eapply scoped_trans;
    [ apply lift_expr_scoped | apply bind_my_closures_scoped ].
Qed.

(* ======================================================================== *)
(* What the unit binds its symbols to                                       *)
(* ======================================================================== *)

Lemma fold_known_named_free (statics : static_env) (d : named) :
  incl (free_variables_of_named (fold_known_named statics d))
    (free_variables_of_named d).
Proof.
  unfold fold_known_named.
  destruct (named_known statics d); [ | apply incl_refl ].
  destruct (eval_named statics [] d) as [v | ]; [ | apply incl_refl ].
  destruct v; try apply incl_refl; apply incl_nil_l.
Qed.

Fixpoint fold_known_scoped (statics : static_env) (e : expr) {struct e} :
  scoped e (fold_known statics e)
with fold_known_handler_scoped (statics : static_env)
    (h : continuation_handler) {struct h} :
  scoped_handler h (fold_known_handler statics h)
with fold_known_code_scoped (statics : static_env) (c : code) {struct c} :
  scoped_code c (fold_known_code statics c).
Proof.
  - destruct e as [x kind d body | bindings body | k h body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [fold_known]; try apply scoped_refl.
    + apply scoped_let;
        [ apply fold_known_named_free | apply fold_known_scoped ].
    + apply scoped_let_static; [ | apply fold_known_scoped ].
      induction bindings as [ | binding bindings IH]; cbn [map];
        [ apply scoped_bindings_nil | ].
      destruct binding as [id c | id | sym const]; cbn [fold_known_binding].
      * apply scoped_bindings_cons_code;
          [ apply fold_known_code_scoped | exact IH ].
      * apply scoped_bindings_cons_same, IH.
      * apply scoped_bindings_cons_same, IH.
    + apply scoped_let_cont;
        [ apply fold_known_handler_scoped | apply fold_known_scoped ].
    + apply scoped_let_cont_recursive; [ | | apply fold_known_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply fold_known_handler_scoped | exact IH ].
  - destruct h as [params metadata handler]. cbn [fold_known_handler].
    apply scoped_handler_intro, fold_known_scoped.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [fold_known_code]. apply scoped_code_intro, fold_known_scoped.
Qed.

Theorem fold_known_keeps_scope : fold_known_keeps_scope_statement.
Proof.
  intros statics. apply keeps_scope_intro. intros e. apply fold_known_scoped.
Qed.

Theorem with_known_keeps_scope : with_known_keeps_scope_statement.
Proof.
  apply keeps_scope_intro. intros e. unfold with_known, fold_known_unit.
  cbv zeta. destruct (bound_as (known_bindings e) e);
    [ apply fold_known_scoped | apply scoped_refl ].
Qed.

(* ======================================================================== *)
(* The removal of value slots                                               *)
(* ======================================================================== *)

Lemma drop_slots_static_const_free (dropped : list value_slot)
    (const : static_const) :
  incl (free_variables_of_static_const (drop_slots_static_const dropped const))
    (free_variables_of_static_const const).
Proof.
  destruct const;
    cbn [drop_slots_static_const free_variables_of_static_const];
    try apply incl_refl;
    unfold free_variables_of_value_slots, keep_slots;
    apply incl_flat_map_filter.
Qed.

Fixpoint drop_slots_scoped (dropped : list value_slot) (e : expr) {struct e} :
  scoped e (drop_slots dropped e)
with drop_slots_handler_scoped (dropped : list value_slot)
    (h : continuation_handler) {struct h} :
  scoped_handler h (drop_slots_handler dropped h)
with drop_slots_code_scoped (dropped : list value_slot) (c : code)
    {struct c} :
  scoped_code c (drop_slots_code dropped c).
Proof.
  - destruct e as [x kind d body | bindings body | k h body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [drop_slots]; try apply scoped_refl.
    + apply scoped_let; [ apply incl_refl | apply drop_slots_scoped ].
    + apply scoped_let_static; [ | apply drop_slots_scoped ].
      induction bindings as [ | binding bindings IH]; cbn [map];
        [ apply scoped_bindings_nil | ].
      destruct binding as [id c | id | sym const]; cbn [drop_slots_binding].
      * apply scoped_bindings_cons_code;
          [ apply drop_slots_code_scoped | exact IH ].
      * apply scoped_bindings_cons_same, IH.
      * apply scoped_bindings_cons_symbol;
          [ apply drop_slots_static_const_free | exact IH ].
    + apply scoped_let_cont;
        [ apply drop_slots_handler_scoped | apply drop_slots_scoped ].
    + apply scoped_let_cont_recursive; [ | | apply drop_slots_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply drop_slots_handler_scoped | exact IH ].
  - destruct h as [params metadata handler]. cbn [drop_slots_handler].
    apply scoped_handler_intro, drop_slots_scoped.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [drop_slots_code]. apply scoped_code_intro, drop_slots_scoped.
Qed.

Theorem drop_slots_keeps_scope : drop_slots_keeps_scope_statement.
Proof.
  intros dropped. apply keeps_scope_intro. intros e. apply drop_slots_scoped.
Qed.

Theorem without_slots_keeps_scope : without_slots_keeps_scope_statement.
Proof.
  intros slots. apply keeps_scope_intro. intros e.
  unfold without_slots, drop_unused_slots.
  destruct (slots_unused slots e);
    [ apply drop_slots_scoped | apply scoped_refl ].
Qed.
