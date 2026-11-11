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

(* Proofs of the statements of FlambdaAlphaSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Bool Setoid.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaBindersSpec FlambdaBindersProofs
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaContextSpec
  FlambdaContextProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaAlphaSpec.
Import ListNotations.

Lemma or_iff (A A' B B' : Prop) :
  (A <-> A') -> (B <-> B') -> (A ∨ B <-> A' ∨ B').
Proof. tauto. Qed.

Lemma and_iff (A A' B B' : Prop) :
  (A <-> A') -> (B <-> B') -> (A ∧ B <-> A' ∧ B').
Proof. tauto. Qed.

(* ======================================================================== *)
(* Permutations: composition and inverse                                    *)
(* ======================================================================== *)

Lemma swap_involutive (a b x : positive) : swap a b (swap a b x) = x.
Proof.
  unfold swap. destruct (Pos.eqb_spec x a) as [-> | Hxa].
  - destruct (Pos.eqb_spec b a) as [-> | _]; [ reflexivity | ].
    rewrite Pos.eqb_refl. reflexivity.
  - destruct (Pos.eqb_spec x b) as [-> | Hxb].
    + rewrite Pos.eqb_refl. reflexivity.
    + destruct (Pos.eqb_spec x a); [ contradiction | ].
      destruct (Pos.eqb_spec x b); [ contradiction | reflexivity ].
Qed.

Lemma permute_app (p q : permutation) (x : positive) :
  permute (p ++ q) x = permute p (permute q x).
Proof.
  induction p as [ | [a b] p IH]; simpl; [ reflexivity | ].
  rewrite IH. reflexivity.
Qed.

Lemma permute_rev_l (p : permutation) (x : positive) :
  permute (rev p) (permute p x) = x.
Proof.
  induction p as [ | [a b] p IH]; simpl; [ reflexivity | ].
  rewrite permute_app. simpl. rewrite swap_involutive. exact IH.
Qed.

Lemma permute_rev_r (p : permutation) :
  ∀ x : positive, permute p (permute (rev p) x) = x.
Proof.
  induction p as [ | [a b] p IH]; intros x; simpl; [ reflexivity | ].
  rewrite permute_app. simpl. rewrite IH. apply swap_involutive.
Qed.

Lemma rename_variable_compose (second first : renaming) (x : variable) :
  rename_variable (compose_renaming second first) x
  = rename_variable second (rename_variable first x).
Proof. apply permute_app. Qed.

Lemma rename_continuation_compose (second first : renaming)
    (k : continuation) :
  rename_continuation (compose_renaming second first) k
  = rename_continuation second (rename_continuation first k).
Proof. apply permute_app. Qed.

Lemma rename_variable_inverse_l (r : renaming) (x : variable) :
  rename_variable (inverse_renaming r) (rename_variable r x) = x.
Proof. apply permute_rev_l. Qed.

Lemma rename_variable_inverse_r (r : renaming) (x : variable) :
  rename_variable r (rename_variable (inverse_renaming r) x) = x.
Proof. apply permute_rev_r. Qed.

Lemma rename_continuation_inverse_l (r : renaming) (k : continuation) :
  rename_continuation (inverse_renaming r) (rename_continuation r k) = k.
Proof. apply permute_rev_l. Qed.

Lemma rename_continuation_inverse_r (r : renaming) (k : continuation) :
  rename_continuation r (rename_continuation (inverse_renaming r) k) = k.
Proof. apply permute_rev_r. Qed.

Lemma rename_variable_injective (r : renaming) (x y : variable) :
  rename_variable r x = rename_variable r y -> x = y.
Proof. apply permute_injective. Qed.

Lemma rename_continuation_injective (r : renaming) (k k' : continuation) :
  rename_continuation r k = rename_continuation r k' -> k = k'.
Proof. apply permute_injective. Qed.

Lemma rename_variable_neq (r : renaming) (x y : variable) :
  rename_variable r x <> rename_variable r y <-> x <> y.
Proof.
  split; intros Hne Heq; apply Hne;
    [ rewrite Heq; reflexivity | exact (rename_variable_injective r _ _ Heq) ].
Qed.

Lemma rename_continuation_neq (r : renaming) (k k' : continuation) :
  rename_continuation r k <> rename_continuation r k' <-> k <> k'.
Proof.
  split; intros Hne Heq; apply Hne;
    [ rewrite Heq; reflexivity
    | exact (rename_continuation_injective r _ _ Heq) ].
Qed.

(* ======================================================================== *)
(* The action depends on a renaming as a function only                      *)
(* ======================================================================== *)

Section Extensional.

Variables r r' : renaming.

Hypothesis same_variables :
  ∀ x : variable, rename_variable r x = rename_variable r' x.

Hypothesis same_continuations :
  ∀ k : continuation, rename_continuation r k = rename_continuation r' k.

Lemma rename_simple_ext (s : simple) : rename_simple r s = rename_simple r' s.
Proof.
  destruct s; simpl; rewrite ?same_variables; reflexivity.
Qed.

Lemma rename_named_ext (d : named) : rename_named r d = rename_named r' d.
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure]; simpl;
    rewrite ?rename_simple_ext, ?(map_ext _ _ rename_simple_ext);
    try reflexivity;
    f_equal; apply map_ext; intros [slot s]; simpl;
    rewrite rename_simple_ext; reflexivity.
Qed.

Lemma rename_static_const_ext (const : static_const) :
  rename_static_const r const = rename_static_const r' const.
Proof.
  destruct const
    as [code slots | fslot syms decls slots | tag fields | s | bytes];
    simpl;
    rewrite ?rename_simple_ext, ?(map_ext _ _ rename_simple_ext);
    try reflexivity;
    f_equal; apply map_ext; intros [slot s]; simpl;
    rewrite rename_simple_ext; reflexivity.
Qed.

Lemma rename_apply_ext (ap : apply_expr) :
  rename_apply r ap = rename_apply r' ap.
Proof.
  unfold rename_apply.
  rewrite !same_continuations, rename_simple_ext,
    (map_ext _ _ rename_simple_ext).
  reflexivity.
Qed.

Lemma rename_apply_cont_ext (ac : apply_cont) :
  rename_apply_cont r ac = rename_apply_cont r' ac.
Proof.
  unfold rename_apply_cont.
  rewrite same_continuations, (map_ext _ _ rename_simple_ext). reflexivity.
Qed.

Fixpoint rename_expr_ext (e : expr) : rename_expr r e = rename_expr r' e
with rename_handler_ext (h : continuation_handler) :
  rename_handler r h = rename_handler r' h
with rename_static_binding_ext (binding : static_binding) :
  rename_static_binding r binding = rename_static_binding r' binding
with rename_code_ext (c : code) : rename_code r c = rename_code r' c.
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
      simpl.
    + rewrite same_variables, rename_named_ext, (rename_expr_ext body).
      reflexivity.
    + rewrite (rename_expr_ext body). f_equal.
      induction bindings as [ | binding bindings IH]; simpl;
        [ reflexivity | ].
      rewrite (rename_static_binding_ext binding), IH. reflexivity.
    + rewrite same_continuations, (rename_handler_ext h),
        (rename_expr_ext body). reflexivity.
    + rewrite (rename_expr_ext body). f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite same_continuations, (rename_handler_ext h), IH. reflexivity.
    + rewrite rename_apply_ext. reflexivity.
    + rewrite rename_apply_cont_ext. reflexivity.
    + rewrite rename_simple_ext. f_equal. apply map_ext. intros [i ac].
      simpl. rewrite rename_apply_cont_ext. reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite (rename_expr_ext handler), (map_ext _ _ same_variables).
    reflexivity.
  - destruct binding as [id c | id | sym const]; simpl.
    + rewrite (rename_code_ext c). reflexivity.
    + reflexivity.
    + rewrite rename_static_const_ext. reflexivity.
  - destruct c as [params my_closure ret exn metadata body]. simpl.
    rewrite (rename_expr_ext body), (map_ext _ _ same_variables),
      !same_continuations, same_variables.
    reflexivity.
Qed.

End Extensional.

(* ======================================================================== *)
(* The action of a composition                                              *)
(* ======================================================================== *)

Section Compose.

Variables second first : renaming.

Lemma rename_simple_compose (s : simple) :
  rename_simple (compose_renaming second first) s
  = rename_simple second (rename_simple first s).
Proof.
  destruct s; simpl; rewrite ?rename_variable_compose; reflexivity.
Qed.

Lemma rename_simples_compose (args : list simple) :
  map (rename_simple (compose_renaming second first)) args
  = map (rename_simple second) (map (rename_simple first) args).
Proof. rewrite map_map. apply map_ext, rename_simple_compose. Qed.

Lemma rename_named_compose (d : named) :
  rename_named (compose_renaming second first) d
  = rename_named second (rename_named first d).
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure]; simpl;
    rewrite ?rename_simple_compose, ?rename_simples_compose;
    try reflexivity;
    f_equal; rewrite map_map; apply map_ext; intros [slot s]; simpl;
    rewrite rename_simple_compose; reflexivity.
Qed.

Lemma rename_static_const_compose (const : static_const) :
  rename_static_const (compose_renaming second first) const
  = rename_static_const second (rename_static_const first const).
Proof.
  destruct const
    as [code slots | fslot syms decls slots | tag fields | s | bytes];
    simpl;
    rewrite ?rename_simple_compose, ?rename_simples_compose;
    try reflexivity;
    f_equal; rewrite map_map; apply map_ext; intros [slot s]; simpl;
    rewrite rename_simple_compose; reflexivity.
Qed.

Lemma rename_variables_compose (xs : list variable) :
  map (rename_variable (compose_renaming second first)) xs
  = map (rename_variable second) (map (rename_variable first) xs).
Proof.
  rewrite map_map. apply map_ext. intros x. apply rename_variable_compose.
Qed.

Lemma rename_apply_compose (ap : apply_expr) :
  rename_apply (compose_renaming second first) ap
  = rename_apply second (rename_apply first ap).
Proof.
  unfold rename_apply. simpl.
  rewrite !rename_continuation_compose, rename_simple_compose,
    rename_simples_compose.
  reflexivity.
Qed.

Lemma rename_apply_cont_compose (ac : apply_cont) :
  rename_apply_cont (compose_renaming second first) ac
  = rename_apply_cont second (rename_apply_cont first ac).
Proof.
  unfold rename_apply_cont. simpl.
  rewrite rename_continuation_compose, rename_simples_compose. reflexivity.
Qed.

Fixpoint rename_expr_compose_aux (e : expr) :
  rename_expr (compose_renaming second first) e
  = rename_expr second (rename_expr first e)
with rename_handler_compose (h : continuation_handler) :
  rename_handler (compose_renaming second first) h
  = rename_handler second (rename_handler first h)
with rename_static_binding_compose (binding : static_binding) :
  rename_static_binding (compose_renaming second first) binding
  = rename_static_binding second (rename_static_binding first binding)
with rename_code_compose (c : code) :
  rename_code (compose_renaming second first) c
  = rename_code second (rename_code first c).
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
      simpl.
    + rewrite rename_variable_compose, rename_named_compose,
        (rename_expr_compose_aux body). reflexivity.
    + rewrite (rename_expr_compose_aux body). f_equal.
      induction bindings as [ | binding bindings IH]; simpl;
        [ reflexivity | ].
      rewrite (rename_static_binding_compose binding), IH. reflexivity.
    + rewrite rename_continuation_compose, (rename_handler_compose h),
        (rename_expr_compose_aux body). reflexivity.
    + rewrite (rename_expr_compose_aux body). f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite rename_continuation_compose, (rename_handler_compose h), IH.
      reflexivity.
    + rewrite rename_apply_compose. reflexivity.
    + rewrite rename_apply_cont_compose. reflexivity.
    + rewrite rename_simple_compose. f_equal.
      induction arms as [ | [i ac] arms IH]; simpl; [ reflexivity | ].
      rewrite rename_apply_cont_compose, IH. reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite (rename_expr_compose_aux handler), rename_variables_compose.
    reflexivity.
  - destruct binding as [id c | id | sym const]; simpl.
    + rewrite (rename_code_compose c). reflexivity.
    + reflexivity.
    + rewrite rename_static_const_compose. reflexivity.
  - destruct c as [params my_closure ret exn metadata body]. simpl.
    rewrite (rename_expr_compose_aux body), rename_variables_compose,
      !rename_continuation_compose, rename_variable_compose.
    reflexivity.
Qed.

End Compose.

Theorem rename_expr_identity : rename_expr_identity_statement.
Proof. exact rename_expr_id. Qed.

Theorem rename_expr_compose : rename_expr_compose_statement.
Proof. exact rename_expr_compose_aux. Qed.

Theorem rename_expr_inverse : rename_expr_inverse_statement.
Proof.
  intros r e. rewrite <- rename_expr_compose.
  rewrite (rename_expr_ext _ identity_renaming); [ apply rename_expr_id | | ].
  - intros x. rewrite rename_variable_compose.
    apply rename_variable_inverse_l.
  - intros k. rewrite rename_continuation_compose.
    apply rename_continuation_inverse_l.
Qed.

(* ======================================================================== *)
(* The free names are equivariant                                           *)
(* ======================================================================== *)

Lemma var_free_in_simple_equivariant (r : renaming) (x : variable)
    (s : simple) :
  var_free_in_simple (rename_variable r x) (rename_simple r s)
  <-> var_free_in_simple x s.
Proof.
  destruct s as [y | sym | c]; simpl; try reflexivity.
  split; [ apply rename_variable_injective | intros ->; reflexivity ].
Qed.

Lemma var_free_in_simples_equivariant (r : renaming) (x : variable)
    (args : list simple) :
  var_free_in_simples (rename_variable r x) (map (rename_simple r) args)
  <-> var_free_in_simples x args.
Proof.
  unfold var_free_in_simples.
  induction args as [ | s args IH]; simpl.
  - split; intros Hfree; inversion Hfree.
  - rewrite !Exists_cons.
    apply or_iff; [ apply var_free_in_simple_equivariant | exact IH ].
Qed.

Lemma var_free_in_named_equivariant (r : renaming) (x : variable)
    (d : named) :
  var_free_in_named (rename_variable r x) (rename_named r d)
  <-> var_free_in_named x d.
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure]; simpl.
  - apply var_free_in_simple_equivariant.
  - apply var_free_in_simples_equivariant.
  - induction slots as [ | [slot s] slots IH]; simpl.
    + split; intros Hfree; inversion Hfree.
    + rewrite !Exists_cons.
      apply or_iff; [ apply var_free_in_simple_equivariant | exact IH ].
  - induction slots as [ | [slot s] slots IH]; simpl.
    + split; intros Hfree; inversion Hfree.
    + rewrite !Exists_cons.
      apply or_iff; [ apply var_free_in_simple_equivariant | exact IH ].
  - apply var_free_in_simple_equivariant.
  - apply var_free_in_simple_equivariant.
  - apply var_free_in_simple_equivariant.
Qed.

Lemma var_free_in_value_slots_equivariant (r : renaming) (x : variable)
    (slots : list (value_slot * simple)) :
  Exists (fun slot => var_free_in_simple (rename_variable r x) (snd slot))
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  <-> Exists (fun slot => var_free_in_simple x (snd slot)) slots.
Proof.
  induction slots as [ | [slot s] slots IH]; simpl.
  - split; intros Hfree; inversion Hfree.
  - rewrite !Exists_cons.
    apply or_iff; [ apply var_free_in_simple_equivariant | exact IH ].
Qed.

Lemma var_free_in_static_bindings_equivariant (r : renaming) (x : variable)
    (bindings : list static_binding) :
  Exists (var_free_in_static_binding (rename_variable r x))
    (map (rename_static_binding r) bindings)
  <-> Exists (var_free_in_static_binding x) bindings.
Proof.
  induction bindings as [ | binding bindings IH]; simpl.
  - split; intros Hfree; inversion Hfree.
  - rewrite !Exists_cons. apply or_iff; [ | exact IH ].
    destruct binding
      as [id c | id
         | sym
             [code slots | fslot syms decls slots | tag fields | s | bytes]];
      simpl; try reflexivity.
    + apply var_free_in_value_slots_equivariant.
    + apply var_free_in_value_slots_equivariant.
    + apply var_free_in_simples_equivariant.
    + apply var_free_in_simple_equivariant.
Qed.

Lemma in_map_rename_variable (r : renaming) (x : variable)
    (params : list variable) :
  rename_variable r x ∈ map (rename_variable r) params <-> x ∈ params.
Proof.
  rewrite in_map_iff. split.
  - intros (y & Heq & Hin). apply rename_variable_injective in Heq.
    subst y. exact Hin.
  - intros Hin. exists x. auto.
Qed.

Fixpoint var_free_in_expr_equivariant (r : renaming) (x : variable)
    (e : expr) {struct e} :
  var_free_in_expr (rename_variable r x) (rename_expr r e)
  <-> var_free_in_expr x e
with var_free_in_handler_equivariant (r : renaming) (x : variable)
    (h : continuation_handler) {struct h} :
  var_free_in_handler (rename_variable r x) (rename_handler r h)
  <-> var_free_in_handler x h.
Proof.
  - destruct e
      as [y kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
      simpl.
    + apply or_iff; [ apply var_free_in_named_equivariant | ].
      apply and_iff;
        [ apply rename_variable_neq
        | apply (var_free_in_expr_equivariant r x body) ].
    + apply or_iff;
        [ apply var_free_in_static_bindings_equivariant
        | apply (var_free_in_expr_equivariant r x body) ].
    + apply or_iff;
        [ apply (var_free_in_handler_equivariant r x h)
        | apply (var_free_in_expr_equivariant r x body) ].
    + apply or_iff; [ | apply (var_free_in_expr_equivariant r x body) ].
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      apply or_iff;
        [ apply (var_free_in_handler_equivariant r x h) | exact IH ].
    + apply or_iff;
        [ apply var_free_in_simple_equivariant
        | apply var_free_in_simples_equivariant ].
    + apply var_free_in_simples_equivariant.
    + apply or_iff; [ apply var_free_in_simple_equivariant | ].
      induction arms as [ | [i ac] arms IH]; simpl.
      * split; intros Hfree; inversion Hfree.
      * rewrite !Exists_cons.
        apply or_iff; [ apply var_free_in_simples_equivariant | exact IH ].
    + reflexivity.
  - destruct h as [params metadata handler]. simpl.
    apply and_iff;
      [ apply not_iff_compat, in_map_rename_variable
      | apply (var_free_in_expr_equivariant r x handler) ].
Qed.

Lemma lookup_renamed_none (r : renaming) (k : continuation)
    (handlers : list (continuation * continuation_handler)) :
  lookup (rename_continuation r k) (rename_handlers r handlers) = None
  <-> lookup k handlers = None.
Proof.
  rewrite lookup_rename_handlers.
  destruct (lookup k handlers); simpl; split; congruence.
Qed.

Fixpoint cont_free_in_expr_equivariant (r : renaming) (k : continuation)
    (e : expr) {struct e} :
  cont_free_in_expr (rename_continuation r k) (rename_expr r e)
  <-> cont_free_in_expr k e
with cont_free_in_handler_equivariant (r : renaming) (k : continuation)
    (h : continuation_handler) {struct h} :
  cont_free_in_handler (rename_continuation r k) (rename_handler r h)
  <-> cont_free_in_handler k h.
Proof.
  - destruct e
      as [y kind d body | bindings body | k' h body | handlers body | ap | ac
       | scrutinee arms | ];
      simpl.
    + apply (cont_free_in_expr_equivariant r k body).
    + apply (cont_free_in_expr_equivariant r k body).
    + apply or_iff; [ apply (cont_free_in_handler_equivariant r k h) | ].
      apply and_iff;
        [ apply rename_continuation_neq
        | apply (cont_free_in_expr_equivariant r k body) ].
    + apply and_iff; [ apply lookup_renamed_none | ].
      apply or_iff; [ | apply (cont_free_in_expr_equivariant r k body) ].
      induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
      apply or_iff;
        [ apply (cont_free_in_handler_equivariant r k h) | exact IH ].
    + apply or_iff;
        (split;
          [ apply rename_continuation_injective | intros ->; reflexivity ]).
    + split; [ apply rename_continuation_injective | intros ->; reflexivity ].
    + induction arms as [ | [i ac] arms IH]; simpl.
      * split; intros Hfree; inversion Hfree.
      * rewrite !Exists_cons. apply or_iff; [ | exact IH ]. simpl.
        split;
          [ apply rename_continuation_injective | intros ->; reflexivity ].
    + reflexivity.
  - destruct h as [params metadata handler]. simpl.
    apply (cont_free_in_expr_equivariant r k handler).
Qed.

Theorem var_free_equivariant : var_free_equivariant_statement.
Proof. exact var_free_in_expr_equivariant. Qed.

Theorem cont_free_equivariant : cont_free_equivariant_statement.
Proof. exact cont_free_in_expr_equivariant. Qed.

(* A name is free in a renamed expression when its preimage is free in the
   expression. *)
Lemma var_free_in_renamed (r : renaming) (y : variable) (e : expr) :
  var_free_in_expr y (rename_expr r e)
  <-> var_free_in_expr (rename_variable (inverse_renaming r) y) e.
Proof.
  rewrite <- (var_free_in_expr_equivariant r _ e),
    rename_variable_inverse_r.
  reflexivity.
Qed.

Lemma cont_free_in_renamed (r : renaming) (k : continuation) (e : expr) :
  cont_free_in_expr k (rename_expr r e)
  <-> cont_free_in_expr (rename_continuation (inverse_renaming r) k) e.
Proof.
  rewrite <- (cont_free_in_expr_equivariant r _ e),
    rename_continuation_inverse_r.
  reflexivity.
Qed.

(* ======================================================================== *)
(* The free names, as functions, are equivariant                            *)
(* ======================================================================== *)

(* Sets of names under a function that keeps names apart. *)
Section Injective.

Variable f : positive -> positive.

Hypothesis f_eqb : ∀ x y : positive, Pos.eqb (f x) (f y) = Pos.eqb x y.

Lemma among_map_injective (name : positive) (names : list positive) :
  among (f name) (map f names) = among name names.
Proof.
  induction names as [ | first names IH]; [ reflexivity | ].
  cbn [map]. rewrite !among_cons, f_eqb, IH. reflexivity.
Qed.

Lemma without_map_injective (bound names : list positive) :
  without (map f bound) (map f names) = map f (without bound names).
Proof.
  unfold without. induction names as [ | name names IH]; [ reflexivity | ].
  cbn [map filter]. rewrite among_map_injective, IH.
  destruct (among name bound); reflexivity.
Qed.

Lemma all_among_map_injective (names allowed : list positive) :
  FlambdaMapSpec.all_among (map f names) (map f allowed)
  = FlambdaMapSpec.all_among names allowed.
Proof.
  unfold FlambdaMapSpec.all_among.
  induction names as [ | name names IH]; [ reflexivity | ].
  cbn [map forallb]. rewrite among_map_injective, IH. reflexivity.
Qed.

Lemma distinct_map_injective (names : list positive) :
  distinct (map f names) = distinct names.
Proof.
  induction names as [ | name names IH]; [ reflexivity | ].
  cbn [map distinct]. rewrite among_map_injective, IH. reflexivity.
Qed.

End Injective.

Lemma is_empty_map {A B : Type} (g : A -> B) (l : list A) :
  Keyed.is_empty (map g l) = Keyed.is_empty l.
Proof. destruct l; reflexivity. Qed.

Section Free_names.

Variable r : renaming.

Lemma free_variables_of_simple_renamed (s : simple) :
  free_variables_of_simple (rename_simple r s)
  = map (rename_variable r) (free_variables_of_simple s).
Proof. destruct s; reflexivity. Qed.

Lemma free_variables_of_simples_renamed (args : list simple) :
  free_variables_of_simples (map (rename_simple r) args)
  = map (rename_variable r) (free_variables_of_simples args).
Proof.
  unfold free_variables_of_simples.
  induction args as [ | s args IH]; [ reflexivity | ].
  cbn [map flat_map].
  rewrite map_app, free_variables_of_simple_renamed, IH. reflexivity.
Qed.

Lemma free_variables_of_value_slots_renamed
    (slots : list (value_slot * simple)) :
  free_variables_of_value_slots
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = map (rename_variable r) (free_variables_of_value_slots slots).
Proof.
  unfold free_variables_of_value_slots.
  induction slots as [ | slot slots IH]; [ reflexivity | ].
  cbn [map flat_map snd].
  rewrite map_app, free_variables_of_simple_renamed, IH. reflexivity.
Qed.

Lemma free_variables_of_named_renamed (d : named) :
  free_variables_of_named (rename_named r d)
  = map (rename_variable r) (free_variables_of_named d).
Proof.
  destruct d; cbn [rename_named free_variables_of_named];
    first
      [ apply free_variables_of_simple_renamed
      | apply free_variables_of_simples_renamed
      | apply free_variables_of_value_slots_renamed ].
Qed.

Lemma free_variables_of_static_const_renamed (const : static_const) :
  free_variables_of_static_const (rename_static_const r const)
  = map (rename_variable r) (free_variables_of_static_const const).
Proof.
  destruct const; cbn [rename_static_const free_variables_of_static_const];
    first
      [ apply free_variables_of_simple_renamed
      | apply free_variables_of_simples_renamed
      | apply free_variables_of_value_slots_renamed | reflexivity ].
Qed.

Lemma free_variables_of_apply_cont_renamed (ac : apply_cont) :
  free_variables_of_apply_cont (rename_apply_cont r ac)
  = map (rename_variable r) (free_variables_of_apply_cont ac).
Proof. apply free_variables_of_simples_renamed. Qed.

Lemma free_variables_of_apply_renamed (ap : apply_expr) :
  free_variables_of_apply (rename_apply r ap)
  = map (rename_variable r) (free_variables_of_apply ap).
Proof.
  unfold free_variables_of_apply, rename_apply. simpl.
  rewrite map_app, free_variables_of_simple_renamed,
    free_variables_of_simples_renamed.
  reflexivity.
Qed.

Fixpoint free_variables_of_expr_renamed (e : expr) {struct e} :
  free_variables_of_expr (rename_expr r e)
  = map (rename_variable r) (free_variables_of_expr e)
with free_variables_of_handler_renamed (h : continuation_handler)
    {struct h} :
  free_variables_of_handler (rename_handler r h)
  = map (rename_variable r) (free_variables_of_handler h)
with free_variables_of_binding_renamed (binding : static_binding)
    {struct binding} :
  free_variables_of_binding (rename_static_binding r binding)
  = map (rename_variable r) (free_variables_of_binding binding)
with free_variables_of_code_renamed (c : code) {struct c} :
  free_variables_of_code (rename_code r c)
  = map (rename_variable r) (free_variables_of_code c).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr free_variables_of_expr].
    + rewrite map_app, free_variables_of_named_renamed,
        (free_variables_of_expr_renamed body).
      rewrite <- (without_map_injective (rename_variable r)
                    (rename_variable_eqb r) [x]).
      reflexivity.
    + rewrite map_app, (free_variables_of_expr_renamed body). f_equal.
      induction bindings as [ | binding bindings IH]; [ reflexivity | ].
      cbn [map flat_map].
      rewrite map_app, (free_variables_of_binding_renamed binding), IH.
      reflexivity.
    + rewrite map_app, (free_variables_of_handler_renamed h),
        (free_variables_of_expr_renamed body).
      reflexivity.
    + rewrite map_app, (free_variables_of_expr_renamed body). f_equal.
      induction handlers as [ | [k h] handlers IH]; [ reflexivity | ].
      cbn [map flat_map].
      rewrite map_app, (free_variables_of_handler_renamed h), IH.
      reflexivity.
    + apply free_variables_of_apply_renamed.
    + apply free_variables_of_apply_cont_renamed.
    + rewrite map_app, free_variables_of_simple_renamed. f_equal.
      induction arms as [ | [i ac] arms IH]; [ reflexivity | ].
      cbn [map flat_map snd].
      rewrite map_app, free_variables_of_apply_cont_renamed, IH.
      reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler free_variables_of_handler].
    rewrite (free_variables_of_expr_renamed handler).
    apply without_map_injective, rename_variable_eqb.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding free_variables_of_binding].
    + apply free_variables_of_code_renamed.
    + reflexivity.
    + apply free_variables_of_static_const_renamed.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code free_variables_of_code].
    rewrite (free_variables_of_expr_renamed body).
    exact (without_map_injective (rename_variable r) (rename_variable_eqb r)
             (my_closure :: params) (free_variables_of_expr body)).
Qed.

Fixpoint free_continuations_of_expr_renamed (e : expr) {struct e} :
  free_continuations_of_expr (rename_expr r e)
  = map (rename_continuation r) (free_continuations_of_expr e)
with free_continuations_of_handler_renamed (h : continuation_handler)
    {struct h} :
  free_continuations_of_handler (rename_handler r h)
  = map (rename_continuation r) (free_continuations_of_handler h)
with free_continuations_of_binding_renamed (binding : static_binding)
    {struct binding} :
  free_continuations_of_binding (rename_static_binding r binding)
  = map (rename_continuation r) (free_continuations_of_binding binding)
with free_continuations_of_code_renamed (c : code) {struct c} :
  free_continuations_of_code (rename_code r c)
  = map (rename_continuation r) (free_continuations_of_code c).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr free_continuations_of_expr].
    + apply free_continuations_of_expr_renamed.
    + rewrite map_app, (free_continuations_of_expr_renamed body). f_equal.
      induction bindings as [ | binding bindings IH]; [ reflexivity | ].
      cbn [map flat_map].
      rewrite map_app, (free_continuations_of_binding_renamed binding), IH.
      reflexivity.
    + rewrite map_app, (free_continuations_of_handler_renamed h),
        (free_continuations_of_expr_renamed body).
      rewrite <- (without_map_injective (rename_continuation r)
                    (rename_continuation_eqb r) [k]).
      reflexivity.
    + fold (rename_handlers r handlers).
      rewrite map_fst_rename_handlers.
      rewrite <- (without_map_injective (rename_continuation r)
                    (rename_continuation_eqb r)).
      rewrite map_app, (free_continuations_of_expr_renamed body).
      do 2 f_equal. unfold rename_handlers.
      induction handlers as [ | [k h] handlers IH]; [ reflexivity | ].
      cbn [map flat_map].
      rewrite map_app, (free_continuations_of_handler_renamed h), IH.
      reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite !map_map. apply map_ext. intros [i ac]. reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler free_continuations_of_handler].
    apply free_continuations_of_expr_renamed.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding free_continuations_of_binding].
    + apply free_continuations_of_code_renamed.
    + reflexivity.
    + reflexivity.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code free_continuations_of_code].
    rewrite (free_continuations_of_expr_renamed body).
    exact (without_map_injective (rename_continuation r)
             (rename_continuation_eqb r) [ret; exn]
             (free_continuations_of_expr body)).
Qed.

(* The three conditions on binders. *)

Fixpoint code_closed_renamed (e : expr) {struct e} :
  code_closed (rename_expr r e) = code_closed e
with handler_code_closed_renamed (h : continuation_handler) {struct h} :
  handler_code_closed (rename_handler r h) = handler_code_closed h
with binding_code_closed_renamed (binding : static_binding)
    {struct binding} :
  binding_code_closed (rename_static_binding r binding)
  = binding_code_closed binding
with code_is_closed_renamed (c : code) {struct c} :
  code_is_closed (rename_code r c) = code_is_closed c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr code_closed]; try reflexivity.
    + apply code_closed_renamed.
    + rewrite (code_closed_renamed body). f_equal.
      induction bindings as [ | binding bindings IH]; [ reflexivity | ].
      cbn [map forallb].
      rewrite (binding_code_closed_renamed binding), IH. reflexivity.
    + rewrite (handler_code_closed_renamed h), (code_closed_renamed body).
      reflexivity.
    + rewrite (code_closed_renamed body). f_equal.
      induction handlers as [ | [k h] handlers IH]; [ reflexivity | ].
      cbn [map forallb].
      rewrite (handler_code_closed_renamed h), IH. reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_code_closed].
    apply code_closed_renamed.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding binding_code_closed];
      [ apply code_is_closed_renamed | reflexivity | reflexivity ].
  - pose proof (free_variables_of_code_renamed c) as Hvars.
    pose proof (free_continuations_of_code_renamed c) as Hconts.
    destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code code_is_closed] in *.
    rewrite Hvars, Hconts, !is_empty_map, (code_closed_renamed body).
    reflexivity.
Qed.

Fixpoint binders_distinct_renamed (e : expr) {struct e} :
  binders_distinct (rename_expr r e) = binders_distinct e
with handler_binders_distinct_renamed (h : continuation_handler)
    {struct h} :
  handler_binders_distinct (rename_handler r h) = handler_binders_distinct h
with binding_binders_distinct_renamed (binding : static_binding)
    {struct binding} :
  binding_binders_distinct (rename_static_binding r binding)
  = binding_binders_distinct binding
with code_binders_distinct_renamed (c : code) {struct c} :
  code_binders_distinct (rename_code r c) = code_binders_distinct c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr binders_distinct]; try reflexivity.
    + apply binders_distinct_renamed.
    + rewrite (binders_distinct_renamed body). f_equal.
      induction bindings as [ | binding bindings IH]; [ reflexivity | ].
      cbn [map forallb].
      rewrite (binding_binders_distinct_renamed binding), IH. reflexivity.
    + rewrite (handler_binders_distinct_renamed h),
        (binders_distinct_renamed body).
      reflexivity.
    + fold (rename_handlers r handlers).
      rewrite map_fst_rename_handlers,
        (distinct_map_injective _ (rename_continuation_eqb r)),
        (binders_distinct_renamed body).
      unfold rename_handlers. rewrite is_empty_map. do 2 f_equal.
      induction handlers as [ | [k h] handlers IH]; [ reflexivity | ].
      cbn [map forallb].
      rewrite (handler_binders_distinct_renamed h), IH. reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_binders_distinct].
    rewrite (distinct_map_injective _ (rename_variable_eqb r)),
      (binders_distinct_renamed handler).
    reflexivity.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding binding_binders_distinct];
      [ apply code_binders_distinct_renamed | reflexivity | reflexivity ].
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code code_binders_distinct].
    rewrite (binders_distinct_renamed body), rename_continuation_eqb.
    change (rename_variable r my_closure :: map (rename_variable r) params)
      with (map (rename_variable r) (my_closure :: params)).
    rewrite (distinct_map_injective _ (rename_variable_eqb r)).
    reflexivity.
Qed.

Lemma names_among_renamed (vs : list variable) (ks : list continuation)
    (e : expr) :
  names_among (map (rename_variable r) vs) (map (rename_continuation r) ks)
    (rename_expr r e)
  = names_among vs ks e.
Proof.
  unfold names_among.
  rewrite free_variables_of_expr_renamed,
    free_continuations_of_expr_renamed,
    (all_among_map_injective _ (rename_variable_eqb r)),
    (all_among_map_injective _ (rename_continuation_eqb r)).
  reflexivity.
Qed.

End Free_names.

Theorem free_variables_equivariant : free_variables_equivariant_statement.
Proof. exact free_variables_of_expr_renamed. Qed.

Theorem free_continuations_equivariant :
  free_continuations_equivariant_statement.
Proof. exact free_continuations_of_expr_renamed. Qed.

Theorem code_closed_equivariant : code_closed_equivariant_statement.
Proof. exact code_closed_renamed. Qed.

Theorem binders_distinct_equivariant :
  binders_distinct_equivariant_statement.
Proof. exact binders_distinct_renamed. Qed.

Theorem names_in_scope_equivariant : names_in_scope_equivariant_statement.
Proof.
  intros r unit_return unit_exn e.
  exact (names_among_renamed r [] [unit_return; unit_exn] e).
Qed.

(* ======================================================================== *)
(* Alpha-equivalent expressions behave alike                                *)
(* ======================================================================== *)

Lemma alpha_binds_statics (e e' : expr) :
  alpha_equivalent e e' -> binds_statics e = binds_statics e'.
Proof.
  intros Halpha.
  induction Halpha
    as [ e | e e' _ IH | e e' e'' _ IH _ IH' | c e e' _ IH
       | r e _ Hvars Hconts | r x kind d body _ Hvars Hconts
       | r k h body _ Hvars Hconts
       | r k params metadata handler body _ Hvars Hconts
       | r before k params metadata handler after body _ Hvars Hconts
       | r before id c after body _ ];
    simpl; try congruence; rewrite ?rename_binds_statics;
    try reflexivity.
  - apply plug_binds_statics, IH.
  - rewrite !existsb_app. simpl. rewrite rename_binds_statics. reflexivity.
  - rewrite !existsb_app. reflexivity.
Qed.

Theorem alpha_equivalent_sound : alpha_equivalent_sound_statement.
Proof.
  intros e e' Halpha.
  induction Halpha
    as [ e | e e' _ IH | e e' e'' _ IH _ IH' | c e e' Hinner IH
       | r e Hclosed Hvars Hconts | r x kind d body Hclosed Hvars Hconts
       | r k h body Hclosed Hvars Hconts
       | r k params metadata handler body Hclosed Hvars Hconts
       | r before k params metadata handler after body Hclosed Hvars Hconts
       | r before id c after body Hclosed ].
  - intros vars conts statics. apply equivalent_refl.
  - intros vars conts statics. apply equivalent_sym, IH.
  - intros vars conts statics.
    exact (equivalent_trans _ _ _ (IH _ _ _) (IH' _ _ _)).
  - apply plug_equivalent;
      [ intros _; apply alpha_binds_statics, Hinner | exact IH ].
  - intros vars conts statics. apply renamed_equivalent.
    + exact Hclosed.
    + intros x Hx. rewrite (Hvars x Hx). reflexivity.
    + intros k Hk. apply conts_agree_same, Hconts, Hk.
  - apply rename_let; assumption.
  - apply rename_let_cont; assumption.
  - apply rename_handler_params; assumption.
  - apply rename_recursive_handler_params; assumption.
  - apply rename_code_binders, Hclosed.
Qed.

(* ======================================================================== *)
(* Alpha-equivalence is equivariant                                         *)
(* ======================================================================== *)

(* A context is renamed as an expression is, the code that the hole is
   in included. *)
Fixpoint rename_context (r : renaming) (c : context) : context :=
  match c with
  | Hole => Hole
  | Let_body x kind d body =>
    Let_body (rename_variable r x) kind (rename_named r d)
      (rename_context r body)
  | Let_static_body bindings body =>
    Let_static_body (map (rename_static_binding r) bindings)
      (rename_context r body)
  | Let_static_code before id params my_closure ret exn metadata code_body
      after body =>
    Let_static_code (map (rename_static_binding r) before) id
      (map (rename_variable r) params) (rename_variable r my_closure)
      (rename_continuation r ret) (rename_continuation r exn) metadata
      (rename_context r code_body) (map (rename_static_binding r) after)
      (rename_expr r body)
  | Let_cont_non_recursive_body k h body =>
    Let_cont_non_recursive_body (rename_continuation r k)
      (rename_handler r h) (rename_context r body)
  | Let_cont_non_recursive_handler k params metadata handler body =>
    Let_cont_non_recursive_handler (rename_continuation r k)
      (map (rename_variable r) params) metadata (rename_context r handler)
      (rename_expr r body)
  | Let_cont_recursive_body handlers body =>
    Let_cont_recursive_body (rename_handlers r handlers)
      (rename_context r body)
  | Let_cont_recursive_handler before k params metadata handler after body
    =>
    Let_cont_recursive_handler (rename_handlers r before)
      (rename_continuation r k) (map (rename_variable r) params) metadata
      (rename_context r handler) (rename_handlers r after)
      (rename_expr r body)
  end.

Lemma rename_plug (r : renaming) (c : context) (e : expr) :
  rename_expr r (plug c e) = plug (rename_context r c) (rename_expr r e).
Proof.
  induction c
    as [ | x kind d c IH | bindings c IH
       | before id params my_closure ret exn metadata c IH after body
       | k h c IH | k params metadata c IH body | handlers c IH
       | before k params metadata c IH after body ];
    simpl; rewrite ?IH; try reflexivity.
  - rewrite map_app. simpl. rewrite IH. reflexivity.
  - unfold rename_handlers. rewrite map_app. simpl. rewrite IH. reflexivity.
Qed.

(* The conjugate of [s] by [r]: what [s] becomes once every name is renamed
   by [r]. *)
Definition conjugate (r s : renaming) : renaming :=
  compose_renaming r (compose_renaming s (inverse_renaming r)).

Lemma conjugate_variable (r s : renaming) (x : variable) :
  rename_variable (conjugate r s) (rename_variable r x)
  = rename_variable r (rename_variable s x).
Proof.
  unfold conjugate.
  rewrite !rename_variable_compose, rename_variable_inverse_l. reflexivity.
Qed.

Lemma conjugate_continuation (r s : renaming) (k : continuation) :
  rename_continuation (conjugate r s) (rename_continuation r k)
  = rename_continuation r (rename_continuation s k).
Proof.
  unfold conjugate.
  rewrite !rename_continuation_compose, rename_continuation_inverse_l.
  reflexivity.
Qed.

Lemma conjugate_expr (r s : renaming) (e : expr) :
  rename_expr (conjugate r s) (rename_expr r e)
  = rename_expr r (rename_expr s e).
Proof.
  unfold conjugate.
  rewrite !rename_expr_compose, rename_expr_inverse. reflexivity.
Qed.

Lemma conjugate_code (r s : renaming) (c : code) :
  rename_code (conjugate r s) (rename_code r c)
  = rename_code r (rename_code s c).
Proof.
  unfold conjugate.
  rewrite !rename_code_compose.
  destruct c as [params my_closure ret exn metadata body]. simpl.
  rewrite !map_map, !rename_variable_inverse_l,
    !rename_continuation_inverse_l, rename_expr_inverse.
  f_equal. apply map_ext. intros x. rewrite rename_variable_inverse_l.
  reflexivity.
Qed.

Lemma conjugate_fixes_variable (r s : renaming) (y : variable) :
  rename_variable s (rename_variable (inverse_renaming r) y)
  = rename_variable (inverse_renaming r) y ->
  rename_variable (conjugate r s) y = y.
Proof.
  intros Hfix. unfold conjugate.
  rewrite !rename_variable_compose, Hfix. apply rename_variable_inverse_r.
Qed.

Lemma conjugate_fixes_continuation (r s : renaming) (k : continuation) :
  rename_continuation s (rename_continuation (inverse_renaming r) k)
  = rename_continuation (inverse_renaming r) k ->
  rename_continuation (conjugate r s) k = k.
Proof.
  intros Hfix. unfold conjugate.
  rewrite !rename_continuation_compose, Hfix.
  apply rename_continuation_inverse_r.
Qed.

(* Each rule that renames by [s] becomes, under [r], the same rule for the
   conjugate of [s]. *)
Theorem alpha_equivalent_equivariant : alpha_equivalent_equivariant_statement.
Proof.
  intros r e e' Halpha.
  induction Halpha
    as [ e | e e' _ IH | e e' e'' _ IH _ IH' | c e e' Halpha IH
       | s e Hclosed Hvars Hconts | s x kind d body Hclosed Hvars Hconts
       | s k h body Hclosed Hvars Hconts
       | s k params metadata handler body Hclosed Hvars Hconts
       | s before k params metadata handler after body Hclosed Hvars Hconts
       | s before id c after body Hclosed ].
  - apply Alpha_refl.
  - apply Alpha_sym, IH.
  - exact (Alpha_trans _ _ _ IH IH').
  - rewrite !rename_plug. apply Alpha_context, IH.
  - rewrite <- conjugate_expr. apply Alpha_rename.
    + rewrite code_closed_renamed. exact Hclosed.
    + intros y Hy.
      apply conjugate_fixes_variable, Hvars, var_free_in_renamed, Hy.
    + intros k Hk.
      apply conjugate_fixes_continuation, Hconts, cont_free_in_renamed, Hk.
  - simpl. rewrite <- conjugate_variable, <- conjugate_expr.
    apply Alpha_let.
    + rewrite code_closed_renamed. exact Hclosed.
    + intros y Hne Hy.
      apply conjugate_fixes_variable, Hvars;
        [ | apply var_free_in_renamed, Hy ].
      intros Heq. apply Hne. rewrite <- Heq.
      symmetry. apply rename_variable_inverse_r.
    + intros k Hk.
      apply conjugate_fixes_continuation, Hconts, cont_free_in_renamed, Hk.
  - simpl. rewrite <- conjugate_continuation, <- conjugate_expr.
    apply Alpha_let_cont.
    + rewrite code_closed_renamed. exact Hclosed.
    + intros y Hy.
      apply conjugate_fixes_variable, Hvars, var_free_in_renamed, Hy.
    + intros k' Hne Hk'.
      apply conjugate_fixes_continuation, Hconts;
        [ | apply cont_free_in_renamed, Hk' ].
      intros Heq. apply Hne. rewrite <- Heq.
      symmetry. apply rename_continuation_inverse_r.
  - simpl. rewrite <- conjugate_expr.
    replace (map (rename_variable r) (map (rename_variable s) params))
      with (map (rename_variable (conjugate r s))
              (map (rename_variable r) params))
      by (rewrite !map_map; apply map_ext; intros x;
          apply conjugate_variable).
    apply (Alpha_handler (conjugate r s) (rename_continuation r k)
      (map (rename_variable r) params) metadata (rename_expr r handler)
      (rename_expr r body)).
    + rewrite code_closed_renamed. exact Hclosed.
    + intros y Hnotin Hy.
      apply conjugate_fixes_variable, Hvars;
        [ | apply var_free_in_renamed, Hy ].
      intros Hin. apply Hnotin.
      rewrite <- (rename_variable_inverse_r r y). apply in_map, Hin.
    + intros k' Hk'.
      apply conjugate_fixes_continuation, Hconts, cont_free_in_renamed, Hk'.
  - simpl. rewrite !map_app. simpl. rewrite <- conjugate_expr.
    replace (map (rename_variable r) (map (rename_variable s) params))
      with (map (rename_variable (conjugate r s))
              (map (rename_variable r) params))
      by (rewrite !map_map; apply map_ext; intros x;
          apply conjugate_variable).
    apply (Alpha_recursive_handler (conjugate r s) (rename_handlers r before)
      (rename_continuation r k) (map (rename_variable r) params) metadata
      (rename_expr r handler) (rename_handlers r after)
      (rename_expr r body)).
    + rewrite code_closed_renamed. exact Hclosed.
    + intros y Hnotin Hy.
      apply conjugate_fixes_variable, Hvars;
        [ | apply var_free_in_renamed, Hy ].
      intros Hin. apply Hnotin.
      rewrite <- (rename_variable_inverse_r r y). apply in_map, Hin.
    + intros k' Hk'.
      apply conjugate_fixes_continuation, Hconts, cont_free_in_renamed, Hk'.
  - simpl. rewrite !map_app. simpl. rewrite <- conjugate_code.
    apply Alpha_code. rewrite code_is_closed_renamed. exact Hclosed.
Qed.

(* ======================================================================== *)
(* Alpha-equivalent expressions have the same free names                    *)
(* ======================================================================== *)

(* A bijection [f] of names that fixes the names with [F] carries [F] to a
   property with the same names. *)
Lemma fixed_free (f g : positive -> positive) (F F' : positive -> Prop) :
  (∀ y : positive, f (g y) = y) ->
  (∀ y : positive, F' (f y) <-> F y) ->
  (∀ y : positive, F y -> f y = y) ->
  ∀ y : positive, F y <-> F' y.
Proof.
  intros Hinverse Hequivariant Hfix y. split; intros Hy.
  - rewrite <- (Hfix y Hy). apply Hequivariant, Hy.
  - rewrite <- (Hinverse y) in Hy. apply Hequivariant in Hy.
    pose proof (Hfix _ Hy) as Heq. rewrite Hinverse in Heq.
    rewrite Heq. exact Hy.
Qed.

(* The same for the names free in the scope [F] of binders [B]: [f] need
   fix only those that are not bound. *)
Lemma abstraction_free (f g : positive -> positive)
    (B F B' F' : positive -> Prop) :
  (∀ y : positive, f (g y) = y) ->
  (∀ y : positive, B' (f y) <-> B y) ->
  (∀ y : positive, F' (f y) <-> F y) ->
  (∀ y : positive, ~ B y -> F y -> f y = y) ->
  ∀ y : positive, (~ B y ∧ F y) <-> (~ B' y ∧ F' y).
Proof.
  intros Hinverse Hbound Hequivariant Hfix.
  apply (fixed_free f g (fun y => ~ B y ∧ F y) (fun y => ~ B' y ∧ F' y)
    Hinverse).
  - intros y. apply and_iff; [ apply not_iff_compat, Hbound | ].
    apply Hequivariant.
  - intros y [Hnotbound Hy]. exact (Hfix y Hnotbound Hy).
Qed.

Lemma any_handler_app {A : Type} (P : A -> Prop)
    (handlers handlers' : list (continuation * A)) :
  any_handler P (handlers ++ handlers')
  <-> any_handler P handlers ∨ any_handler P handlers'.
Proof.
  induction handlers as [ | [k h] handlers IH]; simpl; [ tauto | ].
  rewrite IH. tauto.
Qed.

(* Plugging expressions with the same free names gives expressions with
   the same free names. *)
Lemma plug_var_free (c : context) (e e' : expr) :
  (∀ x : variable, var_free_in_expr x e <-> var_free_in_expr x e') ->
  ∀ x : variable,
    var_free_in_expr x (plug c e) <-> var_free_in_expr x (plug c e').
Proof.
  intros Hfree.
  induction c
    as [ | y kind d c IH | bindings c IH
       | before id params my_closure ret exn metadata c IH after body
       | k h c IH | k params metadata c IH body | handlers c IH
       | before k params metadata c IH after body ];
    intros x; simpl.
  - apply Hfree.
  - apply or_iff; [ reflexivity | ]. apply and_iff; [ reflexivity | apply IH ].
  - apply or_iff; [ reflexivity | apply IH ].
  - apply or_iff; [ | reflexivity ]. rewrite !Exists_app, !Exists_cons.
    reflexivity.
  - apply or_iff; [ reflexivity | apply IH ].
  - apply or_iff; [ | reflexivity ].
    apply and_iff; [ reflexivity | apply IH ].
  - apply or_iff; [ reflexivity | apply IH ].
  - apply or_iff; [ | reflexivity ]. rewrite !any_handler_app. simpl.
    apply or_iff; [ reflexivity | ]. apply or_iff; [ | reflexivity ].
    apply and_iff; [ reflexivity | apply IH ].
Qed.

Lemma plug_cont_free (c : context) (e e' : expr) :
  (∀ k : continuation, cont_free_in_expr k e <-> cont_free_in_expr k e') ->
  ∀ k : continuation,
    cont_free_in_expr k (plug c e) <-> cont_free_in_expr k (plug c e').
Proof.
  intros Hfree.
  induction c
    as [ | y kind d c IH | bindings c IH
       | before id params my_closure ret exn metadata c IH after body
       | k' h c IH | k' params metadata c IH body | handlers c IH
       | before k' params metadata c IH after body ];
    intros k; simpl.
  - apply Hfree.
  - apply IH.
  - apply IH.
  - reflexivity.
  - apply or_iff; [ reflexivity | ]. apply and_iff; [ reflexivity | apply IH ].
  - apply or_iff; [ apply IH | reflexivity ].
  - apply and_iff; [ reflexivity | ]. apply or_iff; [ reflexivity | apply IH ].
  - apply and_iff.
    + rewrite !lookup_app. destruct (lookup k before); [ reflexivity | ].
      simpl. destruct (Pos.eqb k k'); [ | reflexivity ].
      split; discriminate.
    + apply or_iff; [ | reflexivity ]. rewrite !any_handler_app. simpl.
      apply or_iff; [ reflexivity | ]. apply or_iff; [ | reflexivity ].
      apply IH.
Qed.

Theorem alpha_equivalent_free_names : alpha_equivalent_free_names_statement.
Proof.
  intros e e' Halpha.
  induction Halpha
    as [ e | e e' _ [IHv IHk] | e e' e'' _ [IHv IHk] _ [IHv' IHk']
       | c e e' _ [IHv IHk]
       | s e _ Hvars Hconts | s x kind d body _ Hvars Hconts
       | s k h body _ Hvars Hconts
       | s k params metadata handler body _ Hvars Hconts
       | s before k params metadata handler after body _ Hvars Hconts
       | s before id c after body _ ].
  - split; reflexivity.
  - split; intros; symmetry; [ apply IHv | apply IHk ].
  - split; intros y;
      [ rewrite (IHv y); apply IHv' | rewrite (IHk y); apply IHk' ].
  - split; [ apply plug_var_free, IHv | apply plug_cont_free, IHk ].
  - split.
    + exact (fixed_free (rename_variable s)
        (rename_variable (inverse_renaming s))
        (fun y => var_free_in_expr y e)
        (fun y => var_free_in_expr y (rename_expr s e))
        (rename_variable_inverse_r s)
        (fun y => var_free_in_expr_equivariant s y e) Hvars).
    + exact (fixed_free (rename_continuation s)
        (rename_continuation (inverse_renaming s))
        (fun k => cont_free_in_expr k e)
        (fun k => cont_free_in_expr k (rename_expr s e))
        (rename_continuation_inverse_r s)
        (fun k => cont_free_in_expr_equivariant s k e) Hconts).
  - split.
    + intros y. simpl. apply or_iff; [ reflexivity | ].
      exact (abstraction_free (rename_variable s)
        (rename_variable (inverse_renaming s))
        (fun y => y = x) (fun y => var_free_in_expr y body)
        (fun y => y = rename_variable s x)
        (fun y => var_free_in_expr y (rename_expr s body))
        (rename_variable_inverse_r s)
        (fun y =>
           conj (rename_variable_injective s y x)
             (fun Heq : y = x => f_equal (rename_variable s) Heq))
        (fun y => var_free_in_expr_equivariant s y body) Hvars y).
    + exact (fixed_free (rename_continuation s)
        (rename_continuation (inverse_renaming s))
        (fun k => cont_free_in_expr k body)
        (fun k => cont_free_in_expr k (rename_expr s body))
        (rename_continuation_inverse_r s)
        (fun k => cont_free_in_expr_equivariant s k body) Hconts).
  - split.
    + intros y. simpl. apply or_iff; [ reflexivity | ].
      exact (fixed_free (rename_variable s)
        (rename_variable (inverse_renaming s))
        (fun y => var_free_in_expr y body)
        (fun y => var_free_in_expr y (rename_expr s body))
        (rename_variable_inverse_r s)
        (fun y => var_free_in_expr_equivariant s y body) Hvars y).
    + intros k'. simpl. apply or_iff; [ reflexivity | ].
      exact (abstraction_free (rename_continuation s)
        (rename_continuation (inverse_renaming s))
        (fun k' => k' = k) (fun k' => cont_free_in_expr k' body)
        (fun k' => k' = rename_continuation s k)
        (fun k' => cont_free_in_expr k' (rename_expr s body))
        (rename_continuation_inverse_r s)
        (fun k' =>
           conj (rename_continuation_injective s k' k)
             (fun Heq : k' = k => f_equal (rename_continuation s) Heq))
        (fun k' => cont_free_in_expr_equivariant s k' body) Hconts k').
  - split.
    + intros y. simpl. apply or_iff; [ | reflexivity ].
      exact (abstraction_free (rename_variable s)
        (rename_variable (inverse_renaming s))
        (fun y => y ∈ params) (fun y => var_free_in_expr y handler)
        (fun y => y ∈ map (rename_variable s) params)
        (fun y => var_free_in_expr y (rename_expr s handler))
        (rename_variable_inverse_r s)
        (fun y => in_map_rename_variable s y params)
        (fun y => var_free_in_expr_equivariant s y handler) Hvars y).
    + intros k'. simpl. apply or_iff; [ | reflexivity ].
      exact (fixed_free (rename_continuation s)
        (rename_continuation (inverse_renaming s))
        (fun k' => cont_free_in_expr k' handler)
        (fun k' => cont_free_in_expr k' (rename_expr s handler))
        (rename_continuation_inverse_r s)
        (fun k' => cont_free_in_expr_equivariant s k' handler) Hconts k').
  - split.
    + intros y. simpl. apply or_iff; [ | reflexivity ].
      rewrite !any_handler_app. simpl.
      apply or_iff; [ reflexivity | ]. apply or_iff; [ | reflexivity ].
      exact (abstraction_free (rename_variable s)
        (rename_variable (inverse_renaming s))
        (fun y => y ∈ params) (fun y => var_free_in_expr y handler)
        (fun y => y ∈ map (rename_variable s) params)
        (fun y => var_free_in_expr y (rename_expr s handler))
        (rename_variable_inverse_r s)
        (fun y => in_map_rename_variable s y params)
        (fun y => var_free_in_expr_equivariant s y handler) Hvars y).
    + intros k'. simpl. apply and_iff.
      * rewrite !lookup_app. destruct (lookup k' before); [ reflexivity | ].
        simpl. destruct (Pos.eqb k' k); [ | reflexivity ].
        split; discriminate.
      * apply or_iff; [ | reflexivity ]. rewrite !any_handler_app. simpl.
        apply or_iff; [ reflexivity | ]. apply or_iff; [ | reflexivity ].
        exact (fixed_free (rename_continuation s)
          (rename_continuation (inverse_renaming s))
          (fun k' => cont_free_in_expr k' handler)
          (fun k' => cont_free_in_expr k' (rename_expr s handler))
          (rename_continuation_inverse_r s)
          (fun k' => cont_free_in_expr_equivariant s k' handler) Hconts k').
  - split; [ | reflexivity ].
    intros y. simpl. apply or_iff; [ | reflexivity ].
    rewrite !Exists_app, !Exists_cons. reflexivity.
Qed.

Theorem alpha_let_cont_recursive : alpha_let_cont_recursive_statement.
Proof.
  intros r handlers body Hclosed Hvars Hconts.
  exact (Alpha_rename r (Let_cont_recursive handlers body) Hclosed Hvars
           Hconts).
Qed.

(* ======================================================================== *)
(* Execution is equivariant in the variables                                *)
(* ======================================================================== *)

Lemma lookup_rename_env (r : renaming) (x : variable) (vars : env) :
  lookup (rename_variable r x) (rename_env r vars) = lookup x vars.
Proof.
  induction vars as [ | [y v] vars IH]; simpl; [ reflexivity | ].
  rewrite rename_variable_eqb. destruct (Pos.eqb x y); [ reflexivity | ].
  exact IH.
Qed.

Theorem rename_variables_equivalent : rename_variables_equivalent_statement.
Proof.
  intros r e vars conts statics Hclosed Hconts.
  apply renamed_equivalent.
  - exact Hclosed.
  - intros x _. apply lookup_rename_env.
  - intros k Hk. apply conts_agree_same, Hconts, Hk.
Qed.
