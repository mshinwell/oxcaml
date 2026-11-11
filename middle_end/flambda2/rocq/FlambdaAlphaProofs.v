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

From Stdlib Require Import ZArith List Setoid.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaContextSpec FlambdaContextProofs FlambdaNominalSpec
  FlambdaNominalProofs FlambdaAlphaSpec.
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

Lemma rename_static_binding_ext (binding : static_binding) :
  rename_static_binding r binding = rename_static_binding r' binding.
Proof.
  destruct binding
    as [id c | id
       | sym [code slots | fslot syms decls slots | tag fields | s | bytes]];
    simpl;
    rewrite ?rename_simple_ext, ?(map_ext _ _ rename_simple_ext);
    try reflexivity;
    do 2 f_equal; apply map_ext; intros [slot s]; simpl;
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
  rename_handler r h = rename_handler r' h.
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
      simpl.
    + rewrite same_variables, rename_named_ext, (rename_expr_ext body).
      reflexivity.
    + rewrite (rename_expr_ext body),
        (map_ext _ _ rename_static_binding_ext).
      reflexivity.
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

Lemma rename_static_binding_compose (binding : static_binding) :
  rename_static_binding (compose_renaming second first) binding
  = rename_static_binding second (rename_static_binding first binding).
Proof.
  destruct binding
    as [id c | id
       | sym [code slots | fslot syms decls slots | tag fields | s | bytes]];
    simpl;
    rewrite ?rename_simple_compose, ?rename_simples_compose;
    try reflexivity;
    do 2 f_equal; rewrite map_map; apply map_ext; intros [slot s]; simpl;
    rewrite rename_simple_compose; reflexivity.
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
  = rename_handler second (rename_handler first h).
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
      simpl.
    + rewrite rename_variable_compose, rename_named_compose,
        (rename_expr_compose_aux body). reflexivity.
    + rewrite (rename_expr_compose_aux body). f_equal.
      rewrite map_map. apply map_ext, rename_static_binding_compose.
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
    rewrite (rename_expr_compose_aux handler). f_equal.
    rewrite map_map. apply map_ext. intros x.
    apply rename_variable_compose.
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
(* Alpha-equivalent expressions behave alike                                *)
(* ======================================================================== *)

Lemma alpha_binds_statics (e e' : expr) :
  alpha_equivalent e e' -> binds_statics e = binds_statics e'.
Proof.
  intros Halpha.
  induction Halpha
    as [ e | e e' _ IH | e e' e'' _ IH _ IH' | c e e' _ IH
       | r e Hvars Hconts | r x kind d body Hvars Hconts
       | r k h body Hvars Hconts
       | r k params metadata handler body Hvars Hconts
       | r before k params metadata handler after body Hvars Hconts ];
    simpl; try congruence; rewrite ?rename_binds_statics;
    try reflexivity.
  - apply plug_binds_statics, IH.
  - rewrite !existsb_app. simpl. rewrite rename_binds_statics. reflexivity.
Qed.

Theorem alpha_equivalent_sound : alpha_equivalent_sound_statement.
Proof.
  intros e e' Halpha.
  induction Halpha
    as [ e | e e' _ IH | e e' e'' _ IH _ IH' | c e e' Hinner IH
       | r e Hvars Hconts | r x kind d body Hvars Hconts
       | r k h body Hvars Hconts
       | r k params metadata handler body Hvars Hconts
       | r before k params metadata handler after body Hvars Hconts ].
  - intros vars conts statics. apply equivalent_refl.
  - intros vars conts statics. apply equivalent_sym, IH.
  - intros vars conts statics.
    exact (equivalent_trans _ _ _ (IH _ _ _) (IH' _ _ _)).
  - apply plug_equivalent;
      [ intros _; apply alpha_binds_statics, Hinner | exact IH ].
  - intros vars conts statics. apply renamed_equivalent.
    + intros x Hx. rewrite (Hvars x Hx). reflexivity.
    + intros k Hk. apply conts_agree_same, Hconts, Hk.
  - apply rename_let; assumption.
  - apply rename_let_cont; assumption.
  - apply rename_handler_params; assumption.
  - apply rename_recursive_handler_params; assumption.
Qed.

(* ======================================================================== *)
(* Alpha-equivalence is equivariant                                         *)
(* ======================================================================== *)

(* A renaming does not reach into code, so nor does it into a context
   under code. *)
Fixpoint hole_in_code (c : context) : bool :=
  match c with
  | Hole => false
  | Let_static_code _ _ _ _ _ _ _ _ _ _ => true
  | Let_body _ _ _ body | Let_static_body _ body
  | Let_cont_non_recursive_body _ _ body | Let_cont_recursive_body _ body =>
    hole_in_code body
  | Let_cont_non_recursive_handler _ _ _ handler _
  | Let_cont_recursive_handler _ _ _ _ handler _ _ => hole_in_code handler
  end.

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
    Let_static_code (map (rename_static_binding r) before) id params
      my_closure ret exn metadata code_body
      (map (rename_static_binding r) after) (rename_expr r body)
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
  rename_expr r (plug c e)
  = plug (rename_context r c)
      (if hole_in_code c then e else rename_expr r e).
Proof.
  induction c
    as [ | x kind d c IH | bindings c IH
       | before id params my_closure ret exn metadata c IH after body
       | k h c IH | k params metadata c IH body | handlers c IH
       | before k params metadata c IH after body ];
    simpl; rewrite ?IH; try reflexivity.
  - rewrite map_app. reflexivity.
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
       | s e Hvars Hconts | s x kind d body Hvars Hconts
       | s k h body Hvars Hconts
       | s k params metadata handler body Hvars Hconts
       | s before k params metadata handler after body Hvars Hconts ].
  - apply Alpha_refl.
  - apply Alpha_sym, IH.
  - exact (Alpha_trans _ _ _ IH IH').
  - rewrite !rename_plug.
    destruct (hole_in_code c); apply Alpha_context; [ exact Halpha | exact IH ].
  - rewrite <- conjugate_expr. apply Alpha_rename.
    + intros y Hy.
      apply conjugate_fixes_variable, Hvars, var_free_in_renamed, Hy.
    + intros k Hk.
      apply conjugate_fixes_continuation, Hconts, cont_free_in_renamed, Hk.
  - simpl. rewrite <- conjugate_variable, <- conjugate_expr.
    apply Alpha_let.
    + intros y Hne Hy.
      apply conjugate_fixes_variable, Hvars;
        [ | apply var_free_in_renamed, Hy ].
      intros Heq. apply Hne. rewrite <- Heq.
      symmetry. apply rename_variable_inverse_r.
    + intros k Hk.
      apply conjugate_fixes_continuation, Hconts, cont_free_in_renamed, Hk.
  - simpl. rewrite <- conjugate_continuation, <- conjugate_expr.
    apply Alpha_let_cont.
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
    + intros y Hnotin Hy.
      apply conjugate_fixes_variable, Hvars;
        [ | apply var_free_in_renamed, Hy ].
      intros Hin. apply Hnotin.
      rewrite <- (rename_variable_inverse_r r y). apply in_map, Hin.
    + intros k' Hk'.
      apply conjugate_fixes_continuation, Hconts, cont_free_in_renamed, Hk'.
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
       | s e Hvars Hconts | s x kind d body Hvars Hconts
       | s k h body Hvars Hconts
       | s k params metadata handler body Hvars Hconts
       | s before k params metadata handler after body Hvars Hconts ].
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
Qed.

Theorem alpha_let_cont_recursive : alpha_let_cont_recursive_statement.
Proof.
  intros r handlers body Hvars Hconts.
  exact (Alpha_rename r (Let_cont_recursive handlers body) Hvars Hconts).
Qed.

(* ======================================================================== *)
(* Alpha-equivalence by recursion on the two expressions                    *)
(* ======================================================================== *)

Scheme alpha_structural_mutual := Minimality for alpha_structural Sort Prop
  with alpha_structural_handler_mutual :=
    Minimality for alpha_structural_handler Sort Prop
  with alpha_structural_handlers_mutual :=
    Minimality for alpha_structural_handlers Sort Prop.

Combined Scheme alpha_structural_induction from alpha_structural_mutual,
  alpha_structural_handler_mutual, alpha_structural_handlers_mutual.

(* What the three relations come to. Related handlers may replace each
   other in either form of [Let_cont], and related lists of handlers at the
   end of a recursive one. *)
Definition handler_replaceable (h h' : continuation_handler) : Prop :=
  (∀ (k : continuation) (body : expr),
    alpha_equivalent (Let_cont_non_recursive k h body)
      (Let_cont_non_recursive k h' body))
  ∧ (∀ (before : list (continuation * continuation_handler))
       (k : continuation)
       (after : list (continuation * continuation_handler)) (body : expr),
      alpha_equivalent (Let_cont_recursive (before ++ (k, h) :: after) body)
        (Let_cont_recursive (before ++ (k, h') :: after) body)).

Definition handlers_replaceable
    (handlers handlers' : list (continuation * continuation_handler))
    : Prop :=
  ∀ (before : list (continuation * continuation_handler)) (body : expr),
    alpha_equivalent (Let_cont_recursive (before ++ handlers) body)
      (Let_cont_recursive (before ++ handlers') body).

(* Each rule is a rule of [alpha_equivalent] for one side, the premise
   about the scopes under a context, and the same rule backwards for the
   other side. *)
Lemma alpha_structural_sound_mutual :
  (∀ e e' : expr, alpha_structural e e' -> alpha_equivalent e e')
  ∧ (∀ h h' : continuation_handler,
      alpha_structural_handler h h' -> handler_replaceable h h')
  ∧ (∀ handlers handlers' : list (continuation * continuation_handler),
      alpha_structural_handlers handlers handlers' ->
      handlers_replaceable handlers handlers').
Proof.
  apply alpha_structural_induction.
  - (* Let *)
    intros r r' x x' kind d body body' Hvars Hconts Hvars' Hconts' Hbound _
      IH.
    eapply Alpha_trans; [ exact (Alpha_let r x kind d body Hvars Hconts) | ].
    eapply Alpha_trans;
      [ exact
          (Alpha_context (Let_body (rename_variable r x) kind d Hole) _ _ IH)
      | ].
    simpl. rewrite Hbound.
    exact (Alpha_sym _ _ (Alpha_let r' x' kind d body' Hvars' Hconts')).
  - (* Let_cont_non_recursive *)
    intros r r' k k' h h' body body' _ [Hhandler _] Hvars Hconts Hvars' Hconts'
      Hbound _ IH.
    eapply Alpha_trans; [ exact (Hhandler k body) | ].
    eapply Alpha_trans;
      [ exact (Alpha_let_cont r k h' body Hvars Hconts) | ].
    eapply Alpha_trans;
      [ exact (Alpha_context
          (Let_cont_non_recursive_body (rename_continuation r k) h' Hole)
          _ _ IH)
      | ].
    simpl. rewrite Hbound.
    exact (Alpha_sym _ _ (Alpha_let_cont r' k' h' body' Hvars' Hconts')).
  - (* Let_cont_recursive *)
    intros r r' handlers handlers' body body' Hvars Hconts Hvars' Hconts' _
      Hhandlers _ IH.
    eapply Alpha_trans;
      [ exact (Alpha_rename r (Let_cont_recursive handlers body) Hvars
          Hconts)
      | ].
    eapply Alpha_trans; [ exact (Hhandlers [] (rename_expr r body)) | ].
    eapply Alpha_trans;
      [ exact (Alpha_context
          (Let_cont_recursive_body (rename_handlers r' handlers') Hole)
          _ _ IH)
      | ].
    exact (Alpha_sym _ _
      (Alpha_rename r' (Let_cont_recursive handlers' body') Hvars' Hconts')).
  - intros ac. apply Alpha_refl.
  - intros scrutinee arms. apply Alpha_refl.
  - apply Alpha_refl.
  - (* a handler *)
    intros r r' params params' metadata handler handler' Hvars Hconts Hvars'
      Hconts' Hbound _ IH.
    split.
    + intros k body.
      eapply Alpha_trans;
        [ exact (Alpha_handler r k params metadata handler body Hvars Hconts)
        | ].
      eapply Alpha_trans;
        [ exact (Alpha_context
            (Let_cont_non_recursive_handler k
               (map (rename_variable r) params) metadata Hole body)
            _ _ IH)
        | ].
      simpl. rewrite Hbound.
      exact (Alpha_sym _ _
        (Alpha_handler r' k params' metadata handler' body Hvars' Hconts')).
    + intros before k after body.
      eapply Alpha_trans;
        [ exact (Alpha_recursive_handler r before k params metadata handler
            after body Hvars Hconts)
        | ].
      eapply Alpha_trans;
        [ exact (Alpha_context
            (Let_cont_recursive_handler before k
               (map (rename_variable r) params) metadata Hole after body)
            _ _ IH)
        | ].
      simpl. rewrite Hbound.
      exact (Alpha_sym _ _
        (Alpha_recursive_handler r' before k params' metadata handler' after
           body Hvars' Hconts')).
  - intros before body. apply Alpha_refl.
  - (* a handler and the handlers after it *)
    intros k h h' handlers handlers' _ [_ Hhandler] _ IH before body.
    eapply Alpha_trans; [ exact (Hhandler before k handlers body) | ].
    specialize (IH (before ++ [(k, h')]) body).
    rewrite <- !app_assoc in IH. exact IH.
Qed.

Theorem alpha_structural_sound : alpha_structural_sound_statement.
Proof. exact (proj1 alpha_structural_sound_mutual). Qed.


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
  intros r e vars conts statics Hconts.
  apply renamed_equivalent.
  - intros x _. apply lookup_rename_env.
  - intros k Hk. apply conts_agree_same, Hconts, Hk.
Qed.
