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


(* Proofs of the statements of FlambdaValidatorEquivarianceSpec.v. Nothing
   here needs review.

   Each rewrite is taken as the two of FlambdaEquivarianceProofs.v are:
   one lemma for each function the rewrite is made of, saying that the
   function commutes with the action, and one recursion over expressions
   (and over handlers, bindings and code where the rewrite goes into
   them). A test that compares names for equality answers the same on
   the renamed names because a renaming is injective. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaNominalSpec FlambdaNominalProofs FlambdaAlphaSpec FlambdaAlphaProofs
  FlambdaApplySpec FlambdaNormaliseSpec FlambdaEquivarianceSpec
  FlambdaEquivarianceProofs FlambdaUnusedContsSpec FlambdaUnusedStaticsSpec
  FlambdaPrimitiveModel FlambdaPrimitiveSpec FlambdaBlockLoadSpec
  FlambdaUnboxSpec FlambdaWellFormedSpec FlambdaWellKindedSpec
  FlambdaCompareSpec
  FlambdaCompareAlphaSpec FlambdaCompareAlphaProofs FlambdaMyClosureSpec
  FlambdaMyClosureProofs FlambdaLiftSpec FlambdaLiftProofs
  FlambdaUnusedSlotsSpec FlambdaUnusedSlotsProofs FlambdaValidateSpec
  FlambdaValidatorEquivarianceSpec.
From OxCamlFlambda2Types Require Import FlambdaTypesSpec FlambdaAliasesSpec.
Import ListNotations.

(* ======================================================================== *)
(* Lists under a map                                                        *)
(* ======================================================================== *)

Lemma existsb_map_with {A B : Type} (f : B -> bool) (g : A -> B)
    (h : A -> bool) (l : list A) :
  (∀ a : A, f (g a) = h a) -> existsb f (map g l) = existsb h l.
Proof.
  intros Hfg. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hfg, IH. reflexivity.
Qed.

Lemma forallb_map_with {A B : Type} (f : B -> bool) (g : A -> B)
    (h : A -> bool) (l : list A) :
  (∀ a : A, f (g a) = h a) -> forallb f (map g l) = forallb h l.
Proof.
  intros Hfg. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hfg, IH. reflexivity.
Qed.

Lemma filter_map_with {A B : Type} (keep' : B -> bool) (g : A -> B)
    (keep : A -> bool) (l : list A) :
  (∀ a : A, keep' (g a) = keep a) ->
  filter keep' (map g l) = map g (filter keep l).
Proof.
  intros Hkeep. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hkeep, IH. destruct (keep a); reflexivity.
Qed.

(* A test of equality answers the same on the images of an injective
   function. *)
Lemma dec_injective {A B : Type} (dec : ∀ a a' : A, {a = a'} + {a <> a'})
    (g : A -> A) (a a' : A) (yes no : B) :
  (∀ a a' : A, g a = g a' -> a = a') ->
  (if dec (g a) (g a') then yes else no) = (if dec a a' then yes else no).
Proof.
  intros Hinjective.
  destruct (dec a a') as [-> | Hne], (dec (g _) (g _)) as [Heq | Hne'];
    try reflexivity; [ contradiction | ].
  elim Hne. exact (Hinjective _ _ Heq).
Qed.

(* ======================================================================== *)
(* A renaming is injective                                                  *)
(* ======================================================================== *)

Lemma rename_simple_injective (r : renaming) (s s' : simple) :
  rename_simple r s = rename_simple r s' -> s = s'.
Proof.
  destruct s, s'; simpl; intros Heq; try discriminate; try exact Heq.
  injection Heq as Heq. apply rename_variable_injective in Heq. congruence.
Qed.

Lemma rename_simples_injective (r : renaming) (args args' : list simple) :
  map (rename_simple r) args = map (rename_simple r) args' -> args = args'.
Proof.
  revert args'.
  induction args as [ | s args IH]; intros [ | s' args']; simpl; intros Heq;
    try discriminate; [ reflexivity | ].
  injection Heq as Hs Hargs.
  apply rename_simple_injective in Hs. apply IH in Hargs. congruence.
Qed.

Lemma rename_trap_action_injective (r : renaming)
    (action action' : option trap_action) :
  option_map (rename_trap_action r) action
  = option_map (rename_trap_action r) action' ->
  action = action'.
Proof.
  destruct action as [[k | k kind] | ], action' as [[k' | k' kind'] | ];
    simpl; intros Heq; try discriminate; try reflexivity;
    injection Heq as Hk; apply rename_continuation_injective in Hk;
    congruence.
Qed.

Lemma no_trap_action_renamed (r : renaming) (ac : apply_cont) :
  no_trap_action (rename_apply_cont r ac) = no_trap_action ac.
Proof.
  unfold no_trap_action. simpl. destruct (ac_trap_action ac); reflexivity.
Qed.

Lemma no_exn_extra_args_renamed (r : renaming) (ap : apply_expr) :
  no_exn_extra_args (rename_apply r ap) = no_exn_extra_args ap.
Proof.
  unfold no_exn_extra_args. simpl.
  destruct (ap_exn_extra_args ap); reflexivity.
Qed.

(* Whether a continuation is among those that an [Apply_cont] names. *)
Lemma among_apply_cont_continuations_renamed (r : renaming)
    (k : continuation) (ac : apply_cont) :
  among (rename_continuation r k)
    (apply_cont_continuations (rename_apply_cont r ac))
  = among k (apply_cont_continuations ac).
Proof.
  rewrite apply_cont_continuations_renamed.
  apply among_rename_continuation.
Qed.

Lemma rename_apply_cont_injective (r : renaming) (ac ac' : apply_cont) :
  rename_apply_cont r ac = rename_apply_cont r ac' -> ac = ac'.
Proof.
  destruct ac as [k args trap], ac' as [k' args' trap'].
  unfold rename_apply_cont. simpl. intros Heq.
  injection Heq as Hk Hargs Htrap.
  apply rename_continuation_injective in Hk.
  apply rename_simples_injective in Hargs.
  apply rename_trap_action_injective in Htrap. congruence.
Qed.

(* ======================================================================== *)
(* The checks of FlambdaNormaliseSpec.v                                     *)
(* ======================================================================== *)

Theorem expr_in_scope_equivariant : expr_in_scope_equivariant_statement.
Proof.
  intros r vs ks e. apply FlambdaEquivarianceProofs.expr_in_scope_equivariant.
Qed.

Theorem inlinable_b_equivariant : inlinable_b_equivariant_statement.
Proof. exact FlambdaEquivarianceProofs.inlinable_b_equivariant. Qed.

Lemma var_in_simple_equivariant (r : renaming) (x : variable) (s : simple) :
  var_in_simple (rename_variable r x) (rename_simple r s) = var_in_simple x s.
Proof. destruct s; simpl; [ apply rename_variable_eqb | | ]; reflexivity. Qed.

Lemma var_in_value_slots_equivariant (r : renaming) (x : variable)
    (slots : list (value_slot * simple)) :
  var_in_value_slots (rename_variable r x)
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = var_in_value_slots x slots.
Proof.
  unfold var_in_value_slots. apply existsb_map_with. intros slot.
  apply var_in_simple_equivariant.
Qed.

Lemma var_in_named_equivariant (r : renaming) (x : variable) (d : named) :
  var_in_named (rename_variable r x) (rename_named r d) = var_in_named x d.
Proof.
  destruct d; simpl;
    first
      [ apply var_in_simple_equivariant | apply var_in_simples_equivariant
      | apply var_in_value_slots_equivariant ].
Qed.

Lemma var_in_static_binding_equivariant (r : renaming) (x : variable)
    (binding : static_binding) :
  var_in_static_binding (rename_variable r x)
    (rename_static_binding r binding)
  = var_in_static_binding x binding.
Proof.
  destruct binding as [id c | id | sym const]; simpl; try reflexivity.
  destruct const; simpl;
    first
      [ reflexivity | apply var_in_value_slots_equivariant
      | apply var_in_simples_equivariant | apply var_in_simple_equivariant ].
Qed.

Fixpoint var_free_b_equivariant_aux (r : renaming) (x : variable) (e : expr) :
  var_free_b (rename_variable r x) (rename_expr r e) = var_free_b x e
with var_free_in_handler_b_equivariant (r : renaming) (x : variable)
    (h : continuation_handler) :
  var_free_in_handler_b (rename_variable r x) (rename_handler r h)
  = var_free_in_handler_b x h.
Proof.
  - destruct e
      as [ y d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl.
    + rewrite var_in_named_equivariant, rename_variable_eqb,
        var_free_b_equivariant_aux.
      reflexivity.
    + rewrite var_free_b_equivariant_aux. f_equal.
      apply existsb_map_with. intros binding.
      apply var_in_static_binding_equivariant.
    + rewrite var_free_in_handler_b_equivariant, var_free_b_equivariant_aux.
      reflexivity.
    + rewrite var_free_b_equivariant_aux. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (var_free_in_handler_b_equivariant r x h), IH. reflexivity.
    + rewrite exn_extra_simples_rename, var_in_simple_equivariant,
        !var_in_simples_equivariant.
      reflexivity.
    + apply var_in_simples_equivariant.
    + rewrite var_in_simple_equivariant. f_equal.
      apply existsb_map_with. intros arm. apply var_in_simples_equivariant.
    + reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite among_rename_variable, var_free_b_equivariant_aux. reflexivity.
Qed.

Theorem var_free_b_equivariant : var_free_b_equivariant_statement.
Proof. exact var_free_b_equivariant_aux. Qed.

(* ======================================================================== *)
(* Removing unused [Let]s                                                   *)
(* ======================================================================== *)

Lemma named_may_go_renamed (r : renaming) (d : named) :
  named_may_go (rename_named r d) = named_may_go d.
Proof. destruct d; reflexivity. Qed.

Fixpoint remove_unused_lets_equivariant_aux (r : renaming) (e : expr) :
  remove_unused_lets (rename_expr r e) = rename_expr r (remove_unused_lets e)
with remove_unused_lets_in_handler_equivariant (r : renaming)
    (h : continuation_handler) :
  remove_unused_lets_in_handler (rename_handler r h)
  = rename_handler r (remove_unused_lets_in_handler h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite remove_unused_lets_equivariant_aux, var_free_b_equivariant_aux,
        named_may_go_renamed.
      destruct
        (var_free_b x (remove_unused_lets body) || negb (named_may_go d));
        reflexivity.
    + rewrite remove_unused_lets_equivariant_aux. reflexivity.
    + rewrite remove_unused_lets_in_handler_equivariant,
        remove_unused_lets_equivariant_aux.
      reflexivity.
    + rewrite remove_unused_lets_equivariant_aux. reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite remove_unused_lets_equivariant_aux. reflexivity.
Qed.

Theorem remove_unused_lets_equivariant :
  remove_unused_lets_equivariant_statement.
Proof. exact remove_unused_lets_equivariant_aux. Qed.

Lemma named_is_total_renamed (r : renaming) (d : named) :
  named_is_total (rename_named r d) = named_is_total d.
Proof. destruct d as [[x | sym | c] | | | | | | ]; reflexivity. Qed.

Fixpoint remove_unused_total_lets_equivariant_aux (r : renaming) (e : expr) :
  remove_unused_total_lets (rename_expr r e)
  = rename_expr r (remove_unused_total_lets e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try reflexivity.
  - rewrite remove_unused_total_lets_equivariant_aux,
      var_free_b_equivariant_aux, named_is_total_renamed.
    destruct
      (named_is_total d
       && negb (var_free_b x (remove_unused_total_lets body)));
      reflexivity.
  - rewrite remove_unused_total_lets_equivariant_aux. reflexivity.
  - rewrite !remove_unused_total_lets_equivariant_aux. reflexivity.
  - rewrite remove_unused_total_lets_equivariant_aux. reflexivity.
Qed.

Theorem remove_unused_total_lets_equivariant :
  remove_unused_total_lets_equivariant_statement.
Proof. exact remove_unused_total_lets_equivariant_aux. Qed.

Lemma named_defined_equivariant (r : renaming) (vs : list variable)
    (d : named) :
  named_defined (map (rename_variable r) vs) (rename_named r d)
  = named_defined vs d.
Proof.
  destruct d; simpl; try reflexivity;
    [ apply simple_in_scope_equivariant
    | apply value_slots_in_scope_equivariant
    | rewrite value_slots_in_scope_equivariant; reflexivity ].
Qed.

Fixpoint remove_unused_defined_lets_equivariant_aux (r : renaming)
    (e : expr) :
  ∀ vs : list variable,
    remove_unused_defined_lets (map (rename_variable r) vs) (rename_expr r e)
    = rename_expr r (remove_unused_defined_lets vs e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    intros vs; simpl; try reflexivity.
  - change (rename_variable r x :: map (rename_variable r) vs)
      with (map (rename_variable r) (x :: vs)).
    rewrite remove_unused_defined_lets_equivariant_aux,
      named_defined_equivariant, var_free_b_equivariant_aux.
    destruct
      (named_defined vs d
       && negb (var_free_b x (remove_unused_defined_lets (x :: vs) body)));
      reflexivity.
  - rewrite remove_unused_defined_lets_equivariant_aux. reflexivity.
  - rewrite <- map_app, !remove_unused_defined_lets_equivariant_aux.
    reflexivity.
  - rewrite remove_unused_defined_lets_equivariant_aux. reflexivity.
Qed.

Theorem remove_unused_defined_lets_equivariant :
  remove_unused_defined_lets_equivariant_statement.
Proof.
  intros r vs e. apply remove_unused_defined_lets_equivariant_aux.
Qed.

(* ======================================================================== *)
(* A continuation applied once, at the end of its scope                     *)
(* ======================================================================== *)

Lemma inline_cont_at_tail_equivariant_aux (r : renaming) (k : continuation)
    (params : list variable) (metadata : handler_metadata) (handler : expr) :
  ∀ body : expr,
    inline_cont_at_tail (rename_continuation r k)
      (map (rename_variable r) params) metadata (rename_expr r handler)
      (rename_expr r body)
    = option_map (rename_expr r)
        (inline_cont_at_tail k params metadata handler body).
Proof.
  induction body
    as [ x kind d body IH | bindings body IH | k' h body IH | handlers body IH
       | ap | ac | scrutinee arms | ];
    simpl; try reflexivity.
  - rewrite among_rename_variable, var_free_b_equivariant_aux, IH.
    destruct (negb (among x params) && var_free_b x handler);
      [ reflexivity | ].
    destruct (inline_cont_at_tail k params metadata handler body); reflexivity.
  - rewrite IH.
    destruct (inline_cont_at_tail k params metadata handler body); reflexivity.
  - rewrite rename_continuation_eqb, no_trap_action_renamed, !length_map,
      params_not_in_args_equivariant.
    destruct
      (Pos.eqb (ac_continuation ac) k
       && no_trap_action ac
       && Nat.eqb (length params) (length (ac_args ac))
       && forallb (fun param => negb (var_in_simples param (ac_args ac)))
            params);
      [ | reflexivity ].
    simpl. rewrite let_params_equivariant. reflexivity.
Qed.

Theorem inline_cont_at_tail_equivariant :
  inline_cont_at_tail_equivariant_statement.
Proof.
  intros r k params metadata handler body.
  apply inline_cont_at_tail_equivariant_aux.
Qed.

Fixpoint inline_tail_conts_equivariant_aux (r : renaming) (e : expr) :
  inline_tail_conts (rename_expr r e) = rename_expr r (inline_tail_conts e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try reflexivity.
  - rewrite inline_tail_conts_equivariant_aux. reflexivity.
  - rewrite inline_tail_conts_equivariant_aux. reflexivity.
  - rewrite !inline_tail_conts_equivariant_aux,
      inline_cont_at_tail_equivariant_aux.
    destruct
      (inline_cont_at_tail k params metadata (inline_tail_conts handler)
         (inline_tail_conts body));
      reflexivity.
  - rewrite inline_tail_conts_equivariant_aux. reflexivity.
Qed.

Theorem inline_tail_conts_equivariant :
  inline_tail_conts_equivariant_statement.
Proof. exact inline_tail_conts_equivariant_aux. Qed.

(* ======================================================================== *)
(* Static bindings: deleted code, and groups                                *)
(* ======================================================================== *)

Lemma binds_something_renamed (r : renaming) (binding : static_binding) :
  binds_something (rename_static_binding r binding)
  = binds_something binding.
Proof. destruct binding; reflexivity. Qed.

Lemma let_static_if_any_equivariant (r : renaming)
    (bindings : list static_binding) (body : expr) :
  let_static_if_any (map (rename_static_binding r) bindings)
    (rename_expr r body)
  = rename_expr r (let_static_if_any bindings body).
Proof. destruct bindings; reflexivity. Qed.

Fixpoint drop_deleted_code_equivariant_aux (r : renaming) (e : expr) :
  drop_deleted_code (rename_expr r e) = rename_expr r (drop_deleted_code e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try reflexivity.
  - rewrite drop_deleted_code_equivariant_aux. reflexivity.
  - rewrite (filter_map_with _ _ _ _ (binds_something_renamed r)),
      drop_deleted_code_equivariant_aux.
    apply let_static_if_any_equivariant.
  - rewrite !drop_deleted_code_equivariant_aux. reflexivity.
  - rewrite drop_deleted_code_equivariant_aux. reflexivity.
Qed.

Theorem drop_deleted_code_equivariant :
  drop_deleted_code_equivariant_statement.
Proof. exact drop_deleted_code_equivariant_aux. Qed.

Lemma binds_code_renamed (r : renaming) (binding : static_binding) :
  binds_code (rename_static_binding r binding) = binds_code binding.
Proof. destruct binding; reflexivity. Qed.

Lemma code_first_equivariant (r : renaming) (bindings : list static_binding) :
  code_first (map (rename_static_binding r) bindings)
  = map (rename_static_binding r) (code_first bindings).
Proof.
  unfold code_first. rewrite map_app.
  rewrite (filter_map_with _ _ binds_code) by apply binds_code_renamed.
  rewrite (filter_map_with _ _ (fun binding => negb (binds_code binding)))
    by (intros binding; rewrite binds_code_renamed; reflexivity).
  reflexivity.
Qed.

Fixpoint merge_statics_equivariant_aux (r : renaming) (e : expr) :
  merge_statics (rename_expr r e) = rename_expr r (merge_statics e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try reflexivity.
  - rewrite merge_statics_equivariant_aux. reflexivity.
  - rewrite merge_statics_equivariant_aux.
    destruct (merge_statics body); simpl;
      rewrite <- ?map_app, code_first_equivariant; reflexivity.
  - rewrite !merge_statics_equivariant_aux. reflexivity.
  - rewrite merge_statics_equivariant_aux. reflexivity.
Qed.

Theorem merge_statics_equivariant : merge_statics_equivariant_statement.
Proof. exact merge_statics_equivariant_aux. Qed.

(* ======================================================================== *)
(* Inlining calls of symbols known to be closures                           *)
(* ======================================================================== *)

Lemma symbols_of_renamed (r : renaming) (bindings : list static_binding) :
  ∀ known : list (symbol * option code_id),
    symbols_of (map (rename_static_binding r) bindings) known
    = symbols_of bindings known.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH];
    intros known; simpl; [ reflexivity | apply IH | apply IH | ].
  destruct const; simpl; apply IH.
Qed.

Lemma simple_has_kind_b_renamed (r : renaming) (s : simple)
    (kind : flambda_kind) :
  simple_has_kind_b (rename_simple r s) kind = simple_has_kind_b s kind.
Proof. destruct s; reflexivity. Qed.

Lemma args_have_kinds_renamed (r : renaming) (args : list simple) :
  ∀ kinds : list flambda_kind,
    FlambdaCompareSpec.forall2b simple_has_kind_b
      (map (rename_simple r) args) kinds
    = FlambdaCompareSpec.forall2b simple_has_kind_b args kinds.
Proof.
  induction args as [ | arg args IH]; intros [ | kind kinds]; simpl;
    try reflexivity.
  rewrite simple_has_kind_b_renamed, IH. reflexivity.
Qed.

Lemma call_agrees_b_renamed (r : renaming) (ap : apply_expr) (c : code) :
  call_agrees_b (rename_apply r ap) (rename_code r c) = call_agrees_b ap c.
Proof.
  destruct c as [params my_closure ret exn metadata body].
  unfold call_agrees_b. simpl. rewrite args_have_kinds_renamed. reflexivity.
Qed.

Theorem simple_has_kind_b_equivariant :
  simple_has_kind_b_equivariant_statement.
Proof. exact simple_has_kind_b_renamed. Qed.

Theorem call_agrees_b_equivariant : call_agrees_b_equivariant_statement.
Proof. exact call_agrees_b_renamed. Qed.

Lemma inline_known_apply_equivariant (r : renaming)
    (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (ap : apply_expr) :
  inline_known_apply (map_values (rename_code r) known_code) known_symbols
    (rename_apply r ap)
  = rename_expr r (inline_known_apply known_code known_symbols ap).
Proof.
  unfold inline_known_apply.
  replace (ap_callee (rename_apply r ap)) with (rename_simple r (ap_callee ap))
    by reflexivity.
  replace (ap_call_kind (rename_apply r ap)) with (ap_call_kind ap)
    by reflexivity.
  destruct (ap_callee ap) as [x | s | c]; cbn [rename_simple];
    try reflexivity.
  destruct (ap_call_kind ap) as [called | ]; [ | reflexivity ].
  rewrite lookup_map_values.
  destruct (lookup s known_symbols) as [[code | ] | ]; try reflexivity.
  destruct (lookup called known_code) as [c | ]; cbn [option_map];
    [ | reflexivity ].
  rewrite FlambdaEquivarianceProofs.inlinable_b_equivariant,
    call_agrees_b_renamed.
  destruct (Pos.eqb code called && inlinable_b ap c && call_agrees_b ap c);
    [ | reflexivity ].
  apply inlined_body_equivariant.
Qed.

Fixpoint inline_known_calls_equivariant_aux (r : renaming)
    (known_symbols : list (symbol * option code_id)) (e : expr) :
  ∀ known_code : list (code_id * code),
    inline_known_calls (map_values (rename_code r) known_code) known_symbols
      (rename_expr r e)
    = rename_expr r (inline_known_calls known_code known_symbols e)
with inline_known_calls_in_handler_equivariant (r : renaming)
    (known_symbols : list (symbol * option code_id))
    (h : continuation_handler) :
  ∀ known_code : list (code_id * code),
    inline_known_calls_in_handler (map_values (rename_code r) known_code)
      known_symbols (rename_handler r h)
    = rename_handler r
        (inline_known_calls_in_handler known_code known_symbols h)
with inline_known_calls_in_binding_equivariant (r : renaming)
    (known_symbols : list (symbol * option code_id))
    (binding : static_binding) :
  ∀ known_code : list (code_id * code),
    inline_known_calls_in_binding (map_values (rename_code r) known_code)
      known_symbols (rename_static_binding r binding)
    = rename_static_binding r
        (inline_known_calls_in_binding known_code known_symbols binding)
with inline_known_calls_in_code_equivariant (r : renaming)
    (known_symbols : list (symbol * option code_id)) (c : code) :
  ∀ known_code : list (code_id * code),
    inline_known_calls_in_code (map_values (rename_code r) known_code)
      known_symbols (rename_code r c)
    = rename_code r (inline_known_calls_in_code known_code known_symbols c).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros known_code;
      [ | | | | exact
                  (inline_known_apply_equivariant r known_code known_symbols
                     ap)
      | | | ];
      simpl; try reflexivity.
    + rewrite inline_known_calls_equivariant_aux. reflexivity.
    + (* Let_static: what is known in the body is what the group, as
         rewritten, makes known *)
      assert (Hbindings :
        map
          (inline_known_calls_in_binding (map_values (rename_code r) known_code)
             known_symbols)
          (map (rename_static_binding r) bindings)
        = map (rename_static_binding r)
            (map (inline_known_calls_in_binding known_code known_symbols)
               bindings)).
      { induction bindings as [ | binding bindings IH]; simpl;
          [ reflexivity | ].
        rewrite (inline_known_calls_in_binding_equivariant r known_symbols
                   binding), IH.
        reflexivity. }
      rewrite Hbindings, codes_of_equivariant, symbols_of_renamed,
        inline_known_calls_equivariant_aux.
      reflexivity.
    + rewrite inline_known_calls_in_handler_equivariant,
        inline_known_calls_equivariant_aux.
      reflexivity.
    + rewrite inline_known_calls_equivariant_aux. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (inline_known_calls_in_handler_equivariant r known_symbols h),
        IH.
      reflexivity.
  - destruct h as [params metadata handler]. intros known_code. simpl.
    rewrite inline_known_calls_equivariant_aux. reflexivity.
  - destruct binding as [id c | id | sym const]; intros known_code; simpl;
      try reflexivity.
    rewrite inline_known_calls_in_code_equivariant. reflexivity.
  - destruct c as [params my_closure ret exn metadata body].
    intros known_code. simpl.
    rewrite inline_known_calls_equivariant_aux. reflexivity.
Qed.

Theorem inline_known_calls_equivariant :
  inline_known_calls_equivariant_statement.
Proof.
  intros r known_code known_symbols e.
  apply inline_known_calls_equivariant_aux.
Qed.

(* ======================================================================== *)
(* Switches                                                                 *)
(* ======================================================================== *)

Lemma collapse_switch_equivariant (r : renaming) (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  collapse_switch (rename_simple r scrutinee)
    (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  = rename_expr r (collapse_switch scrutinee arms).
Proof.
  destruct arms as [ | [i ac] others]; [ reflexivity | ].
  unfold collapse_switch. cbn [map fst snd].
  rewrite
    (forallb_map_with _ _
       (fun arm => if apply_cont_eq_dec (snd arm) ac then true else false)).
  - destruct
      (forallb
         (fun arm => if apply_cont_eq_dec (snd arm) ac then true else false)
         others);
      reflexivity.
  - intros arm. cbn [snd].
    apply (dec_injective apply_cont_eq_dec (rename_apply_cont r)).
    apply rename_apply_cont_injective.
Qed.

Fixpoint collapse_switches_equivariant_aux (r : renaming) (e : expr) :
  collapse_switches (rename_expr r e) = rename_expr r (collapse_switches e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try reflexivity.
  - rewrite collapse_switches_equivariant_aux. reflexivity.
  - rewrite collapse_switches_equivariant_aux. reflexivity.
  - rewrite !collapse_switches_equivariant_aux. reflexivity.
  - rewrite collapse_switches_equivariant_aux. reflexivity.
  - apply collapse_switch_equivariant.
Qed.

Theorem collapse_switches_equivariant :
  collapse_switches_equivariant_statement.
Proof. exact collapse_switches_equivariant_aux. Qed.

Lemma thread_arm_equivariant (r : renaming) (k : continuation)
    (inner : list (Z * apply_cont)) (arm : Z * apply_cont) :
  thread_arm (rename_continuation r k)
    (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) inner)
    (fst arm, rename_apply_cont r (snd arm))
  = (fst (thread_arm k inner arm),
     rename_apply_cont r (snd (thread_arm k inner arm))).
Proof.
  destruct arm as [i ac]. unfold thread_arm. cbn [fst snd].
  change (ac_args (rename_apply_cont r ac))
    with (map (rename_simple r) (ac_args ac)).
  destruct (ac_args ac) as [ | arg args]; [ | reflexivity ]. cbn [map].
  change (ac_continuation (rename_apply_cont r ac))
    with (rename_continuation r (ac_continuation ac)).
  rewrite rename_continuation_eqb, no_trap_action_renamed.
  destruct (Pos.eqb (ac_continuation ac) k && no_trap_action ac);
    [ | reflexivity ].
  rewrite find_arm_renamed.
  destruct (find_arm i inner) as [ac' | ]; cbn [option_map];
    [ | reflexivity ].
  cbn [rename_apply_cont ac_continuation]. rewrite rename_continuation_eqb.
  destruct (Pos.eqb (ac_continuation ac') k); reflexivity.
Qed.

Lemma arms_apply_equivariant (r : renaming) (k : continuation)
    (arms : list (Z * apply_cont)) :
  arms_apply (rename_continuation r k)
    (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  = arms_apply k arms.
Proof.
  unfold arms_apply. apply existsb_map_with. intros arm. cbn [snd].
  apply among_apply_cont_continuations_renamed.
Qed.

Lemma thread_switch_equivariant (r : renaming) (k : continuation)
    (h : continuation_handler) (body : expr) :
  thread_switch (rename_continuation r k) (rename_handler r h)
    (rename_expr r body)
  = rename_expr r (thread_switch k h body).
Proof.
  destruct h as [[ | param params] metadata handler]; [ | reflexivity ].
  destruct handler as [ | | | | | | inner_scrutinee inner | ];
    try reflexivity.
  destruct body as [ | | | | | | scrutinee arms | ]; try reflexivity.
  cbn [thread_switch rename_handler rename_expr map].
  rewrite (dec_injective simple_eq_dec (rename_simple r))
    by apply rename_simple_injective.
  destruct (simple_eq_dec scrutinee inner_scrutinee); [ | reflexivity ].
  rewrite !map_map.
  rewrite
    (map_ext _
       (fun arm =>
          (fst (thread_arm k inner arm),
           rename_apply_cont r (snd (thread_arm k inner arm))))
       (thread_arm_equivariant r k inner)).
  rewrite <- (map_map (thread_arm k inner)
                (fun arm => (fst arm, rename_apply_cont r (snd arm)))).
  rewrite arms_apply_equivariant.
  destruct (arms_apply k (map (thread_arm k inner) arms)); reflexivity.
Qed.

Fixpoint thread_switches_equivariant_aux (r : renaming) (e : expr) :
  thread_switches (rename_expr r e) = rename_expr r (thread_switches e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try reflexivity.
  - rewrite thread_switches_equivariant_aux. reflexivity.
  - rewrite thread_switches_equivariant_aux. reflexivity.
  - rewrite !thread_switches_equivariant_aux.
    exact
      (thread_switch_equivariant r k
         (Handler params metadata (thread_switches handler))
         (thread_switches body)).
  - rewrite thread_switches_equivariant_aux. reflexivity.
Qed.

Theorem thread_switches_equivariant :
  thread_switches_equivariant_statement.
Proof. exact thread_switches_equivariant_aux. Qed.

(* ======================================================================== *)
(* Rewriting the bodies of code                                             *)
(* ======================================================================== *)

Section Rewrite_code.

Variable f : expr -> expr.
Hypothesis f_equivariant : rewrite_equivariant f.

Lemma rewrite_code_body_equivariant (r : renaming) (body : expr) :
  rewrite_code_body f (rename_expr r body)
  = rename_expr r (rewrite_code_body f body).
Proof.
  unfold rewrite_code_body. rewrite f_equivariant, !rename_binds_statics.
  destruct (Bool.eqb (binds_statics body) (binds_statics (f body)));
    reflexivity.
Qed.

Lemma rewrite_code_in_binding_equivariant (r : renaming)
    (binding : static_binding) :
  rewrite_code_in_binding f (rename_static_binding r binding)
  = rename_static_binding r (rewrite_code_in_binding f binding).
Proof.
  destruct binding
    as [id [params my_closure ret exn metadata body] | id | sym const];
    try reflexivity.
  cbn [rename_static_binding rename_code rewrite_code_in_binding].
  rewrite rewrite_code_body_equivariant. reflexivity.
Qed.

Fixpoint rewrite_code_equivariant_aux (r : renaming) (e : expr) :
  rewrite_code f (rename_expr r e) = rename_expr r (rewrite_code f e)
with rewrite_code_in_handler_equivariant (r : renaming)
    (h : continuation_handler) :
  rewrite_code_in_handler f (rename_handler r h)
  = rename_handler r (rewrite_code_in_handler f h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite rewrite_code_equivariant_aux. reflexivity.
    + rewrite rewrite_code_equivariant_aux, !map_map. f_equal.
      apply map_ext. exact (rewrite_code_in_binding_equivariant r).
    + rewrite rewrite_code_in_handler_equivariant,
        rewrite_code_equivariant_aux.
      reflexivity.
    + rewrite rewrite_code_equivariant_aux. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (rewrite_code_in_handler_equivariant r h), IH. reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite rewrite_code_equivariant_aux. reflexivity.
Qed.

End Rewrite_code.

Theorem rewrite_code_equivariant : rewrite_code_equivariant_statement.
Proof.
  intros f f_equivariant r e.
  apply rewrite_code_equivariant_aux, f_equivariant.
Qed.

(* ======================================================================== *)
(* FlambdaUnusedContsSpec.v                                                 *)
(* ======================================================================== *)

Fixpoint cont_free_b_equivariant_aux (r : renaming) (k : continuation)
    (e : expr) :
  cont_free_b (rename_continuation r k) (rename_expr r e) = cont_free_b k e
with cont_free_in_handler_b_equivariant (r : renaming) (k : continuation)
    (h : continuation_handler) :
  cont_free_in_handler_b (rename_continuation r k) (rename_handler r h)
  = cont_free_in_handler_b k h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | bound h body | handlers body | ap
         | ac | scrutinee arms | ];
      simpl.
    + apply cont_free_b_equivariant_aux.
    + apply cont_free_b_equivariant_aux.
    + rewrite cont_free_in_handler_b_equivariant, rename_continuation_eqb,
        cont_free_b_equivariant_aux.
      reflexivity.
    + rewrite cont_free_b_equivariant_aux. f_equal.
      induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (cont_free_in_handler_b_equivariant r k h), IH. reflexivity.
    + rewrite !rename_continuation_eqb. reflexivity.
    + exact (among_apply_cont_continuations_renamed r k ac).
    + apply existsb_map_with. intros arm.
      exact (among_apply_cont_continuations_renamed r k (snd arm)).
    + reflexivity.
  - destruct h as [params metadata handler]. simpl.
    apply cont_free_b_equivariant_aux.
Qed.

Theorem cont_free_b_equivariant : cont_free_b_equivariant_statement.
Proof. exact cont_free_b_equivariant_aux. Qed.

Fixpoint remove_unused_conts_equivariant_aux (r : renaming) (e : expr) :
  remove_unused_conts (rename_expr r e)
  = rename_expr r (remove_unused_conts e)
with remove_unused_conts_in_handler_equivariant (r : renaming)
    (h : continuation_handler) :
  remove_unused_conts_in_handler (rename_handler r h)
  = rename_handler r (remove_unused_conts_in_handler h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite remove_unused_conts_equivariant_aux. reflexivity.
    + rewrite remove_unused_conts_equivariant_aux. reflexivity.
    + rewrite remove_unused_conts_equivariant_aux,
        cont_free_b_equivariant_aux,
        remove_unused_conts_in_handler_equivariant.
      destruct (cont_free_b k (remove_unused_conts body)); reflexivity.
    + rewrite remove_unused_conts_equivariant_aux. reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite remove_unused_conts_equivariant_aux. reflexivity.
Qed.

Theorem remove_unused_conts_equivariant :
  remove_unused_conts_equivariant_statement.
Proof. exact remove_unused_conts_equivariant_aux. Qed.

(* ======================================================================== *)
(* FlambdaUnusedStaticsSpec.v                                               *)
(* ======================================================================== *)

Section Dropped.

Variable D : dropped.

Lemma simple_avoids_renamed (r : renaming) (s : simple) :
  simple_avoids D (rename_simple r s) = simple_avoids D s.
Proof. destruct s; reflexivity. Qed.

Lemma simples_avoid_renamed (r : renaming) (args : list simple) :
  simples_avoid D (map (rename_simple r) args) = simples_avoid D args.
Proof.
  unfold simples_avoid. apply forallb_map_with. apply simple_avoids_renamed.
Qed.

Lemma value_slots_avoid_renamed (r : renaming)
    (slots : list (value_slot * simple)) :
  value_slots_avoid D
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = value_slots_avoid D slots.
Proof.
  unfold value_slots_avoid. apply forallb_map_with. intros slot.
  apply simple_avoids_renamed.
Qed.

Lemma named_avoids_renamed (r : renaming) (d : named) :
  named_avoids D (rename_named r d) = named_avoids D d.
Proof.
  destruct d; simpl;
    rewrite ?value_slots_avoid_renamed, ?simples_avoid_renamed,
      ?simple_avoids_renamed;
    reflexivity.
Qed.

Lemma static_const_avoids_renamed (r : renaming) (const : static_const) :
  static_const_avoids D (rename_static_const r const)
  = static_const_avoids D const.
Proof.
  destruct const; simpl;
    rewrite ?value_slots_avoid_renamed, ?simples_avoid_renamed,
      ?simple_avoids_renamed;
    reflexivity.
Qed.

Lemma apply_cont_avoids_renamed (r : renaming) (ac : apply_cont) :
  apply_cont_avoids D (rename_apply_cont r ac) = apply_cont_avoids D ac.
Proof. apply simples_avoid_renamed. Qed.

Lemma apply_avoids_renamed (r : renaming) (ap : apply_expr) :
  apply_avoids D (rename_apply r ap) = apply_avoids D ap.
Proof.
  unfold apply_avoids. simpl.
  rewrite exn_extra_simples_rename, simple_avoids_renamed,
    !simples_avoid_renamed.
  reflexivity.
Qed.

Fixpoint expr_avoids_renamed (r : renaming) (e : expr) :
  expr_avoids D (rename_expr r e) = expr_avoids D e
with handler_avoids_renamed (r : renaming) (h : continuation_handler) :
  handler_avoids D (rename_handler r h) = handler_avoids D h
with binding_avoids_renamed (r : renaming) (binding : static_binding) :
  binding_avoids D (rename_static_binding r binding)
  = binding_avoids D binding
with code_avoids_renamed (r : renaming) (c : code) :
  code_avoids D (rename_code r c) = code_avoids D c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl.
    + rewrite named_avoids_renamed, expr_avoids_renamed. reflexivity.
    + rewrite expr_avoids_renamed. f_equal.
      induction bindings as [ | binding bindings IH]; simpl;
        [ reflexivity | ].
      rewrite (binding_avoids_renamed r binding), IH. reflexivity.
    + rewrite handler_avoids_renamed, expr_avoids_renamed. reflexivity.
    + rewrite expr_avoids_renamed. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (handler_avoids_renamed r h), IH. reflexivity.
    + apply apply_avoids_renamed.
    + apply apply_cont_avoids_renamed.
    + rewrite simple_avoids_renamed. f_equal.
      apply forallb_map_with. intros arm. apply apply_cont_avoids_renamed.
    + reflexivity.
  - destruct h as [params metadata handler]. simpl. apply expr_avoids_renamed.
  - destruct binding as [id c | id | sym const]; simpl; try reflexivity.
    + rewrite code_avoids_renamed. reflexivity.
    + rewrite static_const_avoids_renamed. reflexivity.
  - destruct c as [params my_closure ret exn metadata body]. simpl.
    apply expr_avoids_renamed.
Qed.

Lemma binding_kept_renamed (r : renaming) (binding : static_binding) :
  binding_kept D (rename_static_binding r binding) = binding_kept D binding.
Proof. destruct binding; reflexivity. Qed.

Fixpoint erase_expr_equivariant_aux (r : renaming) (e : expr) :
  erase_expr D (rename_expr r e) = rename_expr r (erase_expr D e)
with erase_handler_equivariant (r : renaming) (h : continuation_handler) :
  erase_handler D (rename_handler r h) = rename_handler r (erase_handler D h)
with erase_binding_equivariant (r : renaming) (binding : static_binding) :
  erase_binding D (rename_static_binding r binding)
  = rename_static_binding r (erase_binding D binding)
with erase_code_equivariant (r : renaming) (c : code) :
  erase_code D (rename_code r c) = rename_code r (erase_code D c).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite erase_expr_equivariant_aux. reflexivity.
    + rewrite erase_expr_equivariant_aux. f_equal.
      induction bindings as [ | binding bindings IH]; simpl;
        [ reflexivity | ].
      rewrite binding_kept_renamed, IH.
      destruct (binding_kept D binding); [ | reflexivity ].
      simpl. rewrite (erase_binding_equivariant r binding). reflexivity.
    + rewrite erase_handler_equivariant, erase_expr_equivariant_aux.
      reflexivity.
    + rewrite erase_expr_equivariant_aux. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (erase_handler_equivariant r h), IH. reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite erase_expr_equivariant_aux. reflexivity.
  - destruct binding as [id c | id | sym const]; simpl; try reflexivity.
    rewrite erase_code_equivariant. reflexivity.
  - destruct c as [params my_closure ret exn metadata body]. simpl.
    rewrite erase_expr_equivariant_aux. reflexivity.
Qed.

Fixpoint binds_only_kept_renamed (r : renaming) (e : expr) :
  binds_only_kept D (rename_expr r e) = binds_only_kept D e
with handler_binds_only_kept_renamed (r : renaming)
    (h : continuation_handler) :
  handler_binds_only_kept D (rename_handler r h)
  = handler_binds_only_kept D h
with binding_binds_only_kept_renamed (r : renaming)
    (binding : static_binding) :
  binding_binds_only_kept D (rename_static_binding r binding)
  = binding_binds_only_kept D binding
with code_binds_only_kept_renamed (r : renaming) (c : code) :
  code_binds_only_kept D (rename_code r c) = code_binds_only_kept D c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + apply binds_only_kept_renamed.
    + rewrite binds_only_kept_renamed. f_equal.
      induction bindings as [ | binding bindings IH]; simpl;
        [ reflexivity | ].
      rewrite (binding_binds_only_kept_renamed r binding), IH. reflexivity.
    + rewrite handler_binds_only_kept_renamed, binds_only_kept_renamed.
      reflexivity.
    + rewrite binds_only_kept_renamed. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (handler_binds_only_kept_renamed r h), IH. reflexivity.
  - destruct h as [params metadata handler]. simpl.
    apply binds_only_kept_renamed.
  - destruct binding as [id c | id | sym const]; simpl; try reflexivity.
    rewrite code_binds_only_kept_renamed. reflexivity.
  - destruct c as [params my_closure ret exn metadata body]. simpl.
    apply binds_only_kept_renamed.
Qed.

Lemma handler_free_of_renamed (r : renaming) (h : continuation_handler) :
  handler_free_of D (rename_handler r h) = handler_free_of D h.
Proof.
  unfold handler_free_of.
  rewrite handler_avoids_renamed, handler_binds_only_kept_renamed.
  reflexivity.
Qed.

Lemma code_free_of_renamed (r : renaming) (c : code) :
  code_free_of D (rename_code r c) = code_free_of D c.
Proof.
  unfold code_free_of.
  rewrite code_avoids_renamed, code_binds_only_kept_renamed. reflexivity.
Qed.

Lemma env_free_of_renamed (r : renaming) (vars : env) :
  env_free_of D (rename_env r vars) = env_free_of D vars.
Proof.
  unfold env_free_of, rename_env. apply forallb_map_with.
  intros [x v]. reflexivity.
Qed.

Lemma handlers_free_of_renamed (r : renaming)
    (handlers : list (continuation * continuation_handler)) :
  forallb (fun '(_, h) => handler_free_of D h) (rename_handlers r handlers)
  = forallb (fun '(_, h) => handler_free_of D h) handlers.
Proof.
  unfold rename_handlers. apply forallb_map_with. intros [k h].
  apply handler_free_of_renamed.
Qed.

Fixpoint cont_free_of_renamed (r : renaming) (c : cont_value) :
  cont_free_of D (rename_cont_value r c) = cont_free_of D c.
Proof.
  destruct c as [h vars conts recursive | k | c extra]; simpl;
    [ | reflexivity | rewrite (cont_free_of_renamed r c); reflexivity ].
  rewrite handler_free_of_renamed, env_free_of_renamed,
    handlers_free_of_renamed.
  do 2 f_equal.
  induction conts as [ | [k c] conts IH]; simpl; [ reflexivity | ].
  rewrite (cont_free_of_renamed r c), IH. reflexivity.
Qed.

Lemma statics_free_of_renamed (r : renaming) (statics : static_env) :
  statics_free_of D (rename_static_env r statics) = statics_free_of D statics.
Proof.
  unfold statics_free_of, rename_static_env. simpl. f_equal.
  unfold map_values. apply forallb_map_with. intros [id c].
  apply code_free_of_renamed.
Qed.

End Dropped.

Theorem expr_avoids_equivariant : expr_avoids_equivariant_statement.
Proof. intros r D e. apply expr_avoids_renamed. Qed.

Theorem erase_expr_equivariant : erase_expr_equivariant_statement.
Proof. intros D r e. apply erase_expr_equivariant_aux. Qed.

Theorem drop_statics_equivariant : drop_statics_equivariant_statement.
Proof.
  intros r D e. unfold drop_statics. rewrite expr_avoids_renamed.
  destruct (expr_avoids D e); [ | reflexivity ].
  simpl. rewrite erase_expr_equivariant_aux. reflexivity.
Qed.

Theorem binds_only_kept_equivariant : binds_only_kept_equivariant_statement.
Proof. intros r D e. apply binds_only_kept_renamed. Qed.

Theorem envs_free_of_equivariant : envs_free_of_equivariant_statement.
Proof.
  intros r D vars conts statics. unfold envs_free_of.
  rewrite env_free_of_renamed, statics_free_of_renamed. do 2 f_equal.
  unfold rename_cont_env. apply forallb_map_with. intros [k c].
  apply cont_free_of_renamed.
Qed.

(* ======================================================================== *)
(* FlambdaBlockLoadSpec.v                                                   *)
(* ======================================================================== *)

(* A map whose keys are renamed: a renaming is injective, so a name is
   found where its image is. *)
Lemma lookup_renamed_keys {A B : Type} (p : permutation) (g : A -> B)
    (x : positive) (l : list (positive * A)) :
  lookup (permute p x)
    (map (fun entry => (permute p (fst entry), g (snd entry))) l)
  = option_map g (lookup x l).
Proof.
  induction l as [ | [y a] l IH]; simpl; [ reflexivity | ].
  rewrite permute_eqb. destruct (Pos.eqb x y); [ reflexivity | exact IH ].
Qed.

Lemma lookup_value_slots_renamed (r : renaming) (slot : value_slot)
    (slots : list (value_slot * simple)) :
  lookup slot (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = option_map (rename_simple r) (lookup slot slots).
Proof.
  induction slots as [ | [slot' s] slots IH]; simpl; [ reflexivity | ].
  destruct (Pos.eqb slot slot'); [ reflexivity | exact IH ].
Qed.

Lemma forget_field_equivariant (r : renaming) (x : variable)
    (field : option simple) :
  forget_field (rename_variable r x) (option_map (rename_simple r) field)
  = option_map (rename_simple r) (forget_field x field).
Proof.
  destruct field as [s | ]; simpl; [ | reflexivity ].
  rewrite var_in_simple_equivariant. destruct (var_in_simple x s); reflexivity.
Qed.

Lemma forget_in_block_equivariant (r : renaming) (x : variable)
    (block : known_block) :
  forget_in_block (rename_variable r x) (rename_known_block r block)
  = rename_known_block r (forget_in_block x block).
Proof.
  unfold forget_in_block, rename_known_block. simpl. rewrite !map_map.
  f_equal. apply map_ext. intros field. apply forget_field_equivariant.
Qed.

Lemma forget_var_equivariant (r : renaming) (x : variable)
    (known : known_blocks) :
  forget_var (rename_variable r x) (rename_known_blocks r known)
  = rename_known_blocks r (forget_var x known).
Proof.
  unfold forget_var, rename_known_blocks, map_values. simpl. f_equal.
  - rewrite
      (filter_map_with _ _
         (fun entry => negb (Pos.eqb x (fst entry))))
      by (intros entry; simpl; rewrite rename_variable_eqb; reflexivity).
    rewrite !map_map. apply map_ext. intros entry. simpl.
    rewrite forget_in_block_equivariant. reflexivity.
  - rewrite !map_map. apply map_ext. intros [sym block]. simpl.
    rewrite forget_in_block_equivariant. reflexivity.
Qed.

Lemma forget_vars_equivariant (r : renaming) (xs : list variable) :
  ∀ known : known_blocks,
    forget_vars (map (rename_variable r) xs) (rename_known_blocks r known)
    = rename_known_blocks r (forget_vars xs known).
Proof.
  induction xs as [ | x xs IH]; intros known; simpl; [ reflexivity | ].
  rewrite forget_var_equivariant. apply IH.
Qed.

Lemma block_made_equivariant (r : renaming) (d : named) :
  block_made (rename_named r d)
  = option_map (rename_known_block r) (block_made d).
Proof.
  destruct d as [s | p args | | | | | ]; try reflexivity.
  destruct p as [p | p | [[tag]]]; try reflexivity.
  simpl. unfold rename_known_block. simpl. rewrite !map_map. reflexivity.
Qed.

Lemma known_under_let_equivariant (r : renaming) (known : known_blocks)
    (x : variable) (d : named) :
  known_under_let (rename_known_blocks r known) (rename_variable r x)
    (rename_named r d)
  = rename_known_blocks r (known_under_let known x d).
Proof.
  unfold known_under_let.
  rewrite forget_var_equivariant, block_made_equivariant.
  destruct (block_made d) as [block | ]; cbn [option_map]; [ | reflexivity ].
  rewrite forget_in_block_equivariant. reflexivity.
Qed.

Lemma static_block_made_renamed (r : renaming) (binding : static_binding) :
  static_block_made (rename_static_binding r binding)
  = map_values (rename_known_block r) (static_block_made binding).
Proof.
  destruct binding as [id c | id | sym const]; try reflexivity.
  destruct const; try reflexivity.
  simpl. unfold rename_known_block. simpl. rewrite !map_map. reflexivity.
Qed.

Lemma known_under_statics_equivariant (r : renaming) (known : known_blocks)
    (bindings : list static_binding) :
  known_under_statics (rename_known_blocks r known)
    (map (rename_static_binding r) bindings)
  = rename_known_blocks r (known_under_statics known bindings).
Proof.
  unfold known_under_statics, rename_known_blocks, map_values. simpl.
  f_equal. rewrite map_app. f_equal.
  induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
  rewrite static_block_made_renamed, map_app, IH. reflexivity.
Qed.

Lemma known_block_of_equivariant (r : renaming) (known : known_blocks)
    (s : simple) :
  known_block_of (rename_known_blocks r known) (rename_simple r s)
  = option_map (rename_known_block r) (known_block_of known s).
Proof.
  destruct s as [x | sym | c]; simpl;
    [ apply lookup_renamed_keys | apply lookup_map_values | reflexivity ].
Qed.

Lemma field_loaded_equivariant (r : renaming) (kind : block_access_kind)
    (field : Z) (block : known_block) :
  field_loaded kind field (rename_known_block r block)
  = option_map (rename_simple r) (field_loaded kind field block).
Proof.
  destruct kind as [tag size [ | ]]; [ | reflexivity ].
  unfold field_loaded, rename_known_block. simpl. rewrite length_map.
  destruct
    (known_is tag (fst block)
     && known_is size (Z.of_nat (length (snd block)))
     && (0 <=? field)%Z);
    [ | reflexivity ].
  rewrite nth_error_map.
  destruct (nth_error (snd block) (Z.to_nat field)) as [[contents | ] | ];
    reflexivity.
Qed.

Lemma of_known_block_equivariant (r : renaming) (p : unary_primitive)
    (block : known_block) :
  of_known_block p (rename_known_block r block)
  = option_map (rename_simple r) (of_known_block p block).
Proof.
  destruct p as [kind mut field | | | | | | | | | | | | ]; try reflexivity.
  destruct mut; try reflexivity; apply field_loaded_equivariant.
Qed.

Lemma unary_applied_equivariant (r : renaming) (p : prim)
    (args : list simple) :
  unary_applied p (map (rename_simple r) args)
  = option_map (fun applied => (fst applied, rename_simple r (snd applied)))
      (unary_applied p args).
Proof.
  destruct p; try reflexivity.
  destruct args as [ | arg [ | arg' args]]; reflexivity.
Qed.

Lemma load_known_named_equivariant (r : renaming) (known : known_blocks)
    (d : named) :
  load_known_named (rename_known_blocks r known) (rename_named r d)
  = rename_named r (load_known_named known d).
Proof.
  destruct d as [s | p args | | | | | ]; try reflexivity.
  cbn [rename_named load_known_named]. rewrite unary_applied_equivariant.
  destruct (unary_applied p args) as [[p' block] | ]; cbn [option_map fst snd];
    [ | reflexivity ].
  rewrite known_block_of_equivariant.
  destruct (known_block_of known block) as [made | ]; cbn [option_map];
    [ | reflexivity ].
  rewrite of_known_block_equivariant.
  destruct (of_known_block p' made); reflexivity.
Qed.

Fixpoint load_blocks_knowing_equivariant_aux (r : renaming) (e : expr) :
  ∀ known : known_blocks,
    load_blocks_knowing (rename_known_blocks r known) (rename_expr r e)
    = rename_expr r (load_blocks_knowing known e)
with load_blocks_in_handler_equivariant (r : renaming)
    (h : continuation_handler) :
  ∀ known : known_blocks,
    load_blocks_in_handler (rename_known_blocks r known) (rename_handler r h)
    = rename_handler r (load_blocks_in_handler known h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros known; try reflexivity;
      cbn [rename_expr load_blocks_knowing].
    + rewrite load_known_named_equivariant, known_under_let_equivariant,
        load_blocks_knowing_equivariant_aux.
      reflexivity.
    + rewrite known_under_statics_equivariant,
        load_blocks_knowing_equivariant_aux.
      reflexivity.
    + rewrite load_blocks_in_handler_equivariant,
        load_blocks_knowing_equivariant_aux.
      reflexivity.
    + rewrite load_blocks_knowing_equivariant_aux. reflexivity.
  - destruct h as [params metadata handler]. intros known.
    cbn [rename_handler load_blocks_in_handler].
    rewrite forget_vars_equivariant, load_blocks_knowing_equivariant_aux.
    reflexivity.
Qed.

Theorem load_blocks_knowing_equivariant :
  load_blocks_knowing_equivariant_statement.
Proof. intros r known e. apply load_blocks_knowing_equivariant_aux. Qed.

Theorem load_known_blocks_equivariant :
  load_known_blocks_equivariant_statement.
Proof.
  intros r e. exact (load_blocks_knowing_equivariant_aux r e no_blocks).
Qed.

(* ======================================================================== *)
(* FlambdaUnboxSpec.v                                                       *)
(* ======================================================================== *)

Lemma forget_wrapped_var_equivariant (r : renaming) (x : variable)
    (known : known_numbers) :
  forget_wrapped_var (rename_variable r x) (rename_known_numbers r known)
  = rename_known_numbers r (forget_wrapped_var x known).
Proof.
  unfold forget_wrapped_var, rename_known_numbers. simpl. f_equal.
  apply filter_map_with. intros entry. simpl.
  rewrite rename_variable_eqb, var_in_simple_equivariant. reflexivity.
Qed.

Lemma forget_wrapped_vars_equivariant (r : renaming) (xs : list variable) :
  ∀ known : known_numbers,
    forget_wrapped_vars (map (rename_variable r) xs)
      (rename_known_numbers r known)
    = rename_known_numbers r (forget_wrapped_vars xs known).
Proof.
  induction xs as [ | x xs IH]; intros known; simpl; [ reflexivity | ].
  rewrite forget_wrapped_var_equivariant. apply IH.
Qed.

Lemma number_wrapped_equivariant (r : renaming) (d : named) :
  number_wrapped (rename_named r d)
  = option_map (fun wrapped => (fst wrapped, rename_simple r (snd wrapped)))
      (number_wrapped d).
Proof.
  destruct d as [s | p args | | | | | ]; try reflexivity.
  cbn [rename_named number_wrapped]. rewrite unary_applied_equivariant.
  destruct (unary_applied p args) as [[p' contents] | ];
    cbn [option_map fst snd]; [ | reflexivity ].
  destruct p'; reflexivity.
Qed.

Lemma numbers_under_let_equivariant (r : renaming) (known : known_numbers)
    (x : variable) (d : named) :
  numbers_under_let (rename_known_numbers r known) (rename_variable r x)
    (rename_named r d)
  = rename_known_numbers r (numbers_under_let known x d).
Proof.
  unfold numbers_under_let.
  rewrite forget_wrapped_var_equivariant, number_wrapped_equivariant.
  destruct (number_wrapped d) as [[how contents] | ];
    cbn [option_map fst snd]; [ | reflexivity ].
  rewrite var_in_simple_equivariant.
  destruct (var_in_simple x contents); reflexivity.
Qed.

Lemma static_number_boxed_renamed (r : renaming) (binding : static_binding) :
  static_number_boxed (rename_static_binding r binding)
  = static_number_boxed binding.
Proof.
  destruct binding as [id c | id | sym const]; try reflexivity.
  destruct const as [ | | | [x | sym' | c] | ]; reflexivity.
Qed.

Lemma numbers_under_statics_equivariant (r : renaming)
    (known : known_numbers) (bindings : list static_binding) :
  numbers_under_statics (rename_known_numbers r known)
    (map (rename_static_binding r) bindings)
  = rename_known_numbers r (numbers_under_statics known bindings).
Proof.
  unfold numbers_under_statics, rename_known_numbers. simpl. do 2 f_equal.
  induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
  rewrite static_number_boxed_renamed, IH. reflexivity.
Qed.

Lemma unwrapped_equivariant (r : renaming) (known : known_numbers)
    (how : wrapping) (wrapped : simple) :
  unwrapped (rename_known_numbers r known) how (rename_simple r wrapped)
  = option_map (rename_simple r) (unwrapped known how wrapped).
Proof.
  destruct wrapped as [x | sym | c]; simpl; [ | | reflexivity ].
  - unfold rename_variable.
    rewrite
      (lookup_renamed_keys (variable_permutation r)
         (fun wrapped => (fst wrapped, rename_simple r (snd wrapped)))).
    destruct (lookup x (known_wrapped_vars known)) as [[how' contents] | ];
      cbn [option_map fst snd]; [ | reflexivity ].
    destruct (wrapping_eqb how how'); reflexivity.
  - destruct how as [kind | ]; [ | reflexivity ].
    destruct (lookup sym (known_boxed_symbols known)) as [c | ];
      [ | reflexivity ].
    destruct (is_number_of_kind kind c); reflexivity.
Qed.

Lemma unwrapping_of_known_equivariant (r : renaming) (known : known_numbers)
    (p : prim) (args : list simple) :
  unwrapping_of_known (rename_known_numbers r known) p
    (map (rename_simple r) args)
  = option_map (rename_simple r) (unwrapping_of_known known p args).
Proof.
  unfold unwrapping_of_known. rewrite unary_applied_equivariant.
  destruct (unary_applied p args) as [[p' wrapped] | ];
    cbn [option_map fst snd]; [ | reflexivity ].
  destruct p'; try reflexivity; apply unwrapped_equivariant.
Qed.

Lemma unbox_known_named_equivariant (r : renaming) (known : known_numbers)
    (d : named) :
  unbox_known_named (rename_known_numbers r known) (rename_named r d)
  = rename_named r (unbox_known_named known d).
Proof.
  destruct d as [s | p args | | | | | ]; try reflexivity.
  cbn [rename_named unbox_known_named].
  rewrite unwrapping_of_known_equivariant.
  destruct (unwrapping_of_known known p args); reflexivity.
Qed.

Fixpoint unbox_numbers_knowing_equivariant_aux (r : renaming) (e : expr) :
  ∀ known : known_numbers,
    unbox_numbers_knowing (rename_known_numbers r known) (rename_expr r e)
    = rename_expr r (unbox_numbers_knowing known e)
with unbox_numbers_in_handler_equivariant (r : renaming)
    (h : continuation_handler) :
  ∀ known : known_numbers,
    unbox_numbers_in_handler (rename_known_numbers r known)
      (rename_handler r h)
    = rename_handler r (unbox_numbers_in_handler known h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros known; try reflexivity;
      cbn [rename_expr unbox_numbers_knowing].
    + rewrite unbox_known_named_equivariant, numbers_under_let_equivariant,
        unbox_numbers_knowing_equivariant_aux.
      reflexivity.
    + rewrite numbers_under_statics_equivariant,
        unbox_numbers_knowing_equivariant_aux.
      reflexivity.
    + rewrite unbox_numbers_in_handler_equivariant,
        unbox_numbers_knowing_equivariant_aux.
      reflexivity.
    + rewrite unbox_numbers_knowing_equivariant_aux. reflexivity.
  - destruct h as [params metadata handler]. intros known.
    cbn [rename_handler unbox_numbers_in_handler].
    rewrite forget_wrapped_vars_equivariant,
      unbox_numbers_knowing_equivariant_aux.
    reflexivity.
Qed.

Theorem unbox_numbers_knowing_equivariant :
  unbox_numbers_knowing_equivariant_statement.
Proof. intros r known e. apply unbox_numbers_knowing_equivariant_aux. Qed.

Theorem unbox_known_numbers_equivariant :
  unbox_known_numbers_equivariant_statement.
Proof.
  intros r e. exact (unbox_numbers_knowing_equivariant_aux r e no_numbers).
Qed.

(* ======================================================================== *)
(* Following aliases                                                        *)
(* ======================================================================== *)

Lemma find_alias_equivariant (r : renaming) (tenv : typing_env)
    (x : variable) :
  find_alias (rename_naive_typing_env r tenv) (rename_variable r x)
  = option_map (rename_simple r) (find_alias tenv x).
Proof.
  unfold rename_naive_typing_env.
  induction tenv as [ | [y t] tenv IH]; simpl; [ reflexivity | ].
  destruct t as [ | | s | code slots]; simpl; try exact IH.
  rewrite rename_variable_eqb. destruct (Pos.eqb x y); [ reflexivity | ].
  exact IH.
Qed.

Lemma canonical_simple_equivariant (r : renaming) (tenv : typing_env)
    (s : simple) :
  canonical_simple (rename_naive_typing_env r tenv) (rename_simple r s)
  = rename_simple r (canonical_simple tenv s).
Proof.
  destruct s as [x | sym | c]; simpl; try reflexivity.
  rewrite find_alias_equivariant. destruct (find_alias tenv x); reflexivity.
Qed.

Lemma canonical_simples_equivariant (r : renaming) (tenv : typing_env)
    (args : list simple) :
  map (canonical_simple (rename_naive_typing_env r tenv))
    (map (rename_simple r) args)
  = map (rename_simple r) (map (canonical_simple tenv) args).
Proof.
  rewrite !map_map. apply map_ext. intros s.
  apply canonical_simple_equivariant.
Qed.

Lemma canonical_value_slots_equivariant (r : renaming) (tenv : typing_env)
    (slots : list (value_slot * simple)) :
  canonical_value_slots (rename_naive_typing_env r tenv)
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = map (fun slot => (fst slot, rename_simple r (snd slot)))
      (canonical_value_slots tenv slots).
Proof.
  unfold canonical_value_slots. rewrite !map_map. apply map_ext.
  intros slot. simpl. rewrite canonical_simple_equivariant. reflexivity.
Qed.

(* The action on the closure that a variable is known to be. *)
Definition rename_known_closure (r : renaming)
    (closure : code_id * list (value_slot * simple))
    : code_id * list (value_slot * simple) :=
  (fst closure,
   map (fun slot => (fst slot, rename_simple r (snd slot))) (snd closure)).

Lemma find_closure_equivariant (r : renaming) (tenv : typing_env)
    (x : variable) :
  find_closure (rename_naive_typing_env r tenv) (rename_variable r x)
  = option_map (rename_known_closure r) (find_closure tenv x).
Proof.
  unfold rename_naive_typing_env.
  induction tenv as [ | [y t] tenv IH]; simpl; [ reflexivity | ].
  destruct t as [ | | s | code slots]; simpl; try exact IH.
  rewrite rename_variable_eqb. destruct (Pos.eqb x y); [ reflexivity | ].
  exact IH.
Qed.

Lemma closure_of_simple_equivariant (r : renaming) (tenv : typing_env)
    (s : simple) :
  closure_of_simple (rename_naive_typing_env r tenv) (rename_simple r s)
  = option_map (rename_known_closure r) (closure_of_simple tenv s).
Proof.
  destruct s; simpl; [ apply find_closure_equivariant | | ]; reflexivity.
Qed.

Lemma canonical_project_equivariant (r : renaming) (tenv : typing_env)
    (slot : value_slot) (closure : simple) :
  canonical_project (rename_naive_typing_env r tenv) slot
    (rename_simple r closure)
  = rename_named r (canonical_project tenv slot closure).
Proof.
  unfold canonical_project. rewrite closure_of_simple_equivariant.
  destruct (closure_of_simple tenv closure) as [[code slots] | ];
    cbn [option_map rename_known_closure fst snd]; [ | reflexivity ].
  rewrite lookup_value_slots_renamed. destruct (lookup slot slots); reflexivity.
Qed.

Lemma canonical_named_equivariant (r : renaming) (tenv : typing_env)
    (d : named) :
  canonical_named (rename_naive_typing_env r tenv) (rename_named r d)
  = rename_named r (canonical_named tenv d).
Proof.
  destruct d; cbn [rename_named canonical_named];
    rewrite ?canonical_simple_equivariant, ?canonical_simples_equivariant,
      ?canonical_value_slots_equivariant;
    try reflexivity.
  apply canonical_project_equivariant.
Qed.

Lemma canonical_static_binding_equivariant (r : renaming)
    (tenv : typing_env) (binding : static_binding) :
  canonical_static_binding (rename_naive_typing_env r tenv)
    (rename_static_binding r binding)
  = rename_static_binding r (canonical_static_binding tenv binding).
Proof.
  destruct binding as [id c | id | sym const]; try reflexivity.
  destruct const;
    cbn [rename_static_binding rename_static_const canonical_static_binding
         canonical_static_const];
    rewrite ?canonical_simple_equivariant, ?canonical_simples_equivariant,
      ?canonical_value_slots_equivariant;
    reflexivity.
Qed.

Lemma canonical_apply_cont_equivariant (r : renaming) (tenv : typing_env)
    (ac : apply_cont) :
  canonical_apply_cont (rename_naive_typing_env r tenv)
    (rename_apply_cont r ac)
  = rename_apply_cont r (canonical_apply_cont tenv ac).
Proof.
  unfold canonical_apply_cont, rename_apply_cont.
  cbn [ac_continuation ac_args]. rewrite canonical_simples_equivariant.
  reflexivity.
Qed.

Lemma canonical_call_kind_equivariant (r : renaming) (tenv : typing_env)
    (callee : simple) (kind : call_kind) :
  canonical_call_kind (rename_naive_typing_env r tenv)
    (rename_simple r callee) kind
  = canonical_call_kind tenv callee kind.
Proof.
  unfold canonical_call_kind. rewrite closure_of_simple_equivariant.
  destruct kind as [called | ],
    (closure_of_simple tenv callee) as [[code slots] | ];
    reflexivity.
Qed.

Lemma canonical_exn_extra_args_equivariant (r : renaming) (tenv : typing_env)
    (extra : list (simple * flambda_kind)) :
  map
    (fun arg =>
       (canonical_simple (rename_naive_typing_env r tenv) (fst arg), snd arg))
    (map (fun arg => (rename_simple r (fst arg), snd arg)) extra)
  = map (fun arg => (rename_simple r (fst arg), snd arg))
      (map (fun arg => (canonical_simple tenv (fst arg), snd arg)) extra).
Proof.
  rewrite !map_map. apply map_ext. intros [s kind]. cbn [fst snd].
  rewrite canonical_simple_equivariant. reflexivity.
Qed.

Lemma canonical_apply_equivariant (r : renaming) (tenv : typing_env)
    (ap : apply_expr) :
  canonical_apply (rename_naive_typing_env r tenv) (rename_apply r ap)
  = rename_apply r (canonical_apply tenv ap).
Proof.
  unfold canonical_apply, rename_apply.
  cbn [ap_callee ap_call_kind ap_args ap_continuation ap_exn_continuation
       ap_exn_extra_args ap_args_arity ap_return_arity].
  rewrite canonical_simple_equivariant, canonical_call_kind_equivariant,
    canonical_simples_equivariant, canonical_exn_extra_args_equivariant.
  reflexivity.
Qed.

Lemma var_in_type_equivariant (r : renaming) (x : variable)
    (t : flambda_type) :
  var_in_type (rename_variable r x) (rename_naive_type r t) = var_in_type x t.
Proof.
  destruct t; simpl;
    [ reflexivity | reflexivity | apply var_in_simple_equivariant
    | apply var_in_value_slots_equivariant ].
Qed.

Lemma drop_var_equivariant (r : renaming) (x : variable) (tenv : typing_env) :
  drop_var (rename_variable r x) (rename_naive_typing_env r tenv)
  = rename_naive_typing_env r (drop_var x tenv).
Proof.
  unfold drop_var, rename_naive_typing_env. apply filter_map_with.
  intros [y t]. simpl.
  rewrite rename_variable_eqb, var_in_type_equivariant. reflexivity.
Qed.

Lemma drop_vars_equivariant (r : renaming) (xs : list variable)
    (tenv : typing_env) :
  drop_vars (map (rename_variable r) xs) (rename_naive_typing_env r tenv)
  = rename_naive_typing_env r (drop_vars xs tenv).
Proof.
  unfold drop_vars. induction xs as [ | x xs IH]; simpl; [ reflexivity | ].
  rewrite IH. apply drop_var_equivariant.
Qed.

Lemma typing_env_under_let_equivariant (r : renaming) (tenv : typing_env)
    (x : variable) (d : named) :
  typing_env_under_let (rename_naive_typing_env r tenv) (rename_variable r x)
    (rename_named r d)
  = rename_naive_typing_env r (typing_env_under_let tenv x d).
Proof.
  destruct d as [s | p args | code slots | | | | ];
    cbn [rename_named typing_env_under_let];
    try apply drop_var_equivariant.
  - rewrite var_in_simple_equivariant, drop_var_equivariant.
    destruct (var_in_simple x s); reflexivity.
  - rewrite var_in_value_slots_equivariant, drop_var_equivariant.
    destruct (var_in_value_slots x slots); reflexivity.
Qed.

Fixpoint follow_aliases_equivariant_aux (r : renaming) (e : expr) :
  ∀ tenv : typing_env,
    follow_aliases (rename_naive_typing_env r tenv) (rename_expr r e)
    = rename_expr r (follow_aliases tenv e)
with follow_aliases_in_handler_equivariant (r : renaming)
    (h : continuation_handler) :
  ∀ tenv : typing_env,
    follow_aliases_in_handler (rename_naive_typing_env r tenv)
      (rename_handler r h)
    = rename_handler r (follow_aliases_in_handler tenv h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros tenv; cbn [rename_expr follow_aliases].
    + rewrite canonical_named_equivariant, typing_env_under_let_equivariant,
        follow_aliases_equivariant_aux.
      reflexivity.
    + rewrite follow_aliases_equivariant_aux, !map_map. f_equal.
      apply map_ext. intros binding.
      apply canonical_static_binding_equivariant.
    + rewrite follow_aliases_in_handler_equivariant,
        follow_aliases_equivariant_aux.
      reflexivity.
    + rewrite follow_aliases_equivariant_aux. reflexivity.
    + rewrite canonical_apply_equivariant. reflexivity.
    + rewrite canonical_apply_cont_equivariant. reflexivity.
    + rewrite canonical_simple_equivariant, !map_map. f_equal.
      apply map_ext. intros arm. cbn [fst snd].
      rewrite canonical_apply_cont_equivariant. reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler]. intros tenv.
    cbn [rename_handler follow_aliases_in_handler].
    rewrite drop_vars_equivariant, follow_aliases_equivariant_aux.
    reflexivity.
Qed.

Theorem follow_aliases_equivariant : follow_aliases_equivariant_statement.
Proof. intros r tenv e. apply follow_aliases_equivariant_aux. Qed.

Theorem follow_aliases_unknowing_equivariant :
  follow_aliases_unknowing_equivariant_statement.
Proof. intros r e. exact (follow_aliases_equivariant_aux r e []). Qed.

(* ======================================================================== *)
(* The checks of FlambdaWellFormedSpec.v                                    *)
(* ======================================================================== *)

Lemma forallb_same {A : Type} (f g : A -> bool) (l : list A) :
  (∀ a : A, f a = g a) -> forallb f l = forallb g l.
Proof.
  intros Hfg. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hfg, IH. reflexivity.
Qed.

Lemma existsb_same {A : Type} (f g : A -> bool) (l : list A) :
  (∀ a : A, f a = g a) -> existsb f l = existsb g l.
Proof.
  intros Hfg. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hfg, IH. reflexivity.
Qed.

Fixpoint well_formed_free_continuations_renamed (r : renaming) (e : expr) :
  free_continuations (rename_expr r e)
  = map (rename_continuation r) (free_continuations e)
with handler_free_continuations_renamed (r : renaming)
    (h : continuation_handler) :
  handler_free_continuations (rename_handler r h)
  = map (rename_continuation r) (handler_free_continuations h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr free_continuations].
    + apply well_formed_free_continuations_renamed.
    + apply well_formed_free_continuations_renamed.
    + rewrite map_app, handler_free_continuations_renamed,
        well_formed_free_continuations_renamed.
      rewrite <- (without_map_injective (rename_continuation r)
                    (rename_continuation_eqb r) [k]).
      reflexivity.
    + fold (rename_handlers r handlers).
      rewrite map_fst_rename_handlers.
      rewrite <- (without_map_injective (rename_continuation r)
                    (rename_continuation_eqb r)).
      rewrite map_app, well_formed_free_continuations_renamed.
      do 2 f_equal. unfold rename_handlers.
      induction handlers as [ | [k h] handlers IH]; [ reflexivity | ].
      cbn [map flat_map].
      rewrite map_app, (handler_free_continuations_renamed r h), IH.
      reflexivity.
    + reflexivity.
    + apply apply_cont_continuations_renamed.
    + induction arms as [ | [i ac] arms IH]; [ reflexivity | ].
      cbn [map flat_map fst snd].
      rewrite map_app, apply_cont_continuations_renamed, IH. reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_free_continuations].
    apply well_formed_free_continuations_renamed.
Qed.

Theorem well_formed_free_continuations_equivariant :
  well_formed_free_continuations_equivariant_statement.
Proof. exact well_formed_free_continuations_renamed. Qed.

Lemma traps_renamed (r : renaming) (k : continuation) (ac : apply_cont) :
  traps (rename_continuation r k) (rename_apply_cont r ac) = traps k ac.
Proof.
  unfold traps. simpl.
  destruct (ac_trap_action ac) as [[k' | k' kind] | ]; simpl;
    [ apply rename_continuation_eqb | apply rename_continuation_eqb
    | reflexivity ].
Qed.

Fixpoint raises_to_equivariant_aux (r : renaming) (k : continuation)
    (e : expr) :
  raises_to (rename_continuation r k) (rename_expr r e) = raises_to k e
with handler_raises_to_equivariant (r : renaming) (k : continuation)
    (h : continuation_handler) :
  handler_raises_to (rename_continuation r k) (rename_handler r h)
  = handler_raises_to k h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k' h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + apply raises_to_equivariant_aux.
    + apply raises_to_equivariant_aux.
    + rewrite handler_raises_to_equivariant, raises_to_equivariant_aux.
      reflexivity.
    + rewrite raises_to_equivariant_aux. f_equal.
      induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (handler_raises_to_equivariant r k h), IH. reflexivity.
    + apply rename_continuation_eqb.
    + exact (traps_renamed r k ac).
    + apply existsb_map_with. intros arm.
      exact (traps_renamed r k (snd arm)).
  - destruct h as [params metadata handler]. simpl.
    apply raises_to_equivariant_aux.
Qed.

Theorem raises_to_equivariant : raises_to_equivariant_statement.
Proof. exact raises_to_equivariant_aux. Qed.

Lemma handler_is_exn_handler_renamed (r : renaming)
    (h : continuation_handler) :
  handler_is_exn_handler (rename_handler r h) = handler_is_exn_handler h.
Proof. destruct h; reflexivity. Qed.

Theorem handler_at_toplevel_equivariant :
  handler_at_toplevel_equivariant_statement.
Proof.
  intros r unit_exn k h body. unfold handler_at_toplevel.
  rewrite handler_is_exn_handler_renamed,
    well_formed_free_continuations_renamed.
  f_equal.
  exact
    (all_among_map_injective (rename_continuation r)
       (rename_continuation_eqb r) (free_continuations body) [k; unit_exn]).
Qed.

Fixpoint statics_at_toplevel_equivariant_aux (r : renaming)
    (unit_exn : continuation) (e : expr) :
  ∀ toplevel : bool,
    statics_at_toplevel (rename_continuation r unit_exn) toplevel
      (rename_expr r e)
    = statics_at_toplevel unit_exn toplevel e
with handler_statics_at_toplevel_equivariant (r : renaming)
    (unit_exn : continuation) (h : continuation_handler) :
  ∀ toplevel : bool,
    handler_statics_at_toplevel (rename_continuation r unit_exn) toplevel
      (rename_handler r h)
    = handler_statics_at_toplevel unit_exn toplevel h
with binding_statics_at_toplevel_equivariant (r : renaming)
    (unit_exn : continuation) (binding : static_binding) :
  binding_statics_at_toplevel (rename_continuation r unit_exn)
    (rename_static_binding r binding)
  = binding_statics_at_toplevel unit_exn binding
with code_statics_at_toplevel_equivariant (r : renaming)
    (unit_exn : continuation) (c : code) :
  code_statics_at_toplevel (rename_continuation r unit_exn) (rename_code r c)
  = code_statics_at_toplevel unit_exn c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros toplevel; cbn [rename_expr statics_at_toplevel];
      try reflexivity.
    + apply statics_at_toplevel_equivariant_aux.
    + rewrite statics_at_toplevel_equivariant_aux. do 2 f_equal.
      induction bindings as [ | binding bindings IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (binding_statics_at_toplevel_equivariant r unit_exn binding),
        IH.
      reflexivity.
    + rewrite handler_at_toplevel_equivariant,
        handler_statics_at_toplevel_equivariant,
        statics_at_toplevel_equivariant_aux.
      reflexivity.
    + rewrite statics_at_toplevel_equivariant_aux. f_equal.
      induction handlers as [ | [k h] handlers IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (handler_statics_at_toplevel_equivariant r unit_exn h), IH.
      reflexivity.
  - destruct h as [params metadata handler]. intros toplevel.
    cbn [rename_handler handler_statics_at_toplevel].
    apply statics_at_toplevel_equivariant_aux.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding binding_statics_at_toplevel];
      try reflexivity.
    apply code_statics_at_toplevel_equivariant.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code code_statics_at_toplevel].
    apply statics_at_toplevel_equivariant_aux.
Qed.

Theorem statics_at_toplevel_equivariant :
  statics_at_toplevel_equivariant_statement.
Proof.
  intros r unit_exn toplevel e. apply statics_at_toplevel_equivariant_aux.
Qed.

Section Static_names.

Variable r : renaming.
Variable names_of : static_binding -> list positive.
Hypothesis names_of_renamed :
  ∀ binding : static_binding,
    names_of (rename_static_binding r binding) = names_of binding.

Lemma flat_map_names_renamed (bindings : list static_binding) :
  flat_map names_of (map (rename_static_binding r) bindings)
  = flat_map names_of bindings.
Proof.
  induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
  rewrite names_of_renamed, IH. reflexivity.
Qed.

Fixpoint static_names_renamed (e : expr) :
  static_names names_of (rename_expr r e) = static_names names_of e
with handler_static_names_renamed (h : continuation_handler) :
  handler_static_names names_of (rename_handler r h)
  = handler_static_names names_of h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + apply static_names_renamed.
    + rewrite static_names_renamed, flat_map_names_renamed. reflexivity.
    + rewrite handler_static_names_renamed, static_names_renamed.
      reflexivity.
    + rewrite static_names_renamed. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (handler_static_names_renamed h), IH. reflexivity.
  - destruct h as [params metadata handler]. simpl. apply static_names_renamed.
Qed.

(* A group binds a name twice, or one that is bound, as the renamed
   group does. *)
Lemma rebinds_renamed (is_bound is_bound' : positive -> bool)
    (bindings : list static_binding) :
  (∀ name : positive, is_bound' name = is_bound name) ->
  rebinds names_of is_bound' (map (rename_static_binding r) bindings)
  = rebinds names_of is_bound bindings.
Proof.
  intros Hbound. unfold rebinds. rewrite flat_map_names_renamed.
  f_equal. apply existsb_same, Hbound.
Qed.

End Static_names.

Lemma code_ids_of_binding_renamed (r : renaming) (binding : static_binding) :
  code_ids_of_binding (rename_static_binding r binding)
  = code_ids_of_binding binding.
Proof. destruct binding; reflexivity. Qed.

Lemma symbols_of_binding_renamed (r : renaming) (binding : static_binding) :
  symbols_of_binding (rename_static_binding r binding)
  = symbols_of_binding binding.
Proof. destruct binding; reflexivity. Qed.

Theorem static_names_equivariant : static_names_equivariant_statement.
Proof. intros r names_of e Hnames. apply static_names_renamed, Hnames. Qed.

Theorem bound_static_names_equivariant :
  bound_static_names_equivariant_statement.
Proof.
  intros r e. split; apply static_names_renamed;
    [ apply code_ids_of_binding_renamed | apply symbols_of_binding_renamed ].
Qed.

(* Sets of closures. A static set is bound whole when the group has, for
   each symbol of the set, a binding of that symbol to the very set: the
   test of equality of static constants answers the same on renamed
   ones. *)
Lemma rename_value_slots_injective (r : renaming)
    (slots slots' : list (value_slot * simple)) :
  map (fun slot => (fst slot, rename_simple r (snd slot))) slots
  = map (fun slot => (fst slot, rename_simple r (snd slot))) slots' ->
  slots = slots'.
Proof.
  revert slots'.
  induction slots as [ | [slot s] slots IH]; intros [ | [slot' s'] slots'];
    simpl; intros Heq; try discriminate; [ reflexivity | ].
  injection Heq as Hslot Hs Hslots.
  apply rename_simple_injective in Hs. apply IH in Hslots. congruence.
Qed.

Lemma rename_static_const_injective (r : renaming)
    (const const' : static_const) :
  rename_static_const r const = rename_static_const r const' ->
  const = const'.
Proof.
  destruct const, const'; simpl; intros Heq; try discriminate;
    injection Heq; intros; subst; try reflexivity; f_equal;
    eauto using rename_value_slots_injective, rename_simples_injective,
      rename_simple_injective.
Qed.

Lemma named_sets_well_formed_renamed (r : renaming) (d : named) :
  named_sets_well_formed (rename_named r d) = named_sets_well_formed d.
Proof. destruct d; reflexivity. Qed.

Lemma binds_symbol_to_renamed (r : renaming) (s : symbol)
    (const : static_const) (binding : static_binding) :
  binds_symbol_to s (rename_static_const r const)
    (rename_static_binding r binding)
  = binds_symbol_to s const binding.
Proof.
  destruct binding as [id c | id | s' const']; try reflexivity.
  cbn [rename_static_binding binds_symbol_to]. f_equal.
  apply (dec_injective static_const_eq_dec (rename_static_const r)).
  apply rename_static_const_injective.
Qed.

Lemma static_set_whole_renamed (r : renaming)
    (bindings : list static_binding) (binding : static_binding) :
  static_set_whole (map (rename_static_binding r) bindings)
    (rename_static_binding r binding)
  = static_set_whole bindings binding.
Proof.
  destruct binding as [id c | id | s const]; try reflexivity.
  destruct const as [ | slot closure_symbols function_decls value_slots | | | ];
    try reflexivity.
  cbn [rename_static_binding rename_static_const static_set_whole]. f_equal.
  apply forallb_same. intros [slot' s'].
  apply existsb_map_with. intros binding'.
  exact
    (binds_symbol_to_renamed r s'
       (Static_const_closure_of_set slot' closure_symbols function_decls
          value_slots)
       binding').
Qed.

Lemma static_set_code_ids_renamed (r : renaming) (binding : static_binding) :
  static_set_code_ids (rename_static_binding r binding)
  = static_set_code_ids binding.
Proof.
  destruct binding as [id c | id | s const]; try reflexivity.
  destruct const; reflexivity.
Qed.

Lemma binds_symbol_of_set_renamed (r : renaming)
    (binding binding' : static_binding) :
  binds_symbol_of_set (rename_static_binding r binding)
    (rename_static_binding r binding')
  = binds_symbol_of_set binding binding'.
Proof.
  destruct binding as [id c | id | s const], binding' as [id' c' | id' | s' c'];
    try reflexivity;
    destruct const; reflexivity.
Qed.

Lemma static_sets_code_disjoint_renamed (r : renaming)
    (bindings : list static_binding) :
  static_sets_code_disjoint (map (rename_static_binding r) bindings)
  = static_sets_code_disjoint bindings.
Proof.
  induction bindings as [ | binding bindings IH];
    cbn [map static_sets_code_disjoint]; [ reflexivity | ].
  rewrite IH. f_equal. apply forallb_map_with. intros binding'.
  rewrite binds_symbol_of_set_renamed, !static_set_code_ids_renamed.
  reflexivity.
Qed.

Fixpoint sets_well_formed_renamed (r : renaming) (e : expr) :
  sets_well_formed (rename_expr r e) = sets_well_formed e
with handler_sets_well_formed_renamed (r : renaming)
    (h : continuation_handler) :
  handler_sets_well_formed (rename_handler r h) = handler_sets_well_formed h
with binding_sets_well_formed_renamed (r : renaming)
    (binding : static_binding) :
  binding_sets_well_formed (rename_static_binding r binding)
  = binding_sets_well_formed binding
with code_sets_well_formed_renamed (r : renaming) (c : code) :
  code_sets_well_formed (rename_code r c) = code_sets_well_formed c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr sets_well_formed]; try reflexivity.
    + rewrite named_sets_well_formed_renamed, sets_well_formed_renamed.
      reflexivity.
    + rewrite static_sets_code_disjoint_renamed, sets_well_formed_renamed.
      rewrite (forallb_map_with _ _ (static_set_whole bindings))
        by apply static_set_whole_renamed.
      do 2 f_equal.
      induction bindings as [ | binding bindings IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (binding_sets_well_formed_renamed r binding), IH. reflexivity.
    + rewrite handler_sets_well_formed_renamed, sets_well_formed_renamed.
      reflexivity.
    + rewrite sets_well_formed_renamed. f_equal.
      induction handlers as [ | [k h] handlers IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (handler_sets_well_formed_renamed r h), IH. reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_sets_well_formed].
    apply sets_well_formed_renamed.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding binding_sets_well_formed]; try reflexivity.
    apply code_sets_well_formed_renamed.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code code_sets_well_formed]. apply sets_well_formed_renamed.
Qed.

Theorem sets_well_formed_equivariant : sets_well_formed_equivariant_statement.
Proof. exact sets_well_formed_renamed. Qed.

(* Numbers: a renaming changes no constant, no tag and no discriminant. *)
Lemma simple_in_range_renamed (r : renaming) (s : simple) :
  simple_in_range (rename_simple r s) = simple_in_range s.
Proof. destruct s; reflexivity. Qed.

Lemma simples_in_range_renamed (r : renaming) (args : list simple) :
  forallb simple_in_range (map (rename_simple r) args)
  = forallb simple_in_range args.
Proof. apply forallb_map_with, simple_in_range_renamed. Qed.

Lemma value_slots_in_range_renamed (r : renaming)
    (slots : list (value_slot * simple)) :
  value_slots_in_range
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = value_slots_in_range slots.
Proof.
  unfold value_slots_in_range. apply forallb_map_with. intros slot.
  apply simple_in_range_renamed.
Qed.

Lemma named_in_range_renamed (r : renaming) (d : named) :
  named_in_range (rename_named r d) = named_in_range d.
Proof.
  destruct d; cbn [rename_named named_in_range];
    rewrite ?simples_in_range_renamed, ?value_slots_in_range_renamed,
      ?simple_in_range_renamed;
    reflexivity.
Qed.

Lemma static_const_in_range_renamed (r : renaming) (const : static_const) :
  static_const_in_range (rename_static_const r const)
  = static_const_in_range const.
Proof.
  destruct const; cbn [rename_static_const static_const_in_range];
    rewrite ?simples_in_range_renamed, ?value_slots_in_range_renamed,
      ?simple_in_range_renamed;
    reflexivity.
Qed.

Lemma apply_cont_in_range_renamed (r : renaming) (ac : apply_cont) :
  apply_cont_in_range (rename_apply_cont r ac) = apply_cont_in_range ac.
Proof. apply simples_in_range_renamed. Qed.

Lemma apply_in_range_renamed (r : renaming) (ap : apply_expr) :
  apply_in_range (rename_apply r ap) = apply_in_range ap.
Proof.
  unfold apply_in_range.
  rewrite exn_extra_simples_rename. unfold rename_apply.
  cbn [ap_callee ap_args].
  rewrite simple_in_range_renamed, !simples_in_range_renamed. reflexivity.
Qed.

Fixpoint numbers_in_range_renamed (r : renaming) (e : expr) :
  numbers_in_range (rename_expr r e) = numbers_in_range e
with handler_numbers_in_range_renamed (r : renaming)
    (h : continuation_handler) :
  handler_numbers_in_range (rename_handler r h) = handler_numbers_in_range h
with binding_numbers_in_range_renamed (r : renaming)
    (binding : static_binding) :
  binding_numbers_in_range (rename_static_binding r binding)
  = binding_numbers_in_range binding
with code_numbers_in_range_renamed (r : renaming) (c : code) :
  code_numbers_in_range (rename_code r c) = code_numbers_in_range c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr numbers_in_range].
    + rewrite named_in_range_renamed, numbers_in_range_renamed. reflexivity.
    + rewrite numbers_in_range_renamed. f_equal.
      induction bindings as [ | binding bindings IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (binding_numbers_in_range_renamed r binding), IH. reflexivity.
    + rewrite handler_numbers_in_range_renamed, numbers_in_range_renamed.
      reflexivity.
    + rewrite numbers_in_range_renamed. f_equal.
      induction handlers as [ | [k h] handlers IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (handler_numbers_in_range_renamed r h), IH. reflexivity.
    + apply apply_in_range_renamed.
    + apply apply_cont_in_range_renamed.
    + rewrite simple_in_range_renamed. f_equal.
      apply forallb_map_with. intros arm. unfold arm_in_range. cbn [fst snd].
      rewrite apply_cont_in_range_renamed. reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_numbers_in_range].
    apply numbers_in_range_renamed.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding binding_numbers_in_range]; try reflexivity.
    + apply code_numbers_in_range_renamed.
    + apply static_const_in_range_renamed.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code code_numbers_in_range]. apply numbers_in_range_renamed.
Qed.

Theorem numbers_in_range_equivariant : numbers_in_range_equivariant_statement.
Proof. exact numbers_in_range_renamed. Qed.

(* Exception handlers. *)

Lemma is_raise_renamed (r : renaming) (ac : apply_cont) :
  is_raise (rename_apply_cont r ac) = is_raise ac.
Proof.
  unfold is_raise. simpl.
  destruct (ac_trap_action ac) as [[k | k kind] | ]; simpl; try reflexivity.
  apply rename_continuation_eqb.
Qed.

Lemma applies_renamed (r : renaming) (k : continuation) (ac : apply_cont) :
  applies (rename_continuation r k) (rename_apply_cont r ac) = applies k ac.
Proof.
  unfold applies. rewrite is_raise_renamed. simpl.
  rewrite rename_continuation_eqb. reflexivity.
Qed.

Lemma traps_apart_renamed (r : renaming) (k : continuation)
    (ac : apply_cont) :
  traps_apart (rename_continuation r k) (rename_apply_cont r ac)
  = traps_apart k ac.
Proof.
  unfold traps_apart. rewrite traps_renamed, is_raise_renamed. reflexivity.
Qed.

Lemma gives_extra_args_apply_renamed (r : renaming) (k : continuation)
    (ap : apply_expr) :
  Pos.eqb (rename_continuation r k) (ap_exn_continuation (rename_apply r ap))
  && negb (no_exn_extra_args (rename_apply r ap))
  = Pos.eqb k (ap_exn_continuation ap) && negb (no_exn_extra_args ap).
Proof.
  rewrite no_exn_extra_args_renamed. simpl.
  rewrite rename_continuation_eqb. reflexivity.
Qed.

Fixpoint applies_cont_renamed (r : renaming) (k : continuation) (e : expr) :
  applies_cont (rename_continuation r k) (rename_expr r e) = applies_cont k e
with handler_applies_cont_renamed (r : renaming) (k : continuation)
    (h : continuation_handler) :
  handler_applies_cont (rename_continuation r k) (rename_handler r h)
  = handler_applies_cont k h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k' h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + apply applies_cont_renamed.
    + apply applies_cont_renamed.
    + rewrite handler_applies_cont_renamed, applies_cont_renamed.
      reflexivity.
    + rewrite applies_cont_renamed. f_equal.
      induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (handler_applies_cont_renamed r k h), IH. reflexivity.
    + apply rename_continuation_eqb.
    + exact (applies_renamed r k ac).
    + apply existsb_map_with. intros arm.
      exact (applies_renamed r k (snd arm)).
  - destruct h as [params metadata handler]. simpl.
    apply applies_cont_renamed.
Qed.

Fixpoint gives_extra_args_renamed (r : renaming) (k : continuation)
    (e : expr) :
  gives_extra_args (rename_continuation r k) (rename_expr r e)
  = gives_extra_args k e
with handler_gives_extra_args_renamed (r : renaming) (k : continuation)
    (h : continuation_handler) :
  handler_gives_extra_args (rename_continuation r k) (rename_handler r h)
  = handler_gives_extra_args k h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k' h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr gives_extra_args]; try reflexivity.
    + apply gives_extra_args_renamed.
    + apply gives_extra_args_renamed.
    + rewrite handler_gives_extra_args_renamed, gives_extra_args_renamed.
      reflexivity.
    + rewrite gives_extra_args_renamed. f_equal.
      induction handlers as [ | [k' h] handlers IH]; cbn [map existsb];
        [ reflexivity | ].
      rewrite (handler_gives_extra_args_renamed r k h), IH. reflexivity.
    + apply gives_extra_args_apply_renamed.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_gives_extra_args].
    apply gives_extra_args_renamed.
Qed.

Fixpoint installs_or_removes_renamed (r : renaming) (k : continuation)
    (e : expr) :
  installs_or_removes (rename_continuation r k) (rename_expr r e)
  = installs_or_removes k e
with handler_installs_or_removes_renamed (r : renaming) (k : continuation)
    (h : continuation_handler) :
  handler_installs_or_removes (rename_continuation r k) (rename_handler r h)
  = handler_installs_or_removes k h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k' h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr installs_or_removes]; try reflexivity.
    + apply installs_or_removes_renamed.
    + apply installs_or_removes_renamed.
    + rewrite handler_installs_or_removes_renamed,
        installs_or_removes_renamed.
      reflexivity.
    + rewrite installs_or_removes_renamed. f_equal.
      induction handlers as [ | [k' h] handlers IH]; cbn [map existsb];
        [ reflexivity | ].
      rewrite (handler_installs_or_removes_renamed r k h), IH. reflexivity.
    + apply traps_apart_renamed.
    + apply existsb_map_with. intros arm. cbn [snd].
      apply traps_apart_renamed.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_installs_or_removes].
    apply installs_or_removes_renamed.
Qed.

Lemma ways_out_well_formed_renamed (r : renaming) (exn : continuation)
    (e : expr) :
  ways_out_well_formed (rename_continuation r exn) (rename_expr r e)
  = ways_out_well_formed exn e.
Proof.
  unfold ways_out_well_formed. rewrite well_formed_free_continuations_renamed.
  apply forallb_map_with. intros k.
  rewrite rename_continuation_eqb, installs_or_removes_renamed,
    raises_to_equivariant_aux, gives_extra_args_renamed.
  reflexivity.
Qed.

Lemma takes_exception_renamed (r : renaming) (h : continuation_handler) :
  takes_exception (rename_handler r h) = takes_exception h.
Proof. destruct h as [[ | param params] metadata handler]; reflexivity. Qed.

Lemma handlers_raise_to_renamed (r : renaming) (k : continuation)
    (handlers : list (continuation * continuation_handler)) :
  existsb (fun '(_, h) => handler_raises_to (rename_continuation r k) h)
    (rename_handlers r handlers)
  = existsb (fun '(_, h) => handler_raises_to k h) handlers.
Proof.
  unfold rename_handlers. apply existsb_map_with. intros [k' h].
  apply handler_raises_to_equivariant.
Qed.

Fixpoint exn_handlers_well_formed_renamed (r : renaming) (e : expr)
    {struct e} :
  exn_handlers_well_formed (rename_expr r e) = exn_handlers_well_formed e
with handler_exn_handlers_well_formed_renamed (r : renaming)
    (h : continuation_handler) {struct h} :
  handler_exn_handlers_well_formed (rename_handler r h)
  = handler_exn_handlers_well_formed h
with binding_exn_handlers_well_formed_renamed (r : renaming)
    (binding : static_binding) {struct binding} :
  binding_exn_handlers_well_formed (rename_static_binding r binding)
  = binding_exn_handlers_well_formed binding
with code_exn_handlers_well_formed_renamed (r : renaming) (c : code)
    {struct c} :
  code_exn_handlers_well_formed (rename_code r c)
  = code_exn_handlers_well_formed c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rename_expr exn_handlers_well_formed]; try reflexivity.
    + apply exn_handlers_well_formed_renamed.
    + rewrite exn_handlers_well_formed_renamed. f_equal.
      induction bindings as [ | binding bindings IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (binding_exn_handlers_well_formed_renamed r binding), IH.
      reflexivity.
    + rewrite handler_is_exn_handler_renamed, applies_cont_renamed,
        takes_exception_renamed, raises_to_equivariant_aux,
        handler_exn_handlers_well_formed_renamed,
        exn_handlers_well_formed_renamed.
      reflexivity.
    + rewrite exn_handlers_well_formed_renamed. f_equal.
      assert
        (Hgroup :
          ∀ group : list (continuation * continuation_handler),
            forallb
              (fun '(k, h) =>
                 (negb (handler_is_exn_handler h)
                  && negb (raises_to k (rename_expr r body))
                  && negb
                       (existsb (fun '(_, h') => handler_raises_to k h')
                          (rename_handlers r group))
                  && handler_exn_handlers_well_formed h)%bool)
              (map
                 (fun '(k, h) =>
                    (rename_continuation r k, rename_handler r h))
                 handlers)
            = forallb
                (fun '(k, h) =>
                   (negb (handler_is_exn_handler h)
                    && negb (raises_to k body)
                    && negb
                         (existsb (fun '(_, h') => handler_raises_to k h')
                            group)
                    && handler_exn_handlers_well_formed h)%bool)
                handlers).
      { intros group.
        induction handlers as [ | [k h] handlers IH]; cbn [map forallb];
          [ reflexivity | ].
        rewrite IH, handler_is_exn_handler_renamed, raises_to_equivariant_aux,
          handlers_raise_to_renamed,
          (handler_exn_handlers_well_formed_renamed r h).
        reflexivity. }
      exact (Hgroup handlers).
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_exn_handlers_well_formed].
    apply exn_handlers_well_formed_renamed.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding binding_exn_handlers_well_formed];
      try reflexivity.
    apply code_exn_handlers_well_formed_renamed.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code code_exn_handlers_well_formed].
    rewrite ways_out_well_formed_renamed, applies_cont_renamed,
      exn_handlers_well_formed_renamed.
    reflexivity.
Qed.

Lemma unit_exn_handlers_well_formed_renamed (r : renaming)
    (unit_exn : continuation) (e : expr) :
  unit_exn_handlers_well_formed (rename_continuation r unit_exn)
    (rename_expr r e)
  = unit_exn_handlers_well_formed unit_exn e.
Proof.
  unfold unit_exn_handlers_well_formed.
  rewrite ways_out_well_formed_renamed, applies_cont_renamed,
    exn_handlers_well_formed_renamed.
  reflexivity.
Qed.

Theorem applies_cont_equivariant : applies_cont_equivariant_statement.
Proof. exact applies_cont_renamed. Qed.

Theorem gives_extra_args_equivariant :
  gives_extra_args_equivariant_statement.
Proof. exact gives_extra_args_renamed. Qed.

Theorem installs_or_removes_equivariant :
  installs_or_removes_equivariant_statement.
Proof. exact installs_or_removes_renamed. Qed.

Theorem ways_out_well_formed_equivariant :
  ways_out_well_formed_equivariant_statement.
Proof. exact ways_out_well_formed_renamed. Qed.

Theorem exn_handlers_well_formed_equivariant :
  exn_handlers_well_formed_equivariant_statement.
Proof. exact exn_handlers_well_formed_renamed. Qed.

Theorem unit_exn_handlers_well_formed_equivariant :
  unit_exn_handlers_well_formed_equivariant_statement.
Proof. exact unit_exn_handlers_well_formed_renamed. Qed.

(* Trap actions. *)

Lemma among_trap_stack_renamed (r : renaming) (k : continuation)
    (ts : trap_stack) :
  among (rename_continuation r k) (rename_trap_stack r ts) = among k ts.
Proof. apply among_rename_continuation. Qed.

Lemma trap_stack_eqb_renamed (r : renaming) (ts : trap_stack) :
  ∀ ts' : trap_stack,
    trap_stack_eqb (rename_trap_stack r ts) (rename_trap_stack r ts')
    = trap_stack_eqb ts ts'.
Proof.
  unfold rename_trap_stack.
  induction ts as [ | k ts IH]; intros [ | k' ts']; simpl; try reflexivity.
  rewrite rename_continuation_eqb, IH. reflexivity.
Qed.

Definition rename_entry (r : renaming) (entered : entry) : entry :=
  match entered with
  | Not_entered => Not_entered
  | Entered_with ts => Entered_with (rename_trap_stack r ts)
  | Entered_with_two_stacks => Entered_with_two_stacks
  end.

Lemma map_snd_rename_demands (r : renaming) (ds : demands) :
  map snd (rename_demands r ds) = map (rename_trap_stack r) (map snd ds).
Proof. unfold rename_demands. rewrite !map_map. reflexivity. Qed.

Lemma rename_demands_app (r : renaming) (ds ds' : demands) :
  rename_demands r (ds ++ ds') = rename_demands r ds ++ rename_demands r ds'.
Proof. apply map_app. Qed.

Lemma filter_demands_renamed (r : renaming) (k : continuation)
    (ds : demands) :
  filter (fun d => Pos.eqb (fst d) (rename_continuation r k))
    (rename_demands r ds)
  = rename_demands r (filter (fun d => Pos.eqb (fst d) k) ds).
Proof.
  unfold rename_demands. apply filter_map_with. intros d. cbn [fst].
  apply rename_continuation_eqb.
Qed.

Definition entry_of_stacks (stacks : list trap_stack) : entry :=
  match stacks with
  | [] => Not_entered
  | ts :: others =>
    if forallb (trap_stack_eqb ts) others then Entered_with ts
    else Entered_with_two_stacks
  end.

Lemma entry_of_stacks_renamed (r : renaming) (stacks : list trap_stack) :
  entry_of_stacks (map (rename_trap_stack r) stacks)
  = rename_entry r (entry_of_stacks stacks).
Proof.
  destruct stacks as [ | ts others]; [ reflexivity | ].
  cbn [map entry_of_stacks].
  rewrite (forallb_map_with _ _ (trap_stack_eqb ts))
    by (intros ts'; apply trap_stack_eqb_renamed).
  destruct (forallb (trap_stack_eqb ts) others); reflexivity.
Qed.

Lemma entry_of_renamed (r : renaming) (k : continuation) (ds : demands) :
  entry_of (rename_continuation r k) (rename_demands r ds)
  = rename_entry r (entry_of k ds).
Proof.
  change
    (entry_of_stacks
       (map snd
          (filter (fun d => Pos.eqb (fst d) (rename_continuation r k))
             (rename_demands r ds)))
     = rename_entry r
         (entry_of_stacks
            (map snd (filter (fun d => Pos.eqb (fst d) k) ds)))).
  rewrite filter_demands_renamed, map_snd_rename_demands.
  apply entry_of_stacks_renamed.
Qed.

Definition leave_scope_with (keep clear : continuation * trap_stack -> bool)
    (ds : demands) : option demands :=
  if forallb clear (filter keep ds) then Some (filter keep ds) else None.

Lemma leave_scope_with_renamed
    (g : continuation * trap_stack -> continuation * trap_stack)
    (keep keep' clear clear' : continuation * trap_stack -> bool)
    (ds : demands) :
  (∀ d : continuation * trap_stack, keep' (g d) = keep d) ->
  (∀ d : continuation * trap_stack, clear' (g d) = clear d) ->
  leave_scope_with keep' clear' (map g ds)
  = option_map (map g) (leave_scope_with keep clear ds).
Proof.
  intros Hkeep Hclear. unfold leave_scope_with.
  rewrite (filter_map_with keep' g keep ds Hkeep),
    (forallb_map_with clear' g clear _ Hclear).
  destruct (forallb clear (filter keep ds)); reflexivity.
Qed.

Lemma leave_scope_renamed (r : renaming) (ks : list continuation)
    (ds : demands) :
  leave_scope (map (rename_continuation r) ks) (rename_demands r ds)
  = option_map (rename_demands r) (leave_scope ks ds).
Proof.
  apply
    (leave_scope_with_renamed
       (fun d => (rename_continuation r (fst d), rename_trap_stack r (snd d)))
       (fun d => negb (among (fst d) ks))
       (fun d => negb (among (fst d) (map (rename_continuation r) ks)))
       (fun d => forallb (fun k => negb (among k (snd d))) ks)
       (fun d =>
          forallb (fun k => negb (among k (snd d)))
            (map (rename_continuation r) ks))
       ds).
  - intros d. cbn [fst]. rewrite among_rename_continuation. reflexivity.
  - intros d. cbn [snd]. apply forallb_map_with. intros k.
    rewrite among_trap_stack_renamed. reflexivity.
Qed.

Lemma apply_cont_demands_renamed (r : renaming) (ts : trap_stack)
    (ac : apply_cont) :
  apply_cont_demands (rename_trap_stack r ts) (rename_apply_cont r ac)
  = option_map (rename_demands r) (apply_cont_demands ts ac).
Proof.
  unfold apply_cont_demands. simpl.
  destruct (ac_trap_action ac) as [[k | k kind] | ]; simpl; try reflexivity.
  destruct ts as [ | top rest]; simpl; [ reflexivity | ].
  rewrite rename_continuation_eqb. destruct (Pos.eqb top k); reflexivity.
Qed.

Lemma apply_demands_renamed (r : renaming) (ts : trap_stack)
    (ap : apply_expr) :
  apply_demands (rename_trap_stack r ts) (rename_apply r ap)
  = option_map (rename_demands r) (apply_demands ts ap).
Proof.
  unfold apply_demands. destruct ts as [ | top rest]; simpl; [ reflexivity | ].
  rewrite rename_continuation_eqb.
  destruct (Pos.eqb top (ap_exn_continuation ap)); reflexivity.
Qed.

Lemma arms_demands_renamed (r : renaming) (ts : trap_stack)
    (arms : list (Z * apply_cont)) :
  arms_demands (rename_trap_stack r ts)
    (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  = option_map (rename_demands r) (arms_demands ts arms).
Proof.
  induction arms as [ | [i ac] arms IH]; [ reflexivity | ].
  cbn [map arms_demands fst snd]. rewrite apply_cont_demands_renamed, IH.
  destruct (apply_cont_demands ts ac) as [ds | ]; [ | reflexivity ].
  destruct (arms_demands ts arms) as [ds' | ]; [ | reflexivity ].
  cbn [option_map]. rewrite rename_demands_app. reflexivity.
Qed.

Lemma code_demands_met_renamed (r : renaming) (ret exn : continuation)
    (ds : demands) :
  code_demands_met (rename_continuation r ret) (rename_continuation r exn)
    (rename_demands r ds)
  = code_demands_met ret exn ds.
Proof.
  unfold code_demands_met, rename_demands. apply forallb_map_with. intros d.
  cbn [fst snd]. rewrite !rename_continuation_eqb.
  match goal with
  | |- (if ?c then _ else _) = (if ?c' then _ else _) =>
    change c' with c; destruct c
  end.
  - exact (trap_stack_eqb_renamed r (snd d) []).
  - apply (f_equal2 andb); [ reflexivity | ].
    exact (trap_stack_eqb_renamed r (snd d) [exn]).
Qed.

Lemma fold_left_renamed {S B B' : Type} (g : S -> S) (gb : B -> B')
    (step : S -> B -> S) (step' : S -> B' -> S) (l : list B) :
  Forall (fun b => ∀ s : S, step' (g s) (gb b) = g (step s b)) l ->
  ∀ s : S,
    List.fold_left step' (map gb l) (g s) = g (List.fold_left step l s).
Proof.
  induction 1 as [ | b l Hb Hl IH]; intros s; simpl; [ reflexivity | ].
  rewrite Hb. apply IH.
Qed.

(* A recursive group: the passes over its handlers, with the function
   that gives the demands of a handler as an argument. *)
Definition group_pass
    (demands_of : trap_stack -> continuation_handler -> option demands)
    (handlers : list (continuation * continuation_handler))
    (state : group_state) : option group_state :=
  fold_left
    (fun state '(k, h) =>
       let* '(checked, ds) := state in
       if among k checked then Some (checked, ds)
       else
         match entry_of k ds with
         | Not_entered => Some (checked, ds)
         | Entered_with entered =>
           let* ds' := demands_of entered h in
           Some (k :: checked, ds ++ ds')
         | Entered_with_two_stacks => None
         end)
    (Some state) handlers.

Definition group_demands
    (demands_of : trap_stack -> continuation_handler -> option demands)
    (handlers : list (continuation * continuation_handler)) (ds : demands)
    : option demands :=
  let* '(checked, ds) :=
    FlambdaWellFormedSpec.iterate (length handlers)
      (group_pass demands_of handlers) ([], ds)
  in
  if forallb
       (fun k =>
          match entry_of k ds with
          | Not_entered => true
          | Entered_with _ => among k checked
          | Entered_with_two_stacks => false
          end)
       (map fst handlers)
  then leave_scope (map fst handlers) ds
  else None.

Lemma trap_demands_recursive (ts : trap_stack)
    (handlers : list (continuation * continuation_handler)) (body : expr) :
  trap_demands ts (Let_cont_recursive handlers body)
  = if existsb (fun k => among k ts) (map fst handlers) then None
    else
      let* ds := trap_demands ts body in
      group_demands handler_trap_demands handlers ds.
Proof. reflexivity. Qed.

Definition rename_group_state (r : renaming) (state : group_state)
    : group_state :=
  (map (rename_continuation r) (fst state), rename_demands r (snd state)).

Section Group.

Variable r : renaming.
Variables demands_of demands_of'
  : trap_stack -> continuation_handler -> option demands.

Definition demands_of_renamed (h : continuation_handler) : Prop :=
  ∀ ts : trap_stack,
    demands_of' (rename_trap_stack r ts) (rename_handler r h)
    = option_map (rename_demands r) (demands_of ts h).

Lemma group_step_renamed (k : continuation) (h : continuation_handler)
    (state : option group_state) :
  demands_of_renamed h ->
  (let* '(checked, ds) := option_map (rename_group_state r) state in
   if among (rename_continuation r k) checked then Some (checked, ds)
   else
     match entry_of (rename_continuation r k) ds with
     | Not_entered => Some (checked, ds)
     | Entered_with entered =>
       let* ds' := demands_of' entered (rename_handler r h) in
       Some (rename_continuation r k :: checked, ds ++ ds')
     | Entered_with_two_stacks => None
     end)
  = option_map (rename_group_state r)
      (let* '(checked, ds) := state in
       if among k checked then Some (checked, ds)
       else
         match entry_of k ds with
         | Not_entered => Some (checked, ds)
         | Entered_with entered =>
           let* ds' := demands_of entered h in
           Some (k :: checked, ds ++ ds')
         | Entered_with_two_stacks => None
         end).
Proof.
  intros Hh. destruct state as [[checked ds] | ]; [ | reflexivity ].
  cbn [option_map rename_group_state fst snd].
  rewrite among_rename_continuation.
  destruct (among k checked); [ reflexivity | ].
  rewrite entry_of_renamed.
  destruct (entry_of k ds) as [ | entered | ]; try reflexivity.
  cbn [rename_entry]. rewrite Hh.
  destruct (demands_of entered h) as [ds' | ]; [ | reflexivity ].
  cbn [option_map rename_group_state fst snd map].
  apply f_equal. apply (f_equal2 pair); [ reflexivity | ].
  symmetry. apply map_app.
Qed.

Lemma group_fold_renamed
    (handlers : list (continuation * continuation_handler)) :
  Forall (fun entry => demands_of_renamed (snd entry)) handlers ->
  ∀ state : option group_state,
    fold_left
      (fun state '(k, h) =>
         let* '(checked, ds) := state in
         if among k checked then Some (checked, ds)
         else
           match entry_of k ds with
           | Not_entered => Some (checked, ds)
           | Entered_with entered =>
             let* ds' := demands_of' entered h in
             Some (k :: checked, ds ++ ds')
           | Entered_with_two_stacks => None
           end)
      (option_map (rename_group_state r) state) (rename_handlers r handlers)
    = option_map (rename_group_state r)
        (fold_left
           (fun state '(k, h) =>
              let* '(checked, ds) := state in
              if among k checked then Some (checked, ds)
              else
                match entry_of k ds with
                | Not_entered => Some (checked, ds)
                | Entered_with entered =>
                  let* ds' := demands_of entered h in
                  Some (k :: checked, ds ++ ds')
                | Entered_with_two_stacks => None
                end)
           state handlers).
Proof.
  intros Hhandlers state. unfold fold_left, rename_handlers.
  apply (fold_left_renamed (option_map (rename_group_state r))).
  refine (Forall_impl _ _ Hhandlers).
  intros [k h] Hh s. exact (group_step_renamed k h s Hh).
Qed.

Lemma group_pass_renamed
    (handlers : list (continuation * continuation_handler))
    (state : group_state) :
  Forall (fun entry => demands_of_renamed (snd entry)) handlers ->
  group_pass demands_of' (rename_handlers r handlers)
    (rename_group_state r state)
  = option_map (rename_group_state r) (group_pass demands_of handlers state).
Proof.
  intros Hhandlers. exact (group_fold_renamed handlers Hhandlers (Some state)).
Qed.

Lemma iterate_renamed {A : Type} (g : A -> A) (f f' : A -> option A)
    (n : nat) :
  (∀ x : A, f' (g x) = option_map g (f x)) ->
  ∀ x : A,
    FlambdaWellFormedSpec.iterate n f' (g x)
    = option_map g (FlambdaWellFormedSpec.iterate n f x).
Proof.
  intros Hf. induction n as [ | n IH]; intros x; [ reflexivity | ].
  cbn [FlambdaWellFormedSpec.iterate]. rewrite Hf.
  destruct (f x) as [y | ]; [ | reflexivity ].
  cbn [option_map]. apply IH.
Qed.

Lemma group_demands_renamed
    (handlers : list (continuation * continuation_handler)) (ds : demands) :
  Forall (fun entry => demands_of_renamed (snd entry)) handlers ->
  group_demands demands_of' (rename_handlers r handlers)
    (rename_demands r ds)
  = option_map (rename_demands r) (group_demands demands_of handlers ds).
Proof.
  intros Hhandlers. unfold group_demands.
  replace (length (rename_handlers r handlers)) with (length handlers)
    by (unfold rename_handlers; rewrite length_map; reflexivity).
  change ([], rename_demands r ds) with (rename_group_state r ([], ds)).
  rewrite
    (iterate_renamed (rename_group_state r) (group_pass demands_of handlers)
       (group_pass demands_of' (rename_handlers r handlers)) (length handlers)
       (fun state => group_pass_renamed handlers state Hhandlers)).
  destruct
    (FlambdaWellFormedSpec.iterate (length handlers)
       (group_pass demands_of handlers) ([], ds))
    as [[checked ds'] | ];
    [ | reflexivity ].
  cbn [option_map rename_group_state fst snd].
  rewrite map_fst_rename_handlers.
  rewrite
    (forallb_map_with _ _
       (fun k =>
          match entry_of k ds' with
          | Not_entered => true
          | Entered_with _ => among k checked
          | Entered_with_two_stacks => false
          end)).
  - rewrite leave_scope_renamed.
    destruct
      (forallb
         (fun k =>
            match entry_of k ds' with
            | Not_entered => true
            | Entered_with _ => among k checked
            | Entered_with_two_stacks => false
            end)
         (map fst handlers));
      reflexivity.
  - intros k. rewrite entry_of_renamed.
    destruct (entry_of k ds') as [ | entered | ]; cbn [rename_entry];
      try reflexivity.
    apply among_rename_continuation.
Qed.

End Group.

Fixpoint trap_demands_renamed (r : renaming) (e : expr) {struct e} :
  ∀ ts : trap_stack,
    trap_demands (rename_trap_stack r ts) (rename_expr r e)
    = option_map (rename_demands r) (trap_demands ts e)
with handler_trap_demands_renamed (r : renaming) (h : continuation_handler)
    {struct h} :
  ∀ ts : trap_stack,
    handler_trap_demands (rename_trap_stack r ts) (rename_handler r h)
    = option_map (rename_demands r) (handler_trap_demands ts h)
with binding_traps_well_formed_renamed (r : renaming)
    (binding : static_binding) {struct binding} :
  binding_traps_well_formed (rename_static_binding r binding)
  = binding_traps_well_formed binding
with code_traps_well_formed_renamed (r : renaming) (c : code) {struct c} :
  code_traps_well_formed (rename_code r c) = code_traps_well_formed c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros ts.
    + cbn [rename_expr trap_demands]. apply trap_demands_renamed.
    + cbn [rename_expr trap_demands].
      replace
        (forallb binding_traps_well_formed
           (map (rename_static_binding r) bindings))
        with (forallb binding_traps_well_formed bindings).
      * destruct (forallb binding_traps_well_formed bindings);
          [ apply trap_demands_renamed | reflexivity ].
      * induction bindings as [ | binding bindings IH]; cbn [map forallb];
          [ reflexivity | ].
        rewrite (binding_traps_well_formed_renamed r binding), <- IH.
        reflexivity.
    + cbn [rename_expr trap_demands]. rewrite among_trap_stack_renamed.
      destruct (among k ts); [ reflexivity | ].
      rewrite (trap_demands_renamed r body ts).
      destruct (trap_demands ts body) as [ds | ]; [ | reflexivity ].
      cbn [option_map].
      change [rename_continuation r k]
        with (map (rename_continuation r) [k]).
      rewrite leave_scope_renamed, entry_of_renamed.
      destruct (leave_scope [k] ds) as [outer | ]; [ | reflexivity ].
      destruct (entry_of k ds) as [ | entered | ]; try reflexivity.
      cbn [option_map rename_entry].
      rewrite among_trap_stack_renamed.
      destruct (among k entered); [ reflexivity | ].
      rewrite (handler_trap_demands_renamed r h entered).
      destruct (handler_trap_demands entered h) as [ds' | ];
        [ | reflexivity ].
      cbn [option_map]. rewrite rename_demands_app.
      reflexivity.
    + assert
        (Hhandlers :
          Forall
            (fun entry =>
               demands_of_renamed r handler_trap_demands
                 handler_trap_demands (snd entry))
            handlers).
      { induction handlers as [ | [k h] handlers IH]; constructor;
          [ | exact IH ].
        intros ts'. apply handler_trap_demands_renamed. }
      cbn [rename_expr].
      change
        (map (fun '(k, h) => (rename_continuation r k, rename_handler r h))
           handlers)
        with (rename_handlers r handlers).
      rewrite !trap_demands_recursive, map_fst_rename_handlers.
      rewrite
        (existsb_map_with _ _ (fun k => among k ts))
        by (intros k; apply among_trap_stack_renamed).
      destruct (existsb (fun k => among k ts) (map fst handlers));
        [ reflexivity | ].
      rewrite (trap_demands_renamed r body ts).
      destruct (trap_demands ts body) as [ds | ]; [ | reflexivity ].
      cbn [option_map].
      exact
        (group_demands_renamed r handler_trap_demands handler_trap_demands
           handlers ds Hhandlers).
    + cbn [rename_expr trap_demands]. apply apply_demands_renamed.
    + cbn [rename_expr trap_demands]. apply apply_cont_demands_renamed.
    + cbn [rename_expr trap_demands]. apply arms_demands_renamed.
    + reflexivity.
  - destruct h as [params metadata handler]. intros ts.
    cbn [rename_handler handler_trap_demands]. apply trap_demands_renamed.
  - destruct binding as [id c | id | sym const];
      cbn [rename_static_binding binding_traps_well_formed];
      try reflexivity.
    apply code_traps_well_formed_renamed.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code code_traps_well_formed].
    change [rename_continuation r exn] with (rename_trap_stack r [exn]).
    rewrite (trap_demands_renamed r body [exn]).
    destruct (trap_demands [exn] body) as [ds | ]; [ | reflexivity ].
    cbn [option_map]. apply code_demands_met_renamed.
Qed.

Lemma traps_well_formed_renamed (r : renaming) (unit_exn : continuation)
    (e : expr) :
  traps_well_formed (rename_continuation r unit_exn) (rename_expr r e)
  = traps_well_formed unit_exn e.
Proof.
  unfold traps_well_formed.
  change [rename_continuation r unit_exn]
    with (rename_trap_stack r [unit_exn]).
  rewrite (trap_demands_renamed r e [unit_exn]).
  destruct (trap_demands [unit_exn] e) as [ds | ]; [ | reflexivity ].
  cbn [option_map]. unfold rename_demands. apply forallb_map_with. intros d.
  cbn [fst snd]. rewrite rename_continuation_eqb.
  match goal with
  | |- trap_stack_eqb _ (if ?c then _ else _)
       = trap_stack_eqb _ (if ?c' then _ else _) =>
    change c' with c; destruct c
  end.
  - exact (trap_stack_eqb_renamed r (snd d) []).
  - exact (trap_stack_eqb_renamed r (snd d) [unit_exn]).
Qed.

Theorem trap_demands_equivariant : trap_demands_equivariant_statement.
Proof. intros r ts e. apply trap_demands_renamed. Qed.

Theorem traps_well_formed_equivariant :
  traps_well_formed_equivariant_statement.
Proof. exact traps_well_formed_renamed. Qed.

Theorem well_formed_unit_equivariant : well_formed_unit_equivariant_statement.
Proof.
  intros r u e. unfold well_formed_unit, rename_unit_interface.
  cbn [unit_return unit_exn].
  rewrite statics_at_toplevel_equivariant_aux,
    (static_names_renamed r _ (code_ids_of_binding_renamed r)),
    (static_names_renamed r _ (symbols_of_binding_renamed r)),
    names_in_scope_equivariant, binders_distinct_equivariant,
    code_closed_equivariant, sets_well_formed_renamed,
    numbers_in_range_renamed, unit_exn_handlers_well_formed_renamed,
    traps_well_formed_renamed.
  reflexivity.
Qed.

(* The states that the machine makes undefined. *)
Lemma code_id_bound_renamed (r : renaming) (statics : static_env)
    (id : code_id) :
  code_id_bound (rename_static_env r statics) id = code_id_bound statics id.
Proof.
  unfold code_id_bound. rewrite lookup_rename_code.
  destruct (lookup id (static_code statics)); reflexivity.
Qed.

Lemma calls_code_binding_statics_equivariant (r : renaming) (ap : apply_expr)
    (vars : env) (statics : static_env) :
  calls_code_binding_statics (rename_apply r ap) (rename_env r vars)
    (rename_static_env r statics)
  = calls_code_binding_statics ap vars statics.
Proof.
  unfold calls_code_binding_statics, rename_apply. cbn [ap_callee].
  rewrite eval_simple_equivariant.
  destruct (eval_simple vars (ap_callee ap)) as [callee | ];
    [ | reflexivity ].
  replace (closure_of (rename_static_env r statics) callee)
    with (closure_of statics callee)
    by (destruct callee; reflexivity).
  destruct (closure_of statics callee) as [[called slots] | ];
    [ | reflexivity ].
  rewrite lookup_rename_code.
  destruct (lookup called (static_code statics)) as [c | ]; cbn [option_map];
    [ | reflexivity ].
  destruct c as [params my_closure ret exn metadata body]. simpl.
  apply rename_binds_statics.
Qed.

Theorem static_fault_equivariant : static_fault_equivariant_statement.
Proof.
  intros r s. unfold static_fault, rename_state.
  cbn [state_expr state_vars state_statics].
  destruct (state_expr s)
    as [ x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    cbn [rename_expr]; try reflexivity.
  - rewrite
      (rebinds_renamed r _ (code_ids_of_binding_renamed r)
         (code_id_bound (state_statics s)))
      by apply code_id_bound_renamed.
    rewrite
      (rebinds_renamed r _ (symbols_of_binding_renamed r)
         (symbol_bound (state_statics s)))
      by reflexivity.
    reflexivity.
  - exact (rename_handlers_bind_statics r handlers).
  - apply calls_code_binding_statics_equivariant.
Qed.

(* ======================================================================== *)
(* The normalisations of FlambdaValidateSpec.v                              *)
(* ======================================================================== *)

Theorem iterate_equivariant : iterate_equivariant_statement.
Proof.
  intros rounds f f_equivariant.
  induction rounds as [ | rounds IH]; intros r e; simpl; [ reflexivity | ].
  rewrite f_equivariant. apply IH.
Qed.

(* The rewrites as the validation applies them: with nothing in scope and
   nothing known. *)
Lemma remove_unused_defined_lets_closed_equivariant :
  rewrite_equivariant (remove_unused_defined_lets []).
Proof.
  intros r e. exact (remove_unused_defined_lets_equivariant_aux r e []).
Qed.

Lemma inline_calls_unknowing_equivariant :
  rewrite_equivariant (inline_calls []).
Proof. intros r e. exact (inline_calls_equivariant r [] e). Qed.

Lemma inline_known_calls_unknowing_equivariant :
  rewrite_equivariant (inline_known_calls [] []).
Proof.
  intros r e. exact (inline_known_calls_equivariant_aux r [] e []).
Qed.

(* The renaming is taken out of each rewrite in turn, from the
   innermost. *)
Ltac rename_outwards :=
  repeat
    first
      [ rewrite fold_constants_equivariant
      | rewrite collapse_switches_equivariant_aux
      | rewrite remove_unused_conts_equivariant_aux
      | rewrite inline_tail_conts_equivariant_aux
      | rewrite thread_switches_equivariant_aux
      | rewrite load_known_blocks_equivariant
      | rewrite unbox_known_numbers_equivariant
      | rewrite follow_aliases_unknowing_equivariant
      | rewrite remove_unused_lets_equivariant_aux
      | rewrite remove_unused_defined_lets_closed_equivariant
      | rewrite inline_calls_unknowing_equivariant
      | rewrite inline_known_calls_unknowing_equivariant
      | rewrite drop_deleted_code_equivariant_aux
      | rewrite merge_statics_equivariant_aux ].

Lemma normalise_code_before_equivariant :
  rewrite_equivariant normalise_code_before.
Proof.
  intros r e. unfold normalise_code_before. rename_outwards. reflexivity.
Qed.

Lemma normalise_before_round_equivariant :
  rewrite_equivariant normalise_before_round.
Proof.
  intros r e. unfold normalise_before_round. rename_outwards.
  apply rewrite_code_equivariant, normalise_code_before_equivariant.
Qed.

Theorem normalise_before_equivariant :
  normalise_before_equivariant_statement.
Proof.
  intros rounds. apply iterate_equivariant, normalise_before_round_equivariant.
Qed.

Lemma normalise_code_after_equivariant :
  rewrite_equivariant normalise_code_after.
Proof.
  intros r e. unfold normalise_code_after. rename_outwards. reflexivity.
Qed.

Lemma normalise_after_round_equivariant :
  rewrite_equivariant normalise_after_round.
Proof.
  intros r e. unfold normalise_after_round. rename_outwards.
  apply rewrite_code_equivariant, normalise_code_after_equivariant.
Qed.

Theorem normalise_after_equivariant : normalise_after_equivariant_statement.
Proof.
  intros rounds. apply iterate_equivariant, normalise_after_round_equivariant.
Qed.

Theorem without_statics_equivariant : without_statics_equivariant_statement.
Proof.
  intros D r e. unfold without_statics. rewrite drop_statics_equivariant.
  destruct (drop_statics D e) as [e' | ]; cbn [option_map]; [ | reflexivity ].
  rewrite drop_deleted_code_equivariant_aux, merge_statics_equivariant_aux.
  reflexivity.
Qed.

(* ======================================================================== *)
(* FlambdaWellKindedSpec.v                                                  *)
(* ======================================================================== *)

(* A map whose keys are renamed, and what they are bound to kept. *)
Lemma lookup_map_keys_injective {A : Type} (f : positive -> positive)
    (x : positive) (l : finite_map A) :
  (∀ a b : positive, Pos.eqb (f a) (f b) = Pos.eqb a b) ->
  lookup (f x) (Keyed.map_keys f l) = lookup x l.
Proof.
  intros Hf. unfold Keyed.map_keys, Keyed.map_bindings.
  induction l as [ | [y a] l IH]; simpl; [ reflexivity | ].
  rewrite Hf. destruct (Pos.eqb x y); [ reflexivity | exact IH ].
Qed.

Lemma handler_kinds_renamed (r : renaming) (h : continuation_handler) :
  handler_kinds (rename_handler r h) = handler_kinds h.
Proof. destruct h; reflexivity. Qed.

Lemma kind_of_simple_renamed (r : renaming) (kinds : kind_env) (s : simple) :
  kind_of_simple (rename_kind_env r kinds) (rename_simple r s)
  = kind_of_simple kinds s.
Proof.
  destruct s as [x | sym | c]; simpl; try reflexivity.
  apply lookup_map_keys_injective, rename_variable_eqb.
Qed.

Lemma kinds_of_simples_renamed (r : renaming) (kinds : kind_env)
    (args : list simple) :
  kinds_of_simples (rename_kind_env r kinds) (map (rename_simple r) args)
  = kinds_of_simples kinds args.
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite kind_of_simple_renamed, IH. reflexivity.
Qed.

Lemma bind_param_kinds_renamed (r : renaming) (params : list variable) :
  ∀ (params_kinds : list flambda_kind) (kinds : kind_env),
    bind_param_kinds (map (rename_variable r) params) params_kinds
      (rename_kind_env r kinds)
    = option_map (rename_kind_env r)
        (bind_param_kinds params params_kinds kinds).
Proof.
  induction params as [ | x params IH]; intros [ | k params_kinds] kinds;
    simpl; try reflexivity.
  exact (IH params_kinds ((x, k) :: kinds)).
Qed.

Lemma handler_arities_renamed (r : renaming)
    (handlers : list (continuation * continuation_handler)) :
  handler_arities (rename_handlers r handlers)
  = rename_arity_env r (handler_arities handlers).
Proof.
  unfold handler_arities, rename_handlers, rename_arity_env, Keyed.map_keys,
    Keyed.map_bindings, map_values.
  induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
  rewrite handler_kinds_renamed, IH. reflexivity.
Qed.

Lemma value_slots_well_kinded_renamed (r : renaming) (slots : slot_kinds)
    (kinds : kind_env) (value_slots : list (value_slot * simple)) :
  value_slots_well_kinded slots (rename_kind_env r kinds)
    (map (fun slot => (fst slot, rename_simple r (snd slot))) value_slots)
  = value_slots_well_kinded slots kinds value_slots.
Proof.
  unfold value_slots_well_kinded. apply forallb_map_with. intros [slot s].
  simpl. rewrite kind_of_simple_renamed. reflexivity.
Qed.

Lemma kind_of_named_renamed (r : renaming) (slots : slot_kinds)
    (kinds : kind_env) (d : named) :
  kind_of_named slots (rename_kind_env r kinds) (rename_named r d)
  = kind_of_named slots kinds d.
Proof.
  destruct d; cbn [rename_named kind_of_named];
    rewrite ?kind_of_simple_renamed, ?kinds_of_simples_renamed,
      ?value_slots_well_kinded_renamed;
    reflexivity.
Qed.

Lemma static_const_well_kinded_renamed (r : renaming) (slots : slot_kinds)
    (kinds : kind_env) (const : static_const) :
  static_const_well_kinded slots (rename_kind_env r kinds)
    (rename_static_const r const)
  = static_const_well_kinded slots kinds const.
Proof.
  destruct const; cbn [rename_static_const static_const_well_kinded];
    rewrite ?kind_of_simple_renamed, ?value_slots_well_kinded_renamed;
    try reflexivity.
  apply forallb_map_with. intros s. rewrite kind_of_simple_renamed.
  reflexivity.
Qed.

Lemma is_bound_map_keys_injective {A : Type} (f : positive -> positive)
    (x : positive) (l : finite_map A) :
  (∀ a b : positive, Pos.eqb (f a) (f b) = Pos.eqb a b) ->
  is_bound (f x) (Keyed.map_keys f l) = is_bound x l.
Proof.
  intros Hf. unfold is_bound. rewrite (lookup_map_keys_injective _ _ _ Hf).
  reflexivity.
Qed.

Lemma trap_action_in_scope_renamed (r : renaming) (conts : arity_env)
    (ac : apply_cont) :
  trap_action_in_scope (rename_arity_env r conts) (rename_apply_cont r ac)
  = trap_action_in_scope conts ac.
Proof.
  unfold trap_action_in_scope, rename_arity_env. simpl.
  destruct (ac_trap_action ac) as [[k | k kind] | ]; simpl;
    [ | | reflexivity ];
    apply is_bound_map_keys_injective, rename_continuation_eqb.
Qed.

Lemma exn_extra_kinds_renamed (r : renaming) (ap : apply_expr) :
  map snd (ap_exn_extra_args (rename_apply r ap))
  = map snd (ap_exn_extra_args ap).
Proof. simpl. rewrite map_map. reflexivity. Qed.

Lemma apply_cont_well_kinded_renamed (r : renaming) (kinds : kind_env)
    (conts : arity_env) (ac : apply_cont) :
  apply_cont_well_kinded (rename_kind_env r kinds) (rename_arity_env r conts)
    (rename_apply_cont r ac)
  = apply_cont_well_kinded kinds conts ac.
Proof.
  unfold apply_cont_well_kinded. rewrite trap_action_in_scope_renamed.
  unfold rename_arity_env. simpl.
  rewrite (lookup_map_keys_injective _ _ _ (rename_continuation_eqb r)),
    kinds_of_simples_renamed.
  reflexivity.
Qed.

Lemma apply_well_kinded_renamed (r : renaming) (kinds : kind_env)
    (conts : arity_env) (ap : apply_expr) :
  apply_well_kinded (rename_kind_env r kinds) (rename_arity_env r conts)
    (rename_apply r ap)
  = apply_well_kinded kinds conts ap.
Proof.
  unfold apply_well_kinded.
  rewrite exn_extra_simples_rename, !exn_extra_kinds_renamed.
  unfold rename_arity_env. simpl.
  rewrite !(lookup_map_keys_injective _ _ _ (rename_continuation_eqb r)),
    kind_of_simple_renamed, !kinds_of_simples_renamed.
  reflexivity.
Qed.

Fixpoint well_kinded_renamed (r : renaming) (slots : slot_kinds) (e : expr)
    {struct e} :
  ∀ (kinds : kind_env) (conts : arity_env),
    well_kinded slots (rename_kind_env r kinds) (rename_arity_env r conts)
      (rename_expr r e)
    = well_kinded slots kinds conts e
with handler_well_kinded_renamed (r : renaming) (slots : slot_kinds)
    (h : continuation_handler) {struct h} :
  ∀ (kinds : kind_env) (conts : arity_env),
    handler_well_kinded slots (rename_kind_env r kinds)
      (rename_arity_env r conts) (rename_handler r h)
    = handler_well_kinded slots kinds conts h
with binding_well_kinded_renamed (r : renaming) (slots : slot_kinds)
    (binding : static_binding) {struct binding} :
  ∀ kinds : kind_env,
    binding_well_kinded slots (rename_kind_env r kinds)
      (rename_static_binding r binding)
    = binding_well_kinded slots kinds binding
with code_well_kinded_renamed (r : renaming) (slots : slot_kinds) (c : code)
    {struct c} :
  code_well_kinded slots (rename_code r c) = code_well_kinded slots c.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros kinds conts; cbn [rename_expr well_kinded].
    + rewrite kind_of_named_renamed. f_equal.
      exact (well_kinded_renamed r slots body ((x, kind) :: kinds) conts).
    + rewrite well_kinded_renamed. f_equal.
      induction bindings as [ | binding bindings IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (binding_well_kinded_renamed r slots binding), IH. reflexivity.
    + rewrite handler_well_kinded_renamed, handler_kinds_renamed. f_equal.
      exact
        (well_kinded_renamed r slots body kinds
           ((k, handler_kinds h) :: conts)).
    + change
        (map (fun '(k, h) => (rename_continuation r k, rename_handler r h))
           handlers)
        with (rename_handlers r handlers).
      rewrite handler_arities_renamed.
      replace
        (rename_arity_env r (handler_arities handlers)
         ++ rename_arity_env r conts)
        with (rename_arity_env r (handler_arities handlers ++ conts))
        by apply map_app.
      rewrite well_kinded_renamed. f_equal.
      generalize (handler_arities handlers ++ conts). intros conts'.
      unfold rename_handlers.
      induction handlers as [ | [k h] handlers IH]; cbn [map forallb];
        [ reflexivity | ].
      rewrite (handler_well_kinded_renamed r slots h), IH. reflexivity.
    + apply apply_well_kinded_renamed.
    + apply apply_cont_well_kinded_renamed.
    + rewrite kind_of_simple_renamed. f_equal. apply forallb_map_with.
      intros arm. apply apply_cont_well_kinded_renamed.
    + reflexivity.
  - destruct h as [params metadata handler]. intros kinds conts.
    cbn [rename_handler handler_well_kinded].
    rewrite (distinct_map_injective _ (rename_variable_eqb r)),
      bind_param_kinds_renamed.
    destruct (bind_param_kinds params (hm_params_kinds metadata) kinds)
      as [handler_kinds | ];
      cbn [option_map]; [ | reflexivity ].
    rewrite well_kinded_renamed. reflexivity.
  - destruct binding as [id c | id | sym const]; intros kinds;
      cbn [rename_static_binding binding_well_kinded].
    + apply code_well_kinded_renamed.
    + reflexivity.
    + apply static_const_well_kinded_renamed.
  - destruct c as [params my_closure ret exn metadata body].
    cbn [rename_code code_well_kinded].
    change (rename_variable r my_closure :: map (rename_variable r) params)
      with (map (rename_variable r) (my_closure :: params)).
    rewrite (distinct_map_injective _ (rename_variable_eqb r)).
    change [(rename_variable r my_closure, Value)]
      with (rename_kind_env r [(my_closure, Value)]).
    rewrite bind_param_kinds_renamed.
    destruct
      (bind_param_kinds params (unarize (cm_params_arity metadata))
         [(my_closure, Value)])
      as [body_kinds | ];
      cbn [option_map]; [ | reflexivity ].
    f_equal.
    exact
      (well_kinded_renamed r slots body body_kinds
         [(ret, unarize (cm_result_arity metadata)); (exn, [Value])]).
Qed.

Theorem handler_kinds_equivariant : handler_kinds_equivariant_statement.
Proof. exact handler_kinds_renamed. Qed.

Theorem kind_of_simple_equivariant : kind_of_simple_equivariant_statement.
Proof. exact kind_of_simple_renamed. Qed.

Theorem kinds_of_simples_equivariant : kinds_of_simples_equivariant_statement.
Proof. exact kinds_of_simples_renamed. Qed.

Theorem kind_of_named_equivariant : kind_of_named_equivariant_statement.
Proof. exact kind_of_named_renamed. Qed.

Theorem bind_param_kinds_equivariant : bind_param_kinds_equivariant_statement.
Proof. exact bind_param_kinds_renamed. Qed.

Theorem static_const_well_kinded_equivariant :
  static_const_well_kinded_equivariant_statement.
Proof. exact static_const_well_kinded_renamed. Qed.

Theorem apply_cont_well_kinded_equivariant :
  apply_cont_well_kinded_equivariant_statement.
Proof. exact apply_cont_well_kinded_renamed. Qed.

Theorem apply_well_kinded_equivariant :
  apply_well_kinded_equivariant_statement.
Proof. exact apply_well_kinded_renamed. Qed.

Theorem well_kinded_equivariant : well_kinded_equivariant_statement.
Proof.
  intros r slots kinds conts e. apply well_kinded_renamed.
Qed.

Theorem well_kinded_unit_equivariant : well_kinded_unit_equivariant_statement.
Proof.
  intros r slots unit_return unit_exn e. unfold well_kinded_unit.
  exact
    (well_kinded_renamed r slots e [] (unit_arities unit_return unit_exn)).
Qed.

(* ======================================================================== *)
(* The check                                                                *)
(* ======================================================================== *)

(* The comparison answers the same when both terms are renamed
   (FlambdaCompareAlphaProofs.expr_eqb_equivariant), here with no names
   paired. *)
Lemma expr_eqb_renamed (r : renaming) (e e' : expr) :
  expr_eqb [] [] (rename_expr r e) (rename_expr r e') = expr_eqb [] [] e e'.
Proof. exact (expr_eqb_equivariant r [] [] e e'). Qed.

(* The lifting: its rewrites and its checks commute with renaming by
   the statements of their own files. *)
Lemma only_closures_of_renamed (r : renaming)
    (known : list (code_id * symbol)) (e : expr) :
  only_closures_of known (rename_expr r e) = only_closures_of known e.
Proof.
  unfold only_closures_of.
  induction known as [ | [id s] known IH]; simpl; [ reflexivity | ].
  rewrite only_closure_of_equivariant, IH. reflexivity.
Qed.

Lemma lift_unit_renamed (r : renaming) (L : lifting) (e : expr) :
  lift_unit (rename_lifting r L) (rename_expr r e)
  = option_map (rename_expr r) (lift_unit L e).
Proof.
  unfold lift_unit, rename_lifting.
  cbn [lifting_unit lifted_lets lifted_my_closures]. cbv zeta.
  rewrite <- lift_expr_equivariant, <- bind_my_closures_equivariant.
  rewrite well_formed_unit_equivariant, only_closures_of_renamed.
  pose proof (exits_plain_equivariant r [] e) as Hexits. simpl in Hexits.
  rewrite Hexits.
  destruct
    (exits_plain [] e
     && well_formed_unit (lifting_unit L)
          (bind_my_closures (lifted_my_closures L)
             (lift_expr (lifted_lets L) root e))
     && only_closures_of (lifted_my_closures L)
          (bind_my_closures (lifted_my_closures L)
             (lift_expr (lifted_lets L) root e)));
    reflexivity.
Qed.

Lemma with_lifting_renamed (r : renaming) (L : lifting) (e : expr) :
  with_lifting (rename_lifting r L) (rename_expr r e)
  = rename_expr r (with_lifting L e).
Proof.
  unfold with_lifting. rewrite lift_unit_renamed.
  destruct (lift_unit L e); reflexivity.
Qed.

(* The removal of unused value slots. *)
Lemma without_slots_equivariant (slots : list value_slot) :
  rewrite_equivariant (without_slots slots).
Proof.
  intros r e. unfold without_slots, drop_unused_slots.
  rewrite slots_unused_equivariant, <- drop_slots_equivariant.
  destruct (slots_unused slots e); reflexivity.
Qed.

Theorem validate_unit_equivariant : validate_unit_equivariant_statement.
Proof.
  intros r rounds unused slots L before after. unfold validate_unit.
  rewrite with_lifting_renamed.
  rewrite !normalise_before_equivariant, normalise_after_equivariant,
    without_slots_equivariant, !without_statics_equivariant,
    !expr_eqb_renamed.
  reflexivity.
Qed.
