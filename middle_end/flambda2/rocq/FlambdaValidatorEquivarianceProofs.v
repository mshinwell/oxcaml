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
  FlambdaUnboxSpec FlambdaValidatorEquivarianceSpec.
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

Lemma rename_apply_cont_injective (r : renaming) (ac ac' : apply_cont) :
  rename_apply_cont r ac = rename_apply_cont r ac' -> ac = ac'.
Proof.
  destruct ac as [k args], ac' as [k' args']. unfold rename_apply_cont.
  simpl. intros Heq. injection Heq as Hk Hargs.
  apply rename_continuation_injective in Hk.
  apply rename_simples_injective in Hargs. congruence.
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
    + rewrite var_in_simple_equivariant, var_in_simples_equivariant.
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
  - rewrite rename_continuation_eqb, !length_map,
      params_not_in_args_equivariant.
    destruct
      (Pos.eqb (ac_continuation ac) k
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
  destruct arm as [i [k' args]]. unfold thread_arm.
  cbn [fst snd rename_apply_cont ac_args ac_continuation].
  destruct args as [ | arg args]; [ | reflexivity ]. cbn [map].
  rewrite rename_continuation_eqb. destruct (Pos.eqb k' k); [ | reflexivity ].
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
  unfold arms_apply. apply existsb_map_with. intros arm.
  apply rename_continuation_eqb.
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
    + apply rename_continuation_eqb.
    + apply existsb_map_with. intros arm. apply rename_continuation_eqb.
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
  rewrite simple_avoids_renamed, simples_avoid_renamed. reflexivity.
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
  destruct c as [h vars conts recursive | k]; simpl; [ | reflexivity ].
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
Proof. destruct p; try reflexivity. apply field_loaded_equivariant. Qed.

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

Lemma canonical_apply_equivariant (r : renaming) (tenv : typing_env)
    (ap : apply_expr) :
  canonical_apply (rename_naive_typing_env r tenv) (rename_apply r ap)
  = rename_apply r (canonical_apply tenv ap).
Proof.
  unfold canonical_apply, rename_apply.
  cbn [ap_callee ap_call_kind ap_args ap_continuation ap_exn_continuation].
  rewrite canonical_simple_equivariant, canonical_call_kind_equivariant,
    canonical_simples_equivariant.
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
