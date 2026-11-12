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


(* Proofs of the statements of FlambdaUnboxParamsRenameSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaPrimitiveModel FlambdaBindersSpec
  FlambdaNominalSpec FlambdaNominalProofs FlambdaAlphaProofs
  FlambdaNormaliseSpec FlambdaEquivarianceSpec FlambdaEquivarianceProofs
  FlambdaBlockLoadSpec FlambdaUnboxSpec FlambdaValidatorEquivarianceSpec
  FlambdaValidatorEquivarianceProofs FlambdaScopedProofs
  FlambdaKeepsScopeProofs FlambdaUnboxParamsSpec
  FlambdaUnboxParamsRenameSpec.
Import ListNotations.

(* ======================================================================== *)
(* What is known                                                            *)
(* ======================================================================== *)

Lemma facts_under_let_equivariant (r : renaming) (known : facts)
    (x : variable) (d : named) :
  facts_under_let (rename_facts r known) (rename_variable r x)
    (rename_named r d)
  = rename_facts r (facts_under_let known x d).
Proof.
  unfold facts_under_let, rename_facts. simpl.
  rewrite known_under_let_equivariant, numbers_under_let_equivariant.
  reflexivity.
Qed.

Lemma facts_under_statics_equivariant (r : renaming) (known : facts)
    (bindings : list static_binding) :
  facts_under_statics (rename_facts r known)
    (map (rename_static_binding r) bindings)
  = rename_facts r (facts_under_statics known bindings).
Proof.
  unfold facts_under_statics, rename_facts. simpl.
  rewrite known_under_statics_equivariant, numbers_under_statics_equivariant.
  reflexivity.
Qed.

Lemma facts_under_params_equivariant (r : renaming) (known : facts)
    (params : list variable) :
  facts_under_params (rename_facts r known) (map (rename_variable r) params)
  = rename_facts r (facts_under_params known params).
Proof.
  unfold facts_under_params, rename_facts. simpl.
  rewrite forget_vars_equivariant, forget_wrapped_vars_equivariant.
  reflexivity.
Qed.

(* ======================================================================== *)
(* What reading a box gives, and the applications                           *)
(* ======================================================================== *)

Theorem projection_of_equivariant : projection_of_equivariant_statement.
Proof.
  intros r known p arg. unfold projection_of.
  destruct (reads_a_box p); [ | reflexivity ].
  change (Prim (Unary p) [rename_simple r arg])
    with (rename_named r (Prim (Unary p) [arg])).
  cbn [rename_facts facts_blocks facts_numbers].
  rewrite fold_named_equivariant, load_known_named_equivariant,
    unbox_known_named_equivariant.
  destruct (fold_named (Prim (Unary p) [arg])); try reflexivity;
    (destruct (load_known_named (facts_blocks known) (Prim (Unary p) [arg]));
     try reflexivity;
     (destruct
        (unbox_known_named (facts_numbers known) (Prim (Unary p) [arg]));
      reflexivity)).
Qed.

Lemma extend_args_equivariant (r : renaming) (known : facts) (i : nat)
    (p : unary_primitive) (args : list simple) :
  extend_args (rename_facts r known) i p (map (rename_simple r) args)
  = option_map (map (rename_simple r)) (extend_args known i p args).
Proof.
  unfold extend_args. rewrite nth_error_map.
  destruct (nth_error args i) as [arg | ]; simpl; [ | reflexivity ].
  rewrite projection_of_equivariant.
  destruct (projection_of known p arg); simpl; [ | reflexivity ].
  rewrite map_app. reflexivity.
Qed.

Lemma extend_apply_cont_equivariant (r : renaming) (known : facts)
    (k : continuation) (i : nat) (p : unary_primitive) (ac : apply_cont) :
  extend_apply_cont (rename_facts r known) (rename_continuation r k) i p
    (rename_apply_cont r ac)
  = option_map (rename_apply_cont r) (extend_apply_cont known k i p ac).
Proof.
  unfold extend_apply_cont, rename_apply_cont.
  cbn [ac_continuation ac_args ac_trap_action].
  rewrite rename_continuation_eqb.
  destruct (Pos.eqb (ac_continuation ac) k); [ | reflexivity ].
  rewrite extend_args_equivariant.
  destruct (extend_args known i p (ac_args ac)); reflexivity.
Qed.

Lemma extend_arms_equivariant (r : renaming) (known : facts)
    (k : continuation) (i : nat) (p : unary_primitive)
    (arms : list (Z * apply_cont)) :
  extend_arms (rename_facts r known) (rename_continuation r k) i p
    (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  = option_map (map (fun arm => (fst arm, rename_apply_cont r (snd arm))))
      (extend_arms known k i p arms).
Proof.
  induction arms as [ | [discriminant ac] arms IH]; simpl; [ reflexivity | ].
  rewrite extend_apply_cont_equivariant.
  destruct (extend_apply_cont known k i p ac); simpl; [ | reflexivity ].
  rewrite IH. destruct (extend_arms known k i p arms); reflexivity.
Qed.

Lemma is_bound_renamed_handlers (r : renaming) (k : continuation)
    (handlers : list (continuation * continuation_handler)) :
  is_bound (rename_continuation r k)
    (map (fun '(k', h) => (rename_continuation r k', rename_handler r h))
       handlers)
  = is_bound k handlers.
Proof.
  unfold is_bound.
  induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
  rewrite rename_continuation_eqb.
  destruct (Pos.eqb k k'); [ reflexivity | exact IH ].
Qed.

Fixpoint extend_applications_equivariant_aux (r : renaming) (e : expr) :
  ∀ (known : facts) (k : continuation) (i : nat) (p : unary_primitive),
    extend_applications (rename_facts r known) (rename_continuation r k) i p
      (rename_expr r e)
    = option_map (rename_expr r) (extend_applications known k i p e)
with extend_in_handler_equivariant (r : renaming) (h : continuation_handler) :
  ∀ (known : facts) (k : continuation) (i : nat) (p : unary_primitive),
    extend_in_handler (rename_facts r known) (rename_continuation r k) i p
      (rename_handler r h)
    = option_map (rename_handler r) (extend_in_handler known k i p h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k0 h body | handlers body | ap
         | ac | scrutinee arms | ];
      intros known k i p; cbn [rename_expr extend_applications].
    + rewrite facts_under_let_equivariant,
        extend_applications_equivariant_aux.
      destruct (extend_applications (facts_under_let known x d) k i p body);
        reflexivity.
    + rewrite facts_under_statics_equivariant,
        extend_applications_equivariant_aux.
      destruct
        (extend_applications (facts_under_statics known bindings) k i p body);
        reflexivity.
    + rewrite extend_in_handler_equivariant.
      destruct (extend_in_handler known k i p h) as [h' | ]; simpl;
        [ | reflexivity ].
      rewrite rename_continuation_eqb.
      destruct (Pos.eqb k0 k); [ reflexivity | ].
      rewrite extend_applications_equivariant_aux.
      destruct (extend_applications known k i p body); reflexivity.
    + rewrite is_bound_renamed_handlers.
      destruct (is_bound k handlers); [ reflexivity | ].
      assert (Hhandlers :
        all_some
          (map
             (fun '(k', h) =>
                let* h :=
                  extend_in_handler (rename_facts r known)
                    (rename_continuation r k) i p h
                in
                Some (k', h))
             (map
                (fun '(k', h) => (rename_continuation r k', rename_handler r h))
                handlers))
        = option_map
            (map
               (fun '(k', h) =>
                  (rename_continuation r k', rename_handler r h)))
            (all_some
               (map
                  (fun '(k', h) =>
                     let* h := extend_in_handler known k i p h in
                     Some (k', h))
                  handlers))).
      { induction handlers as [ | [k1 h1] handlers IH]; simpl;
          [ reflexivity | ].
        rewrite (extend_in_handler_equivariant r h1 known k i p).
        destruct (extend_in_handler known k i p h1); simpl; [ | reflexivity ].
        rewrite IH.
        destruct
          (all_some
             (map
                (fun '(k', h) =>
                   let* h := extend_in_handler known k i p h in
                   Some (k', h))
                handlers));
          reflexivity. }
      rewrite Hhandlers.
      destruct
        (all_some
           (map
              (fun '(k', h) =>
                 let* h := extend_in_handler known k i p h in
                 Some (k', h))
              handlers));
        simpl; [ | reflexivity ].
      rewrite extend_applications_equivariant_aux.
      destruct (extend_applications known k i p body); reflexivity.
    + cbn [rename_apply ap_continuation ap_exn_continuation].
      rewrite !rename_continuation_eqb.
      destruct
        (Pos.eqb (ap_continuation ap) k || Pos.eqb (ap_exn_continuation ap) k);
        reflexivity.
    + rewrite extend_apply_cont_equivariant.
      destruct (extend_apply_cont known k i p ac); reflexivity.
    + rewrite extend_arms_equivariant.
      destruct (extend_arms known k i p arms); reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler]. intros known k i p.
    cbn [rename_handler extend_in_handler].
    rewrite facts_under_params_equivariant,
      extend_applications_equivariant_aux.
    destruct
      (extend_applications (facts_under_params known params) k i p handler);
      reflexivity.
Qed.

Theorem extend_applications_equivariant :
  extend_applications_equivariant_statement.
Proof.
  intros r known k i p e. apply extend_applications_equivariant_aux.
Qed.

(* ======================================================================== *)
(* The pass                                                                 *)
(* ======================================================================== *)

Lemma position_renamed (r : renaming) (x : variable) (xs : list variable) :
  position (rename_variable r x) (map (rename_variable r) xs) = position x xs.
Proof.
  induction xs as [ | y xs IH]; simpl; [ reflexivity | ].
  rewrite rename_variable_eqb, IH. reflexivity.
Qed.

Lemma may_take_renamed (r : renaming) (params : list variable)
    (metadata : handler_metadata) (f : variable) :
  may_take (map (rename_variable r) params) metadata (rename_variable r f)
  = may_take params metadata f.
Proof.
  unfold may_take.
  rewrite (distinct_map_injective _ (rename_variable_eqb r)), length_map,
    among_rename_variable.
  reflexivity.
Qed.

Lemma unbox_heads_equivariant (r : renaming) (handler : expr) :
  ∀ (known : facts) (k : continuation) (params : list variable)
    (metadata : handler_metadata) (body : expr),
    unbox_heads (rename_facts r known) (rename_continuation r k)
      (map (rename_variable r) params) metadata (rename_expr r handler)
      (rename_expr r body)
    = rename_expr r (unbox_heads known k params metadata handler body).
Proof.
  induction handler
    as [ f kind d rest IH | bindings rest _ | k0 h rest _ | handlers rest _
       | ap | ac | scrutinee arms | ];
    intros known k params metadata body; try reflexivity.
  destruct d
    as [ s | pr args | code slots | fslot decls slots | slot closure
       | pfrom slot closure | move_from move_to closure ];
    try reflexivity.
  destruct pr as [p | b | v | hp]; try reflexivity.
  destruct args as [ | arg args]; try reflexivity.
  destruct arg as [x | sym | c]; try reflexivity.
  destruct args as [ | arg' args]; try reflexivity.
  cbn [rename_expr rename_named map rename_simple unbox_heads].
  rewrite may_take_renamed, position_renamed.
  destruct (may_take params metadata f); [ | reflexivity ].
  destruct (position x params) as [i | ]; [ | reflexivity ].
  rewrite extend_applications_equivariant.
  destruct (extend_applications known k i p body) as [body' | ]; simpl;
    [ | reflexivity ].
  rewrite <- IH, map_app. reflexivity.
Qed.

Fixpoint unbox_params_knowing_equivariant_aux (r : renaming) (e : expr) :
  ∀ known : facts,
    unbox_params_knowing (rename_facts r known) (rename_expr r e)
    = rename_expr r (unbox_params_knowing known e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k h body | handlers body | ap
       | ac | scrutinee arms | ];
    intros known; cbn [rename_expr unbox_params_knowing]; try reflexivity.
  - rewrite facts_under_let_equivariant,
      unbox_params_knowing_equivariant_aux.
    reflexivity.
  - rewrite facts_under_statics_equivariant,
      unbox_params_knowing_equivariant_aux.
    reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler unbox_params_knowing].
    rewrite facts_under_params_equivariant,
      !unbox_params_knowing_equivariant_aux.
    apply unbox_heads_equivariant.
  - rewrite unbox_params_knowing_equivariant_aux. reflexivity.
Qed.

Theorem unbox_params_knowing_equivariant :
  unbox_params_knowing_equivariant_statement.
Proof. intros r known e. apply unbox_params_knowing_equivariant_aux. Qed.

Theorem unbox_known_params_equivariant :
  unbox_known_params_equivariant_statement.
Proof.
  intros r e. exact (unbox_params_knowing_equivariant_aux r e no_facts).
Qed.

(* ======================================================================== *)
(* The pass keeps scope                                                     *)
(* ======================================================================== *)

(* What is known holds variables that are free in the term or bound
   around the subterm. *)
Definition facts_within (names : list variable) (known : facts) : Prop :=
  blocks_within names (facts_blocks known)
  ∧ numbers_within names (facts_numbers known).

Lemma facts_under_let_within (names : list variable) (known : facts)
    (x : variable) (d : named) :
  facts_within names known ->
  facts_within (x :: names ++ free_variables_of_named d)
    (facts_under_let known x d).
Proof.
  intros [Hblocks Hnumbers].
  split;
    [ apply known_under_let_within, Hblocks
    | apply numbers_under_let_within, Hnumbers ].
Qed.

Lemma facts_under_statics_within (names : list variable) (known : facts)
    (bindings : list static_binding) :
  facts_within names known ->
  facts_within (names ++ flat_map free_variables_of_binding bindings)
    (facts_under_statics known bindings).
Proof.
  intros [Hblocks Hnumbers].
  split; [ apply known_under_statics_within, Hblocks | ].
  intros entry Hentry.
  eapply incl_tran; [ exact (Hnumbers entry Hentry) | ].
  apply incl_appl, incl_refl.
Qed.

Lemma facts_under_params_within (names : list variable) (known : facts)
    (params : list variable) :
  facts_within names known ->
  facts_within names (facts_under_params known params).
Proof.
  intros [Hblocks Hnumbers].
  split;
    [ apply forget_vars_within, Hblocks
    | apply forget_wrapped_vars_within, Hnumbers ].
Qed.

(* What an application is given is of the argument or of what is
   known. *)
Lemma projection_of_free (names : list variable) (known : facts)
    (p : unary_primitive) (arg projection : simple) :
  facts_within names known ->
  projection_of known p arg = Some projection ->
  incl (free_variables_of_simple projection)
    (free_variables_of_simple arg ++ names).
Proof.
  intros [Hblocks Hnumbers]. unfold projection_of. cbv zeta.
  destruct (reads_a_box p); [ | discriminate ].
  remember (Prim (Unary p) [arg]) as d eqn:Hd.
  assert (Hfree : free_variables_of_named d = free_variables_of_simple arg).
  { subst d. cbn [free_variables_of_named]. unfold free_variables_of_simples.
    cbn [flat_map]. apply app_nil_r. }
  pose proof (fold_named_free d) as Hfold.
  pose proof (load_known_named_free names (facts_blocks known) d Hblocks)
    as Hload.
  pose proof (unbox_known_named_free names (facts_numbers known) d Hnumbers)
    as Hunbox.
  rewrite Hfree in Hfold, Hload, Hunbox. clear Hd Hfree.
  destruct (fold_named d);
    [ intros [= <-]; apply incl_appl; exact Hfold | .. ];
    (destruct (load_known_named (facts_blocks known) d);
     [ intros [= <-]; exact Hload | .. ];
     (destruct (unbox_known_named (facts_numbers known) d);
      [ intros [= <-]; exact Hunbox | discriminate .. ])).
Qed.

Lemma extend_apply_cont_free (names : list variable) (known : facts)
    (k : continuation) (i : nat) (p : unary_primitive) (ac ac' : apply_cont) :
  facts_within names known ->
  extend_apply_cont known k i p ac = Some ac' ->
  incl (free_variables_of_apply_cont ac')
    (free_variables_of_apply_cont ac ++ names)
  ∧ apply_cont_continuations ac' = apply_cont_continuations ac.
Proof.
  intros Hknown. unfold extend_apply_cont.
  destruct (Pos.eqb (ac_continuation ac) k).
  - unfold extend_args.
    destruct (nth_error (ac_args ac) i) as [arg | ] eqn:Hnth;
      [ | discriminate ].
    destruct (projection_of known p arg) as [projection | ] eqn:Hprojection;
      [ | discriminate ].
    intros [= <-]. split; [ | reflexivity ].
    unfold free_variables_of_apply_cont, free_variables_of_simples.
    cbn [ac_args]. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r.
    intros y Hy. apply in_app_or in Hy.
    destruct Hy as [Hy | Hy]; [ apply in_or_app; left; exact Hy | ].
    apply (projection_of_free names known p arg projection Hknown
             Hprojection)
      in Hy.
    apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy | Hy]; [ left | right; exact Hy ].
    apply in_flat_map. exists arg.
    split; [ exact (nth_error_In _ _ Hnth) | exact Hy ].
  - intros [= <-]. split; [ apply incl_appl, incl_refl | reflexivity ].
Qed.

Lemma extend_arms_free (names : list variable) (known : facts)
    (k : continuation) (i : nat) (p : unary_primitive) :
  ∀ arms arms' : list (Z * apply_cont),
    facts_within names known ->
    extend_arms known k i p arms = Some arms' ->
    incl (flat_map (fun arm => free_variables_of_apply_cont (snd arm)) arms')
      (flat_map (fun arm => free_variables_of_apply_cont (snd arm)) arms
       ++ names)
    ∧ flat_map (fun arm => apply_cont_continuations (snd arm)) arms'
      = flat_map (fun arm => apply_cont_continuations (snd arm)) arms.
Proof.
  induction arms as [ | [discriminant ac] arms IH]; intros arms' Hknown;
    cbn [extend_arms flat_map snd].
  - intros [= <-]. split; [ intros y [] | reflexivity ].
  - destruct (extend_apply_cont known k i p ac) as [ac' | ] eqn:Hac;
      [ | discriminate ].
    destruct (extend_arms known k i p arms) as [rest | ]; [ | discriminate ].
    intros [= <-].
    destruct (extend_apply_cont_free names known k i p ac ac' Hknown Hac)
      as [Hv Hk].
    destruct (IH rest Hknown eq_refl) as [Hv' Hk'].
    cbn [flat_map snd]. rewrite Hk, Hk'. split; [ | reflexivity ].
    intros y Hy. apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy | Hy].
    + apply Hv, in_app_or in Hy.
      destruct Hy as [Hy | Hy];
        [ left; apply in_or_app; left; exact Hy | right; exact Hy ].
    + apply Hv', in_app_or in Hy.
      destruct Hy as [Hy | Hy];
        [ left; apply in_or_app; right; exact Hy | right; exact Hy ].
Qed.

Fixpoint extend_applications_scoped (e : expr) :
  ∀ (names : list variable) (known : facts) (k : continuation) (i : nat)
    (p : unary_primitive) (e' : expr),
    facts_within names known ->
    extend_applications known k i p e = Some e' ->
    scoped_under names e e'
with extend_in_handler_scoped (h : continuation_handler) :
  ∀ (names : list variable) (known : facts) (k : continuation) (i : nat)
    (p : unary_primitive) (h' : continuation_handler),
    facts_within names known ->
    extend_in_handler known k i p h = Some h' ->
    handler_code_closed h = true ->
    handler_code_closed h' = true
    ∧ incl (free_variables_of_handler h') (free_variables_of_handler h ++ names)
    ∧ incl (free_continuations_of_handler h')
        (free_continuations_of_handler h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k0 h body | handlers body | ap
         | ac | scrutinee arms | ];
      intros names known k i p e' Hknown; cbn [extend_applications].
    + destruct (extend_applications (facts_under_let known x d) k i p body)
        as [body' | ] eqn:Hbody; [ | discriminate ].
      intros [= <-].
      apply scoped_under_let; [ apply incl_appl, incl_refl | ].
      exact (extend_applications_scoped body _ _ k i p body'
        (facts_under_let_within names known x d Hknown) Hbody).
    + destruct
        (extend_applications (facts_under_statics known bindings) k i p body)
        as [body' | ] eqn:Hbody; [ | discriminate ].
      intros [= <-]. apply scoped_under_let_static.
      exact (extend_applications_scoped body _ _ k i p body'
        (facts_under_statics_within names known bindings Hknown) Hbody).
    + destruct h as [params metadata handler]. cbn [extend_in_handler].
      destruct
        (extend_applications (facts_under_params known params) k i p handler)
        as [handler' | ] eqn:Hhandler; [ | discriminate ].
      pose proof (extend_applications_scoped handler names _ k i p handler'
        (facts_under_params_within names known params Hknown) Hhandler)
        as Hin_handler.
      destruct (Pos.eqb k0 k).
      * intros [= <-].
        apply scoped_under_let_cont;
          [ exact Hin_handler | apply scoped_under_refl ].
      * destruct (extend_applications known k i p body) as [body' | ]
          eqn:Hbody; [ | discriminate ].
        intros [= <-].
        apply scoped_under_let_cont; [ exact Hin_handler | ].
        exact (extend_applications_scoped body names known k i p body' Hknown
          Hbody).
    + destruct (is_bound k handlers);
        [ intros [= <-]; apply scoped_under_refl | ].
      destruct
        (all_some
           (map
              (fun '(k', h) =>
                 let* h := extend_in_handler known k i p h in
                 Some (k', h))
              handlers))
        as [handlers' | ] eqn:Hhandlers; [ | discriminate ].
      destruct (extend_applications known k i p body) as [body' | ]
        eqn:Hbody; [ | discriminate ].
      intros [= <-] Hclosed. scope_in Hclosed. scope.
      apply andb_true_iff in Hclosed. destruct Hclosed as [Hgroup Hclosed].
      destruct
        (extend_applications_scoped body names known k i p body' Hknown Hbody
           Hclosed)
        as (Hclosed' & Hv & Hk).
      assert (Hin_handlers :
        forallb (fun '(_, h) => handler_code_closed h) handlers' = true
        ∧ incl
            (flat_map (fun '(_, h) => free_variables_of_handler h) handlers')
            (flat_map (fun '(_, h) => free_variables_of_handler h) handlers
             ++ names)
        ∧ incl
            (flat_map (fun '(_, h) => free_continuations_of_handler h)
               handlers')
            (flat_map (fun '(_, h) => free_continuations_of_handler h)
               handlers)
        ∧ map fst handlers' = map fst handlers).
      { clear Hbody Hclosed Hclosed' Hv Hk. revert handlers' Hhandlers Hgroup.
        induction handlers as [ | [k1 h1] handlers IH]; intros handlers';
          simpl.
        - intros [= <-] _.
          split; [ reflexivity | ].
          split; [ intros y [] | split; [ intros y [] | reflexivity ] ].
        - destruct (extend_in_handler known k i p h1) as [h1' | ] eqn:Hh1;
            [ | discriminate ].
          destruct
            (all_some
               (map
                  (fun '(k', h) =>
                     let* h := extend_in_handler known k i p h in
                     Some (k', h))
                  handlers))
            as [rest | ]; [ | discriminate ].
          intros [= <-] Hgroup. apply andb_true_iff in Hgroup.
          destruct Hgroup as [Hfirst Hrest].
          destruct
            (extend_in_handler_scoped h1 names known k i p h1' Hknown Hh1
               Hfirst)
            as (Hfirst' & Hv1 & Hk1).
          destruct (IH rest eq_refl Hrest) as (Hrest' & Hv2 & Hk2 & Hnames).
          simpl. rewrite Hfirst', Hrest', Hnames.
          split; [ reflexivity | ].
          split; [ | split; [ apply incl_app_app; assumption | reflexivity ] ].
          intros y Hy. apply in_app_or in Hy. apply in_or_app.
          destruct Hy as [Hy | Hy].
          + apply Hv1, in_app_or in Hy.
            destruct Hy as [Hy | Hy];
              [ left; apply in_or_app; left; exact Hy | right; exact Hy ].
          + apply Hv2, in_app_or in Hy.
            destruct Hy as [Hy | Hy];
              [ left; apply in_or_app; right; exact Hy | right; exact Hy ]. }
      destruct Hin_handlers as (Hgroup' & Hgroup_v & Hgroup_k & Hnames).
      rewrite Hgroup', Hclosed', Hnames. split; [ reflexivity | split ].
      * intros y Hy. apply in_app_or in Hy. apply in_or_app.
        destruct Hy as [Hy | Hy].
        -- apply Hgroup_v, in_app_or in Hy.
           destruct Hy as [Hy | Hy];
             [ left; apply in_or_app; left; exact Hy | right; exact Hy ].
        -- apply Hv, in_app_or in Hy.
           destruct Hy as [Hy | Hy];
             [ left; apply in_or_app; right; exact Hy | right; exact Hy ].
      * apply incl_without, incl_app_app; assumption.
    + destruct
        (Pos.eqb (ap_continuation ap) k || Pos.eqb (ap_exn_continuation ap) k);
        [ discriminate | intros [= <-]; apply scoped_under_refl ].
    + destruct (extend_apply_cont known k i p ac) as [ac' | ] eqn:Hac;
        [ | discriminate ].
      intros [= <-] _. scope.
      destruct (extend_apply_cont_free names known k i p ac ac' Hknown Hac)
        as [Hv Hk].
      split; [ reflexivity | split; [ exact Hv | ] ].
      rewrite Hk. apply incl_refl.
    + destruct (extend_arms known k i p arms) as [arms' | ] eqn:Harms;
        [ | discriminate ].
      intros [= <-] _. scope.
      destruct (extend_arms_free names known k i p arms arms' Hknown Harms)
        as [Hv Hk].
      split; [ reflexivity | split; [ | rewrite Hk; apply incl_refl ] ].
      intros y Hy. apply in_app_or in Hy. apply in_or_app.
      destruct Hy as [Hy | Hy];
        [ left; apply in_or_app; left; exact Hy | ].
      apply Hv, in_app_or in Hy.
      destruct Hy as [Hy | Hy];
        [ left; apply in_or_app; right; exact Hy | right; exact Hy ].
    + intros [= <-]. apply scoped_under_refl.
  - destruct h as [params metadata handler].
    intros names known k i p h' Hknown. cbn [extend_in_handler].
    destruct
      (extend_applications (facts_under_params known params) k i p handler)
      as [handler' | ] eqn:Hhandler; [ | discriminate ].
    intros [= <-] Hclosed. scope_in Hclosed. scope.
    destruct
      (extend_applications_scoped handler names _ k i p handler'
         (facts_under_params_within names known params Hknown) Hhandler
         Hclosed)
      as (Hclosed' & Hv & Hk).
    split; [ exact Hclosed' | split; [ | exact Hk ] ].
    intros y Hy. apply in_without in Hy. destruct Hy as [Hy Hparams].
    apply Hv, in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy | Hy]; [ left | right; exact Hy ].
    apply in_without. split; assumption.
Qed.

Lemma scoped_under_trans (names : list variable) (e e' e'' : expr) :
  scoped_under names e e' ->
  scoped_under names e' e'' ->
  scoped_under names e e''.
Proof.
  intros Hfirst Hsecond Hclosed.
  destruct (Hfirst Hclosed) as (Hclosed' & Hv & Hk).
  destruct (Hsecond Hclosed') as (Hclosed'' & Hv' & Hk').
  split; [ exact Hclosed'' | split; [ | eapply incl_tran; eassumption ] ].
  intros y Hy. apply Hv', in_app_or in Hy.
  destruct Hy as [Hy | Hy]; [ exact (Hv y Hy) | ].
  apply in_or_app. right. exact Hy.
Qed.

(* The [Let] at the head of the handler made a parameter. *)
Lemma unbox_head_scoped (names : list variable) (k : continuation)
    (params : list variable) (metadata metadata' : handler_metadata)
    (f : variable) (kind : flambda_kind) (d : named) (rest body body' : expr) :
  scoped_under names body body' ->
  scoped_under names
    (Let_cont_non_recursive k (Handler params metadata (Let f kind d rest))
       body)
    (Let_cont_non_recursive k (Handler (params ++ [f]) metadata' rest) body').
Proof.
  intros Hbody Hclosed. scope_in Hclosed. scope.
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hrest Hclosed].
  destruct (Hbody Hclosed) as (Hclosed' & Hv & Hk).
  rewrite Hrest, Hclosed'. split; [ reflexivity | split ].
  - intros y Hy. apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy | Hy].
    + left. apply in_or_app. left.
      apply in_without in Hy. destruct Hy as [Hy Hparams].
      apply in_without. split.
      * apply in_or_app. right. apply in_without.
        split; [ exact Hy | ].
        intros [Heq | []]. apply Hparams, in_or_app. right. left. exact Heq.
      * intros Hin. apply Hparams, in_or_app. left. exact Hin.
    + apply Hv, in_app_or in Hy.
      destruct Hy as [Hy | Hy];
        [ left; apply in_or_app; right; exact Hy | right; exact Hy ].
  - apply incl_app_app; [ apply incl_refl | apply incl_without, Hk ].
Qed.

Lemma unbox_heads_scoped (handler : expr) :
  ∀ (names : list variable) (known : facts) (k : continuation)
    (params : list variable) (metadata : handler_metadata) (body : expr),
    facts_within names known ->
    scoped_under names
      (Let_cont_non_recursive k (Handler params metadata handler) body)
      (unbox_heads known k params metadata handler body).
Proof.
  induction handler
    as [ f kind d rest IH | bindings rest _ | k0 h rest _ | handlers rest _
       | ap | ac | scrutinee arms | ];
    intros names known k params metadata body Hknown;
    try (simpl; apply scoped_under_refl).
  destruct d
    as [ s | pr args | code slots | fslot decls slots | slot closure
       | pfrom slot closure | move_from move_to closure ];
    try (simpl; apply scoped_under_refl).
  destruct pr as [p | b | v | hp]; try (simpl; apply scoped_under_refl).
  destruct args as [ | arg args]; try (simpl; apply scoped_under_refl).
  destruct arg as [x | sym | c]; try (simpl; apply scoped_under_refl).
  destruct args as [ | arg' args]; try (simpl; apply scoped_under_refl).
  simpl.
  destruct (may_take params metadata f); [ | apply scoped_under_refl ].
  destruct (position x params) as [i | ]; [ | apply scoped_under_refl ].
  destruct (extend_applications known k i p body) as [body' | ] eqn:Hbody;
    [ | apply scoped_under_refl ].
  eapply scoped_under_trans; [ | apply IH; exact Hknown ].
  apply unbox_head_scoped.
  exact (extend_applications_scoped body names known k i p body' Hknown
    Hbody).
Qed.

Fixpoint unbox_params_knowing_scoped (e : expr) :
  ∀ (names : list variable) (known : facts),
    facts_within names known ->
    scoped_under names e (unbox_params_knowing known e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    intros names known Hknown; cbn [unbox_params_knowing];
    try apply scoped_under_refl.
  - apply scoped_under_let; [ apply incl_appl, incl_refl | ].
    apply unbox_params_knowing_scoped, facts_under_let_within, Hknown.
  - apply scoped_under_let_static.
    apply unbox_params_knowing_scoped, facts_under_statics_within, Hknown.
  - eapply scoped_under_trans; [ | apply unbox_heads_scoped, Hknown ].
    apply scoped_under_let_cont; apply unbox_params_knowing_scoped;
      [ apply facts_under_params_within, Hknown | exact Hknown ].
  - apply scoped_under_let_cont_recursive.
    apply unbox_params_knowing_scoped, Hknown.
Qed.

Theorem unbox_known_params_keeps_scope :
  unbox_known_params_keeps_scope_statement.
Proof.
  apply keeps_scope_intro. intros e.
  apply scoped_under_none, unbox_params_knowing_scoped.
  split; [ split; intros entry [] | intros entry [] ].
Qed.
