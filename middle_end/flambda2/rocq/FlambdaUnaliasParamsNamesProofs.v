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

(* FlambdaUnaliasParamsSpec.unalias_params commutes with renaming and
   keeps scope: the lemmas from which
   FlambdaValidatorEquivarianceProofs.v and FlambdaStaticsScopeProofs.v
   prove the two statements. There is no statement here, and nothing
   here needs review.

   The pass compares names by equality only and makes none, so each of
   its functions gives, on a renamed term, the renamed result. For the
   scope: an application that loses an argument loses free variables
   and no continuation; the [Let] that the handler gains mentions the
   variable that the applications gave, which is free in the body of
   the [Let_cont] where an application gives it and no binder on the
   way binds it; and the parameter that the handler loses is bound by
   that [Let]. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaNominalSpec FlambdaNominalProofs
  FlambdaEquivarianceSpec FlambdaEquivarianceProofs FlambdaBindersSpec
  FlambdaValidatorEquivarianceSpec FlambdaScopedProofs
  FlambdaUnaliasParamsSpec FlambdaUnaliasParamsProofs.
Import ListNotations.

(* ======================================================================== *)
(* The pass commutes with renaming                                          *)
(* ======================================================================== *)

Lemma drop_nth_map {A B : Type} (f : A -> B) (i : nat) (l : list A) :
  drop_nth i (map f l) = map f (drop_nth i l).
Proof.
  unfold drop_nth. rewrite map_app, firstn_map, skipn_map. reflexivity.
Qed.

Lemma first_answer_map {A A' B B' : Type} (f : A -> option B)
    (f' : A' -> option B') (g : A -> A') (h : B -> B') (l : list A) :
  (∀ a : A, f' (g a) = option_map h (f a)) ->
  first_answer f' (map g l) = option_map h (first_answer f l).
Proof.
  intros Hfg. induction l as [ | a l IH]; [ reflexivity | ].
  cbn [map first_answer]. rewrite Hfg.
  destruct (f a); [ reflexivity | exact IH ].
Qed.

Lemma trap_action_handler_renamed (r : renaming) (action : trap_action) :
  trap_action_handler (rename_trap_action r action)
  = rename_continuation r (trap_action_handler action).
Proof. destruct action; reflexivity. Qed.

Lemma apply_cont_gives_var_equivariant (r : renaming) (k : continuation)
    (i : nat) (x : variable) (ok : bool) (ac : apply_cont) :
  apply_cont_gives_var (rename_continuation r k) i (rename_variable r x) ok
    (rename_apply_cont r ac)
  = apply_cont_gives_var k i x ok ac.
Proof.
  unfold apply_cont_gives_var, rename_apply_cont.
  cbn [ac_trap_action ac_continuation ac_args].
  rewrite rename_continuation_eqb, nth_error_map.
  f_equal.
  - destruct (ac_trap_action ac) as [action | ]; [ | reflexivity ].
    cbn [option_map].
    rewrite trap_action_handler_renamed, rename_continuation_eqb.
    reflexivity.
  - destruct (Pos.eqb (ac_continuation ac) k); [ | reflexivity ].
    destruct (nth_error (ac_args ac) i) as [[y | sym | c] | ];
      cbn [option_map rename_simple]; try reflexivity.
    rewrite rename_variable_eqb. reflexivity.
Qed.

Fixpoint all_give_var_equivariant (r : renaming) (k : continuation)
    (i : nat) (x : variable) (ok : bool) (e : expr) {struct e} :
  all_give_var (rename_continuation r k) i (rename_variable r x) ok
    (rename_expr r e)
  = all_give_var k i x ok e
with handler_all_give_var_equivariant (r : renaming) (k : continuation)
    (i : nat) (x : variable) (ok : bool) (h : continuation_handler)
    {struct h} :
  handler_all_give_var (rename_continuation r k) i (rename_variable r x) ok
    (rename_handler r h)
  = handler_all_give_var k i x ok h.
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [rename_expr all_give_var]; try reflexivity.
    + rewrite rename_variable_eqb. apply all_give_var_equivariant.
    + apply all_give_var_equivariant.
    + rewrite rename_continuation_eqb, handler_all_give_var_equivariant,
        all_give_var_equivariant.
      reflexivity.
    + rewrite all_give_var_equivariant. f_equal.
      induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
      cbn [map forallb].
      rewrite rename_continuation_eqb, handler_all_give_var_equivariant, IH.
      reflexivity.
    + cbn [rename_apply ap_continuation ap_exn_continuation].
      rewrite !rename_continuation_eqb. reflexivity.
    + apply apply_cont_gives_var_equivariant.
    + induction arms as [ | [n ac] arms IH]; [ reflexivity | ].
      cbn [map forallb fst snd].
      rewrite apply_cont_gives_var_equivariant, IH. reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_all_give_var].
    rewrite among_rename_variable. apply all_give_var_equivariant.
Qed.

Definition rename_given (r : renaming) (given : option (option variable))
    : option (option variable) :=
  option_map (option_map (rename_variable r)) given.

Lemma given_var_by_equivariant (r : renaming) (k : continuation) (i : nat)
    (ac : apply_cont) :
  given_var_by (rename_continuation r k) i (rename_apply_cont r ac)
  = rename_given r (given_var_by k i ac).
Proof.
  unfold given_var_by, rename_apply_cont.
  cbn [ac_continuation ac_args].
  rewrite rename_continuation_eqb, nth_error_map.
  destruct (Pos.eqb (ac_continuation ac) k); [ | reflexivity ].
  destruct (nth_error (ac_args ac) i) as [[y | sym | c] | ]; reflexivity.
Qed.

Fixpoint first_given_var_equivariant (r : renaming) (k : continuation)
    (i : nat) (e : expr) {struct e} :
  first_given_var (rename_continuation r k) i (rename_expr r e)
  = rename_given r (first_given_var k i e)
with handler_first_given_var_equivariant (r : renaming) (k : continuation)
    (i : nat) (h : continuation_handler) {struct h} :
  handler_first_given_var (rename_continuation r k) i (rename_handler r h)
  = rename_given r (handler_first_given_var k i h).
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [rename_expr first_given_var]; try reflexivity.
    + apply first_given_var_equivariant.
    + apply first_given_var_equivariant.
    + rewrite handler_first_given_var_equivariant,
        first_given_var_equivariant.
      destruct (handler_first_given_var k i hh); reflexivity.
    + rewrite first_given_var_equivariant.
      assert (Hhandlers :
        first_answer
          (fun '(_, h) =>
             handler_first_given_var (rename_continuation r k) i h)
          (map (fun '(k0, h) => (rename_continuation r k0, rename_handler r h))
             handlers)
        = rename_given r
            (first_answer (fun '(_, h) => handler_first_given_var k i h)
               handlers)).
      { induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
        cbn [map first_answer]. rewrite handler_first_given_var_equivariant.
        destruct (handler_first_given_var k i hh); [ reflexivity | exact IH ]. }
      rewrite Hhandlers.
      destruct (first_answer (fun '(_, h) => handler_first_given_var k i h)
                  handlers);
        reflexivity.
    + apply given_var_by_equivariant.
    + induction arms as [ | [n ac] arms IH]; [ reflexivity | ].
      cbn [map first_answer fst snd]. rewrite given_var_by_equivariant.
      destruct (given_var_by k i ac); [ reflexivity | exact IH ].
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_first_given_var].
    apply first_given_var_equivariant.
Qed.

Lemma drop_arg_of_equivariant (r : renaming) (k : continuation) (i : nat)
    (ac : apply_cont) :
  drop_arg_of (rename_continuation r k) i (rename_apply_cont r ac)
  = rename_apply_cont r (drop_arg_of k i ac).
Proof.
  unfold drop_arg_of, rename_apply_cont.
  cbn [ac_continuation ac_args ac_trap_action].
  rewrite rename_continuation_eqb.
  destruct (Pos.eqb (ac_continuation ac) k); [ | reflexivity ].
  cbn [ac_continuation ac_args ac_trap_action]. rewrite drop_nth_map.
  reflexivity.
Qed.

Fixpoint drop_arg_equivariant (r : renaming) (k : continuation) (i : nat)
    (e : expr) {struct e} :
  drop_arg (rename_continuation r k) i (rename_expr r e)
  = rename_expr r (drop_arg k i e)
with drop_arg_in_handler_equivariant (r : renaming) (k : continuation)
    (i : nat) (h : continuation_handler) {struct h} :
  drop_arg_in_handler (rename_continuation r k) i (rename_handler r h)
  = rename_handler r (drop_arg_in_handler k i h).
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [rename_expr drop_arg]; try reflexivity.
    + rewrite drop_arg_equivariant. reflexivity.
    + rewrite drop_arg_equivariant. reflexivity.
    + rewrite drop_arg_in_handler_equivariant, drop_arg_equivariant.
      reflexivity.
    + rewrite drop_arg_equivariant. f_equal.
      induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
      cbn [map]. rewrite drop_arg_in_handler_equivariant, IH. reflexivity.
    + rewrite drop_arg_of_equivariant. reflexivity.
    + f_equal. induction arms as [ | [n ac] arms IH]; [ reflexivity | ].
      cbn [map fst snd]. rewrite drop_arg_of_equivariant, IH. reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler drop_arg_in_handler].
    rewrite drop_arg_equivariant. reflexivity.
Qed.

Definition rename_unaliased (r : renaming)
    (result : option (continuation_handler * expr))
    : option (continuation_handler * expr) :=
  option_map (fun '(h, body) => (rename_handler r h, rename_expr r body))
    result.

Lemma unalias_param_equivariant (r : renaming) (i : nat) (k : continuation)
    (h : continuation_handler) (body : expr) :
  unalias_param i (rename_continuation r k) (rename_handler r h)
    (rename_expr r body)
  = rename_unaliased r (unalias_param i k h body).
Proof.
  destruct h as [params metadata handler].
  cbn [rename_handler unalias_param].
  rewrite nth_error_map, first_given_var_equivariant.
  destruct (nth_error params i) as [p | ]; [ | reflexivity ].
  cbn [option_map].
  destruct (nth_error (hm_params_kinds metadata) i) as [kind | ];
    [ | reflexivity ].
  destruct (first_given_var k i body) as [[x | ] | ]; try reflexivity.
  cbn [rename_given option_map].
  rewrite all_give_var_equivariant, among_rename_variable, drop_nth_map,
    among_rename_variable, drop_arg_equivariant.
  destruct
    (negb (hm_is_exn_handler metadata) && all_give_var k i x true body
     && negb (among x params) && negb (among p (drop_nth i params)));
    reflexivity.
Qed.

Lemma unalias_from_equivariant (r : renaming) (i : nat) :
  ∀ (k : continuation) (h : continuation_handler) (body : expr),
    unalias_from i (rename_continuation r k) (rename_handler r h)
      (rename_expr r body)
    = (rename_handler r (fst (unalias_from i k h body)),
       rename_expr r (snd (unalias_from i k h body))).
Proof.
  induction i as [ | i IH]; intros k h body; cbn [unalias_from];
    [ reflexivity | ].
  rewrite unalias_param_equivariant.
  destruct (unalias_param i k h body) as [[h' body'] | ];
    cbn [rename_unaliased option_map]; apply IH.
Qed.

Fixpoint unalias_params_equivariant_aux (r : renaming) (e : expr) :
  unalias_params (rename_expr r e) = rename_expr r (unalias_params e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    cbn [rename_expr rename_handler unalias_params]; try reflexivity.
  - rewrite unalias_params_equivariant_aux. reflexivity.
  - rewrite unalias_params_equivariant_aux. reflexivity.
  - rewrite !unalias_params_equivariant_aux, length_map.
    pose proof
      (unalias_from_equivariant r (length params) k
         (Handler params metadata (unalias_params handler))
         (unalias_params body))
      as Hfrom.
    cbn [rename_handler] in Hfrom. rewrite Hfrom.
    destruct
      (unalias_from (length params) k
         (Handler params metadata (unalias_params handler))
         (unalias_params body))
      as [h' body'].
    reflexivity.
  - rewrite unalias_params_equivariant_aux. reflexivity.
Qed.

Lemma unalias_params_renamed : rewrite_equivariant unalias_params.
Proof. exact unalias_params_equivariant_aux. Qed.

(* ======================================================================== *)
(* The pass keeps scope                                                     *)
(* ======================================================================== *)

Lemma in_nth_or_drop_nth {A : Type} (i : nat) :
  ∀ (l : list A) (p a : A),
    nth_error l i = Some p -> In a l -> a = p ∨ In a (drop_nth i l).
Proof.
  induction i as [ | i IH]; intros [ | b l] p a; cbn [nth_error];
    try discriminate.
  - intros [= ->] [-> | Hin]; [ left; reflexivity | right; exact Hin ].
  - intros Hnth [-> | Hin]; [ right; left; reflexivity | ].
    destruct (IH l p a Hnth Hin) as [-> | Hin'];
      [ left; reflexivity | right; right; exact Hin' ].
Qed.

Lemma drop_arg_of_free_variables (k : continuation) (i : nat)
    (ac : apply_cont) :
  incl (free_variables_of_apply_cont (drop_arg_of k i ac))
    (free_variables_of_apply_cont ac).
Proof.
  unfold drop_arg_of.
  destruct (Pos.eqb (ac_continuation ac) k); [ | apply incl_refl ].
  unfold free_variables_of_apply_cont, free_variables_of_simples.
  cbn [ac_args]. intros a Ha. apply in_flat_map in Ha as (s & Hs & Ha).
  apply in_flat_map. exists s.
  split; [ exact (in_drop_nth i _ s Hs) | exact Ha ].
Qed.

Lemma drop_arg_of_continuations (k : continuation) (i : nat)
    (ac : apply_cont) :
  apply_cont_continuations (drop_arg_of k i ac) = apply_cont_continuations ac.
Proof.
  unfold drop_arg_of.
  destruct (Pos.eqb (ac_continuation ac) k); reflexivity.
Qed.

Fixpoint drop_arg_scoped (k : continuation) (i : nat) (e : expr) {struct e} :
  scoped e (drop_arg k i e)
with drop_arg_in_handler_scoped (k : continuation) (i : nat)
    (h : continuation_handler) {struct h} :
  scoped_handler h (drop_arg_in_handler k i h).
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [drop_arg]; try apply scoped_refl.
    + apply scoped_let; [ apply incl_refl | apply drop_arg_scoped ].
    + apply scoped_let_static;
        [ apply scoped_bindings_refl | apply drop_arg_scoped ].
    + apply scoped_let_cont;
        [ apply drop_arg_in_handler_scoped | apply drop_arg_scoped ].
    + apply scoped_let_cont_recursive; [ | | apply drop_arg_scoped ].
      * rewrite map_map. apply map_ext. intros [k' hh]. reflexivity.
      * induction handlers as [ | [k' hh] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply drop_arg_in_handler_scoped | exact IH ].
    + intros _.
      cbn [code_closed free_variables_of_expr free_continuations_of_expr].
      split; [ reflexivity | split ].
      * apply drop_arg_of_free_variables.
      * rewrite drop_arg_of_continuations. apply incl_refl.
    + intros _.
      cbn [code_closed free_variables_of_expr free_continuations_of_expr].
      split; [ reflexivity | split ].
      * apply incl_app_app; [ apply incl_refl | ].
        induction arms as [ | [n ac] arms IH]; [ apply incl_refl | ].
        cbn [map flat_map snd].
        apply incl_app_app; [ apply drop_arg_of_free_variables | exact IH ].
      * induction arms as [ | [n ac] arms IH]; [ apply incl_refl | ].
        cbn [map flat_map snd]. rewrite drop_arg_of_continuations.
        apply incl_app_app; [ apply incl_refl | exact IH ].
  - destruct h as [params metadata handler]. cbn [drop_arg_in_handler].
    apply scoped_handler_intro, drop_arg_scoped.
Qed.

(* The variable that the applications of [k] give is free in a term
   that applies [k]. *)
Lemma given_by_free (k : continuation) (i : nat) (x : variable) (ok : bool)
    (ac : apply_cont) (given : option variable) :
  given_var_by k i ac = Some given ->
  apply_cont_gives_var k i x ok ac = true ->
  ok = true ∧ In x (free_variables_of_apply_cont ac).
Proof.
  unfold given_var_by, apply_cont_gives_var.
  destruct (Pos.eqb (ac_continuation ac) k); [ | discriminate ].
  intros _ Hgives. apply andb_true_iff in Hgives as [_ Hgives].
  destruct (nth_error (ac_args ac) i) as [[y | sym | c] | ] eqn:Hnth;
    try discriminate.
  apply andb_true_iff in Hgives as [Hok Hy]. apply Pos.eqb_eq in Hy.
  subst y. split; [ exact Hok | ].
  unfold free_variables_of_apply_cont, free_variables_of_simples.
  apply in_flat_map. exists (Var x).
  split; [ exact (nth_error_In _ _ Hnth) | left; reflexivity ].
Qed.

Fixpoint given_free (k : continuation) (i : nat) (x : variable) (e : expr)
    {struct e} :
  ∀ (ok : bool) (given : option variable),
    first_given_var k i e = Some given ->
    all_give_var k i x ok e = true ->
    ok = true ∧ In x (free_variables_of_expr e)
with handler_given_free (k : continuation) (i : nat) (x : variable)
    (h : continuation_handler) {struct h} :
  ∀ (ok : bool) (given : option variable),
    handler_first_given_var k i h = Some given ->
    handler_all_give_var k i x ok h = true ->
    ok = true ∧ In x (free_variables_of_handler h).
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      intros ok given;
      cbn [first_given_var all_give_var free_variables_of_expr];
      try discriminate.
    + intros Hfirst Hgive.
      destruct (given_free k i x body _ given Hfirst Hgive) as [Hboth Hin].
      apply andb_true_iff in Hboth as [Hok Hne].
      apply negb_true_iff, Pos.eqb_neq in Hne.
      split; [ exact Hok | ]. apply in_or_app. right. apply in_without.
      split; [ exact Hin | ]. intros [Heq | []]. congruence.
    + intros Hfirst Hgive.
      destruct (given_free k i x body ok given Hfirst Hgive) as [Hok Hin].
      split; [ exact Hok | ]. apply in_or_app. right. exact Hin.
    + intros Hfirst Hgive. apply andb_true_iff in Hgive as [Hgive Hbody].
      apply andb_true_iff in Hgive as [_ Hhh].
      destruct (handler_first_given_var k i hh) as [given' | ] eqn:Hhandler.
      * destruct (handler_given_free k i x hh ok given' Hhandler Hhh)
          as [Hok Hin].
        split; [ exact Hok | ]. apply in_or_app. left. exact Hin.
      * destruct (given_free k i x body ok given Hfirst Hbody) as [Hok Hin].
        split; [ exact Hok | ]. apply in_or_app. right. exact Hin.
    + intros Hfirst Hgive. apply andb_true_iff in Hgive as [Hhandlers Hbody].
      destruct
        (first_answer (fun '(_, h) => handler_first_given_var k i h) handlers)
        as [given' | ] eqn:Hsome.
      * clear Hfirst Hbody.
        assert (Hin :
          ok = true
          ∧ In x
              (flat_map (fun '(_, h) => free_variables_of_handler h)
                 handlers)).
        { induction handlers as [ | [k' hh] handlers IH];
            cbn [first_answer forallb flat_map] in Hsome, Hhandlers |- *;
            [ discriminate | ].
          apply andb_true_iff in Hhandlers as [Hhead Hrest].
          apply andb_true_iff in Hhead as [_ Hhh].
          destruct (handler_first_given_var k i hh) as [given'' | ]
            eqn:Hhandler.
          - destruct (handler_given_free k i x hh ok given'' Hhandler Hhh)
              as [Hok Hin].
            split; [ exact Hok | ]. apply in_or_app. left. exact Hin.
          - destruct (IH Hsome Hrest) as [Hok Hin].
            split; [ exact Hok | ]. apply in_or_app. right. exact Hin. }
        destruct Hin as [Hok Hin].
        split; [ exact Hok | ]. apply in_or_app. left. exact Hin.
      * destruct (given_free k i x body ok given Hfirst Hbody) as [Hok Hin].
        split; [ exact Hok | ]. apply in_or_app. right. exact Hin.
    + apply given_by_free.
    + intros Hfirst Hgive.
      assert (Hin :
        ok = true
        ∧ In x
            (flat_map (fun arm => free_variables_of_apply_cont (snd arm))
               arms)).
      { induction arms as [ | [n ac] arms IH];
          cbn [first_answer forallb flat_map snd] in Hfirst, Hgive |- *;
          [ discriminate | ].
        apply andb_true_iff in Hgive as [Hhead Hrest].
        destruct (given_var_by k i ac) as [given' | ] eqn:Hby.
        - destruct (given_by_free k i x ok ac given' Hby Hhead) as [Hok Hin].
          split; [ exact Hok | ]. apply in_or_app. left. exact Hin.
        - destruct (IH Hfirst Hrest) as [Hok Hin].
          split; [ exact Hok | ]. apply in_or_app. right. exact Hin. }
      destruct Hin as [Hok Hin].
      split; [ exact Hok | ]. apply in_or_app. right. exact Hin.
  - destruct h as [params metadata handler]. intros ok given.
    cbn [handler_first_given_var handler_all_give_var
         free_variables_of_handler].
    intros Hfirst Hgive.
    destruct (given_free k i x handler _ given Hfirst Hgive) as [Hboth Hin].
    apply andb_true_iff in Hboth as [Hok Hnot].
    apply negb_true_iff in Hnot.
    split; [ exact Hok | ]. apply in_without.
    split; [ exact Hin | ]. intros Hparam. apply among_In in Hparam.
    congruence.
Qed.

Lemma unalias_param_scoped (i : nat) (k : continuation)
    (h : continuation_handler) (body : expr) (h' : continuation_handler)
    (body' : expr) :
  unalias_param i k h body = Some (h', body') ->
  scoped (Let_cont_non_recursive k h body)
    (Let_cont_non_recursive k h' body').
Proof.
  destruct h as [params metadata handler]. unfold unalias_param.
  destruct (nth_error params i) as [p | ] eqn:Hparam; [ | discriminate ].
  destruct (nth_error (hm_params_kinds metadata) i) as [kind | ];
    [ | discriminate ].
  destruct (first_given_var k i body) as [[x | ] | ] eqn:Hfirst;
    try discriminate.
  destruct
    (negb (hm_is_exn_handler metadata) && all_give_var k i x true body
     && negb (among x params) && negb (among p (drop_nth i params)))
    eqn:Hcond; [ | discriminate ].
  intros [= <- <-].
  apply andb_true_iff in Hcond as [Hcond _].
  apply andb_true_iff in Hcond as [Hcond _].
  apply andb_true_iff in Hcond as [_ Hgive].
  destruct (given_free k i x body true (Some x) Hfirst Hgive) as [_ Hx].
  intros Hclosed.
  cbn [code_closed handler_code_closed] in Hclosed |- *.
  apply andb_true_iff in Hclosed as [Hhandler Hbody].
  destruct (drop_arg_scoped k i body Hbody) as (Hbody' & Hv & Hk).
  split; [ rewrite Hhandler, Hbody'; reflexivity | ].
  cbn [free_variables_of_expr free_variables_of_handler
       free_variables_of_named free_variables_of_simple
       free_continuations_of_expr free_continuations_of_handler].
  split.
  - intros a Ha. apply in_or_app. apply in_app_or in Ha as [Ha | Ha];
      [ | right; exact (Hv a Ha) ].
    apply in_without in Ha as [Ha Hnot].
    apply in_app_or in Ha as [[<- | []] | Ha]; [ right; exact Hx | ].
    apply in_without in Ha as [Ha Hne].
    left. apply in_without. split; [ exact Ha | ].
    intros Hin.
    destruct (in_nth_or_drop_nth i params p a Hparam Hin) as [-> | Hin'];
      [ apply Hne; left; reflexivity | exact (Hnot Hin') ].
  - apply incl_app_app; [ apply incl_refl | apply incl_without, Hk ].
Qed.

Lemma unalias_from_scoped (i : nat) :
  ∀ (k : continuation) (h : continuation_handler) (body : expr),
    scoped (Let_cont_non_recursive k h body)
      (Let_cont_non_recursive k (fst (unalias_from i k h body))
         (snd (unalias_from i k h body))).
Proof.
  induction i as [ | i IH]; intros k h body; cbn [unalias_from];
    [ apply scoped_refl | ].
  destruct (unalias_param i k h body) as [[h' body'] | ] eqn:Hparam;
    [ | apply IH ].
  exact (scoped_trans _ _ _ (unalias_param_scoped i k h body h' body' Hparam)
    (IH k h' body')).
Qed.

Fixpoint unalias_params_scoped (e : expr) : scoped e (unalias_params e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    cbn [unalias_params]; try apply scoped_refl.
  - apply scoped_let; [ apply incl_refl | apply unalias_params_scoped ].
  - apply scoped_let_static;
      [ apply scoped_bindings_refl | apply unalias_params_scoped ].
  - pose proof
      (unalias_from_scoped (length params) k
         (Handler params metadata (unalias_params handler))
         (unalias_params body))
      as Hfrom.
    destruct
      (unalias_from (length params) k
         (Handler params metadata (unalias_params handler))
         (unalias_params body))
      as [h' body'].
    refine (scoped_trans _ _ _ _ Hfrom).
    apply scoped_let_cont;
      [ apply scoped_handler_intro, unalias_params_scoped
      | apply unalias_params_scoped ].
  - apply scoped_let_cont_recursive;
      [ reflexivity | apply scoped_handlers_refl
      | apply unalias_params_scoped ].
Qed.

Lemma unalias_params_scope : keeps_scope unalias_params.
Proof. apply keeps_scope_intro, unalias_params_scoped. Qed.
