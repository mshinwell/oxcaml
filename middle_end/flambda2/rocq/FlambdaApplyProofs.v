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

(* Proofs of the statements of FlambdaApplySpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaApplySpec.
Import ListNotations.

Theorem apply_indirect_known : apply_indirect_known_statement.
Proof.
  intros callee args k exn v called slots vars conts statics Hcallee
    Hclosure.
  apply step_eq_equivalent. rewrite !step_apply. simpl. rewrite Hcallee.
  destruct (eval_simples vars args) as [vs | ]; [ | reflexivity ].
  unfold call_function. rewrite Hclosure, Pos.eqb_refl. reflexivity.
Qed.

(* ======================================================================== *)
(* Binding the parameters                                                   *)
(* ======================================================================== *)

Lemma eval_simple_extend (vars : env) (x : variable) (v : value) (s : simple) :
  ~ var_free_in_simple x s ->
  eval_simple ((x, v) :: vars) s = eval_simple vars s.
Proof.
  destruct s as [y | sym | c]; simpl; try reflexivity.
  intros Hnotfree. destruct (Pos.eqb_spec y x) as [-> | _]; [ | reflexivity ].
  exfalso. apply Hnotfree. reflexivity.
Qed.

Lemma eval_simples_extend (vars : env) (x : variable) (v : value)
    (args : list simple) :
  ~ var_free_in_simples x args ->
  eval_simples ((x, v) :: vars) args = eval_simples vars args.
Proof.
  unfold var_free_in_simples.
  induction args as [ | s args IH]; intros Hnotfree; simpl; [ reflexivity | ].
  rewrite eval_simple_extend, IH; [ reflexivity | | ];
    intros Hfree; apply Hnotfree;
    [ apply Exists_cons_tl | apply Exists_cons_hd ]; exact Hfree.
Qed.

(* The [Let]s of [let_params] run to the body, with the parameters bound as
   a call binds them, provided no parameter is free in an argument. *)
Lemma let_params_run (params : list variable) :
  ∀ (args : list simple) (vs : list value) (vars bound : env) (body : expr)
    (conts : cont_env) (statics : static_env),
    eval_simples vars args = Some vs ->
    (∀ param : variable,
      param ∈ params -> ~ var_free_in_simples param args) ->
    bind_params params vs vars = Some bound ->
    ∃ n : nat,
      run n (State (let_params params args body) vars conts statics)
      = Step (State body bound conts statics).
Proof.
  induction params as [ | param params IH];
    intros args vs vars bound body conts statics Hargs Hfresh Hbind.
  - destruct vs; [ | discriminate ]. injection Hbind as <-.
    exists 0. reflexivity.
  - destruct vs as [ | v vs]; [ discriminate | ].
    destruct args as [ | arg args]; [ discriminate | ].
    simpl in Hargs, Hbind.
    destruct (eval_simple vars arg) as [v' | ] eqn:Harg; [ | discriminate ].
    destruct (eval_simples vars args) as [vs' | ] eqn:Hrest;
      [ | discriminate ].
    simpl in Hargs. injection Hargs as -> ->.
    assert (Hnotfree : ~ var_free_in_simples param args).
    { intros Hfree. apply (Hfresh param (or_introl eq_refl)).
      apply Exists_cons_tl. exact Hfree. }
    destruct (IH args vs ((param, v) :: vars) bound body conts statics)
      as [n Hrun].
    + rewrite eval_simples_extend; assumption.
    + intros p Hin Hfree. apply (Hfresh p (or_intror Hin)).
      apply Exists_cons_tl. exact Hfree.
    + exact Hbind.
    + exists (S n). simpl. rewrite step_let. simpl. rewrite Harg.
      exact Hrun.
Qed.

(* ======================================================================== *)
(* Inlining                                                                 *)
(* ======================================================================== *)

(* The step of a direct call of a closure of the code named. *)
Lemma step_apply_direct (ap : apply_expr) (callee : value) (called : code_id)
    (slots : list (value_slot * value)) (vs : list value) (vars : env)
    (conts : cont_env) (statics : static_env) :
  eval_simple vars (ap_callee ap) = Some callee ->
  closure_of statics callee = Some (called, slots) ->
  eval_simples vars (ap_args ap) = Some vs ->
  ap_call_kind ap = Direct called ->
  step (State (Apply ap) vars conts statics)
  = match lookup called (static_code statics) with
    | Some c =>
      if binds_statics (code_body c) then Undefined
      else
        match
          bind_params (code_params c) vs [(code_my_closure c, callee)]
        with
        | Some callee_vars =>
          Step (State (code_body c) callee_vars
            [(code_return_continuation c,
              resolve (ap_continuation ap) conts);
             (code_exn_continuation c,
              resolve (ap_exn_continuation ap) conts)]
            statics)
        | None => Undefined
        end
    | None => Undefined
    end.
Proof.
  intros Hcallee Hclosure Hargs Hkind.
  rewrite step_apply, Hcallee, Hargs, Hkind.
  unfold call_function. rewrite Hclosure, Pos.eqb_refl.
  destruct (lookup called (static_code statics)); reflexivity.
Qed.

(* The call goes wrong, or it steps to the body under the callee's
   variables. The inlined body runs its [Let]s to the renamed body under
   those variables followed by the caller's. The two are a state and its
   renaming: the body's free variables are bound alike, and its return and
   exception continuations stand for those of the call. *)
Theorem inline : inline_statement.
Proof.
  intros ap called c r vars conts statics Hkind Hcode
    (Hclosed_vars & Hclosed_conts & Hvars & Hret & Hexn & Hmy_closure
     & Hparams & Harity & Hstatic).
  pose proof
    (step_undefined_refines (State (Apply ap) vars conts statics)
       (State (inlined_body c r ap) vars conts statics))
    as Hwrong.
  destruct (eval_simple vars (ap_callee ap)) as [callee | ] eqn:Hcallee;
    [ | apply Hwrong; rewrite step_apply, Hcallee; reflexivity ].
  destruct (eval_simples vars (ap_args ap)) as [vs | ] eqn:Hargs;
    [ | apply Hwrong; rewrite step_apply, Hcallee, Hargs; reflexivity ].
  destruct (closure_of statics callee) as [[called' slots] | ] eqn:Hclosure;
    [ | apply Hwrong; rewrite step_apply, Hcallee, Hargs;
        unfold call_function; rewrite Hclosure; reflexivity ].
  destruct (Pos.eqb_spec called' called) as [-> | Hother];
    [ | apply Hwrong; rewrite step_apply, Hcallee, Hargs, Hkind;
        unfold call_function; rewrite Hclosure;
        destruct (Pos.eqb_spec called' called);
        [ contradiction | reflexivity ] ].
  pose proof (step_apply_direct ap callee called slots vs vars conts statics
    Hcallee Hclosure Hargs Hkind) as Hstep.
  rewrite Hcode, Hstatic in Hstep.
  destruct (bind_params (code_params c) vs [(code_my_closure c, callee)])
    as [callee_vars | ] eqn:Hbind; [ | exact (Hwrong Hstep) ].
  apply equivalent_refines.
  (* the call *)
  eapply equivalent_trans; [ exact (step_equivalent _ _ Hstep) | ].
  (* the inlined body *)
  destruct (let_params_run (code_params c) (ap_args ap) vs
              ((code_my_closure c, callee) :: vars) (callee_vars ++ vars)
              (rename_expr r (code_body c)) conts statics)
    as [n Hrun].
  { rewrite eval_simples_extend; assumption. }
  { exact Hparams. }
  { exact (bind_params_app (code_params c) vs
      [(code_my_closure c, callee)] callee_vars vars Hbind). }
  apply equivalent_sym.
  eapply equivalent_trans.
  { apply (equivalent_of_run (S n) 0). unfold inlined_body.
    rewrite run_succ, step_let. simpl. rewrite Hcallee. exact Hrun. }
  apply equivalent_sym, renamed_equivalent, State_renamed.
  - intros x Hx. rewrite Hvars, lookup_app.
    destruct (bind_params_bound (code_params c) vs
                [(code_my_closure c, callee)] callee_vars x Hbind)
      as [v Hlookup]; [ | rewrite Hlookup; reflexivity ].
    destruct (Hclosed_vars x Hx) as [-> | Hin]; [ right | left; exact Hin ].
    exists callee. simpl. rewrite Pos.eqb_refl. reflexivity.
  - intros k Hk. unfold conts_agree_at.
    destruct (Hclosed_conts k Hk) as [-> | ->].
    + rewrite Hret. unfold resolve at 1. simpl. rewrite Pos.eqb_refl.
      apply Closure_same.
    + rewrite Hexn. unfold resolve at 1. simpl.
      destruct (Pos.eqb_spec (code_exn_continuation c)
                  (code_return_continuation c)) as [Heq | _].
      * rewrite <- Hexn, Heq, Hret. apply Closure_same.
      * rewrite Pos.eqb_refl. apply Closure_same.
Qed.

(* One step binds the code; then [inline]. *)
Theorem inline_let_code : inline_let_code_statement.
Proof.
  intros ap called c r Hkind Hinlinable vars conts statics.
  apply let_static_refines_step. simpl.
  destruct (lookup called (static_code statics)) as [bound | ];
    [ exact I | ].
  apply (inline ap called c r); [ exact Hkind | | exact Hinlinable ].
  simpl. rewrite Pos.eqb_refl. reflexivity.
Qed.

(* Swap the return continuation with the call's, then what the exception
   continuation has become with the call's. *)
Theorem inline_renaming_exists : inline_renaming_exists_statement.
Proof.
  intros ret exn k k_exn Hcode Hcall.
  exists (Renaming [] [(swap ret k exn, k_exn); (ret, k)]).
  split; [ reflexivity | ].
  unfold rename_continuation. simpl. split.
  - assert (Hk : swap ret k ret = k)
      by (unfold swap; rewrite Pos.eqb_refl; reflexivity).
    rewrite Hk. unfold swap at 1.
    destruct (Pos.eqb_spec k (swap ret k exn)) as [Heq | _].
    + rewrite <- Hk in Heq at 1. apply swap_injective in Heq.
      contradiction.
    + destruct (Pos.eqb_spec k k_exn); [ contradiction | reflexivity ].
  - unfold swap at 1. rewrite Pos.eqb_refl. reflexivity.
Qed.

(* ======================================================================== *)
(* Inlining as an equivalence                                               *)
(* ======================================================================== *)

Lemma eval_simples_length (vars : env) (args : list simple) :
  ∀ vs : list value,
    eval_simples vars args = Some vs -> length vs = length args.
Proof.
  induction args as [ | s args IH]; intros vs; simpl.
  - intros [= <-]. reflexivity.
  - destruct (eval_simple vars s); [ | discriminate ].
    destruct (eval_simples vars args) as [vs' | ]; [ | discriminate ].
    simpl. intros [= <-]. simpl. rewrite (IH vs' eq_refl). reflexivity.
Qed.

Lemma bind_params_some (params : list variable) :
  ∀ (vs : list value) (vars : env),
    length params = length vs ->
    ∃ bound : env, bind_params params vs vars = Some bound.
Proof.
  induction params as [ | p params IH]; intros [ | v vs] vars; simpl;
    try discriminate; [ eauto | ].
  intros [= Hlength]. apply IH, Hlength.
Qed.

(* Where an argument has no value, the [Let]s of [let_params] go wrong. *)
Lemma let_params_wrong (params : list variable) :
  ∀ (args : list simple) (vars : env) (body : expr) (conts : cont_env)
    (statics : static_env),
    length params = length args ->
    eval_simples vars args = None ->
    (∀ param : variable,
      param ∈ params -> ~ var_free_in_simples param args) ->
    behaves (State (let_params params args body) vars conts statics)
      Goes_wrong.
Proof.
  induction params as [ | param params IH];
    intros [ | arg args] vars body conts statics; simpl; try discriminate.
  intros [= Hlength] Hargs Hfresh.
  destruct (eval_simple vars arg) as [v | ] eqn:Harg.
  - destruct (eval_simples vars args) as [vs | ] eqn:Hrest;
      [ discriminate | ].
    apply (step_behaves _ Goes_wrong). rewrite step_let. simpl.
    rewrite Harg. apply (IH args _ body conts statics Hlength).
    + rewrite eval_simples_extend; [ exact Hrest | ].
      intros Hfree. apply (Hfresh param (or_introl eq_refl)).
      apply Exists_cons_tl. exact Hfree.
    + intros p Hin Hfree. apply (Hfresh p (or_intror Hin)).
      apply Exists_cons_tl. exact Hfree.
  - apply step_undefined_wrong. rewrite step_let. simpl. rewrite Harg.
    reflexivity.
Qed.

(* Two states that go wrong are equivalent. *)
Lemma both_wrong_equivalent (s s' : state) :
  behaves s Goes_wrong -> behaves s' Goes_wrong -> equivalent s s'.
Proof.
  intros Hs Hs' b. split; intros Hb.
  - rewrite (behaviour_unique _ _ _ Hb Hs). exact Hs'.
  - rewrite (behaviour_unique _ _ _ Hb Hs'). exact Hs.
Qed.

(* Where the callee is a closure of the code called, the call cannot be
   undefined for being of something else, and inlining is an equivalence:
   if the arguments have values the two meet as in [inline], and if not
   both go wrong. *)
Lemma inline_equivalent (ap : apply_expr) (called : code_id) (c : code)
    (r : renaming) (callee : value) (slots : list (value_slot * value))
    (vars : env) (conts : cont_env) (statics : static_env) :
  ap_call_kind ap = Direct called ->
  eval_simple vars (ap_callee ap) = Some callee ->
  closure_of statics callee = Some (called, slots) ->
  lookup called (static_code statics) = Some c ->
  inlinable ap c r ->
  equivalent (State (Apply ap) vars conts statics)
    (State (inlined_body c r ap) vars conts statics).
Proof.
  intros Hkind Hcallee Hclosure Hcode
    (Hclosed_vars & Hclosed_conts & Hvars & Hret & Hexn & Hmy_closure
     & Hparams & Harity & Hstatic).
  destruct (eval_simples vars (ap_args ap)) as [vs | ] eqn:Hargs.
  - pose proof (step_apply_direct ap callee called slots vs vars conts
      statics Hcallee Hclosure Hargs Hkind) as Hstep.
    rewrite Hcode, Hstatic in Hstep.
    destruct (bind_params_some (code_params c) vs
                [(code_my_closure c, callee)])
      as [callee_vars Hbind].
    { rewrite (eval_simples_length vars _ vs Hargs). exact Harity. }
    rewrite Hbind in Hstep.
    eapply equivalent_trans; [ exact (step_equivalent _ _ Hstep) | ].
    destruct (let_params_run (code_params c) (ap_args ap) vs
                ((code_my_closure c, callee) :: vars) (callee_vars ++ vars)
                (rename_expr r (code_body c)) conts statics)
      as [n Hrun].
    { rewrite eval_simples_extend; assumption. }
    { exact Hparams. }
    { exact (bind_params_app (code_params c) vs
        [(code_my_closure c, callee)] callee_vars vars Hbind). }
    apply equivalent_sym.
    eapply equivalent_trans.
    { apply (equivalent_of_run (S n) 0). unfold inlined_body.
      rewrite run_succ, step_let. simpl. rewrite Hcallee. exact Hrun. }
    apply equivalent_sym, renamed_equivalent, State_renamed.
    + intros x Hx. rewrite Hvars, lookup_app.
      destruct (bind_params_bound (code_params c) vs
                  [(code_my_closure c, callee)] callee_vars x Hbind)
        as [v Hlookup]; [ | rewrite Hlookup; reflexivity ].
      destruct (Hclosed_vars x Hx) as [-> | Hin]; [ right | left; exact Hin ].
      exists callee. simpl. rewrite Pos.eqb_refl. reflexivity.
    + intros k Hk. unfold conts_agree_at.
      destruct (Hclosed_conts k Hk) as [-> | ->].
      * rewrite Hret. unfold resolve at 1. simpl. rewrite Pos.eqb_refl.
        apply Closure_same.
      * rewrite Hexn. unfold resolve at 1. simpl.
        destruct (Pos.eqb_spec (code_exn_continuation c)
                    (code_return_continuation c)) as [Heq | _].
        -- rewrite <- Hexn, Heq, Hret. apply Closure_same.
        -- rewrite Pos.eqb_refl. apply Closure_same.
  - apply both_wrong_equivalent.
    + apply step_undefined_wrong. rewrite step_apply, Hcallee, Hargs.
      reflexivity.
    + apply (step_behaves _ Goes_wrong). unfold inlined_body.
      rewrite step_let. simpl. rewrite Hcallee.
      apply let_params_wrong; [ exact Harity | | exact Hparams ].
      rewrite eval_simples_extend; assumption.
Qed.
