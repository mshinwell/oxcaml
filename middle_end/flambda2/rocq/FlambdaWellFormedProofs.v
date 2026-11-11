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

(* Proofs of the statements of FlambdaWellFormedSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaWellFormedSpec.
Import ListNotations.

Lemma statics_extend_refl (statics : static_env) :
  statics_extend statics statics.
Proof. split; auto. Qed.

Lemma statics_extend_trans (statics statics' statics'' : static_env) :
  statics_extend statics statics' ->
  statics_extend statics' statics'' ->
  statics_extend statics statics''.
Proof. intros [Hcode Hvalues] [Hcode' Hvalues']. split; auto. Qed.

(* A binding added for a name that was not bound. *)
Lemma lookup_fresh {A : Type} (name fresh : positive) (a added : A)
    (bindings : list (positive * A)) :
  lookup fresh bindings = None ->
  lookup name bindings = Some a ->
  lookup name ((fresh, added) :: bindings) = Some a.
Proof.
  intros Hfresh Hname. simpl.
  destruct (Pos.eqb_spec name fresh) as [-> | _]; [ congruence | exact Hname ].
Qed.

Lemma eval_static_bindings_extend (vars : env)
    (bindings : list static_binding) :
  ∀ statics extended : static_env,
    eval_static_bindings vars bindings statics = Some extended ->
    statics_extend statics extended.
Proof.
  induction bindings as [ | binding bindings IH]; intros statics extended;
    simpl.
  - intros [= <-]. apply statics_extend_refl.
  - destruct binding as [id c | id | sym const].
    + destruct (lookup id (static_code statics)) eqn:Hbound;
        [ discriminate | ].
      intros Heval. refine (statics_extend_trans _ _ _ _ (IH _ _ Heval)).
      split; simpl; [ | auto ].
      intros id' c' Hid'. exact (lookup_fresh id' id c' c _ Hbound Hid').
    + apply IH.
    + destruct (lookup sym (static_values statics)) eqn:Hbound;
        [ discriminate | ].
      destruct (eval_static_const vars const) as [allocated | ]; simpl;
        [ | discriminate ].
      intros Heval. refine (statics_extend_trans _ _ _ _ (IH _ _ Heval)).
      split; simpl; [ auto | ].
      intros s a Hs. exact (lookup_fresh s sym a allocated _ Hbound Hs).
Qed.

Theorem step_extends_statics : step_extends_statics_statement.
Proof.
  intros [e vars conts statics] s' Hstep.
  destruct e
    as [x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl in Hstep.
  - destruct (eval_named statics vars d); [ | discriminate ].
    injection Hstep as <-. apply statics_extend_refl.
  - destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Heval; [ | discriminate ].
    injection Hstep as <-.
    exact (eval_static_bindings_extend vars bindings statics extended Heval).
  - injection Hstep as <-. apply statics_extend_refl.
  - injection Hstep as <-. apply statics_extend_refl.
  - destruct (eval_simple vars (ap_callee ap)) as [callee | ];
      [ | discriminate ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | discriminate ].
    destruct (call_function_cases callee (ap_call_kind ap) vs statics)
      as [Hundefined | (body & callee_vars & ret & exn & Hcall)].
    + rewrite Hundefined in Hstep. discriminate.
    + rewrite Hcall in Hstep. injection Hstep as <-.
      apply statics_extend_refl.
  - destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | discriminate ].
    unfold apply_continuation, apply_cont_value in Hstep.
    destruct (resolve (ac_continuation ac) conts)
      as [[params handler] def_vars def_conts recursive | k];
      [ | discriminate ].
    destruct (bind_params params vs def_vars); [ | discriminate ].
    injection Hstep as <-. apply statics_extend_refl.
  - destruct (eval_simple vars scrutinee) as [v | ]; [ | discriminate ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | discriminate ].
    destruct (find_arm i arms); [ | discriminate ].
    injection Hstep as <-. apply statics_extend_refl.
  - discriminate.
Qed.

Theorem run_extends_statics : run_extends_statics_statement.
Proof.
  intros n. induction n as [ | n IH]; intros s s'; simpl.
  - intros [= <-]. apply statics_extend_refl.
  - destruct (step s) as [next | k vs | ] eqn:Hstep; try discriminate.
    intros Hrun.
    exact (statics_extend_trans _ _ _ (step_extends_statics s next Hstep)
      (IH next s' Hrun)).
Qed.
