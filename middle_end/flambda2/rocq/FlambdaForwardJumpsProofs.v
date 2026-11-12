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

(* Proofs of the statements of FlambdaForwardJumpsSpec.v. Nothing here
   needs review.

   The pass is FlambdaForwardSpec.forward_applications with fewer
   entries, and the relation between a term and its result is that of
   FlambdaForwardProofs.v, taken strict: every entry is for a
   continuation of no parameters whose handler gives no kinds. An
   application of the first term that goes on is then defined where
   the [Apply_cont] it becomes is: there is no argument to evaluate, no
   kind to test and nothing to bind. So the first run is undefined only
   where the second is, the rounds of FlambdaForwardProofs.v are read
   both ways ([fwd_round], [fwd_round_back]), and each term refines the
   other. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaNormaliseSpec
  FlambdaNormaliseProofs FlambdaRoundsProofs FlambdaUnusedParamsSpec
  FlambdaUnusedParamsProofs FlambdaParamAliasesSpec FlambdaParamAliasesProofs
  FlambdaForwardSpec FlambdaForwardProofs FlambdaForwardJumpsSpec.
Import ListNotations.

Fixpoint forward_jumps_binds_statics (e : expr) :
  ∀ F : forwards,
    binds_statics (forward_jumps_under F e) = binds_statics e.
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    intros F; simpl; try reflexivity.
  - apply forward_jumps_binds_statics.
  - rewrite forward_jumps_binds_statics. reflexivity.
  - rewrite !forward_jumps_binds_statics. reflexivity.
  - rewrite forward_jumps_binds_statics. f_equal.
    generalize (map (fun '(k, _) => (k, @None (list variable * apply_cont)))
                  handlers
                ++ F).
    intros F'.
    induction handlers as [ | [k [params metadata handler]] handlers IH];
      simpl; [ reflexivity | ].
    rewrite forward_jumps_binds_statics, IH. reflexivity.
Qed.

(* The entry that the pass makes is a strict one for the handler, which
   the body leaves alone. *)
Lemma jump_entry_fits (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler' body : expr) :
  entry_fits true k params metadata handler'
    (jump_entry k params metadata handler' body)
  ∧ (∀ x : variable,
      frozen_var (jump_entry k params metadata handler' body) x ->
      binds_var x body = false)
  ∧ (∀ k0 : continuation,
      frozen_cont (jump_entry k params metadata handler' body) k0 ->
      binds_cont k0 body = false).
Proof.
  unfold jump_entry.
  assert (Hnone :
    entry_fits true k params metadata handler' None
    ∧ (∀ x : variable, frozen_var None x -> binds_var x body = false)
    ∧ (∀ k0 : continuation, frozen_cont None k0 -> binds_cont k0 body = false)).
  { split; [ exact I | ].
    split; [ intros x (params0 & target & Hsome & _)
           | intros k0 (params0 & target & Hsome & _) ];
      discriminate Hsome. }
  destruct params as [ | p params]; [ | exact Hnone ].
  destruct (hm_params_kinds metadata) eqn:Hkinds; [ | exact Hnone ].
  apply forwarding_fits. intros _. split; [ reflexivity | exact Hkinds ].
Qed.

Fixpoint forward_jumps_fwd (e : expr) :
  ∀ F : forwards, safe F e -> fwd true F e (forward_jumps_under F e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    intros F Hsafe; simpl.
  - destruct (safe_let F x kind d body Hsafe) as [Hbody Hx].
    apply Fwd_let; [ exact Hx | apply forward_jumps_fwd, Hbody ].
  - apply Fwd_let_static, forward_jumps_fwd. exact Hsafe.
  - destruct (safe_let_cont F k params metadata handler body Hsafe)
      as (Hhandler & Hbody & Hparams & Hk).
    destruct
      (jump_entry_fits k params metadata
         (forward_jumps_under F handler) body)
      as (Hfits & Hvars & Hconts).
    apply (Fwd_let_cont true F k params metadata metadata handler
      (forward_jumps_under F handler)
      (jump_entry k params metadata (forward_jumps_under F handler)
         body));
      [ apply forward_jumps_fwd, Hhandler | reflexivity
      | exact Hparams | exact Hk | exact Hfits | ].
    apply forward_jumps_fwd, safe_cons; assumption.
  - destruct (safe_let_cont_recursive F handlers body Hsafe)
      as [Hbody Hhandlers].
    change (map (fun '(k, _) => (k, @None (list variable * apply_cont)))
              handlers)
      with (plain_forwards handlers).
    assert (Hall :
      Forall
        (fun kh =>
           safe (plain_forwards handlers ++ F) (handler_expr (snd kh))
           ∧ (∀ p : variable, p ∈ handler_params (snd kh) -> var_unfrozen F p)
           ∧ cont_unfrozen F (fst kh))
        handlers).
    { apply Forall_forall. intros [k [params metadata handler]] Hin.
      destruct (Hhandlers k params metadata handler Hin)
        as (Hhandler & Hparams & Hk).
      split; [ apply safe_plain, Hhandler | split; assumption ]. }
    apply Fwd_let_cont_recursive.
    + clear Hsafe Hhandlers. revert Hall.
      generalize (plain_forwards handlers ++ F). intros F' Hall.
      induction handlers as [ | [k [params metadata handler]] handlers IH];
        [ apply Forall2_nil | ].
      inversion Hall as [ | kh rest (Hhandler & Hparams & Hk) Hrest].
      subst kh rest.
      apply Forall2_cons; [ | exact (IH Hrest) ].
      simpl. split; [ reflexivity | ]. split; [ reflexivity | ].
      split; [ reflexivity | ].
      split; [ apply forward_jumps_fwd, Hhandler | ].
      split; assumption.
    + clear. unfold handlers_bind_statics.
      generalize (plain_forwards handlers ++ F). intros F'.
      induction handlers as [ | [k [params metadata handler]] handlers IH];
        simpl; [ reflexivity | ].
      rewrite forward_jumps_binds_statics, IH. reflexivity.
    + apply forward_jumps_fwd, safe_plain, Hbody.
  - apply Fwd_apply.
  - apply Fwd_apply_cont, goes_forward_apply_cont.
  - apply Fwd_switch. clear Hsafe.
    induction arms as [ | arm arms IH]; simpl; [ apply Forall2_nil | ].
    apply Forall2_cons; [ | exact IH ].
    split; [ reflexivity | apply goes_forward_apply_cont ].
  - apply Fwd_invalid.
Qed.

Theorem forward_jumps_equivalent : forward_jumps_equivalent_statement.
Proof.
  intros e vars conts statics hp.
  assert (Hrel :
    state_fwd true (State e vars conts statics hp)
      (State (forward_jumps e) vars conts statics hp)).
  { apply (State_fwd true []);
      [ apply forward_jumps_fwd, safe_none; reflexivity
      | intros k; apply Same_fwd | apply held_nil ]. }
  apply refines_antisymmetric.
  - exact (rounds_refines (state_fwd true) (fwd_round true) _ _ Hrel).
  - exact
      (rounds_refines (fun t' t => state_fwd true t t') fwd_round_back _ _
         Hrel).
Qed.
