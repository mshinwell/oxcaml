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

(* Proofs for FlambdaLiftFromArmsSpec.v. Nothing here needs review.

   The second run first binds the group at the head of the unit. From
   then on the two runs are those of FlambdaLiftFromCodeProofs.v, with
   no code named: the second expression is the first with its [Let]s
   made aliases, and the symbols of those [Let]s are bound to what the
   [Let]s make (FlambdaLiftFromCodeProofs.eval_lifted_out_bindings).
   So the first step of the first run is answered by two of the second,
   and every other step by the step that
   FlambdaLiftFromCodeProofs.lifted_out_step gives. *)

From Stdlib Require Import ZArith List Bool Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaSimulationProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaWellFormedSpec FlambdaWellFormedProofs FlambdaUnusedStaticsSpec
  FlambdaLiftSpec FlambdaLiftProofs FlambdaLiftFromCodeSpec
  FlambdaLiftFromCodeProofs FlambdaLiftFromArmsSpec.
Import ListNotations.

(* ======================================================================== *)
(* The run of the unit lifted                                               *)
(* ======================================================================== *)

Section Unit.

Variable u : unit_interface.
Variable lets : list (path * lift_to).
Variable e : expr.

(* The unit lifted, where something is lifted. *)
Let bindings : list static_binding := lifted_out_bindings lets root e.
Let lifted : expr := Let_static bindings (lift_from_code [] lets root e).

Hypothesis Hwf : well_formed_unit u lifted = true.
Hypothesis Hplain : exits_plain [] e = true.
Hypothesis Hsome : bindings <> [].

(* The second state is one that the run of the unit lifted reaches. *)
Definition reached_lifted (s' : state) : Prop :=
  ∃ n : nat, run n (State lifted [] [] empty_static_env empty_heap) = Step s'.

(* The two states are the initial ones; or they are related as in
   FlambdaLiftFromCodeProofs.v, the second is reached, and the first is
   one of a unit that exits with symbols and constants only. *)
Definition unit_lifted (s s' : state) : Prop :=
  (s = State e [] [] empty_static_env empty_heap
   ∧ s' = State lifted [] [] empty_static_env empty_heap)
  ∨ (state_lifted_out [] s s' ∧ reached_lifted s' ∧ plain_state s).

(* The first step of the second run binds the group; the states are
   then related. *)
Lemma head_bound :
  ∃ statics' : static_env,
    step (State lifted [] [] empty_static_env empty_heap)
    = Step (State (lift_from_code [] lets root e) [] [] statics' empty_heap)
    ∧ state_lifted_out [] (State e [] [] empty_static_env empty_heap)
        (State (lift_from_code [] lets root e) [] [] statics' empty_heap).
Proof.
  pose proof (well_formed_never_faults u lifted 0 _ Hwf eq_refl) as Hfault.
  unfold static_fault in Hfault. simpl in Hfault.
  apply orb_false_iff in Hfault as [_ Hfault].
  destruct (no_rebinding empty_static_env _ Hfault) as [Hdistinct Hfresh].
  destruct (eval_lifted_out_bindings [] lets root e empty_static_env
              Hdistinct Hfresh)
    as (statics' & Heval & Hcode & Hbound).
  exists statics'. split.
  - unfold lifted. rewrite step_let_static. fold bindings in Heval.
    rewrite Heval. reflexivity.
  - apply State_lifted_out;
      [ intros x v [=] | constructor | | exact Hbound ].
    split; [ intros id; rewrite Hcode; reflexivity | ].
    split; [ intros s a [=] | intros id c [=] ].
Qed.

(* A unit of which something is lifted begins with a [Let] or a
   [Let_cont]: its first step is not an exit. *)
Lemma first_step_no_exit (k : continuation) (vs : list value) (hp : heap) :
  step (State e [] [] empty_static_env empty_heap) <> Exit k vs hp.
Proof.
  unfold bindings in Hsome.
  destruct e
    as [ x xkind d body | group body | k0 h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl in Hsome; try (exfalso; apply Hsome; reflexivity).
  - rewrite step_let.
    destruct (eval_named empty_static_env [] d) as [v | ]; [ | discriminate ].
    destruct (kind_eqb (kind_of_value v) xkind); discriminate.
  - rewrite step_let_static.
    destruct (eval_static_bindings [] group empty_static_env); discriminate.
  - rewrite step_let_cont_non_recursive. discriminate.
  - rewrite step_let_cont_recursive.
    destruct (handlers_bind_statics handlers); discriminate.
Qed.

(* A step of the first state is answered by the second: an exit by an
   exit with the same values, a step by one or more steps. *)
Lemma unit_lifted_step (s s' : state) :
  unit_lifted s s' ->
  answered unit_lifted (fun _ vs vs' => vs' = vs) (step s) s'.
Proof.
  intros [[-> ->] | (Hlifted & [n Hn] & Hplain_s)].
  - destruct head_bound as (statics' & Hhead & Hrelated).
    assert (Hreached :
      reached_lifted
        (State (lift_from_code [] lets root e) [] [] statics' empty_heap)).
    { exists 1. simpl. rewrite Hhead. reflexivity. }
    destruct Hreached as [n Hn].
    pose proof (lifted_out_step [] _ _ Hrelated
      (well_formed_never_faults u _ n _ Hwf Hn)) as Hanswer.
    pose proof (plain_step _ (plain_initial e Hplain)) as Hstep.
    pose proof first_step_no_exit as Hno_exit.
    destruct (step (State e [] [] empty_static_env empty_heap)) as
      [t | k vs | ];
      unfold answered in *; [ | | exact I ].
    + destruct Hanswer as (m & t' & Hrun & Ht).
      exists (S m), t'. split.
      * change (S (S m)) with (1 + S m). rewrite run_add. simpl.
        rewrite Hhead. exact Hrun.
      * right. split; [ exact Ht | ]. split; [ | exact Hstep ].
        exists (n + S m). rewrite run_add, Hn. exact Hrun.
    + exfalso. exact (Hno_exit k vs hp eq_refl).
  - pose proof (lifted_out_step [] s s' Hlifted
      (well_formed_never_faults u _ n s' Hwf Hn)) as Hanswer.
    pose proof (plain_step s Hplain_s) as Hstep.
    destruct (step s) as [t | k vs | ]; unfold answered in *; [ | | exact I ].
    + destruct Hanswer as (m & t' & Hrun & Ht).
      exists m, t'. split; [ exact Hrun | ].
      right. split; [ exact Ht | ]. split; [ | exact Hstep ].
      exists (n + S m). rewrite run_add, Hn. exact Hrun.
    + destruct Hanswer as (vs' & Hexit & Hvs).
      exists vs'. split; [ exact Hexit | ].
      exact (plain_values_lifted _ vs vs' Hstep Hvs).
Qed.

Lemma unit_lifted_refines :
  refines (State e [] [] empty_static_env empty_heap)
    (State lifted [] [] empty_static_env empty_heap).
Proof.
  apply (stuttering_refines unit_lifted (fun _ vs vs' => vs' = vs)
           unit_lifted_step).
  - intros last vs vs' Hsame. exact Hsame.
  - left. split; reflexivity.
Qed.

End Unit.

Theorem lift_to_head_unit_program_refines :
  lift_to_head_unit_program_refines_statement.
Proof.
  intros u lets e e'. unfold lift_to_head_unit. cbv zeta.
  destruct (exits_plain [] e) eqn:Hplain; [ | discriminate ].
  destruct (well_formed_unit u (lift_to_head lets e)) eqn:Hwf;
    [ | discriminate ].
  intros [= <-]. unfold program_refines.
  destruct (lifted_out_bindings lets root e) as [ | binding rest]
    eqn:Hbindings.
  - unfold lift_to_head. cbv zeta. rewrite Hbindings. apply refines_refl.
  - assert (Hsome : lifted_out_bindings lets root e <> [])
      by (rewrite Hbindings; discriminate).
    assert (Hshape :
      lift_to_head lets e
      = Let_static (lifted_out_bindings lets root e)
          (lift_from_code [] lets root e)).
    { unfold lift_to_head. cbv zeta. rewrite Hbindings. reflexivity. }
    rewrite Hshape in Hwf |- *.
    exact (unit_lifted_refines u lets e Hwf Hplain Hsome).
Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

Theorem lift_to_head_equivariant : lift_to_head_equivariant_statement.
Proof.
  intros r lets e. unfold lift_to_head. cbv zeta.
  rewrite (lifted_out_bindings_equivariant r lets root e).
  destruct (lifted_out_bindings lets root e) as [ | binding rest]
    eqn:Hbindings; [ reflexivity | ].
  pose proof (lifted_out_bindings_closed r lets root e) as Hclosed.
  rewrite Hbindings in Hclosed. simpl in Hclosed |- *.
  rewrite Hclosed, (lift_from_code_equivariant r [] lets root e).
  reflexivity.
Qed.
