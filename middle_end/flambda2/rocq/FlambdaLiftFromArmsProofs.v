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
   [Let]s make (FlambdaLiftFromCodeProofs.eval_lifted_out_bindings,
   which is of the bindings put once each).
   So the first step of the first run is answered by two of the second,
   and every other step by the step that
   FlambdaLiftFromCodeProofs.lifted_out_step gives. *)

From Stdlib Require Import ZArith List Bool Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaSimulationProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaWellFormedSpec FlambdaWellFormedProofs FlambdaUnusedStaticsSpec
  FlambdaImportsSpec FlambdaUnitFromProofs FlambdaLiftSpec FlambdaLiftProofs
  FlambdaLiftFromCodeSpec FlambdaLiftFromCodeProofs FlambdaLiftFromArmsSpec.
Import ListNotations.

(* ======================================================================== *)
(* The run of the unit lifted                                               *)
(* ======================================================================== *)

Section Unit.

Variable u : unit_interface.
Variable lets : list (path * lift_to).
Variable e : expr.

(* The static environment and the heap that the two runs start from:
   the environment holds no code and binds no name that the unit lifted
   binds. *)
Variable statics0 : static_env.
Variable hp0 : heap.

(* The unit lifted, where something is lifted. *)
Let bindings : list static_binding :=
  once_each [] (lifted_out_bindings lets root e).
Let lifted : expr := Let_static bindings (lift_from_code [] lets root e).

Hypothesis Hwf : well_formed_unit u lifted = true.
Hypothesis Hplain : exits_plain [] e = true.
Hypothesis Hsome : bindings <> [].
Hypothesis Hno_code : static_code statics0 = [].
Hypothesis Hfree : static_names_free_in statics0 lifted = true.

(* The second state is one that the run of the unit lifted reaches. *)
Definition reached_lifted (s' : state) : Prop :=
  ∃ n : nat, run n (State lifted [] [] statics0 hp0) = Step s'.

(* The two states are the initial ones; or they are related as in
   FlambdaLiftFromCodeProofs.v, the second is reached, and the first is
   one of a unit that exits with symbols and constants only. *)
Definition unit_lifted (s s' : state) : Prop :=
  (s = State e [] [] statics0 hp0 ∧ s' = State lifted [] [] statics0 hp0)
  ∨ (state_lifted_out [] s s' ∧ reached_lifted s' ∧ plain_state s).

(* The first step of the second run binds the group; the states are
   then related. *)
Lemma head_bound :
  ∃ statics' : static_env,
    step (State lifted [] [] statics0 hp0)
    = Step (State (lift_from_code [] lets root e) [] [] statics' hp0)
    ∧ state_lifted_out [] (State e [] [] statics0 hp0)
        (State (lift_from_code [] lets root e) [] [] statics' hp0).
Proof.
  pose proof
    (well_formed_never_faults_from u lifted statics0 hp0 0 _ Hwf Hno_code
       Hfree eq_refl)
    as Hfault.
  unfold static_fault in Hfault. simpl in Hfault.
  apply orb_false_iff in Hfault as [_ Hfault].
  destruct (no_rebinding statics0 _ Hfault) as [Hdistinct Hfresh].
  destruct (eval_lifted_out_bindings [] lets root e statics0 Hdistinct Hfresh)
    as (statics' & Heval & Hcode & Hbound).
  pose proof (eval_static_bindings_extend [] _ statics0 statics' Heval)
    as Hextend.
  exists statics'. split.
  - unfold lifted. rewrite step_let_static. fold bindings in Heval.
    rewrite Heval. reflexivity.
  - apply State_lifted_out;
      [ intros x v [=] | constructor | | exact Hbound ].
    split; [ intros id; rewrite Hcode, Hno_code; reflexivity | ].
    split.
    + intros s allocated Hs. exists allocated.
      split; [ exact (proj2 Hextend s allocated Hs) | ].
      apply allocated_lifted_refl.
    + intros id c Hlookup. rewrite Hno_code in Hlookup.
      discriminate Hlookup.
Qed.

(* A unit of which something is lifted begins with a [Let] or a
   [Let_cont]: its first step is not an exit. *)
Lemma first_step_no_exit (k : continuation) (vs : list value) (hp : heap) :
  step (State e [] [] statics0 hp0) <> Exit k vs hp.
Proof.
  unfold bindings in Hsome.
  destruct e
    as [ x xkind d body | group body | k0 h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl in Hsome; try (exfalso; apply Hsome; reflexivity).
  - rewrite step_let.
    destruct (eval_named statics0 [] d) as [v | ]; [ | discriminate ].
    destruct (kind_eqb (kind_of_value v) xkind); discriminate.
  - rewrite step_let_static.
    destruct (eval_static_bindings [] group statics0); discriminate.
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
        (State (lift_from_code [] lets root e) [] [] statics' hp0)).
    { exists 1. simpl. rewrite Hhead. reflexivity. }
    destruct Hreached as [n Hn].
    pose proof (lifted_out_step [] _ _ Hrelated
      (well_formed_never_faults_from u _ statics0 hp0 n _ Hwf Hno_code Hfree
         Hn)) as Hanswer.
    pose proof (plain_step _ (plain_from e statics0 hp0 Hplain Hno_code))
      as Hstep.
    pose proof first_step_no_exit as Hno_exit.
    destruct (step (State e [] [] statics0 hp0)) as [t | k vs | ];
      unfold answered in *; [ | | exact I ].
    + destruct Hanswer as (m & t' & Hrun & Ht).
      exists (S m), t'. split.
      * change (S (S m)) with (1 + S m). rewrite run_add. simpl.
        rewrite Hhead. exact Hrun.
      * right. split; [ exact Ht | ]. split; [ | exact Hstep ].
        exists (n + S m). rewrite run_add, Hn. exact Hrun.
    + exfalso. exact (Hno_exit k vs hp eq_refl).
  - pose proof (lifted_out_step [] s s' Hlifted
      (well_formed_never_faults_from u _ statics0 hp0 n s' Hwf Hno_code
         Hfree Hn)) as Hanswer.
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
  refines (State e [] [] statics0 hp0) (State lifted [] [] statics0 hp0).
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
  destruct (once_each [] (lifted_out_bindings lets root e))
    as [ | binding rest] eqn:Hbindings.
  - unfold lift_to_head. cbv zeta. rewrite Hbindings. apply refines_refl.
  - assert (Hsome : once_each [] (lifted_out_bindings lets root e) <> [])
      by (rewrite Hbindings; discriminate).
    assert (Hshape :
      lift_to_head lets e
      = Let_static (once_each [] (lifted_out_bindings lets root e))
          (lift_from_code [] lets root e)).
    { unfold lift_to_head. cbv zeta. rewrite Hbindings. reflexivity. }
    rewrite Hshape in Hwf |- *.
    exact (unit_lifted_refines u lets e empty_static_env empty_heap Hwf
             Hplain Hsome eq_refl (free_in_empty _)).
Qed.

Theorem lift_to_head_unit_refines_imports :
  lift_to_head_unit_refines_imports_statement.
Proof.
  intros imports u lets e e'. unfold lift_to_head_unit. cbv zeta.
  destruct (exits_plain [] e) eqn:Hplain; [ | discriminate ].
  destruct (well_formed_unit u (lift_to_head lets e)) eqn:Hwf;
    [ | discriminate ].
  intros [= <-]. unfold unit_refines.
  destruct (once_each [] (lifted_out_bindings lets root e))
    as [ | binding rest] eqn:Hbindings.
  - unfold lift_to_head. cbv zeta. rewrite Hbindings. intros _.
    apply refines_refl.
  - assert (Hsome : once_each [] (lifted_out_bindings lets root e) <> [])
      by (rewrite Hbindings; discriminate).
    assert (Hshape :
      lift_to_head lets e
      = Let_static (once_each [] (lifted_out_bindings lets root e))
          (lift_from_code [] lets root e)).
    { unfold lift_to_head. cbv zeta. rewrite Hbindings. reflexivity. }
    rewrite Hshape in Hwf |- *. intros Hfree.
    exact (unit_lifted_refines u lets e (imports_statics imports) empty_heap
             Hwf Hplain Hsome eq_refl Hfree).
Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

Theorem lift_to_head_equivariant : lift_to_head_equivariant_statement.
Proof.
  intros r lets e. unfold lift_to_head. cbv zeta.
  rewrite (lifted_out_bindings_equivariant r lets root e).
  destruct (once_each [] (lifted_out_bindings lets root e))
    as [ | binding rest] eqn:Hbindings; [ reflexivity | ].
  pose proof
    (once_each_closed r _ [] (lifted_out_bindings_closed r lets root e))
    as Hclosed.
  rewrite Hbindings in Hclosed. simpl in Hclosed |- *.
  rewrite Hclosed, (lift_from_code_equivariant r [] lets root e).
  reflexivity.
Qed.
