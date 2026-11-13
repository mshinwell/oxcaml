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


(* Proofs of the statements of FlambdaLiftObservedSpec.v. Nothing here
   needs review.

   The simulation of each lifting is the one of its own proofs file,
   from the state that the unit starts in with a continuation
   environment of what may follow a unit
   (FlambdaObserversSpec.observers), and without the invariant of the
   first run that the test of the exits gives. What may follow a unit
   has no [Let] to lift and no code, so each rewrite leaves it as it is
   and it is related to itself; it binds nothing static, so the run of
   the unit lifted from it makes no static fault
   (FlambdaUnitFromProofs.well_formed_never_faults_under); and it names
   no code id, so it makes no closure of the code of a function. The
   values of two exits that answer each other are lifted, so they have
   the same constants and the same locations
   (FlambdaLiftProofs.lifted_same_scalars), and the two heaps are the
   same.

   The lifting to a group around needs, of the run of the unit
   rewritten, that it reads no variable that has no value, which is so
   of a unit run on its own and not of what may follow it. Its
   statement is proved from the one about the two exits
   (FlambdaObserversSpec.under_observers_worlds_statement): the two
   units are run on their own to their exits, as in
   FlambdaLiftAroundProofs.v, and what follows is the same term in the
   two runs, with no group put (FlambdaLiftAroundProofs.unit_around_worlds). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaWellFormedSpec FlambdaImportsSpec
  FlambdaObserversSpec FlambdaObserversProofs FlambdaMyClosureSpec
  FlambdaLiftSpec FlambdaLiftProofs FlambdaLiftFromCodeSpec
  FlambdaLiftFromCodeProofs FlambdaLiftFromArmsSpec FlambdaLiftFromArmsProofs
  FlambdaLiftAroundSpec FlambdaLiftAroundProofs FlambdaLiftObservedSpec.
Import ListNotations.

Theorem lift_to_head_unit_observed_refines :
  lift_to_head_unit_observed_refines_statement.
Proof.
  intros imports u lets e e'. unfold lift_to_head_unit_observed. cbv zeta.
  destruct (well_formed_unit u (lift_to_head lets e)) eqn:Hwf;
    [ | discriminate ].
  intros [= <-].
  destruct (once_each [] (lifted_out_bindings lets root e))
    as [ | binding rest] eqn:Hbindings.
  - unfold lift_to_head. cbv zeta. rewrite Hbindings. intros _ conts _.
    apply observed_refines_refl.
  - assert (Hsome : once_each [] (lifted_out_bindings lets root e) <> [])
      by (rewrite Hbindings; discriminate).
    assert (Hshape :
      lift_to_head lets e
      = Let_static (once_each [] (lifted_out_bindings lets root e))
          (lift_from_code [] lets root e)).
    { unfold lift_to_head. cbv zeta. rewrite Hbindings. reflexivity. }
    rewrite Hshape in Hwf |- *. intros Hfree conts Hobservers.
    exact (FlambdaLiftFromArmsProofs.unit_lifted_observed u lets e
             (imports_statics imports) empty_heap conts Hwf Hsome eq_refl
             Hfree Hobservers).
Qed.

Theorem lift_from_code_unit_observed_refines :
  lift_from_code_unit_observed_refines_statement.
Proof.
  intros imports u K e e'. unfold lift_from_code_unit_observed. cbv zeta.
  destruct (well_formed_unit u (lift_from_code K [] root e)) eqn:Hwf;
    [ | discriminate ].
  intros [= <-] Hfree conts Hobservers.
  exact (unit_lifted_out_observed K u e (imports_statics imports) empty_heap
           conts Hwf eq_refl Hfree Hobservers).
Qed.

Theorem lift_unit_observed_refines : lift_unit_observed_refines_statement.
Proof.
  intros imports L e e'. unfold lift_unit_observed. cbv zeta.
  fold (lifted_unit (lifted_my_closures L) (lifted_lets L) e).
  destruct
    (well_formed_unit (lifting_unit L)
       (lifted_unit (lifted_my_closures L) (lifted_lets L) e))
    eqn:Hwf;
    simpl; [ | discriminate ].
  destruct
    (only_closures_of (lifted_my_closures L)
       (lifted_unit (lifted_my_closures L) (lifted_lets L) e))
    eqn:Honly;
    [ | discriminate ].
  intros [= <-] Hfree conts Hobservers.
  exact (FlambdaLiftProofs.unit_lifted_observed (lifted_my_closures L)
           (lifting_unit L) (lifted_lets L) e (imports_statics imports)
           empty_heap conts Hwf Honly eq_refl Hfree
           (fun id sym _ => statics_ok_imports id sym imports) Hobservers).
Qed.

Theorem lift_around_unit_observed_refines :
  lift_around_unit_observed_refines_statement.
Proof.
  intros imports u lets places e e'. unfold lift_around_unit_observed.
  cbv zeta.
  set (groups := groups_of lets places e).
  destruct (around_ok lets groups [] root e) eqn:Hok; simpl;
    [ | discriminate ].
  destruct (well_formed_unit u (lift_around lets groups root e)) eqn:Hwf;
    [ | discriminate ].
  intros [= <-] Hfree conts Hobservers.
  exact (unit_around_observed u lets groups e (imports_statics imports)
           empty_heap conts Hwf Hok eq_refl Hfree Hobservers).
Qed.
