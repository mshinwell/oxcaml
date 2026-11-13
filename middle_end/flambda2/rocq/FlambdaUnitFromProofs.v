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

(* The run of a well-formed unit from a static environment that binds
   something. Nothing here needs review: these are the two facts of
   FlambdaWellFormedSpec.v about the run of a unit from the empty
   static environment ([well_formed_never_faults_statement],
   [well_formed_names_bound_statement]), for a run that starts from a
   static environment that holds no code and binds no name that the
   unit binds (FlambdaImportsSpec.static_names_free_in), such as the
   one of the imports of a unit (FlambdaImportsSpec.imports_statics),
   and from any heap. The proofs are those of
   FlambdaWellFormedProofs.v with another first state: the invariants
   there are of any state.

   They are for the proofs of the passes that are stated of a unit run
   on its own and that take the two facts of the run of their result:
   the liftings to symbols and the two hoistings. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaBindersSpec FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaScopeSpec FlambdaScopeProofs
  FlambdaWellFormedSpec FlambdaWellFormedProofs FlambdaImportsSpec.
Import ListNotations.

(* ======================================================================== *)
(* What the test of the names gives                                         *)
(* ======================================================================== *)

Lemma free_in_symbols (statics : static_env) (e : expr) :
  static_names_free_in statics e = true ->
  ∀ n : positive,
    In n (static_names symbols_of_binding e) -> symbol_bound statics n = false.
Proof.
  unfold static_names_free_in. intros H n Hn.
  apply andb_true_iff in H as [Hsymbols _].
  rewrite forallb_forall in Hsymbols. specialize (Hsymbols n Hn).
  apply negb_true_iff in Hsymbols. exact Hsymbols.
Qed.

Lemma free_in_code_ids (statics : static_env) (e : expr) :
  static_names_free_in statics e = true ->
  ∀ n : positive,
    In n (static_names code_ids_of_binding e) ->
    code_id_bound statics n = false.
Proof.
  unfold static_names_free_in. intros H n Hn.
  apply andb_true_iff in H as [_ Hcode].
  rewrite forallb_forall in Hcode. specialize (Hcode n Hn).
  apply negb_true_iff in Hcode. exact Hcode.
Qed.

(* The empty static environment binds nothing. *)
Lemma free_in_empty (e : expr) :
  static_names_free_in empty_static_env e = true.
Proof.
  unfold static_names_free_in. apply andb_true_iff.
  split; apply forallb_forall; intros n _; reflexivity.
Qed.

(* ======================================================================== *)
(* No static binding is executed twice                                      *)
(* ======================================================================== *)

(* The invariant of FlambdaWellFormedProofs.v holds of the first state,
   for either sort of name. *)
Lemma inv_from (unit_exn : continuation)
    (names_of : static_binding -> list positive)
    (is_bound : static_env -> positive -> bool) (e : expr)
    (statics : static_env) (hp : heap) :
  (∀ n : positive,
    In n (static_names names_of e) -> is_bound statics n = false) ->
  static_code statics = [] ->
  statics_at_toplevel unit_exn true e = true ->
  distinct (static_names names_of e) = true ->
  inv unit_exn names_of is_bound (State e [] [] statics hp).
Proof.
  intros Hfree Hno_code P D.
  refine
    (conj P (conj (proj1 (distinct_NoDup _) D) (conj I (conj _ (conj _ _))))).
  - intros n _ [].
  - intros n [Hn | []]. exact (Hfree n Hn).
  - intros id c Hlookup. simpl in Hlookup. rewrite Hno_code in Hlookup.
    discriminate Hlookup.
Qed.

Lemma well_formed_never_faults_from (u : unit_interface) (e : expr)
    (statics : static_env) (hp : heap) (n : nat) (s : state) :
  well_formed_unit u e = true ->
  static_code statics = [] ->
  static_names_free_in statics e = true ->
  run n (State e [] [] statics hp) = Step s ->
  static_fault s = false.
Proof.
  intros Hwf Hno_code Hfree Hrun.
  pose proof (well_formed_unit_statics_at_toplevel u e Hwf) as P.
  pose proof (well_formed_unit_code_ids_distinct u e Hwf) as Dcode.
  pose proof (well_formed_unit_symbols_distinct u e Hwf) as Dsymbols.
  pose proof (inv_run (unit_exn u) code_ids_of_binding code_id_bound
    code_bound_after n _ s
    (inv_from (unit_exn u) code_ids_of_binding code_id_bound e statics hp
       (free_in_code_ids statics e Hfree) Hno_code P Dcode)
    Hrun) as Hcode.
  pose proof (inv_run (unit_exn u) symbols_of_binding symbol_bound
    symbol_bound_after n _ s
    (inv_from (unit_exn u) symbols_of_binding symbol_bound e statics hp
       (free_in_symbols statics e Hfree) Hno_code P Dsymbols)
    Hrun) as Hsymbols.
  rewrite (state_eta s) in Hcode, Hsymbols. unfold static_fault.
  destruct (state_expr s)
    as [ x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    try reflexivity.
  - rewrite (inv_no_rebinding (unit_exn u) _ _ _ _ _ _ _ _ Hcode),
      (inv_no_rebinding (unit_exn u) _ _ _ _ _ _ _ _ Hsymbols).
    reflexivity.
  - exact (inv_no_recursive_statics (unit_exn u) _ _ _ _ _ _ _ _ Hcode).
  - exact (inv_no_call_binding_statics (unit_exn u) _ _ _ _ _ _ _ Hcode).
Qed.

(* ======================================================================== *)
(* No variable is read that has no value                                    *)
(* ======================================================================== *)

Lemma well_formed_names_bound_from (u : unit_interface) (e : expr)
    (statics : static_env) (hp : heap) (n : nat) :
  well_formed_unit u e = true ->
  static_code statics = [] ->
  match run n (State e [] [] statics hp) with
  | Step s => reads_unbound_variable s = false
  | Exit k _ _ => k = unit_return u ∨ k = unit_exn u
  | Undefined => True
  end.
Proof.
  intros Hwf Hno_code.
  assert (Hclosed : code_all_closed statics).
  { unfold code_all_closed. rewrite Hno_code. apply Forall_nil. }
  pose proof
    (run_in_scope [unit_return u; unit_exn u] n _
       (state_in_scope_intro [unit_return u; unit_exn u] e [] [] statics hp
          (well_formed_unit_names_in_scope u e Hwf)
          (well_formed_unit_code_closed u e Hwf) I Hclosed))
    as Hrun.
  destruct (run n (State e [] [] statics hp)) as [s | k vs | ];
    [ exact (in_scope_reads_bound _ s Hrun) | | exact I ].
  apply among_In in Hrun.
  destruct Hrun as [<- | [<- | []]]; [ left | right ]; reflexivity.
Qed.
