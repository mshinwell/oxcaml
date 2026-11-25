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

(* THE LAWS OF THE KIT, AND THE RULES BY WHICH A STATEMENT ABOUT A PORTED
   FUNCTION IS PROVED. A file of the real build only: the identity build
   never compiles it, and nothing of it is extracted. It has no axiom and no
   parameter: everything here is proved from the definitions of
   Port_monad.v. This file follows no file of the compiler.

   WHAT IT OFFERS.
   1. Exceptions. A handler for an exception takes what a raise of it
      raises ([exn_match_make]); two exceptions of one name that carry one
      type are one exception ([exn_match_same_name]); a handler does not
      take an exception of another name ([exn_match_other]). [named] is the
      form of what is assumed of a declared exception.
   2. ONE notion of "ends in a fatal error" ([fatal_exn], [ends_fatal]).
   3. How each operation runs ([run_bind], [run_try_with], ..), for proofs
      that rewrite.
   4. The fuel: [run_let_fuel], [fuel_induction].
   5. PARTIAL CORRECTNESS: the form of a statement ([spec]) and a rule for
      each operation ([wp_bind], [wp_try_with], [wp_match_exn],
      [wp_recursive], [wp_let_fuel], [wp_while], ..); and the form of the
      weakest thing to assume of a call ([returns_or_fatal]).

   WHAT IT DOES NOT OFFER.
   - Anything of a run that is OUT OF FUEL. A statement of the form [spec]
     holds of such a run whatever it says: a computation that is out of
     fuel for every fuel satisfies every statement. So a statement is about
     the runs that have enough fuel; that OCaml's run is one of them, and
     ends as it does, is not proved here (GUIDE.md, section 8).
   - A law that relates two fuels ("more fuel, the same end"). A
     computation may look at its fuel, and a function that holds a fuel is
     another function with another fuel. Where a proof needs such a thing,
     it is a statement about the function in hand.
   - Anything of the state: no rule for references, lazy values or arrays.
   - Anything of a parameter. What a proof needs of one is a contract
     (contracts/README.md).
   - A tactic that walks the body of a function. *)

From SimplifyPort Require Import Port_monad.
Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* 1. Exceptions                                                      *)
(* ------------------------------------------------------------------ *)

(* A handler for [e] takes what [raise_ e p] raises. This holds of EVERY
   exception, also of one that is a parameter (a declared exception). *)
Theorem exn_match_make {P : Type} {C : Carried P} (e : exception P) (p : P) :
  exn_match e (exn_make e p) = Some p.
Proof.
  unfold exn_match, exn_make. rewrite String.eqb_refl.
  apply exn_carried_carry.
Qed.

(* TWO EXCEPTIONS OF ONE NAME THAT CARRY ONE TYPE ARE ONE EXCEPTION: a
   handler for the one takes what the other raises. So two declarations of
   one exception of OCaml (one in decl/, one in a ported file) need no more
   than the same name. *)
Theorem exn_match_same_name {P : Type} {C : Carried P} (e e' : exception P)
    (p : P) :
  exception_name e' = exception_name e ->
  exn_match e (exn_make e' p) = Some p.
Proof.
  intro Hname. unfold exn_match, exn_make. rewrite Hname, String.eqb_refl.
  apply exn_carried_carry.
Qed.

(* A handler for [e] does not take an exception of another name. *)
Theorem exn_match_other {P Q : Type} {C : Carried P} {D : Carried Q}
    (e : exception P) (e' : exception Q) (q : Q) :
  exception_name e' <> exception_name e -> exn_match e (exn_make e' q) = None.
Proof.
  intro Hne. unfold exn_match, exn_make.
  destruct (String.eqb_spec (exception_name e') (exception_name e));
    [contradiction | reflexivity].
Qed.

(* THE FORM OF WHAT IS ASSUMED OF A DECLARED EXCEPTION: its name. *)
Definition named {P : Type} (e : exception P) (name : string) : Prop :=
  exception_name e = name.

(* The name is all that there is to know of an exception. *)
Theorem named_is {P : Type} (e : exception P) (name : string) :
  named e name <-> e = {| exception_name := name |}.
Proof.
  unfold named. destruct e as [name0]. simpl. split.
  - intros ->. reflexivity.
  - intro H. injection H as ->. reflexivity.
Qed.

(* The exceptions of the kit have their names by their definitions. *)
Lemma Fatal_error_named : named Fatal_error "Misc.Fatal_error".
Proof. reflexivity. Qed.
Lemma Not_found_named : named Not_found "Not_found".
Proof. reflexivity. Qed.
Lemma Assert_failure_named : named Assert_failure "Assert_failure".
Proof. reflexivity. Qed.
Lemma Division_by_zero_named : named Division_by_zero "Division_by_zero".
Proof. reflexivity. Qed.
Create HintDb exn_names.
#[export] Hint Resolve Fatal_error_named Not_found_named
  Assert_failure_named Division_by_zero_named : exn_names.

Theorem named_same {P : Type} {C : Carried P} (e e' : exception P)
    (name : string) (p : P) :
  named e name -> named e' name -> exn_match e (exn_make e' p) = Some p.
Proof.
  unfold named. intros H H'. apply exn_match_same_name. rewrite H, H'.
  reflexivity.
Qed.

Theorem named_other {P Q : Type} {C : Carried P} {D : Carried Q}
    (e : exception P) (e' : exception Q) (name name' : string) (q : Q) :
  named e name -> named e' name' -> String.eqb name' name = false ->
  exn_match e (exn_make e' q) = None.
Proof.
  unfold named. intros <- <- Hne. apply exn_match_other.
  apply String.eqb_neq. exact Hne.
Qed.

(* [exn_other] proves [exn_match e (exn_make e' q) = None] from the names
   of the two exceptions: those of the kit, and those in the hypotheses. *)
Ltac exn_other :=
  eapply named_other;
  [ first [eassumption | eauto with exn_names]
  | first [eassumption | eauto with exn_names]
  | first [assumption | reflexivity] ].

(* THE CLASS [Carried] HAS THE KIT'S TWO INSTANCES AND NO OTHER. An instance
   must not be ASSUMED (as a parameter or a hypothesis) for a type: for some
   types there is none, and the assumption would be a contradiction. The
   functions from [exn_payload] to [bool] are such a type. *)
Theorem no_carried_of_a_larger_type (C : Carried (exn_payload -> bool)) :
  False.
Proof.
  pose (d := fun x : exn_payload =>
               match exn_carried x with
               | Some f => negb (f x)
               | None => false
               end).
  assert (H : d (exn_carry d) = negb (d (exn_carry d))).
  { unfold d at 1. rewrite exn_carried_carry. reflexivity. }
  destruct (d (exn_carry d)); discriminate H.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. ONE notion of "ends in a fatal error"                           *)
(* ------------------------------------------------------------------ *)

(* The value of [Misc.Fatal_error]. *)
Definition fatal_exn : exn := exn_make Fatal_error tt.

(* A run ends in a fatal error: it ends [Raised] with that value. There is
   no other end for a fatal error. *)
Definition ends_fatal {A : Type} (r : result A) : Prop :=
  exists s : ocaml_state, r = Raised fatal_exn s.

(* It is the one value that a handler for [Misc.Fatal_error] takes. *)
Theorem handler_takes_fatal (x : exn) :
  exn_match Fatal_error x = Some tt <-> x = fatal_exn.
Proof.
  destruct x as [name c]. unfold fatal_exn, exn_make, exn_match. simpl.
  split.
  - destruct (String.eqb_spec name "Misc.Fatal_error") as [-> | ];
      [ | discriminate].
    destruct c; [reflexivity | discriminate].
  - intro H. injection H as -> ->. reflexivity.
Qed.

(* A handler for an exception of another name lets it pass. *)
Theorem fatal_passes {P : Type} {C : Carried P} (e : exception P)
    (name : string) :
  named e name -> String.eqb "Misc.Fatal_error" name = false ->
  exn_match e fatal_exn = None.
Proof. intros. unfold fatal_exn. exn_other. Qed.
Arguments fatal_passes {P C e name}.

(* A failed assertion passes too. *)
Theorem assert_failure_passes {P : Type} {C : Carried P} (e : exception P)
    (name : string) :
  named e name -> String.eqb "Assert_failure" name = false ->
  exn_match e assert_failure = None.
Proof. intros. unfold assert_failure. exn_other. Qed.
Arguments assert_failure_passes {P C e name}.

(* ------------------------------------------------------------------ *)
(* 3. How each operation runs                                         *)
(* ------------------------------------------------------------------ *)

(* Each is the definition, unfolded: the proofs are [reflexivity]. *)
Lemma run_ret {A : Type} (a : A) (n : nat) (s : ocaml_state) :
  run (ret a) n s = Returned a s.
Proof. reflexivity. Qed.

Lemma run_bind {A B : Type} (m : M A) (k : A -> M B) (n : nat)
    (s : ocaml_state) :
  run (bind m k) n s =
  match run m n s with
  | Returned a s' => run (k a) n s'
  | Raised e s' => Raised e s'
  | Out_of_fuel => Out_of_fuel
  end.
Proof. reflexivity. Qed.

Lemma run_raise {P A : Type} {C : Carried P} (e : exception P) (p : P)
    (n : nat) (s : ocaml_state) :
  run (raise_ e p : M A) n s = Raised (exn_make e p) s.
Proof. reflexivity. Qed.

Lemma run_try_with {P A : Type} {C : Carried P} (body : unit -> M A)
    (e : exception P) (handler : P -> M A) (n : nat) (s : ocaml_state) :
  run (try_with body e handler) n s =
  match run (body tt) n s with
  | Raised x s' =>
    match exn_match e x with
    | Some p => run (handler p) n s'
    | None => Raised x s'
    end
  | r => r
  end.
Proof. reflexivity. Qed.

Lemma run_match_exn {P A B : Type} {C : Carried P} (body : unit -> M A)
    (e : exception P) (handler : P -> M B) (k : A -> M B) (n : nat)
    (s : ocaml_state) :
  run (match_exn body e handler k) n s =
  match run (body tt) n s with
  | Returned a s' => run (k a) n s'
  | Raised x s' =>
    match exn_match e x with
    | Some p => run (handler p) n s'
    | None => Raised x s'
    end
  | Out_of_fuel => Out_of_fuel
  end.
Proof. reflexivity. Qed.

Lemma run_try_with_any {A : Type} (body : unit -> M A)
    (handler : exn -> M A) (n : nat) (s : ocaml_state) :
  run (try_with_any body handler) n s =
  match run (body tt) n s with
  | Raised x s' => run (handler x) n s'
  | r => r
  end.
Proof. reflexivity. Qed.

(* A fatal error never returns, whatever its printing does. (That it ends
   in a fatal error needs a contract of the printing.) *)
Theorem fatal_errorf_args_never_returns {A : Type} (format : string)
    (args : fmt_args) (n : nat) (s : ocaml_state) (a : A)
    (s' : ocaml_state) :
  run (fatal_errorf_args format args) n s <> Returned a s'.
Proof.
  unfold fatal_errorf_args. rewrite run_bind.
  destruct (run (print_fatal_message format args) n s); discriminate.
Qed.

Theorem fatal_error_never_returns {A : Type} (message : string) (n : nat)
    (s : ocaml_state) (a : A) (s' : ocaml_state) :
  run (fatal_error message) n s <> Returned a s'.
Proof.
  unfold fatal_error. rewrite run_bind.
  destruct (run (print_fatal_message "%s" (Fmt_cons message Fmt_nil)) n s);
    discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The fuel                                                        *)
(* ------------------------------------------------------------------ *)

(* [let_fuel! f in k]: [k] with the fuel of the run, run with that fuel. *)
Lemma run_let_fuel {A : Type} (k : fuel -> M A) (n : nat) (s : ocaml_state) :
  run (let_fuel! f in k f) n s = run (k (fuel_of_nat n)) n s.
Proof. reflexivity. Qed.

Lemma run_while (cond : unit -> M bool) (body : unit -> M unit) (n : nat)
    (s : ocaml_state) :
  run (while_ cond body) n s = run (while_fuel n cond body) n s.
Proof. reflexivity. Qed.

(* Induction on the fuel. (The kit switches the making of schemes off.) *)
Lemma fuel_induction (P : fuel -> Prop) :
  P Out -> (forall f : fuel, P f -> P (More f)) -> forall f : fuel, P f.
Proof.
  intros HOut HMore. fix IH 1. intros [ | f]; [exact HOut | apply HMore, IH].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Partial correctness                                             *)
(* ------------------------------------------------------------------ *)

(* What a statement says of an end: [Q] of a value returned and the state,
   [E] of an exception raised and the state, NOTHING of a run that is out
   of fuel. *)
Definition ends {A : Type} (r : result A) (Q : A -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) : Prop :=
  match r with
  | Returned a s => Q a s
  | Raised e s => E e s
  | Out_of_fuel => True
  end.

(* [wp m Q E n s]: the run of [m] with the fuel [n] from the state [s] ends
   as [Q] and [E] say. *)
Definition wp {A : Type} (m : M A) (Q : A -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) : Prop :=
  ends (run m n s) Q E.

(* THE FORM OF A SPECIFICATION: for every fuel and every state that [P]
   holds of. For [f : a -> M b] it is [forall x, spec (P x) (f x) (Q x) E]. *)
Definition spec {A : Type} (P : ocaml_state -> Prop) (m : M A)
    (Q : A -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) : Prop :=
  forall (n : nat) (s : ocaml_state), P s -> wp m Q E n s.

(* Three things to say of exceptions: none is raised; only a fatal error;
   nothing is said. *)
Definition no_exn : exn -> ocaml_state -> Prop := fun _ _ => False.
Definition fatal_only : exn -> ocaml_state -> Prop := fun e _ => e = fatal_exn.
Definition any_exn : exn -> ocaml_state -> Prop := fun _ _ => True.

(* What [spec] says of a run that returns: for every fuel and every state
   that [P] holds of, if the run returns [v] in the state [s'], then
   [Q v s']. *)
Theorem spec_returns {A : Type} (P : ocaml_state -> Prop) (m : M A)
    (Q : A -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) :
  spec P m Q E ->
  forall (n : nat) (s : ocaml_state) (v : A) (s' : ocaml_state),
    P s -> run m n s = Returned v s' -> Q v s'.
Proof.
  intros H n s v s' HP Hrun. specialize (H n s HP). unfold wp in H.
  rewrite Hrun in H. exact H.
Qed.

(* What it says of every run when [E] is [fatal_only]: the run returns a
   value of which [Q] holds, or ends in a fatal error, or is out of fuel. *)

Theorem spec_fatal_only {A : Type} (P : ocaml_state -> Prop) (m : M A)
    (Q : A -> ocaml_state -> Prop) :
  spec P m Q fatal_only ->
  forall (n : nat) (s : ocaml_state), P s ->
    (exists (v : A) (s' : ocaml_state), run m n s = Returned v s' /\ Q v s')
    \/ ends_fatal (run m n s) \/ run m n s = Out_of_fuel.
Proof.
  intros H n s HP. specialize (H n s HP). unfold wp in H.
  destruct (run m n s) as [v s' | e s' | ]; simpl in H.
  - left. exists v, s'. split; [reflexivity | exact H].
  - right. left. exists s'. rewrite H. reflexivity.
  - right. right. reflexivity.
Qed.

(* OF A RUN THAT IS OUT OF FUEL A STATEMENT SAYS NOTHING: the computation
   that is out of fuel with every fuel has every specification. So a
   statement of this form tells nothing of OCaml's run without the sentence
   of adequacy (GUIDE.md, section 8). *)
Theorem out_of_fuel_has_every_spec {A : Type} (P : ocaml_state -> Prop)
    (Q : A -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) :
  spec P out_of_fuel Q E.
Proof. intros n s _. exact I. Qed.

Lemma wp_weaken {A : Type} (m : M A) (Q Q' : A -> ocaml_state -> Prop)
    (E E' : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  wp m Q E n s ->
  (forall (a : A) (s' : ocaml_state), Q a s' -> Q' a s') ->
  (forall (e : exn) (s' : ocaml_state), E e s' -> E' e s') ->
  wp m Q' E' n s.
Proof. unfold wp. destruct (run m n s); simpl; auto. Qed.

(* A call of which nothing is known (a declared function without a
   contract): whatever it returns or raises. *)
Lemma wp_any {A : Type} (m : M A) (Q : A -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  (forall (a : A) (s' : ocaml_state), Q a s') ->
  (forall (e : exn) (s' : ocaml_state), E e s') ->
  wp m Q E n s.
Proof. unfold wp. destruct (run m n s); simpl; auto. Qed.

(* A call that never returns (a fatal error): whatever it raises. *)
Lemma wp_never_returns {A : Type} (m : M A) (Q : A -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  (forall (a : A) (s' : ocaml_state), run m n s <> Returned a s') ->
  (forall (e : exn) (s' : ocaml_state), E e s') ->
  wp m Q E n s.
Proof.
  unfold wp. destruct (run m n s) as [a s' | e s' | ]; simpl; auto.
  intros H _. exfalso. exact (H a s' eq_refl).
Qed.

Lemma wp_ret {A : Type} (a : A) (Q : A -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  Q a s -> wp (ret a) Q E n s.
Proof. intro H. exact H. Qed.

(* THE LEAST THAT A PROOF NEEDS OF A CALL so that a fatal error stays the
   only exception: from every state the call returns, or ends in a fatal
   error (or is out of fuel). Nothing is said of the value or of the state.
   It is the form of the weakest contract of a declared function
   (contracts/README.md). *)
Definition returns_or_fatal {A : Type} (m : M A) : Prop :=
  forall (n : nat) (s : ocaml_state), wp m (fun _ _ => True) fatal_only n s.

(* It is not a contradiction at any type: a computation that returns has
   it, and so has a fatal error. *)
Lemma returns_or_fatal_ret {A : Type} (a : A) : returns_or_fatal (ret a).
Proof. intros n s. exact I. Qed.

Lemma returns_or_fatal_raise_fatal {A : Type} :
  returns_or_fatal (raise_ Fatal_error tt : M A).
Proof. intros n s. reflexivity. Qed.

(* A call that has it: whatever it returns, and the fatal error. *)
Lemma wp_returns_or_fatal {A : Type} (m : M A)
    (Q : A -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) (n : nat)
    (s : ocaml_state) :
  returns_or_fatal m ->
  (forall (a : A) (s' : ocaml_state), Q a s') ->
  (forall s' : ocaml_state, E fatal_exn s') ->
  wp m Q E n s.
Proof.
  intros Hm HQ HE. eapply wp_weaken; [apply Hm | intros a s' _; apply HQ | ].
  intros e s' ->. apply HE.
Qed.

(* [let* x := m in k x] (and [let!], [;;]). *)
Lemma wp_bind {A B : Type} (m : M A) (k : A -> M B)
    (Q : B -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) (n : nat)
    (s : ocaml_state) :
  wp m (fun a s' => wp (k a) Q E n s') E n s -> wp (bind m k) Q E n s.
Proof. unfold wp. rewrite run_bind. destruct (run m n s); simpl; auto. Qed.

Lemma wp_seq {B : Type} (m : M unit) (k : M B)
    (Q : B -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) (n : nat)
    (s : ocaml_state) :
  wp m (fun _ s' => wp k Q E n s') E n s -> wp (m ;; k) Q E n s.
Proof. apply wp_bind. Qed.

Lemma wp_raise {P A : Type} {C : Carried P} (e : exception P) (p : P)
    (Q : A -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) (n : nat)
    (s : ocaml_state) :
  E (exn_make e p) s -> wp (raise_ e p) Q E n s.
Proof. intro H. exact H. Qed.

(* What a handler for [e] makes of what its body raises: [h] of what it
   takes, [E] of what it lets pass. *)
Definition handled {P : Type} {C : Carried P} (e : exception P)
    (h : P -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop)
    : exn -> ocaml_state -> Prop :=
  fun x s => match exn_match e x with Some p => h p s | None => E x s end.

Lemma wp_try_with {P A : Type} {C : Carried P} (body : unit -> M A)
    (e : exception P) (handler : P -> M A) (Q : A -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  wp (body tt) Q (handled e (fun p s' => wp (handler p) Q E n s') E) n s ->
  wp (try_with body e handler) Q E n s.
Proof.
  unfold wp, handled. rewrite run_try_with.
  destruct (run (body tt) n s) as [a s' | x s' | ]; simpl; auto.
  destruct (exn_match e x); auto.
Qed.

Lemma wp_match_exn {P A B : Type} {C : Carried P} (body : unit -> M A)
    (e : exception P) (handler : P -> M B) (k : A -> M B)
    (Q : B -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  wp (body tt) (fun a s' => wp (k a) Q E n s')
    (handled e (fun p s' => wp (handler p) Q E n s') E) n s ->
  wp (match_exn body e handler k) Q E n s.
Proof.
  unfold wp, handled. rewrite run_match_exn.
  destruct (run (body tt) n s) as [a s' | x s' | ]; simpl; auto.
  destruct (exn_match e x); auto.
Qed.

Lemma wp_try_with_any {A : Type} (body : unit -> M A) (handler : exn -> M A)
    (Q : A -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) (n : nat)
    (s : ocaml_state) :
  wp (body tt) Q (fun x s' => wp (handler x) Q E n s') n s ->
  wp (try_with_any body handler) Q E n s.
Proof.
  unfold wp. rewrite run_try_with_any.
  destruct (run (body tt) n s); simpl; auto.
Qed.

(* [recursive! fuel in k]: nothing to prove when the fuel is out. With
   [fuel_induction] this is the rule of a recursion on the fuel. *)
Lemma wp_out_of_fuel {A : Type} (Q : A -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  wp out_of_fuel Q E n s.
Proof. exact I. Qed.

Lemma wp_recursive {A : Type} (f : fuel) (k : fuel -> M A)
    (Q : A -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) (n : nat)
    (s : ocaml_state) :
  (forall f' : fuel, f = More f' -> wp (k f') Q E n s) ->
  wp (recursive! f in k f) Q E n s.
Proof. destruct f as [ | f']; intro H; [exact I | apply H; reflexivity]. Qed.

(* [let_fuel! f in k f]: [k] with the fuel of the run. *)
Lemma wp_let_fuel {A : Type} (k : fuel -> M A)
    (Q : A -> ocaml_state -> Prop) (E : exn -> ocaml_state -> Prop) (n : nat)
    (s : ocaml_state) :
  wp (k (fuel_of_nat n)) Q E n s -> wp (let_fuel! f in k f) Q E n s.
Proof. intro H. exact H. Qed.

(* [while_ cond body]: an invariant. *)
Lemma wp_while_fuel (cond : unit -> M bool) (body : unit -> M unit)
    (Inv : ocaml_state -> Prop) (Q : unit -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) :
  (forall s1 : ocaml_state, Inv s1 ->
     wp (cond tt)
       (fun b s2 =>
          if b then wp (body tt) (fun _ s3 => Inv s3) E n s2 else Q tt s2)
       E n s1) ->
  forall (i : nat) (s : ocaml_state),
    Inv s -> wp (while_fuel i cond body) Q E n s.
Proof.
  intros Hstep i. induction i as [ | i IH]; intros s HInv.
  - exact I.
  - simpl. apply wp_bind.
    eapply wp_weaken; [apply Hstep; exact HInv | | auto].
    intros [ | ] s2 H2; simpl in H2.
    + apply wp_bind. eapply wp_weaken; [exact H2 | | auto].
      intros u s3 H3. apply IH. exact H3.
    + apply wp_ret. exact H2.
Qed.

Lemma wp_while (cond : unit -> M bool) (body : unit -> M unit)
    (Inv : ocaml_state -> Prop) (Q : unit -> ocaml_state -> Prop)
    (E : exn -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  Inv s ->
  (forall s1 : ocaml_state, Inv s1 ->
     wp (cond tt)
       (fun b s2 =>
          if b then wp (body tt) (fun _ s3 => Inv s3) E n s2 else Q tt s2)
       E n s1) ->
  wp (while_ cond body) Q E n s.
Proof.
  intros HInv Hstep. unfold wp. rewrite run_while.
  apply (wp_while_fuel cond body Inv Q E n Hstep). exact HInv.
Qed.
