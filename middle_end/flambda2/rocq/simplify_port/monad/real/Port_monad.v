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

(* THE MONAD OF THE PORT OF SIMPLIFY, ITS REAL IMPLEMENTATION: the one that
   says what a ported function does. A computation is run with a fuel, from
   a state of OCaml; it returns a value, or raises an exception, or is out of
   fuel. A fatal error is the exception [Misc.Fatal_error], as in OCaml.
   Every ported function and every declared function of OxCaml answers in
   [M]. This file follows no file of the compiler. Read GUIDE.md first.

   The ported files are compiled twice, against two files of this name with
   the same operations and notations: this one, and monad/id/Port_monad.v, in
   which [M A] is [A] and from which Rocq extracts the OCaml. Nothing is
   extracted from this one, and statements about the port are statements
   about this one.

   WHAT IS DEFINED HERE AND IS A PARAMETER THERE. The exceptions ([exn],
   [exception], [exn_make], [exn_match], [Fatal_error], [Not_found],
   [Division_by_zero], [assert_failure]) are definitions of this file, so
   that their laws are theorems; so are the fatal errors, the handlers and
   the fuel. What is a parameter here too: the state ([ocaml_state]), the
   printing of a fatal error, references, lazy values, arrays, OCaml's
   polymorphic comparisons and its physical equality. This file has no
   [Axiom]. The laws of what it defines, and the rules by which a statement
   about a ported function is proved, are in Kit_laws.v. What a proof
   assumes of a parameter is a contract (contracts/README.md). *)

From Stdlib Require Export String List ZArith Bool.
(* The extraction is loaded only so that Rocq reads the directives of the
   declarations (decl/), which this build compiles too and does not use. *)
From Stdlib Require Export Extraction.
Export ListNotations.

Set Implicit Arguments.

(* The ported files and the declarations make no elimination schemes: they
   would be extracted as definitions that the compiler's files do not have. *)
#[export] Unset Elimination Schemes.

(* ------------------------------------------------------------------ *)
(* The state                                                          *)
(* ------------------------------------------------------------------ *)

(* Everything mutable in the OCaml program that the port does not define:
   the counters from which [Int_ids] and the other modules make new names,
   the contents of every reference and table, the flags, the channels. It
   is not described in this version: the declared functions are parameters
   that read and change it.
   NOT IN IT: what OCaml's runtime keeps of the last exception that was
   raised (its backtrace). Here a raise changes no state, and a handler that
   lets an exception go on lets the same value go on; OCaml writes that
   record at each. [Printexc.get_raw_backtrace] and
   [Printexc.raise_with_backtrace] are parameters like the others
   (decl/Printexc.v): what they do with that record, the model does not
   say. So no statement speaks of a backtrace. *)
Parameter ocaml_state : Type.

(* ------------------------------------------------------------------ *)
(* The values of OCaml's type [exn]                                   *)
(* ------------------------------------------------------------------ *)

(* What the value of an exception carries: nothing, or a string. *)
Inductive exn_payload : Type :=
| Payload_unit
| Payload_string (s : string).

(* A value of OCaml's type [exn]: the name of its constructor and what it
   carries. Two values of the same name that carry the same are ONE value
   here: so two exceptions of OCaml must have two names. *)
Inductive exn : Type := Exn (name : string) (carried : exn_payload).

(* THE TYPES THAT AN EXCEPTION CAN CARRY: [unit] (a constant exception) and
   [string]. For such a type, how a value of it is put into an [exn_payload]
   and found again, with the proof that it is found. It is given by the TYPE
   and not by the exception: two exceptions that carry the same type carry
   it in the same way. An exception that carries another type needs one more
   constructor of [exn_payload] and one more instance here. ONLY THIS FILE
   MAKES AN INSTANCE: with a second one for a type, two files could carry
   that type in two ways. [make exceptions] (tools/exceptions.py) checks
   that no file of decl/ and no ported file names the class. *)
Class Carried (P : Type) : Type := Make_carried {
  exn_carry : P -> exn_payload;
  exn_carried : exn_payload -> option P;
  exn_carried_carry : forall p : P, exn_carried (exn_carry p) = Some p
}.

#[export] Instance Carried_unit : Carried unit :=
  {| exn_carry := fun _ => Payload_unit;
     exn_carried := fun c =>
       match c with Payload_unit => Some tt | Payload_string _ => None end;
     exn_carried_carry := fun p => match p with tt => eq_refl end |}.

#[export] Instance Carried_string : Carried string :=
  {| exn_carry := Payload_string;
     exn_carried := fun c =>
       match c with Payload_string s => Some s | Payload_unit => None end;
     exn_carried_carry := fun _ => eq_refl |}.

(* An exception constructor whose argument has type [P] ([unit] for a
   constant exception): ITS NAME, and no more. An exception of the kit is a
   definition (below). A DECLARED exception is a parameter of this type
   ([Parameter E : exception T.] in decl/ and in the ported files): it has a
   name, which Rocq does not know; a proof that needs the name takes it as a
   contract (contracts/README.md). TWO DECLARATIONS OF ONE EXCEPTION OF
   OCAML (one in decl/, one in the ported file that has the exception) are
   two parameters; with one name they are one exception, and a handler for
   the one takes what the other raises ([exn_match_same_name] in
   Kit_laws.v). An exception can be declared for any type [T]; it can be
   raised, made a value of, or handled only if [T] is a type that an
   exception can carry: Rocq refuses the other uses (Kit_refuses.v). *)
Record exception (P : Type) : Type := Make_exception {
  exception_name : string
}.

(* The value [E p]. *)
Definition exn_make {P : Type} {C : Carried P} (e : exception P) (p : P)
    : exn :=
  Exn (exception_name e) (exn_carry p).

(* What a handler for [e] asks of a value [x] that its body raised: [Some p]
   if [x] is [e] carrying [p], and then the handler takes it; else [None],
   and [x] goes on. It looks at the name first. *)
Definition exn_match {P : Type} {C : Carried P} (e : exception P) (x : exn)
    : option P :=
  match x with
  | Exn name carried =>
    if String.eqb name (exception_name e) then exn_carried carried else None
  end.

(* The exception [Misc.Fatal_error], which [Misc.fatal_error] raises after it
   has printed the message; OCaml's [Not_found]; and [Assert_failure], which
   a failed assertion raises. ([Division_by_zero] is below, with the
   division.) They are definitions: their names are known, and Rocq computes
   that a handler for one of them does not take another.
   PORT-GAP(loose): OCaml's [Assert_failure] carries the place of the
   assertion that failed; here it carries nothing, so two assertions that
   fail are not told apart. *)
Definition Fatal_error : exception unit :=
  {| exception_name := "Misc.Fatal_error" |}.
Definition Not_found : exception unit := {| exception_name := "Not_found" |}.
Definition Assert_failure : exception unit :=
  {| exception_name := "Assert_failure" |}.

(* ------------------------------------------------------------------ *)
(* The monad                                                          *)
(* ------------------------------------------------------------------ *)

(* How a computation ends. The state is kept in every case but the last:
   OCaml does not undo a write when an exception passes. A FATAL ERROR HAS
   NO END OF ITS OWN: it is the exception [Misc.Fatal_error], as it is in
   OCaml, and such a run ends [Raised] with the value of that exception
   ([fatal_exn] in Kit_laws.v). *)
Inductive result (A : Type) : Type :=
| Returned (a : A) (s : ocaml_state)
| Raised (e : exn) (s : ocaml_state)
| Out_of_fuel.

Arguments Returned {A}.
Arguments Raised {A}.
Arguments Out_of_fuel {A}.

(* A computation: a function of THE FUEL, a number, and of the state. The
   fuel is what the recursions that Rocq cannot see to end go down on (see
   [fuel] below). No end holds it: so no computation changes it, and
   everything that one run runs is run with the same fuel. A computation may
   look at it. It is an inductive type, not an abbreviation of a function
   type, so that no function of the port can be taken for a computation or
   a computation for a function: only the operations of this file make and
   run one. The ported files never write [Make_M] or [run]. *)
Inductive M (A : Type) : Type :=
  Make_M (f : nat -> ocaml_state -> result A).

(* [run m n s]: how [m] ends when it is run with the fuel [n] from the state
   [s]. *)
Definition run {A : Type} (m : M A) (n : nat) (s : ocaml_state) : result A :=
  match m with Make_M f => f n s end.

Definition ret {A : Type} (a : A) : M A := Make_M (fun _ s => Returned a s).

Definition bind {A B : Type} (m : M A) (k : A -> M B) : M B :=
  Make_M (fun n s =>
    match run m n s with
    | Returned a s => run (k a) n s
    | Raised e s => Raised e s
    | Out_of_fuel => Out_of_fuel
    end).

(* [let* x := e in k] is OCaml's [let x = e in k]. [let! tmp1 := e in k] is
   the same in Rocq; it is written for a call that the compiler's code has
   INSIDE another call, and the extraction puts [e] back where [tmp1] is
   used (GUIDE.md, section 2). *)
Notation "'let*' x ':=' m 'in' k" := (bind m (fun x => k))
  (at level 10, x name, m at level 200, k at level 200,
   format "'[v' 'let*'  x  ':='  m  'in' '/' k ']'").
Notation "'let*' ' p ':=' m 'in' k" :=
  (bind m (fun x => match x with p => k end))
  (at level 10, p strict pattern, m at level 200, k at level 200,
   format "'[v' 'let*'  ' p  ':='  m  'in' '/' k ']'").
Notation "'let!' x ':=' m 'in' k" := (bind m (fun x => k))
  (at level 10, x name, m at level 200, k at level 200,
   format "'[v' 'let!'  x  ':='  m  'in' '/' k ']'").

(* [let& x := v in k] is OCaml's [let x = v in k] where [v] is a VALUE and
   not a call: a constant, a constructor, a local function. Here it is
   Rocq's own [let]; the extraction keeps it where it is. *)
Notation "'let&' x ':=' v 'in' k" := (let x := v in k)
  (at level 10, x name, v at level 200, k at level 200,
   format "'[v' 'let&'  x  ':='  v  'in' '/' k ']'").

(* [m ;; k] is OCaml's [m; k]. *)
Definition seq {B : Type} (m : M unit) (k : M B) : M B := bind m (fun _ => k).
Notation "m ;; k" := (seq m k) (at level 100, right associativity).

(* A LABEL OF THE COMPILER'S TEXT, FOR THE READER ONLY. [~l:x] is [x]: Rocq
   reads the label [l] and throws it away. So [f ~body:b ~is_cold:false k]
   is [f b false k]: the arguments stay by place (GUIDE.md, section 1).
   NOTHING CHECKS A LABEL: Rocq takes a wrong one, and one at the wrong
   argument. Rocq never prints one, and the extracted text has none. There
   is no pun: OCaml's [~l] alone is written [~l:l]. An argument that is an
   application is in brackets, [~l:(Some x)]; without them [~l:Some x] is
   two arguments. The label [by] cannot be written: it is a word of Rocq.
   A label is read only where an argument stands. A term that BEGINS with
   one ([(~l:x)], [let* y := ~l:x in]) is no label: Rocq reads its negation
   of [l], with a cast to [x]. Rocq refuses that where [l] is no proposition,
   and takes it, as that negation, where it is one: with [P : Prop],
   [(~P : Prop)] is [P -> False]. So never write a label there.
   Rocq's negation [~ P] begins with the same sign. Rocq warns of that
   where the notation is made, and again in every file that imports this
   one: the line before the notation switches that warning off, here and
   in those files. Both notations are read (tried with Rocq 9.3.0). *)
#[export] Set Warnings "-notation-incompatible-prefix".
Notation "~ l : x" := x (at level 9, l name, x at level 9, only parsing).


(* ------------------------------------------------------------------ *)
(* Fatal errors and assertions                                        *)
(* ------------------------------------------------------------------ *)

(* The arguments that follow a format, of any types. *)
Inductive fmt_args : Type :=
| Fmt_nil
| Fmt_cons {A : Type} (a : A) (rest : fmt_args).


(* What [Misc.fatal_error] and [Misc.fatal_errorf] do before they raise:
   they print the message, which runs the printers given for [%a]. A printer
   is a declared function like any other: it may change the state or raise.
   Nothing is stated of it here (a contract: contracts/Port_monad.v). *)
Parameter print_fatal_message : string -> fmt_args -> M unit.

(* [raise e] for a value [e] of type [exn]. *)
Definition raise_exn {A : Type} (e : exn) : M A :=
  Make_M (fun _ s => Raised e s).

(* [raise (E p)]; for a constant exception [raise_ E tt] is [raise E]. A
   constant exception is declared with the string "E"; one with an argument
   with the string "(fun x__1 -> E x__1)". *)
Definition raise_ {P A : Type} {C : Carried P} (e : exception P) (p : P)
    : M A :=
  raise_exn (exn_make e p).

(* [Misc.fatal_error msg]: the printing, then [raise Misc.Fatal_error]. So
   it never returns, whatever the printing does (Kit_laws.v). That it ends in
   a fatal error, and not in an exception that the printing raises, needs a
   contract of the printing. *)
Definition fatal_error {A : Type} (message : string) : M A :=
  bind (print_fatal_message "%s" (Fmt_cons message Fmt_nil))
    (fun _ => raise_ Fatal_error tt).

(* [Misc.fatal_errorf fmt a1 .. an]: [fatal_errorfN] for N arguments after
   the format. The end of the run does not hold the message. *)
Definition fatal_errorf_args {A : Type} (format : string) (args : fmt_args)
    : M A :=
  bind (print_fatal_message format args)
    (fun _ => raise_ Fatal_error tt).
Definition fatal_errorf0 {A : Type} (format : string) : M A :=
  fatal_errorf_args format Fmt_nil.
Definition fatal_errorf1 {A A1 : Type} (format : string)
    (a1 : A1) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 Fmt_nil).
Definition fatal_errorf2 {A A1 A2 : Type} (format : string)
    (a1 : A1) (a2 : A2) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 Fmt_nil)).
Definition fatal_errorf3 {A A1 A2 A3 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 Fmt_nil))).
Definition fatal_errorf4 {A A1 A2 A3 A4 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 Fmt_nil)))).
Definition fatal_errorf5 {A A1 A2 A3 A4 A5 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 Fmt_nil))))).
Definition fatal_errorf6 {A A1 A2 A3 A4 A5 A6 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 Fmt_nil)))))).
Definition fatal_errorf7 {A A1 A2 A3 A4 A5 A6 A7 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 Fmt_nil))))))).
Definition fatal_errorf8 {A A1 A2 A3 A4 A5 A6 A7 A8 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 Fmt_nil)))))))).
Definition fatal_errorf9 {A A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) (a9 : A9) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 (Fmt_cons a9 Fmt_nil))))))))).
Definition fatal_errorf10 {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 (Fmt_cons a9 (Fmt_cons a10 Fmt_nil)))))))))).
Definition fatal_errorf11 {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 (Fmt_cons a9 (Fmt_cons a10 (Fmt_cons a11 Fmt_nil))))))))))).
Definition fatal_errorf12 {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) (a12 : A12) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 (Fmt_cons a9 (Fmt_cons a10 (Fmt_cons a11 (Fmt_cons a12 Fmt_nil)))))))))))).
Definition fatal_errorf13 {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) (a12 : A12) (a13 : A13) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 (Fmt_cons a9 (Fmt_cons a10 (Fmt_cons a11 (Fmt_cons a12 (Fmt_cons a13 Fmt_nil))))))))))))).
Definition fatal_errorf14 {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) (a12 : A12) (a13 : A13) (a14 : A14) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 (Fmt_cons a9 (Fmt_cons a10 (Fmt_cons a11 (Fmt_cons a12 (Fmt_cons a13 (Fmt_cons a14 Fmt_nil)))))))))))))).
Definition fatal_errorf15 {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) (a12 : A12) (a13 : A13) (a14 : A14) (a15 : A15) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 (Fmt_cons a9 (Fmt_cons a10 (Fmt_cons a11 (Fmt_cons a12 (Fmt_cons a13 (Fmt_cons a14 (Fmt_cons a15 Fmt_nil))))))))))))))).
Definition fatal_errorf16 {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type} (format : string)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) (a12 : A12) (a13 : A13) (a14 : A14) (a15 : A15) (a16 : A16) : M A :=
  fatal_errorf_args format
    (Fmt_cons a1 (Fmt_cons a2 (Fmt_cons a3 (Fmt_cons a4 (Fmt_cons a5 (Fmt_cons a6 (Fmt_cons a7 (Fmt_cons a8 (Fmt_cons a9 (Fmt_cons a10 (Fmt_cons a11 (Fmt_cons a12 (Fmt_cons a13 (Fmt_cons a14 (Fmt_cons a15 (Fmt_cons a16 Fmt_nil)))))))))))))))).

(* The value of [Assert_failure (file, line, column)] that a failed
   assertion raises. It is an exception like another: a handler for every
   exception catches it, one for [Misc.Fatal_error] does not. *)
Definition assert_failure : exn := exn_make Assert_failure tt.

(* [assert b]. (The port assumes that the compiler is built with its
   assertions, as it is.) *)
Definition assert_ (b : bool) : M unit :=
  if b then ret tt else raise_exn assert_failure.

(* [assert false]. *)
Definition assert_false {A : Type} : M A := raise_exn assert_failure.

(* ------------------------------------------------------------------ *)
(* Handlers                                                           *)
(* ------------------------------------------------------------------ *)

(* [try body () with E p -> handler p]. *)
Definition try_with {P A : Type} {C : Carried P} (body : unit -> M A)
    (e : exception P) (handler : P -> M A) : M A :=
  Make_M (fun n s =>
    match run (body tt) n s with
    | Raised x s =>
      match exn_match e x with
      | Some p => run (handler p) n s
      | None => Raised x s
      end
    | r => r
    end).

(* [try body () with e -> handler e]: every exception. *)
Definition try_with_any {A : Type} (body : unit -> M A)
    (handler : exn -> M A) : M A :=
  Make_M (fun n s =>
    match run (body tt) n s with
    | Raised x s => run (handler x) n s
    | r => r
    end).

(* [match body () with exception E p -> handler p | x -> k x]: only what
   [body] raises is caught, not what [k] raises. *)
Definition match_exn {P A B : Type} {C : Carried P} (body : unit -> M A)
    (e : exception P) (handler : P -> M B) (k : A -> M B) : M B :=
  Make_M (fun n s =>
    match run (body tt) n s with
    | Returned a s => run (k a) n s
    | Raised x s =>
      match exn_match e x with
      | Some p => run (handler p) n s
      | None => Raised x s
      end
    | Out_of_fuel => Out_of_fuel
    end).

(* ------------------------------------------------------------------ *)
(* Recursion that Rocq cannot see to end                              *)
(* ------------------------------------------------------------------ *)

(* Such a function takes [fuel] as its FIRST argument and is a [Fixpoint]
   on it whose body is [recursive! fuel in BODY], the recursive calls of BODY
   with that smaller [fuel]. A caller that is not itself in the recursion
   writes [let_fuel! fuel in]. In the implementation that is extracted the
   fuel is a proposition, which Rocq's extraction erases: the OCaml function
   is the compiler's [let rec], and it does not run out. No axiom is used
   here. What this file says of a function can only be about runs for which
   the fuel was enough; that it holds of the extracted OCaml is not
   established (GUIDE.md, section 8).
   The fuel of a run is the number that [run] takes. [let_fuel! fuel in k]
   is [k] with that number as a value of type [fuel]: a function that it
   makes with that value (a function given its fuel only) holds the fuel of
   the run. *)
Inductive fuel : Type :=
| Out
| More (fuel : fuel).

Fixpoint fuel_of_nat (n : nat) : fuel :=
  match n with
  | O => Out
  | S n => More (fuel_of_nat n)
  end.

Definition get_fuel (_ : unit) : M fuel :=
  Make_M (fun n s => Returned (fuel_of_nat n) s).

Definition out_of_fuel {A : Type} : M A := Make_M (fun _ _ => Out_of_fuel).

Notation "'recursive!' f 'in' k" :=
  (match f with Out => out_of_fuel | More f => k end)
  (at level 10, f name, k at level 200,
   format "'[v' 'recursive!'  f  'in' '/' k ']'").
Notation "'let_fuel!' f 'in' k" := (bind (get_fuel tt) (fun f => k))
  (at level 10, f name, k at level 200,
   format "'[v' 'let_fuel!'  f  'in' '/' k ']'").

(* [while cond () do body () done]. *)
Fixpoint while_fuel (n : nat) (cond : unit -> M bool) (body : unit -> M unit)
    : M unit :=
  match n with
  | O => out_of_fuel
  | S n =>
    bind (cond tt) (fun b =>
      if b then bind (body tt) (fun _ => while_fuel n cond body) else ret tt)
  end.

Definition while_ (cond : unit -> M bool) (body : unit -> M unit) : M unit :=
  Make_M (fun n s => run (while_fuel n cond body) n s).

(* ------------------------------------------------------------------ *)
(* References and lazy values                                         *)
(* ------------------------------------------------------------------ *)

(* OCaml's ['a ref], [ref x], [!r], [r := x]. Their
   contents are in [ocaml_state]; nothing is stated of them yet. *)
Parameter ref : Type -> Type.
Parameter mk_ref : forall {A : Type}, A -> M (ref A).
Parameter get : forall {A : Type}, ref A -> M A.
Parameter set : forall {A : Type}, ref A -> A -> M unit.

(* OCaml's ['a Lazy.t], [lazy (body ())] (extracted as [Lazy.from_fun body]),
   [Lazy.force]. *)
Parameter lazy_t : Type -> Type.
Parameter lazy_ : forall {A : Type}, (unit -> M A) -> M (lazy_t A).
Parameter force : forall {A : Type}, lazy_t A -> M A.

(* OCaml's arrays. They can be written to: every operation on one is a
   declared function, in [M]. The two array literals that the compiler's
   files of Simplify write: [[||]], which is one value, and [[| x |]], which
   makes an array anew each time and so is in [M]. *)
Parameter array : Type -> Type.
Parameter array_empty : forall {A : Type}, array A.
Parameter array_singleton : forall {A : Type}, A -> M (array A).

(* ------------------------------------------------------------------ *)
(* OCaml's values that Rocq's own types stand for                     *)
(* ------------------------------------------------------------------ *)

(* [int] is Rocq's [Z]: the operations of [Z] on it are pure. OCaml's
   integers wrap at 63 bits and Rocq's do not. The literals 0 and 1 are
   written as they are; any other literal has a name ([i2] .. [i16] here; a
   file declares what else it needs, GUIDE.md): Rocq's extraction has no
   direct way to print one. *)
Definition int : Type := Z.
Definition i2 : int := 2%Z.
Definition i3 : int := 3%Z.
Definition i4 : int := 4%Z.
Definition i5 : int := 5%Z.
Definition i6 : int := 6%Z.
Definition i7 : int := 7%Z.
Definition i8 : int := 8%Z.
Definition i9 : int := 9%Z.
Definition i10 : int := 10%Z.
Definition i16 : int := 16%Z.

(* Tuples of three to six: [T3 a b c] is OCaml's [(a, b, c)], in terms and
   in patterns. *)
Inductive tuple3 (A B C : Type) : Type := T3 (a : A) (b : B) (c : C).
Inductive tuple4 (A B C D : Type) : Type := T4 (a : A) (b : B) (c : C) (d : D).
Inductive tuple5 (A B C D E : Type) : Type :=
  T5 (a : A) (b : B) (c : C) (d : D) (e : E).
Inductive tuple6 (A B C D E F : Type) : Type :=
  T6 (a : A) (b : B) (c : C) (d : D) (e : E) (f : F).
Arguments T3 {A B C}.
Arguments T4 {A B C D}.
Arguments T5 {A B C D E}.
Arguments T6 {A B C D E F}.

(* OCaml's [a <> b] on integers. *)
Definition int_neq (a b : int) : bool := negb (Z.eqb a b).
Notation "a <>? b" := (int_neq a b) (at level 70, no associativity).

(* OCaml's [a / b] and [a mod b] on integers: they round towards zero and
   raise [Division_by_zero]. *)
Definition Division_by_zero : exception unit :=
  {| exception_name := "Division_by_zero" |}.
Definition int_div (a b : int) : M int :=
  if Z.eqb b 0 then raise_ Division_by_zero tt else ret (Z.quot a b).
Definition int_mod (a b : int) : M int :=
  if Z.eqb b 0 then raise_ Division_by_zero tt else ret (Z.rem a b).

(* OCaml's [a || b] and [a && b] where [b] is a call: [b] is not run when
   [a] decides. ([a] is a value: a call there is a [let!] before.) *)
Definition or_else (a : bool) (b : M bool) : M bool :=
  if a then ret true else b.
Definition and_then (a : bool) (b : M bool) : M bool :=
  if a then b else ret false.

(* OCaml's polymorphic comparisons and physical equality. *)
Parameter poly_equal : forall {A : Type}, A -> A -> M bool.
Parameter poly_not_equal : forall {A : Type}, A -> A -> M bool.
Parameter poly_compare : forall {A : Type}, A -> A -> M int.
Parameter phys_equal : forall {A : Type}, A -> A -> M bool.
Parameter phys_not_equal : forall {A : Type}, A -> A -> M bool.

(* A PARTIAL APPLICATION, where the compiler gives a function only its first
   arguments and passes the result on ([~f:(Flow.Acc.exit_continuation k)],
   [~simplify_expr]): [let! tmp1 := papp1 f a in]. In OCaml it is [f a].
   The types say that at least one argument is still to come, so the
   result is a function and never a computation. This is right for OCaml
   where the DEFINITION of [f] has more parameters than the use gives it
   arguments: OCaml then runs nothing of [f]. The interface does not say
   how many parameters the definition has. tools/lint.py checks it for
   each use of a declared function, against decl/ARITIES.tsv (GUIDE.md,
   section 2); a use for which it does not hold, or is not known, has the
   mark PORT-GAP(papp), which says what runs there. *)
Definition papp1 {A B C : Type} (f : A -> B -> C) (a : A) : M (B -> C) :=
  ret (f a).
Definition papp2 {A1 A2 B C : Type} (f : A1 -> A2 -> B -> C) (a1 : A1)
    (a2 : A2) : M (B -> C) := ret (f a1 a2).
Definition papp3 {A1 A2 A3 B C : Type} (f : A1 -> A2 -> A3 -> B -> C)
    (a1 : A1) (a2 : A2) (a3 : A3) : M (B -> C) := ret (f a1 a2 a3).
Definition papp4 {A1 A2 A3 A4 B C : Type}
    (f : A1 -> A2 -> A3 -> A4 -> B -> C) (a1 : A1) (a2 : A2) (a3 : A3)
    (a4 : A4) : M (B -> C) := ret (f a1 a2 a3 a4).

(* [ignore x]. *)
Definition ignore {A : Type} (_ : A) : M unit := ret tt.

Unset Implicit Arguments.
