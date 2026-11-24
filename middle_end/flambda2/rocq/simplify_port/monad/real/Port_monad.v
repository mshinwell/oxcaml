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
   says what a ported function does (the world, fatal errors, exceptions, the
   fuel). Every ported function and every declared function of OxCaml answers
   in [M]. This file follows no file of the compiler. Read GUIDE.md first.

   The ported files are compiled twice, against two files of this name with
   the same operations and notations: this one, and monad/id/Port_monad.v, in
   which [M A] is [A] and from which Rocq extracts the OCaml. Nothing is
   extracted from this one, and statements about the port are statements
   about this one. *)

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
(* The world                                                          *)
(* ------------------------------------------------------------------ *)

(* Everything mutable in the OCaml program that the port does not define:
   the counters from which [Int_ids] and the other modules make new names,
   the contents of every reference and table, the flags, the channels. It
   is not described in this version: the declared functions are parameters
   that read and change it. *)
Parameter ocaml_state : Type.

(* The fuel is what the recursions that Rocq cannot see to end go down on
   (see [fuel] below). It is not changed by any operation. *)
Record world : Type := {
  world_fuel : nat;
  world_state : ocaml_state
}.

(* A value of OCaml's type [exn], and a declared exception constructor whose
   argument has type [P] ([unit] for a constant exception). *)
Parameter exn : Type.
Parameter exception : Type -> Type.
Parameter exn_make : forall {P : Type}, exception P -> P -> exn.
Parameter exn_match : forall {P : Type}, exception P -> exn -> option P.

(* The exception [Misc.Fatal_error], which [Misc.fatal_error] raises after it
   has printed the message, and OCaml's [Not_found]. *)
Parameter Fatal_error : exception unit.
Parameter Not_found : exception unit.

(* ------------------------------------------------------------------ *)
(* The monad                                                          *)
(* ------------------------------------------------------------------ *)

(* How a computation ends. The world is kept in every case but the last:
   OCaml does not undo a write when an exception passes. *)
Inductive result (A : Type) : Type :=
| Returned (a : A) (w : world)
| Fatal (message : string) (w : world)
| Raised (e : exn) (w : world)
| Out_of_fuel.

Arguments Returned {A}.
Arguments Fatal {A}.
Arguments Raised {A}.
Arguments Out_of_fuel {A}.

(* A computation. It is an inductive type, not an abbreviation of a function
   type, so that no function of the port can be taken for a computation or
   a computation for a function: only the operations of this file make and
   run one. The ported files never write [Make_M] or [run]. *)
Inductive M (A : Type) : Type := Make_M (f : world -> result A).

Definition run {A : Type} (m : M A) (w : world) : result A :=
  match m with Make_M f => f w end.

Definition ret {A : Type} (a : A) : M A := Make_M (fun w => Returned a w).

Definition bind {A B : Type} (m : M A) (k : A -> M B) : M B :=
  Make_M (fun w =>
    match run m w with
    | Returned a w => run (k a) w
    | Fatal message w => Fatal message w
    | Raised e w => Raised e w
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


(* ------------------------------------------------------------------ *)
(* Fatal errors and assertions                                        *)
(* ------------------------------------------------------------------ *)

(* The arguments that follow a format, of any types. *)
Inductive fmt_args : Type :=
| Fmt_nil
| Fmt_cons {A : Type} (a : A) (rest : fmt_args).


(* What [Misc.fatal_error] and [Misc.fatal_errorf] do before they raise:
   they print the message, which runs the printers given for [%a]. A printer
   is a declared function like any other: it may change the world or raise.
   Nothing is stated of it. *)
Parameter print_fatal_message : string -> fmt_args -> M unit.

(* [Misc.fatal_error msg]. *)
Definition fatal_error {A : Type} (message : string) : M A :=
  bind (print_fatal_message "%s" (Fmt_cons message Fmt_nil))
    (fun _ => Make_M (fun w => Fatal message w)).

(* [Misc.fatal_errorf fmt a1 .. an]: [fatal_errorfN] for N arguments after
   the format. In Rocq the message is the format. *)
Definition fatal_errorf_args {A : Type} (format : string) (args : fmt_args)
    : M A :=
  bind (print_fatal_message format args)
    (fun _ => Make_M (fun w => Fatal format w)).
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
   exception catches it, one for [Misc.Fatal_error] does not.
   PORT-GAP(loose): OCaml's exception carries the place of the assertion
   that failed; here ONE value stands for every place, so two assertions
   that fail are not told apart. *)
Parameter assert_failure : exn.

(* [assert b]. (The port assumes that the compiler is built with its
   assertions, as it is.) *)
Definition assert_ (b : bool) : M unit :=
  Make_M (fun w => if b then Returned tt w else Raised assert_failure w).

(* [assert false]. *)
Definition assert_false {A : Type} : M A :=
  Make_M (fun w => Raised assert_failure w).

(* ------------------------------------------------------------------ *)
(* Exceptions                                                         *)
(* ------------------------------------------------------------------ *)

(* [raise (E p)]; for a constant exception [raise_ E tt] is [raise E]. A
   constant exception is declared with the string "E"; one with an argument
   with the string "(fun x__1 -> E x__1)". *)
Definition raise_ {P A : Type} (e : exception P) (p : P) : M A :=
  Make_M (fun w => Raised (exn_make e p) w).

(* [raise e] for a value [e] that a handler caught. *)
Definition raise_exn {A : Type} (e : exn) : M A :=
  Make_M (fun w => Raised e w).

(* Which handler takes the end of a computation. A fatal error is the
   exception [Misc.Fatal_error]. *)
Definition caught {P A : Type} (e : exception P) (r : result A)
    : option (P * world) :=
  match r with
  | Raised x w =>
    match exn_match e x with
    | Some p => Some (p, w)
    | None => None
    end
  | Fatal _ w =>
    match exn_match e (exn_make Fatal_error tt) with
    | Some p => Some (p, w)
    | None => None
    end
  | Returned _ _ | Out_of_fuel => None
  end.

(* [try body () with E p -> handler p]. *)
Definition try_with {P A : Type} (body : unit -> M A) (e : exception P)
    (handler : P -> M A) : M A :=
  Make_M (fun w =>
    let r := run (body tt) w in
    match caught e r with
    | Some (p, w) => run (handler p) w
    | None => r
    end).

(* [try body () with e -> handler e]: every exception. *)
Definition try_with_any {A : Type} (body : unit -> M A)
    (handler : exn -> M A) : M A :=
  Make_M (fun w =>
    match run (body tt) w with
    | Raised x w => run (handler x) w
    | Fatal _ w => run (handler (exn_make Fatal_error tt)) w
    | r => r
    end).

(* [match body () with exception E p -> handler p | x -> k x]: only what
   [body] raises is caught, not what [k] raises. *)
Definition match_exn {P A B : Type} (body : unit -> M A) (e : exception P)
    (handler : P -> M B) (k : A -> M B) : M B :=
  Make_M (fun w =>
    let r := run (body tt) w in
    match caught e r with
    | Some (p, w) => run (handler p) w
    | None =>
      match r with
      | Returned a w => run (k a) w
      | Fatal message w => Fatal message w
      | Raised x w => Raised x w
      | Out_of_fuel => Out_of_fuel
      end
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
   the fuel of the world was enough; that it holds of the extracted OCaml
   is not established (GUIDE.md, section 7). *)
Inductive fuel : Type :=
| Out
| More (fuel : fuel).

Fixpoint fuel_of_nat (n : nat) : fuel :=
  match n with
  | O => Out
  | S n => More (fuel_of_nat n)
  end.

Definition get_fuel (_ : unit) : M fuel :=
  Make_M (fun w => Returned (fuel_of_nat (world_fuel w)) w).

Definition out_of_fuel {A : Type} : M A := Make_M (fun _ => Out_of_fuel).

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
  Make_M (fun w => run (while_fuel (world_fuel w) cond body) w).

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
   declared function, in [M]. *)
Parameter array : Type -> Type.

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
Parameter Division_by_zero : exception unit.
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
   under the assumption that the whole port makes of a declared function:
   it does nothing until it has all the arguments of its interface. *)
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
