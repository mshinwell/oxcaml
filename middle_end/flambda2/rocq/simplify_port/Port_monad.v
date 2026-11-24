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

(* The kit of the port of Simplify: the monad in which every ported function
   and every declared function of OxCaml answers, its operations, and what
   each becomes in the extracted OCaml. Read GUIDE.md first.

   This file follows no file of the compiler.

   In Rocq a value of [M A] is a function of the world. In the extracted
   OCaml [M A] is [A]: the tool tools/unmonad removes [bind] and [ret], and
   each other operation becomes the OCaml that its directive names. So an
   operation here is a real definition for Rocq and a piece of syntax for
   OCaml. *)

From Stdlib Require Export String List ZArith Bool.
From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZInt.
Export ListNotations.

Set Implicit Arguments.

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
   has printed the message. *)
Parameter Fatal_error : exception unit.
Extract Inlined Constant Fatal_error => "Misc.Fatal_error".

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

Definition M (A : Type) : Type := world -> result A.

Definition ret {A : Type} (a : A) : M A := fun w => Returned a w.

Definition bind {A B : Type} (m : M A) (k : A -> M B) : M B :=
  fun w =>
    match m w with
    | Returned a w => k a w
    | Fatal message w => Fatal message w
    | Raised e w => Raised e w
    | Out_of_fuel => Out_of_fuel
    end.

(* [let* x := e in k] is OCaml's [let x = e in k]; [e ;; k] is [e; k]. *)
Notation "'let*' x ':=' m 'in' k" := (bind m (fun x => k))
  (at level 10, x name, m at level 200, k at level 200,
   format "'[v' 'let*'  x  ':='  m  'in' '/' k ']'").
Notation "'let*' ' p ':=' m 'in' k" :=
  (bind m (fun x => match x with p => k end))
  (at level 10, p strict pattern, m at level 200, k at level 200,
   format "'[v' 'let*'  ' p  ':='  m  'in' '/' k ']'").
Notation "m ;; k" := (bind m (fun _ : unit => k))
  (at level 100, right associativity).

(* The type and the two operations are removed by tools/unmonad. *)
Extract Constant M "'a" => "'a".
Extract Inlined Constant ret => "port__ret".
Extract Inlined Constant bind => "port__bind".

(* ------------------------------------------------------------------ *)
(* Fatal errors and assertions                                        *)
(* ------------------------------------------------------------------ *)

(* [Misc.fatal_error msg]. *)
Definition fatal_error {A : Type} (message : string) : M A :=
  fun w => Fatal message w.
Extract Inlined Constant fatal_error => "Misc.fatal_error".

(* The arguments of a format: [Misc.fatal_errorf "%a is wrong:@ %a" print x
   print y] is written [fatal_errorf "%a is wrong:@ %a" (fmt: print; x;
   print; y)]. The tool writes the arguments after the format again. Every
   function with a format argument is declared so. *)
Inductive fmt_args : Type :=
| Fmt_nil
| Fmt_cons {A : Type} (a : A) (rest : fmt_args).

Notation "'(fmt:' ')'" := Fmt_nil.
Notation "'(fmt:' x ; .. ; y ')'" := (Fmt_cons x .. (Fmt_cons y Fmt_nil) ..).

Extract Inductive fmt_args => "port__fmt_args"
  [ "port__fmt_nil" "port__fmt_cons" ].

(* [Misc.fatal_errorf fmt args]. In Rocq the message is the format. *)
Definition fatal_errorf {A : Type} (format : string) (args : fmt_args) : M A :=
  fun w => Fatal format w.
Extract Inlined Constant fatal_errorf => "Misc.fatal_errorf".

(* [assert b]. *)
Definition assert_ (b : bool) : M unit :=
  fun w => if b then Returned tt w else Fatal "Assert_failure" w.
Extract Inlined Constant assert_ => "(fun x__1 -> assert x__1)".

(* [assert false]. *)
Definition assert_false {A : Type} : M A :=
  fun w => Fatal "Assert_failure" w.
Extract Inlined Constant assert_false => "(assert false)".

(* A thing of the compiler's file that is not ported yet: the extracted code
   stops with a fatal error that names it. Used as the realisation of a
   parameter marked PORT-GAP(unported):
     Extract Inlined Constant f => "(port__gap ""Foo.f"")". *)

(* ------------------------------------------------------------------ *)
(* Exceptions                                                         *)
(* ------------------------------------------------------------------ *)

(* [raise (E p)]; for a constant exception [raise_ E tt] is [raise E]. *)
Definition raise_ {P A : Type} (e : exception P) (p : P) : M A :=
  fun w => Raised (exn_make e p) w.
Extract Inlined Constant raise_ => "port__raise".

(* [raise e] for a value [e] that a handler caught. *)
Definition raise_exn {A : Type} (e : exn) : M A := fun w => Raised e w.
Extract Inlined Constant raise_exn => "raise".

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
  fun w =>
    let r := body tt w in
    match caught e r with
    | Some (p, w) => handler p w
    | None => r
    end.
Extract Inlined Constant try_with => "port__try_with".

(* [try body () with e -> handler e]: every exception. *)
Definition try_with_any {A : Type} (body : unit -> M A)
    (handler : exn -> M A) : M A :=
  fun w =>
    match body tt w with
    | Raised x w => handler x w
    | Fatal _ w => handler (exn_make Fatal_error tt) w
    | r => r
    end.
Extract Inlined Constant try_with_any => "port__try_with_any".

(* [match body () with exception E p -> handler p | x -> k x]: only what
   [body] raises is caught, not what [k] raises. *)
Definition match_exn {P A B : Type} (body : unit -> M A) (e : exception P)
    (handler : P -> M B) (k : A -> M B) : M B :=
  fun w =>
    let r := body tt w in
    match caught e r with
    | Some (p, w) => handler p w
    | None =>
      match r with
      | Returned a w => k a w
      | Fatal message w => Fatal message w
      | Raised x w => Raised x w
      | Out_of_fuel => Out_of_fuel
      end
    end.
Extract Inlined Constant match_exn => "port__match_exn".

(* ------------------------------------------------------------------ *)
(* Recursion that Rocq cannot see to end                              *)
(* ------------------------------------------------------------------ *)

(* Such a function takes [fuel] as its FIRST argument and is a [Fixpoint]
   on it: [match fuel with Out => out_of_fuel | More fuel => BODY end], the
   recursive calls of BODY with the smaller [fuel]. A caller that is not
   itself in the recursion writes [let* fuel := get_fuel tt in]. In OCaml
   the fuel is [()] and never runs out, and the tool removes it. What the
   Rocq function says of an OCaml run is therefore said only of runs for
   which the fuel of the world was enough. *)
Inductive fuel : Type :=
| Out
| More (fuel : fuel).

Fixpoint fuel_of_nat (n : nat) : fuel :=
  match n with
  | O => Out
  | S n => More (fuel_of_nat n)
  end.

Definition get_fuel (_ : unit) : M fuel :=
  fun w => Returned (fuel_of_nat (world_fuel w)) w.
Extract Inlined Constant get_fuel => "port__get_fuel".

Definition out_of_fuel {A : Type} : M A := fun _ => Out_of_fuel.
Extract Inlined Constant out_of_fuel => "port__out_of_fuel".

Extract Inductive fuel => "unit" [ "()" "(fun _ -> ())" ]
  "(fun f__1 f__2 x__0 -> f__2 x__0)".

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
  fun w => while_fuel (world_fuel w) cond body w.
Extract Inlined Constant while_ =>
  "(fun f__1 f__2 -> while f__1 () do f__2 () done)".

(* ------------------------------------------------------------------ *)
(* References and lazy values                                         *)
(* ------------------------------------------------------------------ *)

(* OCaml's ['a ref], [ref x], [!r], [r := x], [incr r], [decr r]. Their
   contents are in [ocaml_state]; nothing is stated of them yet. *)
Parameter ref : Type -> Type.
Extract Constant ref "'a" => "'a ref".
Parameter mk_ref : forall {A : Type}, A -> M (ref A).
Extract Inlined Constant mk_ref => "ref".
Parameter get : forall {A : Type}, ref A -> M A.
Extract Inlined Constant get => "(!)".
Parameter set : forall {A : Type}, ref A -> A -> M unit.
Extract Inlined Constant set => "(:=)".

(* OCaml's ['a Lazy.t], [lazy (body ())], [Lazy.force]. *)
Parameter lazy_t : Type -> Type.
Extract Constant lazy_t "'a" => "'a Lazy.t".
Parameter lazy_ : forall {A : Type}, (unit -> M A) -> M (lazy_t A).
Extract Inlined Constant lazy_ => "(fun f__1 -> lazy (f__1 ()))".
Parameter force : forall {A : Type}, lazy_t A -> M A.
Extract Inlined Constant force => "Lazy.force".

(* ------------------------------------------------------------------ *)
(* OCaml's values that Rocq's own types stand for                     *)
(* ------------------------------------------------------------------ *)

(* [int] is Rocq's [Z] (ExtrOcamlZInt): the literals and the operations
   below are pure. OCaml's integers wrap at 63 bits and Rocq's do not. *)
Definition int : Type := Z.
Extract Inlined Constant int => "int".
Extract Inlined Constant Z.add => "(+)".
Extract Inlined Constant Z.sub => "(-)".
Extract Inlined Constant Z.mul => "( * )".
Extract Inlined Constant Z.opp => "(~-)".
Extract Inlined Constant Z.succ => "succ".
Extract Inlined Constant Z.pred => "pred".
Extract Inlined Constant Z.max => "max".
Extract Inlined Constant Z.min => "min".
Extract Inlined Constant Z.eqb => "(=)".
Extract Inlined Constant Z.ltb => "(<)".
Extract Inlined Constant Z.leb => "(<=)".
Extract Inlined Constant Z.gtb => "(>)".
Extract Inlined Constant Z.geb => "(>=)".
Extract Inlined Constant negb => "not".
Extract Inlined Constant String.eqb => "String.equal".
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant List.app => "(@)".

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
Extract Inductive tuple3 => "port__tuple3" [ "" ].
Extract Inductive tuple4 => "port__tuple4" [ "" ].
Extract Inductive tuple5 => "port__tuple5" [ "" ].
Extract Inductive tuple6 => "port__tuple6" [ "" ].

(* OCaml's polymorphic comparisons and physical equality. *)
Parameter poly_equal : forall {A : Type}, A -> A -> M bool.
Extract Inlined Constant poly_equal => "(=)".
Parameter poly_not_equal : forall {A : Type}, A -> A -> M bool.
Extract Inlined Constant poly_not_equal => "(<>)".
Parameter poly_compare : forall {A : Type}, A -> A -> M int.
Extract Inlined Constant poly_compare => "compare".
Parameter phys_equal : forall {A : Type}, A -> A -> M bool.
Extract Inlined Constant phys_equal => "(==)".
Parameter phys_not_equal : forall {A : Type}, A -> A -> M bool.
Extract Inlined Constant phys_not_equal => "(!=)".

(* [ignore x]. *)
Definition ignore {A : Type} (_ : A) : M unit := ret tt.
Extract Inlined Constant ignore => "ignore".

Unset Implicit Arguments.
