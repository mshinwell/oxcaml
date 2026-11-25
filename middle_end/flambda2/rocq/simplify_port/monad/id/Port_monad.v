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

(* THE MONAD OF THE PORT OF SIMPLIFY, ITS IDENTITY IMPLEMENTATION: [M A] is
   [A]. The ported files are compiled against this file only so that Rocq
   extracts them: its extraction then prints OCaml in direct style, with no
   tool after it. This file follows no file of the compiler.

   It has the names of monad/real/Port_monad.v, which is the implementation
   that says what the port means. NOTHING IS TO BE PROVED AGAINST THIS FILE:
   it declares, as parameters that OCaml realises, things that have no
   definition when [M A] is [A] (a fatal error of any type, a fuel that does
   not run out).

   How each notation is extracted (GUIDE.md, sections 2 and 7):
   - [let* x := e in k] is a match on [Box e], a type of one constructor that
     is printed as nothing: Rocq prints the match as [let x = e in k], and,
     the optimisations of matches being off, keeps it where it is even if
     [x] is not used;
   - [e ;; k] is a match on [tt]: [let () = e in k];
   - [let! tmp1 := e in k] is Rocq's own [let]; with the flag that inlines a
     let used once, Rocq writes [e] where [tmp1] is used;
   - [let& x := v in k] is the same match as [let*]: a let that stays;
   - [~l:x] is [x]: the label is not in the term, and is not extracted;
   - the fuel is a proposition, which the extraction erases. *)

From Stdlib Require Export String List ZArith Bool.
From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZInt.
Export ListNotations.

Set Implicit Arguments.

#[export] Unset Elimination Schemes.

(* ------------------------------------------------------------------ *)
(* The monad                                                          *)
(* ------------------------------------------------------------------ *)

Definition M (A : Type) : Type := A.

Definition ret {A : Type} (a : A) : M A := a.
Extraction Inline ret.

Inductive box (A : Type) : Type := Box (a : A).
Arguments Box {A}.
Extract Inductive box => "Port_monad.box" [ "" ].

Notation "'let*' x ':=' m 'in' k" := (match Box m with Box x => k end)
  (at level 10, x name, m at level 200, k at level 200,
   format "'[v' 'let*'  x  ':='  m  'in' '/' k ']'").
Notation "'let*' ' p ':=' m 'in' k" := (match m with p => k end)
  (at level 10, p strict pattern, m at level 200, k at level 200,
   format "'[v' 'let*'  ' p  ':='  m  'in' '/' k ']'").
Notation "'let!' x ':=' m 'in' k" := (let x := m in k)
  (at level 10, x name, m at level 200, k at level 200,
   format "'[v' 'let!'  x  ':='  m  'in' '/' k ']'").
Notation "'let&' x ':=' v 'in' k" := (match Box v with Box x => k end)
  (at level 10, x name, v at level 200, k at level 200,
   format "'[v' 'let&'  x  ':='  v  'in' '/' k ']'").
Notation "m ;; k" := (match m with tt => k end)
  (at level 100, right associativity).

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

Parameter fatal_error : forall {A : Type}, string -> M A.
Extract Inlined Constant fatal_error => "Misc.fatal_error".
Parameter fatal_errorf0 : forall {A : Type}, string -> M A.
Extract Inlined Constant fatal_errorf0 => "Misc.fatal_errorf".
Parameter fatal_errorf1 : forall {A A1 : Type}, string -> A1 -> M A.
Extract Inlined Constant fatal_errorf1 => "Misc.fatal_errorf".
Parameter fatal_errorf2 : forall {A A1 A2 : Type}, string -> A1 -> A2 -> M A.
Extract Inlined Constant fatal_errorf2 => "Misc.fatal_errorf".
Parameter fatal_errorf3 : forall {A A1 A2 A3 : Type}, string -> A1 -> A2 -> A3 -> M A.
Extract Inlined Constant fatal_errorf3 => "Misc.fatal_errorf".
Parameter fatal_errorf4 : forall {A A1 A2 A3 A4 : Type}, string -> A1 -> A2 -> A3 -> A4 -> M A.
Extract Inlined Constant fatal_errorf4 => "Misc.fatal_errorf".
Parameter fatal_errorf5 : forall {A A1 A2 A3 A4 A5 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> M A.
Extract Inlined Constant fatal_errorf5 => "Misc.fatal_errorf".
Parameter fatal_errorf6 : forall {A A1 A2 A3 A4 A5 A6 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> M A.
Extract Inlined Constant fatal_errorf6 => "Misc.fatal_errorf".
Parameter fatal_errorf7 : forall {A A1 A2 A3 A4 A5 A6 A7 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> M A.
Extract Inlined Constant fatal_errorf7 => "Misc.fatal_errorf".
Parameter fatal_errorf8 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> M A.
Extract Inlined Constant fatal_errorf8 => "Misc.fatal_errorf".
Parameter fatal_errorf9 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> M A.
Extract Inlined Constant fatal_errorf9 => "Misc.fatal_errorf".
Parameter fatal_errorf10 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> M A.
Extract Inlined Constant fatal_errorf10 => "Misc.fatal_errorf".
Parameter fatal_errorf11 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> M A.
Extract Inlined Constant fatal_errorf11 => "Misc.fatal_errorf".
Parameter fatal_errorf12 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> M A.
Extract Inlined Constant fatal_errorf12 => "Misc.fatal_errorf".
Parameter fatal_errorf13 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> M A.
Extract Inlined Constant fatal_errorf13 => "Misc.fatal_errorf".
Parameter fatal_errorf14 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> M A.
Extract Inlined Constant fatal_errorf14 => "Misc.fatal_errorf".
Parameter fatal_errorf15 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> M A.
Extract Inlined Constant fatal_errorf15 => "Misc.fatal_errorf".
Parameter fatal_errorf16 : forall {A A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> M A.
Extract Inlined Constant fatal_errorf16 => "Misc.fatal_errorf".

(* [assert_ b] is printed [assert b]. *)
Parameter assert_ : bool -> M unit.
Extract Inlined Constant assert_ => "assert".
Parameter assert_false : forall {A : Type}, M A.
Extract Inlined Constant assert_false => "(assert false)".

(* ------------------------------------------------------------------ *)
(* Exceptions: calls of runtime/port_monad.ml                         *)
(* ------------------------------------------------------------------ *)

Parameter exn : Type.
Extract Inlined Constant exn => "exn".
Parameter exception : Type -> Type.
Extract Constant exception "'p" => "'p Port_monad.exception_".
Parameter Fatal_error : exception unit.
Extract Inlined Constant Fatal_error => "Port_monad.fatal_error_exception".
Parameter Not_found : exception unit.
Extract Inlined Constant Not_found => "Port_monad.not_found".
(* The value [E p] of a declared exception, for a function that takes an
   [exn]. *)
Parameter exn_make : forall {P : Type}, exception P -> P -> exn.
Extract Inlined Constant exn_make => "Port_monad.exn_make".
Parameter raise_ : forall {P A : Type}, exception P -> P -> M A.
Extract Inlined Constant raise_ => "Port_monad.raise_".
Parameter raise_exn : forall {A : Type}, exn -> M A.
Extract Inlined Constant raise_exn => "raise".
Parameter try_with :
  forall {P A : Type}, (unit -> M A) -> exception P -> (P -> M A) -> M A.
Extract Inlined Constant try_with => "Port_monad.try_with".
Parameter try_with_any : forall {A : Type}, (unit -> M A) -> (exn -> M A) -> M A.
Extract Inlined Constant try_with_any => "Port_monad.try_with_any".
Parameter match_exn :
  forall {P A B : Type},
  (unit -> M A) -> exception P -> (P -> M B) -> (A -> M B) -> M B.
Extract Inlined Constant match_exn => "Port_monad.match_exn".

(* ------------------------------------------------------------------ *)
(* Recursion                                                          *)
(* ------------------------------------------------------------------ *)

(* The fuel is a proposition with one constructor: a [Fixpoint] on it is
   accepted, and the extraction erases the argument and the match. Its one
   inhabitant is a parameter: in OCaml the fuel does not run out. *)
Inductive fuel : Prop := More (f : fuel).
Parameter infinite_fuel : fuel.

Notation "'recursive!' f 'in' k" := (match f with More f => k end)
  (at level 10, f name, k at level 200,
   format "'[v' 'recursive!'  f  'in' '/' k ']'").
Notation "'let_fuel!' f 'in' k" := (let f := infinite_fuel in k)
  (at level 10, f name, k at level 200,
   format "'[v' 'let_fuel!'  f  'in' '/' k ']'").

Parameter while_ : (unit -> M bool) -> (unit -> M unit) -> M unit.
Extract Inlined Constant while_ => "Port_monad.while_".

(* ------------------------------------------------------------------ *)
(* References and lazy values                                         *)
(* ------------------------------------------------------------------ *)

Parameter ref : Type -> Type.
Extract Constant ref "'a" => "'a Stdlib.ref".
Parameter mk_ref : forall {A : Type}, A -> M (ref A).
Extract Inlined Constant mk_ref => "ref".
Parameter get : forall {A : Type}, ref A -> M A.
Extract Inlined Constant get => "!".
Parameter set : forall {A : Type}, ref A -> A -> M unit.
Extract Inlined Constant set => "(:=)".

Parameter lazy_t : Type -> Type.
Extract Constant lazy_t "'a" => "'a Lazy.t".
Parameter lazy_ : forall {A : Type}, (unit -> M A) -> M (lazy_t A).
Extract Inlined Constant lazy_ => "Lazy.from_fun".
Parameter force : forall {A : Type}, lazy_t A -> M A.
Extract Inlined Constant force => "Lazy.force".

Parameter array : Type -> Type.
Extract Constant array "'a" => "'a array".
Parameter array_empty : forall {A : Type}, array A.
Extract Inlined Constant array_empty => "[||]".
Parameter array_singleton : forall {A : Type}, A -> M (array A).
Extract Inlined Constant array_singleton => "(fun x__1 -> [| x__1 |])".

(* ------------------------------------------------------------------ *)
(* OCaml's values that Rocq's own types stand for                     *)
(* ------------------------------------------------------------------ *)

Definition int : Type := Z.
Extract Inlined Constant int => "int".
Definition i2 : int := 2%Z.
Extract Inlined Constant i2 => "2".
Definition i3 : int := 3%Z.
Extract Inlined Constant i3 => "3".
Definition i4 : int := 4%Z.
Extract Inlined Constant i4 => "4".
Definition i5 : int := 5%Z.
Extract Inlined Constant i5 => "5".
Definition i6 : int := 6%Z.
Extract Inlined Constant i6 => "6".
Definition i7 : int := 7%Z.
Extract Inlined Constant i7 => "7".
Definition i8 : int := 8%Z.
Extract Inlined Constant i8 => "8".
Definition i9 : int := 9%Z.
Extract Inlined Constant i9 => "9".
Definition i10 : int := 10%Z.
Extract Inlined Constant i10 => "10".
Definition i16 : int := 16%Z.
Extract Inlined Constant i16 => "16".
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
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant String.eqb => "String.equal".
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant List.app => "(@)".

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
Extract Inductive tuple3 => "Port_monad.tuple3" [ "" ].
Extract Inductive tuple4 => "Port_monad.tuple4" [ "" ].
Extract Inductive tuple5 => "Port_monad.tuple5" [ "" ].
Extract Inductive tuple6 => "Port_monad.tuple6" [ "" ].

Definition int_neq (a b : int) : bool := negb (Z.eqb a b).
Extract Inlined Constant int_neq => "(<>)".
Notation "a <>? b" := (int_neq a b) (at level 70, no associativity).

Parameter Division_by_zero : exception unit.
Extract Inlined Constant Division_by_zero => "Port_monad.division_by_zero".
Parameter int_div : int -> int -> M int.
Extract Inlined Constant int_div => "(/)".
Parameter int_mod : int -> int -> M int.
Extract Inlined Constant int_mod => "(mod)".

(* Printed [a || b] and [a && b]: OCaml does not evaluate [b] when [a]
   decides. *)
Definition or_else (a : bool) (b : M bool) : M bool := if a then true else b.
Extract Inlined Constant or_else => "(||)".
Definition and_then (a : bool) (b : M bool) : M bool :=
  if a then b else false.
Extract Inlined Constant and_then => "(&&)".

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

Definition papp1 {A B C : Type} (f : A -> B -> C) (a : A) : M (B -> C) := f a.
Definition papp2 {A1 A2 B C : Type} (f : A1 -> A2 -> B -> C) (a1 : A1)
    (a2 : A2) : M (B -> C) := f a1 a2.
Definition papp3 {A1 A2 A3 B C : Type} (f : A1 -> A2 -> A3 -> B -> C)
    (a1 : A1) (a2 : A2) (a3 : A3) : M (B -> C) := f a1 a2 a3.
Definition papp4 {A1 A2 A3 A4 B C : Type}
    (f : A1 -> A2 -> A3 -> A4 -> B -> C) (a1 : A1) (a2 : A2) (a3 : A3)
    (a4 : A4) : M (B -> C) := f a1 a2 a3 a4.
Extraction Inline papp1 papp2 papp3 papp4.

Parameter ignore : forall {A : Type}, A -> M unit.
Extract Inlined Constant ignore => "ignore".

Unset Implicit Arguments.
