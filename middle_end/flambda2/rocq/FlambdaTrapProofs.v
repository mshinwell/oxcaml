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

(* Examples for the checks of exception handlers and of trap actions in
   FlambdaWellFormedSpec.v ([unit_exn_handlers_well_formed],
   [traps_well_formed]): terms that each accepts and terms that it
   refuses. There is no theorem here yet. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaBindersSpec FlambdaWellFormedSpec.
Import ListNotations.

(* So that the checks are not satisfied, or refused, for nothing: each
   example is a small term with the shape of what the front end builds
   for [try ... with], or of a mistake in it. The unit's exception
   continuation is [error]; [leave] is a continuation that the term does
   not bind, a way out. *)
Section Examples.

Local Open Scope positive_scope.

Definition error : continuation := 1.
Definition leave : continuation := 2.
Definition handler : continuation := 3.
Definition body : continuation := 4.
Definition inner : continuation := 5.
Definition loop : continuation := 6.
Definition x : variable := 1.

(* A handler with no parameter that is not an exception handler, and an
   exception handler with a parameter for the exception. *)
Definition plain (e : expr) : continuation_handler :=
  Handler [] (make_handler_metadata []) e.

Definition catches (e : expr) : continuation_handler :=
  Handler [x] (make_exn_handler_metadata [Value]) e.

Definition goto (k : continuation) (action : option trap_action)
    : expr :=
  Apply_cont (Apply_cont_expr k [] action).

Definition raise_to (k : continuation) : expr :=
  Apply_cont
    (Apply_cont_expr k [Const (Tagged_immediate 0)]
       (Some (Pop k (Some No_trace)))).

(* [try body with x -> leave]: the handler is installed on the way into
   the body, and [in_body] is what the body does. *)
Definition try_with (in_body : expr) : expr :=
  Let_cont_non_recursive handler (catches (goto leave None))
    (Let_cont_non_recursive body (plain in_body)
       (goto body (Some (Push handler)))).

Definition call_with (exn : continuation)
    (extra : list (simple * flambda_kind)) : expr :=
  Apply
    (Apply_expr (Var x) Indirect [] leave exn extra [] [Singleton Value]).

Definition call (exn : continuation) : expr :=
  call_with exn [(Const (Tagged_immediate 1), Value)].

Definition code_of (e : expr) : code :=
  Code [] x leave error (make_code_metadata [] [Singleton Value]) e.

(* The body raises to the handler. *)
Example raise_in_try :
  traps_well_formed error (try_with (raise_to handler)) = true.
Proof. reflexivity. Qed.

(* The body leaves, removing the handler on the way. *)
Example leave_try :
  traps_well_formed error
    (try_with (goto leave (Some (Pop handler None))))
  = true.
Proof. reflexivity. Qed.

(* The body leaves with the handler still installed. *)
Example leave_try_without_pop :
  traps_well_formed error (try_with (goto leave None)) = false.
Proof. reflexivity. Qed.

(* The body raises to the exception continuation of the unit, over the
   handler. The machine of the semantics goes to [error]; the backend's
   code would go to the handler. *)
Example raise_over_handler :
  traps_well_formed error (try_with (raise_to error)) = false.
Proof. reflexivity. Qed.

(* Outside a [try], a raise to the exception continuation of the unit. *)
Example raise_to_unit : traps_well_formed error (raise_to error) = true.
Proof. reflexivity. Qed.

(* A trap action that removes a handler that is not installed. *)
Example pop_not_installed :
  traps_well_formed error
    (Let_cont_non_recursive handler (catches (goto leave None))
       (goto leave (Some (Pop handler None))))
  = false.
Proof. reflexivity. Qed.

(* A call in the body, with the handler, and then the unit's exception
   continuation, as its exception continuation. Extra arguments make no
   difference. *)
Example call_in_try :
  traps_well_formed error
    (try_with
       (Let_cont_non_recursive leave
          (plain (goto 7 (Some (Pop handler None))))
          (call handler)))
  = true.
Proof. reflexivity. Qed.

Example call_over_handler :
  traps_well_formed error
    (try_with
       (Let_cont_non_recursive leave
          (plain (goto 7 (Some (Pop handler None))))
          (call error)))
  = false.
Proof. reflexivity. Qed.

(* A loop in the body, entered and repeated with the handler installed,
   and one that installs the handler again each time round. *)
Example loop_in_try :
  traps_well_formed error
    (try_with
       (Let_cont_recursive [(loop, plain (goto loop None))]
          (goto loop None)))
  = true.
Proof. reflexivity. Qed.

Example loop_pushing :
  traps_well_formed error
    (Let_cont_non_recursive handler (catches (goto leave None))
       (Let_cont_recursive
          [(loop, plain (goto loop (Some (Push handler))))]
          (goto loop None)))
  = false.
Proof. reflexivity. Qed.

(* A continuation defined outside the [try] and entered from inside it:
   the stack with which it is entered is that of its application, not
   that of its definition. *)
Example defined_outside_entered_inside :
  traps_well_formed error
    (Let_cont_non_recursive handler (catches (goto leave None))
       (Let_cont_non_recursive inner
          (plain (goto leave (Some (Pop handler None))))
          (Let_cont_non_recursive body (plain (goto inner None))
             (goto body (Some (Push handler))))))
  = true.
Proof. reflexivity. Qed.

(* Code: a raise to its exception continuation, and a return with a
   handler still installed. *)
Example code_raises :
  code_traps_well_formed (code_of (raise_to error)) = true.
Proof. reflexivity. Qed.

Example code_returns_in_try :
  code_traps_well_formed (code_of (try_with (goto leave None))) = false.
Proof. reflexivity. Qed.

(* Exception handlers apart from the others: a handler that is also
   applied as an ordinary continuation, one with no parameter, and a
   recursive one. *)
Example handler_well_used :
  unit_exn_handlers_well_formed error (try_with (raise_to handler)) = true.
Proof. reflexivity. Qed.

Example handler_applied :
  unit_exn_handlers_well_formed error
    (try_with
       (Apply_cont
          (Apply_cont_expr handler [Const (Tagged_immediate 0)] None)))
  = false.
Proof. reflexivity. Qed.

Example handler_without_parameter :
  unit_exn_handlers_well_formed error
    (Let_cont_non_recursive handler
       (Handler [] (make_exn_handler_metadata []) (goto leave None))
       (goto leave (Some (Push handler))))
  = false.
Proof. reflexivity. Qed.

Example recursive_handler :
  unit_exn_handlers_well_formed error
    (Let_cont_recursive [(handler, catches (goto leave None))]
       (goto leave (Some (Push handler))))
  = false.
Proof. reflexivity. Qed.

(* What a handler says it is, and how it is used. A handler that is
   installed and raised to and does not say that it is an exception
   handler; one that says so and is never installed, which is allowed;
   one of a recursive [Let_cont] that says so and is not used at all;
   and one of a recursive [Let_cont] that does not say so and is
   installed. *)
Example handler_not_marked :
  unit_exn_handlers_well_formed error
    (Let_cont_non_recursive handler
       (Handler [x] (make_handler_metadata [Value]) (goto leave None))
       (Let_cont_non_recursive body (plain (raise_to handler))
          (goto body (Some (Push handler)))))
  = false.
Proof. reflexivity. Qed.

Example handler_marked_and_unused :
  unit_exn_handlers_well_formed error
    (Let_cont_non_recursive handler (catches (goto leave None))
       (goto leave None))
  = true.
Proof. reflexivity. Qed.

Example recursive_handler_marked :
  unit_exn_handlers_well_formed error
    (Let_cont_recursive [(handler, catches (goto leave None))]
       (goto leave None))
  = false.
Proof. reflexivity. Qed.

Example recursive_handler_not_marked :
  unit_exn_handlers_well_formed error
    (Let_cont_recursive
       [(handler,
         Handler [x] (make_handler_metadata [Value]) (goto leave None))]
       (goto leave (Some (Push handler))))
  = false.
Proof. reflexivity. Qed.

(* The continuations that a unit, or code, does not bind. A way out that
   is not the exception continuation, installed as an exception handler
   and raised to: the stack is in order, and the term is refused as it
   uses the return of the unit, or of the code, as a handler. *)
Definition return_as_handler : expr :=
  Let_cont_non_recursive body (plain (raise_to leave))
    (goto body (Some (Push leave))).

Example unit_return_as_handler_stack :
  traps_well_formed error return_as_handler = true.
Proof. reflexivity. Qed.

Example unit_return_as_handler :
  unit_exn_handlers_well_formed error return_as_handler = false.
Proof. reflexivity. Qed.

Example code_return_as_handler :
  code_exn_handlers_well_formed (code_of return_as_handler) = false.
Proof. reflexivity. Qed.

(* The exception continuation of a unit, or of code, is for calls and
   raises: here it is removed on the way to a continuation that installs
   it again. The stack is in order; the term is refused as it names the
   exception continuation in a trap action that is not that of a
   raise. *)
Definition pop_and_push_of_exn : expr :=
  Let_cont_non_recursive body (plain (goto leave (Some (Push error))))
    (goto body (Some (Pop error None))).

Example pop_and_push_of_exn_stack :
  traps_well_formed error pop_and_push_of_exn = true.
Proof. reflexivity. Qed.

Example pop_and_push_of_unit_exn :
  unit_exn_handlers_well_formed error pop_and_push_of_exn = false.
Proof. reflexivity. Qed.

Example pop_and_push_of_code_exn :
  code_exn_handlers_well_formed (code_of pop_and_push_of_exn) = false.
Proof. reflexivity. Qed.

(* Code whose return and exception continuations are one name: a raise
   to it would return. The check of trap actions does not see it; the
   check of binders, which a well-formed unit is asked first, refuses
   it. *)
Definition code_of_one_continuation : code :=
  Code [] x leave leave (make_code_metadata [] [Singleton Value])
    (raise_to leave).

Example code_of_one_continuation_stack :
  code_traps_well_formed code_of_one_continuation = true.
Proof. reflexivity. Qed.

Example code_of_one_continuation_binders :
  FlambdaBindersSpec.code_binders_distinct code_of_one_continuation = false.
Proof. reflexivity. Qed.

(* A recursive group that binds one name twice. The machine enters the
   first handler of the name. The check of trap actions finds the name
   entered only after it has passed that handler, tests the second, and
   does not see that the first removes a handler that is not installed.
   The check of binders refuses the group. *)
Definition group_of_one_name_twice : expr :=
  Let_cont_recursive
    [(loop, plain (goto leave (Some (Pop handler None))));
     (inner, plain (goto loop None));
     (loop, plain (goto leave None))]
    (goto inner None).

Example group_of_one_name_twice_stack :
  traps_well_formed error group_of_one_name_twice = true.
Proof. reflexivity. Qed.

Example group_of_one_name_twice_binders :
  FlambdaBindersSpec.binders_distinct group_of_one_name_twice = false.
Proof. reflexivity. Qed.

(* A call that gives an extra argument to its exception continuation:
   to a handler of the term, and to the exception continuation of the
   unit or of the code, which takes the exception alone. The stack is in
   order in each. *)
Definition call_in_try_body : expr :=
  try_with
    (Let_cont_non_recursive leave
       (plain (goto 7 (Some (Pop handler None))))
       (call handler)).

Example extra_args_to_handler :
  unit_exn_handlers_well_formed error call_in_try_body = true.
Proof. reflexivity. Qed.

Example extra_args_to_unit_stack :
  traps_well_formed error (call error) = true.
Proof. reflexivity. Qed.

Example extra_args_to_unit :
  unit_exn_handlers_well_formed error (call error) = false.
Proof. reflexivity. Qed.

Example no_extra_args_to_unit :
  unit_exn_handlers_well_formed error (call_with error []) = true.
Proof. reflexivity. Qed.

Example extra_args_to_code_exn :
  code_exn_handlers_well_formed (code_of (call error)) = false.
Proof. reflexivity. Qed.

End Examples.
