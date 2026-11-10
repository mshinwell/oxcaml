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

(* Normalising a term by rewrites that are proved: the first of them,
   inlining direct calls of known code.

   This file is to be reviewed: the functions, which are extracted and run
   by the validation of middle_end/flambda2/tests/semantics/, and the
   statement.

   The validation compares the term before Simplify with the term after
   (FlambdaCompareSpec.v). They are seldom the same as they stand, so each
   is first brought to a normal form by rewrites whose correctness is a
   theorem; what the comparison then accepts is correct by those theorems
   and the soundness of the comparison. The rewrites applied to the term
   before may be refinements; those applied to the term after must be
   equivalences, as the chain runs from the one to the other.

   [inline_calls] is for the term before. It goes down the bodies of [Let],
   [Let_static] and [Let_cont], keeping the code that the [Let_static]s
   passed have bound ([known]), and replaces a direct call of known code by
   the code inlined (FlambdaApplySpec.inlined_body) where that is sound
   ([inlinable_b], which decides FlambdaApplySpec.inlinable). It does not
   go into handlers or code: what is known where a handler is defined need
   not hold where it runs, if a code id may be bound twice, and nothing
   yet says that it is not.

   [expr_in_scope] is the check that code is closed. It is a sufficient
   condition, by its soundness (in the Proofs file); nothing is claimed
   where it answers no.

   [remove_unused_lets], also for the term before, removes each [Let] whose
   variable is not free in its body, in bodies and in the handlers of
   non-recursive continuations. [var_free_b] is the test; it may say that
   a variable is free when it is not, never the reverse.

   The proofs are in FlambdaNormaliseProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaNominalSpec FlambdaApplySpec.
Import ListNotations.

(* ======================================================================== *)
(* Names in scope                                                           *)
(* ======================================================================== *)

Definition name_in (name : positive) (names : list positive) : bool :=
  existsb (Pos.eqb name) names.

Definition simple_in_scope (vs : list variable) (s : simple) : bool :=
  match s with
  | Var x => name_in x vs
  | Symbol _ | Const _ => true
  end.

Definition simples_in_scope (vs : list variable) (args : list simple) : bool :=
  forallb (simple_in_scope vs) args.

Definition named_in_scope (vs : list variable) (d : named) : bool :=
  match d with
  | Simple s => simple_in_scope vs s
  | Prim _ args => simples_in_scope vs args
  | Set_of_closures _ slots =>
    forallb (fun slot => simple_in_scope vs (snd slot)) slots
  | Project_value_slot _ closure => simple_in_scope vs closure
  end.

Definition static_binding_in_scope (vs : list variable)
    (binding : static_binding) : bool :=
  match binding with
  | Bind_code _ _ | Bind_deleted_code _ => true
  | Bind_symbol _ (Static_const_set_of_closures _ slots) =>
    forallb (fun slot => simple_in_scope vs (snd slot)) slots
  | Bind_symbol _ (Static_const_block _ fields) => simples_in_scope vs fields
  | Bind_symbol _ (Static_const_boxed_number contents) =>
    simple_in_scope vs contents
  | Bind_symbol _ (Static_const_immutable_string _) => true
  end.

Definition apply_cont_in_scope (vs : list variable) (ks : list continuation)
    (ac : apply_cont) : bool :=
  name_in (ac_continuation ac) ks && simples_in_scope vs (ac_args ac).

(* Every variable and continuation the expression uses is bound in it or is
   one of those given. *)
Fixpoint expr_in_scope (vs : list variable) (ks : list continuation)
    (e : expr) : bool :=
  match e with
  | Let x d body => named_in_scope vs d && expr_in_scope (x :: vs) ks body
  | Let_static bindings body =>
    forallb (static_binding_in_scope vs) bindings
    && expr_in_scope vs ks body
  | Let_cont_non_recursive k h body =>
    handler_in_scope vs ks h && expr_in_scope vs (k :: ks) body
  | Let_cont_recursive handlers body =>
    let ks' := map fst handlers ++ ks in
    forallb (fun '(_, h) => handler_in_scope vs ks' h) handlers
    && expr_in_scope vs ks' body
  | Apply ap =>
    simple_in_scope vs (ap_callee ap)
    && simples_in_scope vs (ap_args ap)
    && name_in (ap_continuation ap) ks
    && name_in (ap_exn_continuation ap) ks
  | Apply_cont ac => apply_cont_in_scope vs ks ac
  | Switch scrutinee arms =>
    simple_in_scope vs scrutinee
    && forallb (fun arm => apply_cont_in_scope vs ks (snd arm)) arms
  | Invalid => true
  end
with handler_in_scope (vs : list variable) (ks : list continuation)
    (h : continuation_handler) : bool :=
  match h with
  | Handler params handler => expr_in_scope (params ++ vs) ks handler
  end.

(* ======================================================================== *)
(* Inlining direct calls of known code                                      *)
(* ======================================================================== *)

(* The renaming of FlambdaApplySpec.inline_renaming_exists_statement. *)
Definition inline_renaming (ret exn k k_exn : continuation) : renaming :=
  Renaming [] [(swap ret k exn, k_exn); (ret, k)].

Definition var_in_simples (x : variable) (args : list simple) : bool :=
  existsb
    (fun s =>
       match s with
       | Var y => Pos.eqb x y
       | Symbol _ | Const _ => false
       end)
    args.

(* Decides FlambdaApplySpec.inlinable, for [inline_renaming]. *)
Definition inlinable_b (ap : apply_expr) (c : code) : bool :=
  expr_in_scope (code_my_closure c :: code_params c)
    [code_return_continuation c; code_exn_continuation c] (code_body c)
  && negb (Pos.eqb (code_return_continuation c) (code_exn_continuation c))
  && negb (Pos.eqb (ap_continuation ap) (ap_exn_continuation ap))
  && negb (var_in_simples (code_my_closure c) (ap_args ap))
  && forallb (fun param => negb (var_in_simples param (ap_args ap)))
       (code_params c)
  && Nat.eqb (length (code_params c)) (length (ap_args ap)).

(* The code that a group of bindings adds to what is known, the last
   bound first, as FlambdaSemanticsSpec.eval_static_bindings adds it to
   the static environment. *)
Fixpoint codes_of (bindings : list static_binding)
    (known : list (code_id * code)) : list (code_id * code) :=
  match bindings with
  | [] => known
  | Bind_code id c :: bindings => codes_of bindings ((id, c) :: known)
  | (Bind_deleted_code _ | Bind_symbol _ _) :: bindings =>
    codes_of bindings known
  end.

Definition inline_apply (known : list (code_id * code)) (ap : apply_expr)
    : expr :=
  match ap_call_kind ap with
  | Direct called =>
    match lookup called known with
    | Some c =>
      if inlinable_b ap c
      then
        inlined_body c
          (inline_renaming (code_return_continuation c)
             (code_exn_continuation c) (ap_continuation ap)
             (ap_exn_continuation ap))
          ap
      else Apply ap
    | None => Apply ap
    end
  | Indirect => Apply ap
  end.

Fixpoint inline_calls (known : list (code_id * code)) (e : expr) : expr :=
  match e with
  | Let x d body => Let x d (inline_calls known body)
  | Let_static bindings body =>
    Let_static bindings (inline_calls (codes_of bindings known) body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k h (inline_calls known body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (inline_calls known body)
  | Apply ap => inline_apply known ap
  | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition inline_calls_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (inline_calls [] e).

(* ======================================================================== *)
(* Removing unused [Let]s                                                   *)
(* ======================================================================== *)

Definition var_in_simple (x : variable) (s : simple) : bool :=
  match s with
  | Var y => Pos.eqb x y
  | Symbol _ | Const _ => false
  end.

Definition var_in_value_slots (x : variable)
    (slots : list (value_slot * simple)) : bool :=
  existsb (fun slot => var_in_simple x (snd slot)) slots.

Definition var_in_named (x : variable) (d : named) : bool :=
  match d with
  | Simple s => var_in_simple x s
  | Prim _ args => var_in_simples x args
  | Set_of_closures _ slots => var_in_value_slots x slots
  | Project_value_slot _ closure => var_in_simple x closure
  end.

Definition var_in_static_binding (x : variable) (binding : static_binding)
    : bool :=
  match binding with
  | Bind_code _ _ | Bind_deleted_code _ => false
  | Bind_symbol _ (Static_const_set_of_closures _ slots) =>
    var_in_value_slots x slots
  | Bind_symbol _ (Static_const_block _ fields) => var_in_simples x fields
  | Bind_symbol _ (Static_const_boxed_number contents) =>
    var_in_simple x contents
  | Bind_symbol _ (Static_const_immutable_string _) => false
  end.

(* Whether a variable may be free in an expression. *)
Fixpoint var_free_b (x : variable) (e : expr) : bool :=
  match e with
  | Let y d body =>
    var_in_named x d || (negb (Pos.eqb x y) && var_free_b x body)
  | Let_static bindings body =>
    existsb (var_in_static_binding x) bindings || var_free_b x body
  | Let_cont_non_recursive _ h body =>
    var_free_in_handler_b x h || var_free_b x body
  | Let_cont_recursive handlers body =>
    existsb (fun '(_, h) => var_free_in_handler_b x h) handlers
    || var_free_b x body
  | Apply ap =>
    var_in_simple x (ap_callee ap) || var_in_simples x (ap_args ap)
  | Apply_cont ac => var_in_simples x (ac_args ac)
  | Switch scrutinee arms =>
    var_in_simple x scrutinee
    || existsb (fun arm => var_in_simples x (ac_args (snd arm))) arms
  | Invalid => false
  end
with var_free_in_handler_b (x : variable) (h : continuation_handler) : bool :=
  match h with
  | Handler params handler => negb (name_in x params) && var_free_b x handler
  end.

Fixpoint remove_unused_lets (e : expr) : expr :=
  match e with
  | Let x d body =>
    let body' := remove_unused_lets body in
    if var_free_b x body' then Let x d body' else body'
  | Let_static bindings body => Let_static bindings (remove_unused_lets body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (remove_unused_lets_in_handler h)
      (remove_unused_lets body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (remove_unused_lets body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end
with remove_unused_lets_in_handler (h : continuation_handler)
    : continuation_handler :=
  match h with
  | Handler params handler => Handler params (remove_unused_lets handler)
  end.

Definition remove_unused_lets_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (remove_unused_lets e).
