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

   [inline_calls] is for the term before. It goes down the term, into the
   handlers of continuations too, keeping the code that the [Let_static]s
   passed have bound ([known]), and replaces a direct call of known code by
   the code inlined (FlambdaApplySpec.inlined_body) where that is sound
   ([inlinable_b], which decides FlambdaApplySpec.inlinable). What is
   known where a handler is defined holds where it runs, however much
   later: a code id is bound once (FlambdaWellFormedSpec.v).

   CR mshinwell: it does not go into the bodies of code. Rewriting them
   changes what the code ids are bound to, so the two runs no longer have
   the same static environment for the calls inlined to be those of.

   [expr_in_scope] is the check that code is closed. It is a sufficient
   condition, by its soundness (in the Proofs file); nothing is claimed
   where it answers no.

   [inline_tail_conts], for the term before, puts the handler of a
   non-recursive continuation where the continuation is applied, when that
   is at the end of a run of [Let]s that is the body of its [Let_cont]:
   the continuation is then applied exactly once. The parameters become
   [Let]s. It is what inlining a call leaves to be done, the continuation
   of the call being applied at the end of the inlined body.

   [drop_deleted_code], for either term, removes the bindings of deleted
   code, which bind nothing, and a [Let_static] left with no binding.

   [remove_unused_total_lets], for either term, is the part of
   [remove_unused_lets] that is an equivalence: it removes an unused [Let]
   only where the defining expression is a constant or a symbol, which
   always has a value.

   [remove_unused_defined_lets] goes further, also as an equivalence: it
   keeps the variables in scope as it goes, and removes an unused [Let]
   whose defining expression is a [Simple] or a closure made of constants,
   symbols and variables in scope, which has a value where those
   variables are bound.

   [inline_known_calls] is inlining as an equivalence, for either term:
   it inlines a direct call only where the callee is a symbol that a
   [Let_static] passed has bound to a closure of the code called, so that
   the call cannot be undefined for being of something else. It goes
   where [inline_calls] goes.

   [merge_statics], for either term, makes one group of [Let_static]s that
   follow one another, and puts the code of a group before its symbols.
   Neither changes the static environment that results, so groups that
   differ only in how they are cut up and ordered become the same.

   [collapse_switches], for the term before, replaces a [Switch] whose
   arms are all the same by that arm. It is a refinement only: the
   [Switch] is undefined where its scrutinee has no arm.

   [fold_constants], for either term, replaces a primitive applied to
   constants by its value, when that is a constant, and a [Switch] on a
   constant by its arm. The value of the primitive is whatever
   FlambdaSemanticsSpec.eval_prim says, so nothing is assumed of the
   primitives: the function calls the same [eval_prim] that the semantics
   does, and the extracted function calls what realises it.

   [remove_unused_lets], also for the term before, removes each [Let] whose
   variable is not free in its body, in bodies and in the handlers of
   non-recursive continuations. [var_free_b] is the test; it may say that
   a variable is free when it is not, never the reverse.

   The proofs are in FlambdaNormaliseProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaNominalSpec FlambdaApplySpec FlambdaCompareSpec.
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
    Let_cont_non_recursive k (inline_calls_in_handler known h)
      (inline_calls known body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive
      (map (fun '(k, h) => (k, inline_calls_in_handler known h)) handlers)
      (inline_calls known body)
  | Apply ap => inline_apply known ap
  | Apply_cont _ | Switch _ _ | Invalid => e
  end
with inline_calls_in_handler (known : list (code_id * code))
    (h : continuation_handler) : continuation_handler :=
  match h with
  | Handler params handler => Handler params (inline_calls known handler)
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

(* Which primitives the normalisation may fold, and remove when unused.
   Any choice is sound; it is there so that a primitive meant to hide a
   value from the simplifier ([Opaque_identity]) can be left alone, as
   Simplify leaves it. *)
Parameter prim_may_fold : prim -> bool.

Definition named_may_go (d : named) : bool :=
  match d with
  | Prim p _ => prim_may_fold p
  | Simple _ | Set_of_closures _ _ | Project_value_slot _ _ => true
  end.

Fixpoint remove_unused_lets (e : expr) : expr :=
  match e with
  | Let x d body =>
    let body' := remove_unused_lets body in
    if var_free_b x body' || negb (named_may_go d)
    then Let x d body'
    else body'
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

(* ======================================================================== *)
(* A continuation applied once, at the end of its scope                     *)
(* ======================================================================== *)

(* [body] with the handler in place of the application of [k] that ends
   it, if it is a run of [Let]s ending so, none of which binds a variable
   of the handler. *)
Fixpoint inline_cont_at_tail (k : continuation) (params : list variable)
    (handler : expr) (body : expr) : option expr :=
  match body with
  | Let x d body =>
    if var_free_in_handler_b x (Handler params handler)
    then None
    else option_map (Let x d) (inline_cont_at_tail k params handler body)
  | Let_static bindings body =>
    option_map (Let_static bindings)
      (inline_cont_at_tail k params handler body)
  | Apply_cont ac =>
    if Pos.eqb (ac_continuation ac) k
       && Nat.eqb (length params) (length (ac_args ac))
       && forallb (fun param => negb (var_in_simples param (ac_args ac)))
            params
    then Some (let_params params (ac_args ac) handler)
    else None
  | Let_cont_non_recursive _ _ _ | Let_cont_recursive _ _ | Apply _
  | Switch _ _ | Invalid =>
    None
  end.

Fixpoint inline_tail_conts (e : expr) : expr :=
  match e with
  | Let x d body => Let x d (inline_tail_conts body)
  | Let_static bindings body => Let_static bindings (inline_tail_conts body)
  | Let_cont_non_recursive k (Handler params handler) body =>
    let handler' := inline_tail_conts handler in
    let body' := inline_tail_conts body in
    match inline_cont_at_tail k params handler' body' with
    | Some inlined => inlined
    | None => Let_cont_non_recursive k (Handler params handler') body'
    end
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (inline_tail_conts body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition inline_tail_conts_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (inline_tail_conts e).

(* ======================================================================== *)
(* Bindings of deleted code                                                 *)
(* ======================================================================== *)

Definition binds_something (binding : static_binding) : bool :=
  match binding with
  | Bind_deleted_code _ => false
  | Bind_code _ _ | Bind_symbol _ _ => true
  end.

Definition let_static_if_any (bindings : list static_binding) (body : expr)
    : expr :=
  match bindings with
  | [] => body
  | _ :: _ => Let_static bindings body
  end.

Fixpoint drop_deleted_code (e : expr) : expr :=
  match e with
  | Let x d body => Let x d (drop_deleted_code body)
  | Let_static bindings body =>
    let_static_if_any (filter binds_something bindings)
      (drop_deleted_code body)
  | Let_cont_non_recursive k (Handler params handler) body =>
    Let_cont_non_recursive k (Handler params (drop_deleted_code handler))
      (drop_deleted_code body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (drop_deleted_code body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition drop_deleted_code_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (drop_deleted_code e).

(* ======================================================================== *)
(* Folding constants                                                        *)
(* ======================================================================== *)

Fixpoint consts_of_simples (args : list simple) : option (list const) :=
  match args with
  | [] => Some []
  | Const c :: args => option_map (cons c) (consts_of_simples args)
  | (Var _ | Symbol _) :: _ => None
  end.

Definition fold_named (d : named) : named :=
  match d with
  | Prim p args =>
    match (if prim_may_fold p then consts_of_simples args else None) with
    | Some cs =>
      match eval_prim p (map Value_const cs) with
      | Some (Value_const c) => Simple (Const c)
      | Some (Value_closure _ _ | Value_symbol _) | None => d
      end
    | None => d
    end
  | Simple _ | Set_of_closures _ _ | Project_value_slot _ _ => d
  end.

Definition fold_switch (scrutinee : simple) (arms : list (Z * apply_cont))
    : expr :=
  match scrutinee with
  | Const (Naked_immediate i) =>
    match find_arm i arms with
    | Some ac => Apply_cont ac
    | None => Switch scrutinee arms
    end
  | _ => Switch scrutinee arms
  end.

Fixpoint fold_constants (e : expr) : expr :=
  match e with
  | Let x d body => Let x (fold_named d) (fold_constants body)
  | Let_static bindings body => Let_static bindings (fold_constants body)
  | Let_cont_non_recursive k (Handler params handler) body =>
    Let_cont_non_recursive k (Handler params (fold_constants handler))
      (fold_constants body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (fold_constants body)
  | Switch scrutinee arms => fold_switch scrutinee arms
  | Apply _ | Apply_cont _ | Invalid => e
  end.

Definition fold_constants_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (fold_constants e).

(* ======================================================================== *)
(* Removing unused [Let]s whose defining expression always has a value     *)
(* ======================================================================== *)

Definition named_is_total (d : named) : bool :=
  match d with
  | Simple (Const _ | Symbol _) => true
  | Simple (Var _) | Prim _ _ | Set_of_closures _ _ | Project_value_slot _ _ =>
    false
  end.

Fixpoint remove_unused_total_lets (e : expr) : expr :=
  match e with
  | Let x d body =>
    let body' := remove_unused_total_lets body in
    if named_is_total d && negb (var_free_b x body')
    then body'
    else Let x d body'
  | Let_static bindings body =>
    Let_static bindings (remove_unused_total_lets body)
  | Let_cont_non_recursive k (Handler params handler) body =>
    Let_cont_non_recursive k
      (Handler params (remove_unused_total_lets handler))
      (remove_unused_total_lets body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (remove_unused_total_lets body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition remove_unused_total_lets_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (remove_unused_total_lets e).

(* ======================================================================== *)
(* Removing unused [Let]s whose defining expression has a value in scope   *)
(* ======================================================================== *)

(* The defining expression has a value wherever the variables given are
   bound. *)
Definition named_defined (vs : list variable) (d : named) : bool :=
  match d with
  | Simple s => simple_in_scope vs s
  | Set_of_closures _ slots =>
    forallb (fun slot => simple_in_scope vs (snd slot)) slots
  | Prim _ _ | Project_value_slot _ _ => false
  end.

Fixpoint remove_unused_defined_lets (vs : list variable) (e : expr) : expr :=
  match e with
  | Let x d body =>
    let body' := remove_unused_defined_lets (x :: vs) body in
    if named_defined vs d && negb (var_free_b x body')
    then body'
    else Let x d body'
  | Let_static bindings body =>
    Let_static bindings (remove_unused_defined_lets vs body)
  | Let_cont_non_recursive k (Handler params handler) body =>
    Let_cont_non_recursive k
      (Handler params (remove_unused_defined_lets (params ++ vs) handler))
      (remove_unused_defined_lets vs body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (remove_unused_defined_lets vs body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition remove_unused_defined_lets_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (remove_unused_defined_lets [] e).

(* ======================================================================== *)
(* Inlining calls of symbols known to be closures                           *)
(* ======================================================================== *)

(* What a group of bindings adds to what is known of the symbols: the code
   of those bound to closures, and that the others are not known to be
   closures, the last bound first. *)
Fixpoint symbols_of (bindings : list static_binding)
    (known : list (symbol * option code_id))
    : list (symbol * option code_id) :=
  match bindings with
  | [] => known
  | Bind_symbol s (Static_const_set_of_closures code _) :: bindings =>
    symbols_of bindings ((s, Some code) :: known)
  | Bind_symbol s
      (Static_const_block _ _ | Static_const_boxed_number _
      | Static_const_immutable_string _)
    :: bindings =>
    symbols_of bindings ((s, None) :: known)
  | (Bind_code _ _ | Bind_deleted_code _) :: bindings =>
    symbols_of bindings known
  end.

Definition inline_known_apply (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (ap : apply_expr)
    : expr :=
  match ap_callee ap, ap_call_kind ap with
  | Symbol s, Direct called =>
    match lookup s known_symbols, lookup called known_code with
    | Some (Some code), Some c =>
      if Pos.eqb code called && inlinable_b ap c
      then
        inlined_body c
          (inline_renaming (code_return_continuation c)
             (code_exn_continuation c) (ap_continuation ap)
             (ap_exn_continuation ap))
          ap
      else Apply ap
    | _, _ => Apply ap
    end
  | _, _ => Apply ap
  end.

Fixpoint inline_known_calls (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (e : expr) : expr :=
  match e with
  | Let x d body => Let x d (inline_known_calls known_code known_symbols body)
  | Let_static bindings body =>
    Let_static bindings
      (inline_known_calls (codes_of bindings known_code)
         (symbols_of bindings known_symbols) body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k
      (inline_known_calls_in_handler known_code known_symbols h)
      (inline_known_calls known_code known_symbols body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive
      (map
         (fun '(k, h) =>
            (k, inline_known_calls_in_handler known_code known_symbols h))
         handlers)
      (inline_known_calls known_code known_symbols body)
  | Apply ap => inline_known_apply known_code known_symbols ap
  | Apply_cont _ | Switch _ _ | Invalid => e
  end
with inline_known_calls_in_handler (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id))
    (h : continuation_handler) : continuation_handler :=
  match h with
  | Handler params handler =>
    Handler params (inline_known_calls known_code known_symbols handler)
  end.

Definition inline_known_calls_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (inline_known_calls [] [] e).

(* ======================================================================== *)
(* Groups of static bindings                                                *)
(* ======================================================================== *)

Definition binds_code (binding : static_binding) : bool :=
  match binding with
  | Bind_code _ _ | Bind_deleted_code _ => true
  | Bind_symbol _ _ => false
  end.

(* The bindings of code, then those of symbols, each in their order. *)
Definition code_first (bindings : list static_binding) : list static_binding :=
  filter binds_code bindings
  ++ filter (fun binding => negb (binds_code binding)) bindings.

Fixpoint merge_statics (e : expr) : expr :=
  match e with
  | Let x d body => Let x d (merge_statics body)
  | Let_static bindings body =>
    match merge_statics body with
    | Let_static bindings' body' =>
      Let_static (code_first (bindings ++ bindings')) body'
    | body' => Let_static (code_first bindings) body'
    end
  | Let_cont_non_recursive k (Handler params handler) body =>
    Let_cont_non_recursive k (Handler params (merge_statics handler))
      (merge_statics body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (merge_statics body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition merge_statics_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (merge_statics e).

(* ======================================================================== *)
(* Switches whose arms are all the same                                     *)
(* ======================================================================== *)

Definition simple_eq_dec : ∀ s s' : simple, {s = s'} + {s <> s'}.
Proof. decide equality; try apply Pos.eq_dec; apply const_eq_dec. Defined.

Definition apply_cont_eq_dec :
  ∀ ac ac' : apply_cont, {ac = ac'} + {ac <> ac'}.
Proof.
  decide equality; [ apply (list_eq_dec simple_eq_dec) | apply Pos.eq_dec ].
Defined.

Definition collapse_switch (scrutinee : simple)
    (arms : list (Z * apply_cont)) : expr :=
  match arms with
  | (_, ac) :: others =>
    if forallb
         (fun arm => if apply_cont_eq_dec (snd arm) ac then true else false)
         others
    then Apply_cont ac
    else Switch scrutinee arms
  | [] => Switch scrutinee arms
  end.

Fixpoint collapse_switches (e : expr) : expr :=
  match e with
  | Let x d body => Let x d (collapse_switches body)
  | Let_static bindings body => Let_static bindings (collapse_switches body)
  | Let_cont_non_recursive k (Handler params handler) body =>
    Let_cont_non_recursive k (Handler params (collapse_switches handler))
      (collapse_switches body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (collapse_switches body)
  | Switch scrutinee arms => collapse_switch scrutinee arms
  | Apply _ | Apply_cont _ | Invalid => e
  end.

Definition collapse_switches_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (collapse_switches e).
