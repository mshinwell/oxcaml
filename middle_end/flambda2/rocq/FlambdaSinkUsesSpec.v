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

(* Moving a continuation down to the call or the test that uses it: a
   normalisation that is an equivalence.

   This file is to be reviewed: [sink_conts_to_uses] and [sink_to_use],
   which are extracted and run by the validation of
   middle_end/flambda2/tests/semantics/, and the statement.

   The comparison of two terms is of their bindings in their order, and
   the two terms of a unit may bind a continuation at different places
   among the [Let]s around it.

   The front end binds the continuation that a call returns to before
   the arguments of the call are computed:

     let_cont k (r) = h in
     let x = d in
     apply f (x) -> k

   Simplify leaves such a term in that order. But where it changes the
   parameter of [k] (the boolean result of a call that an [if] tests is
   untagged; a result that [h] does not use is not passed), the call
   can no longer return to [k]. Simplify makes the call return to a new
   continuation, bound at the call, that applies [k]
   (simplify/simplify_apply_expr.ml rebuilds the call with
   [Expr_builder.rewrite_fixed_arity_apply]; the case [New_wrapper] of
   [Expr_builder.rewrite_fixed_arity_continuation] binds the new
   continuation around the [Apply]):

     let_cont k (u) = h' in
     let x = d in
     let_cont k' (r) = (let u = untag r in cont k (u)) in
     apply f (x) -> k'

   Once [k], applied once, is inlined in [k']
   (FlambdaSinkContsSpec.sink_let_conts, then the inlining of a
   continuation applied at the end of the body of its [Let_cont]), the
   handler is the one the term had before, bound after the [Let] and
   not before it. In that handler, the [Let] of the untagging then
   stands before the bindings of the continuations of the test, where
   the term before has it after them:

     let u = untag r in             let_cont k1 () = .. in
     let_cont k1 () = .. in         let u = untag r in
     switch u | 0 -> k1 () | ..     switch u | 0 -> k1 () | ..

   [sink_conts_to_uses] gives the two terms one order: a non-recursive
   [Let_cont] goes down to the [Apply] that returns to its continuation
   or raises to it, or to the [Switch] of which an arm names it, if
   only bindings are between the two. [sink_to_use k h body] is
   [Let_cont_non_recursive k h body] with the binding of [k] so moved,
   and nothing if it cannot be. On its way the binding goes
   - past a [Let] whose variable is not free in the handler [h], which
     would otherwise come to mean that variable;
   - past a [Let_static], with no condition;
   - past a non-recursive [Let_cont] of another name, if [k] is not
     free in the handler of that one and its name is not free in [h].
   It stops at anything else, and the binding is then left where it
   was. Each of the three moves is one of
   FlambdaSinkContsSpec.sink_into_handler; this pass does not move a
   binding into a handler.

   The tests of freedom are FlambdaNormaliseSpec.var_free_in_handler_b
   and FlambdaUnusedContsSpec.cont_free_b, which may say that a name is
   free when it is not, never the reverse; so the pass may fail to move
   a binding, and never moves one wrongly.

   A move takes the handler with its binding, as it is, and the pass
   removes nothing: it is an equivalence. Going down a term, the pass
   also places the bindings that are inside the handlers of
   non-recursive continuations; the parameters of a handler, their
   kinds and the rest of its metadata are never changed. It does not
   go into the handlers of recursive continuations nor into the
   bodies of code (FlambdaRecHandlersSpec.rewrite_rec_handlers and
   FlambdaNormaliseSpec.rewrite_code take it there).

   It is for the two terms that are compared, once, when the rounds of
   their normalisation are over (FlambdaValidateSpec.placed). In a
   round it would change where a continuation is bound for the
   rewrites of the next round that look at that
   (FlambdaForwardSpec.given_one_inner_variable,
   FlambdaParamAliasesSpec.bind_aliased_params, the inlining of a call
   whose continuation was moved), which follow Simplify on the term as
   it was.

   Renaming: [sink_conts_to_uses] compares names by equality only and
   binds none, so it commutes with a renaming
   (FlambdaValidatorEquivarianceProofs.v).

   The proofs are in FlambdaSinkUsesProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaNormaliseSpec FlambdaUnusedContsSpec.
Import ListNotations.

Fixpoint sink_to_use (k : continuation) (h : continuation_handler)
    (body : expr) : option expr :=
  match body with
  | Let x kind d body =>
    if var_free_in_handler_b x h then None
    else option_map (Let x kind d) (sink_to_use k h body)
  | Let_static bindings body =>
    option_map (Let_static bindings) (sink_to_use k h body)
  | Let_cont_non_recursive k' (Handler params' metadata' handler') body =>
    if negb (Pos.eqb k k')
       && negb (cont_free_b k handler')
       && negb (cont_free_in_handler_b k' h)
    then
      option_map
        (Let_cont_non_recursive k' (Handler params' metadata' handler'))
        (sink_to_use k h body)
    else None
  | Apply ap =>
    if cont_free_b k (Apply ap)
    then Some (Let_cont_non_recursive k h (Apply ap))
    else None
  | Switch scrutinee arms =>
    if arms_apply k arms
    then Some (Let_cont_non_recursive k h (Switch scrutinee arms))
    else None
  | Let_cont_recursive _ _ | Apply_cont _ | Invalid => None
  end.

(* Every non-recursive [Let_cont] moved where it can be, those of the
   handler and of the body of a [Let_cont] before that [Let_cont]
   itself. *)
Fixpoint sink_conts_to_uses (e : expr) : expr :=
  match e with
  | Let x kind d body => Let x kind d (sink_conts_to_uses body)
  | Let_static bindings body =>
    Let_static bindings (sink_conts_to_uses body)
  | Let_cont_non_recursive k (Handler params metadata handler) body =>
    let h := Handler params metadata (sink_conts_to_uses handler) in
    let body := sink_conts_to_uses body in
    match sink_to_use k h body with
    | Some sunk => sunk
    | None => Let_cont_non_recursive k h body
    end
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (sink_conts_to_uses body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition sink_conts_to_uses_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (sink_conts_to_uses e).
