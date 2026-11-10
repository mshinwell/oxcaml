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

(* Following aliases through a term: a normalisation that is an
   equivalence.

   This file is to be reviewed: [follow_aliases] and what it is made of,
   which are extracted and run by the validation of
   middle_end/flambda2/tests/semantics/, and the statement.

   [follow_aliases] goes through a term with a typing environment
   (FlambdaTypesSpec.v) holding, for the variables bound by a [Let] to a
   [Simple], that [Simple]. Every use of such a variable is replaced by
   what it is bound to ([canonical_simple]). This is what the simplifier
   does with its aliases: there is no substitution, and the [Let] stays,
   to be removed if it is then unused
   (../../rocq/FlambdaNormaliseSpec.remove_unused_lets).

   Going under a binder, what is known of its name, and of anything said
   to be an alias of it, is dropped ([drop_var]): the name stands for
   something else from there on. So nothing is asked of the names of the
   term. Handlers of non-recursive continuations are gone into, with what
   is known where they are defined; those of recursive ones and code are
   left as they are.

   The result is equivalent to the term, not only a refinement of it
   ([follow_aliases_equivalent_statement]), so it may be applied on both
   sides of the comparison.

   The proofs are in FlambdaAliasesProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaNominalSpec FlambdaNormaliseSpec.
From OxCamlFlambda2Types Require Import FlambdaTypesSpec.
Import ListNotations.

(* ======================================================================== *)
(* Forgetting a name                                                        *)
(* ======================================================================== *)

Definition var_in_type (x : variable) (t : flambda_type) : bool :=
  match t with
  | Equals s => var_in_simple x s
  | Unknown | Bottom => false
  end.

(* What is known that does not mention [x]. *)
Definition drop_var (x : variable) (tenv : typing_env) : typing_env :=
  filter (fun '(y, t) => negb (Pos.eqb x y) && negb (var_in_type x t)) tenv.

Definition drop_vars (xs : list variable) (tenv : typing_env) : typing_env :=
  fold_right drop_var tenv xs.

(* ======================================================================== *)
(* Following aliases                                                        *)
(* ======================================================================== *)

Definition canonical_value_slots (tenv : typing_env)
    (slots : list (value_slot * simple)) : list (value_slot * simple) :=
  map (fun slot => (fst slot, canonical_simple tenv (snd slot))) slots.

Definition canonical_named (tenv : typing_env) (d : named) : named :=
  match d with
  | Simple s => Simple (canonical_simple tenv s)
  | Prim p args => Prim p (map (canonical_simple tenv) args)
  | Set_of_closures code slots =>
    Set_of_closures code (canonical_value_slots tenv slots)
  | Project_value_slot slot closure =>
    Project_value_slot slot (canonical_simple tenv closure)
  end.

Definition canonical_static_const (tenv : typing_env) (const : static_const)
    : static_const :=
  match const with
  | Static_const_set_of_closures code slots =>
    Static_const_set_of_closures code (canonical_value_slots tenv slots)
  | Static_const_block tag fields =>
    Static_const_block tag (map (canonical_simple tenv) fields)
  | Static_const_boxed_number contents =>
    Static_const_boxed_number (canonical_simple tenv contents)
  | Static_const_immutable_string bytes => Static_const_immutable_string bytes
  end.

Definition canonical_static_binding (tenv : typing_env)
    (binding : static_binding) : static_binding :=
  match binding with
  | Bind_code id c => Bind_code id c
  | Bind_deleted_code id => Bind_deleted_code id
  | Bind_symbol s const => Bind_symbol s (canonical_static_const tenv const)
  end.

Definition canonical_apply_cont (tenv : typing_env) (ac : apply_cont)
    : apply_cont :=
  Apply_cont_expr (ac_continuation ac)
    (map (canonical_simple tenv) (ac_args ac)).

Definition canonical_apply (tenv : typing_env) (ap : apply_expr) : apply_expr :=
  Apply_expr (canonical_simple tenv (ap_callee ap)) (ap_call_kind ap)
    (map (canonical_simple tenv) (ap_args ap)) (ap_continuation ap)
    (ap_exn_continuation ap).

(* What is known in the body of a [Let] of [x] to [d]: nothing of the old
   [x], and that the new one is [d] if that is a [Simple] not mentioning
   it. *)
Definition typing_env_under_let (tenv : typing_env) (x : variable) (d : named)
    : typing_env :=
  match d with
  | Simple s =>
    if var_in_simple x s
    then drop_var x tenv
    else (x, Equals s) :: drop_var x tenv
  | Prim _ _ | Set_of_closures _ _ | Project_value_slot _ _ => drop_var x tenv
  end.

Fixpoint follow_aliases (tenv : typing_env) (e : expr) : expr :=
  match e with
  | Let x d body =>
    let d' := canonical_named tenv d in
    Let x d' (follow_aliases (typing_env_under_let tenv x d') body)
  | Let_static bindings body =>
    Let_static (map (canonical_static_binding tenv) bindings)
      (follow_aliases tenv body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (follow_aliases_in_handler tenv h)
      (follow_aliases tenv body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (follow_aliases tenv body)
  | Apply ap => Apply (canonical_apply tenv ap)
  | Apply_cont ac => Apply_cont (canonical_apply_cont tenv ac)
  | Switch scrutinee arms =>
    Switch (canonical_simple tenv scrutinee)
      (map (fun arm => (fst arm, canonical_apply_cont tenv (snd arm))) arms)
  | Invalid => Invalid
  end
with follow_aliases_in_handler (tenv : typing_env) (h : continuation_handler)
    : continuation_handler :=
  match h with
  | Handler params handler =>
    Handler params (follow_aliases (drop_vars params tenv) handler)
  end.

Definition follow_aliases_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (follow_aliases [] e).
