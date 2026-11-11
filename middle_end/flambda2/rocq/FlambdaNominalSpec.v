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

(* Names: renamings, free names, and the binders of Flambda 2 as name
   abstractions.

   This file is to be reviewed, against middle_end/flambda2/nominal/: the
   renamings and their application to terms ([Renaming], [apply_renaming]),
   the free names ([free_names]), and the statements, which say what
   [Name_abstraction] relies on.

   The compiler treats a binder as a name abstraction in the sense of
   nominal sets: [Name_abstraction.t] holds a bound name and a term,
   [apply_renaming] acts on it by a permutation of names, and its only
   eliminator, [pattern_match], gives the term with the bound name replaced
   by a fresh one. So a term stands for its alpha-equivalence class. Rocq
   has no quotients, and the terms of FlambdaModel.v stay what they are,
   expressions with named binders that shadow; the semantics needs nothing
   else. What this file adds is the part of the theory of nominal sets that
   the compiler uses, with [expr_equivalent] in the place of equality of
   classes:
   - the permutations of names with finite support, as lists of swaps, and
     a renaming as one permutation of variables and one of continuations;
   - their action on terms ([rename_expr]), which renames bound and free
     occurrences alike and so never captures;
   - the support of a term up to its binders, its free names
     ([var_free_in_expr], [cont_free_in_expr]);
   - the defining property of an abstraction: a permutation that fixes the
     free names of a binder with its scope may be applied to the bound name
     and the scope ([rename_let_statement] and the four after it). The
     concretion at a fresh name that [pattern_match] performs is the case
     of a swap ([freshen_let_statement]);
   - that behaviour depends on the free names only, by which a binding
     that is not used may be removed ([unused_let_statement] and the two
     after it).
   With FlambdaContextSpec.v these apply to any subterm.

   It is partial: there is no type of alpha-equivalence classes, no general
   notion of nominal set or of support, and no equivariance of the machine
   itself. Fresh names are not generated here; a statement holds of every
   name that is fresh enough.

   The proofs are in FlambdaNominalProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec.
Import ListNotations.

(* ======================================================================== *)
(* Renamings                                                                *)
(* ======================================================================== *)

(* A permutation of names: the swaps of the list, the last one first. *)
Definition permutation : Type := list (positive * positive).

Definition swap (a b name : positive) : positive :=
  if Pos.eqb name a then b else if Pos.eqb name b then a else name.

Fixpoint permute (p : permutation) (name : positive) : positive :=
  match p with
  | [] => name
  | (a, b) :: p => swap a b (permute p name)
  end.

(* [Renaming.t], for variables and continuations. *)
Record renaming : Type := Renaming {
  variable_permutation : permutation;
  continuation_permutation : permutation
}.

Definition identity_renaming : renaming := Renaming [] [].

Definition rename_variable (r : renaming) (x : variable) : variable :=
  permute (variable_permutation r) x.

Definition rename_continuation (r : renaming) (k : continuation)
    : continuation :=
  permute (continuation_permutation r) k.

Arguments rename_variable : simpl never.
Arguments rename_continuation : simpl never.

(* [apply_renaming], on each sort of term. *)
Definition rename_simple (r : renaming) (s : simple) : simple :=
  match s with
  | Var x => Var (rename_variable r x)
  | Symbol sym => Symbol sym
  | Const c => Const c
  end.

Definition rename_named (r : renaming) (defining_expr : named) : named :=
  match defining_expr with
  | Simple s => Simple (rename_simple r s)
  | Prim p args => Prim p (map (rename_simple r) args)
  | Set_of_closures code value_slots =>
    Set_of_closures code
      (map (fun slot => (fst slot, rename_simple r (snd slot))) value_slots)
  | Project_value_slot slot closure =>
    Project_value_slot slot (rename_simple r closure)
  end.

Definition rename_apply_cont (r : renaming) (ac : apply_cont) : apply_cont :=
  Apply_cont_expr (rename_continuation r (ac_continuation ac))
    (map (rename_simple r) (ac_args ac)).

(* A renaming acts on the variables and the continuations of a term.
   Symbols and code ids are not renamed, and nor is code: it is closed, so
   none of its names is one of the term around it. *)
Definition rename_static_const (r : renaming) (const : static_const)
    : static_const :=
  match const with
  | Static_const_set_of_closures code value_slots =>
    Static_const_set_of_closures code
      (map (fun slot => (fst slot, rename_simple r (snd slot))) value_slots)
  | Static_const_block tag fields =>
    Static_const_block tag (map (rename_simple r) fields)
  | Static_const_boxed_number contents =>
    Static_const_boxed_number (rename_simple r contents)
  | Static_const_immutable_string bytes => Static_const_immutable_string bytes
  end.

Definition rename_static_binding (r : renaming) (binding : static_binding)
    : static_binding :=
  match binding with
  | Bind_code id c => Bind_code id c
  | Bind_deleted_code id => Bind_deleted_code id
  | Bind_symbol s const => Bind_symbol s (rename_static_const r const)
  end.

Definition rename_apply (r : renaming) (ap : apply_expr) : apply_expr :=
  Apply_expr (rename_simple r (ap_callee ap)) (ap_call_kind ap)
    (map (rename_simple r) (ap_args ap))
    (rename_continuation r (ap_continuation ap))
    (rename_continuation r (ap_exn_continuation ap)).

Fixpoint rename_expr (r : renaming) (e : expr) : expr :=
  match e with
  | Let x defining_expr body =>
    Let (rename_variable r x) (rename_named r defining_expr)
      (rename_expr r body)
  | Let_static bindings body =>
    Let_static (map (rename_static_binding r) bindings) (rename_expr r body)
  | Let_cont_non_recursive k handler body =>
    Let_cont_non_recursive (rename_continuation r k)
      (rename_handler r handler) (rename_expr r body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive
      (map (fun '(k, h) => (rename_continuation r k, rename_handler r h))
         handlers)
      (rename_expr r body)
  | Apply ap => Apply (rename_apply r ap)
  | Apply_cont ac => Apply_cont (rename_apply_cont r ac)
  | Switch scrutinee arms =>
    Switch (rename_simple r scrutinee)
      (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  | Invalid => Invalid
  end
with rename_handler (r : renaming) (h : continuation_handler)
    : continuation_handler :=
  match h with
  | Handler params handler =>
    Handler (map (rename_variable r) params) (rename_expr r handler)
  end.

Definition rename_handlers (r : renaming)
    (handlers : list (continuation * continuation_handler))
    : list (continuation * continuation_handler) :=
  map (fun '(k, h) => (rename_continuation r k, rename_handler r h)) handlers.

(* ======================================================================== *)
(* Free names                                                               *)
(* ======================================================================== *)

(* Some handler of the list satisfies [P]. *)
Fixpoint any_handler {A : Type} (P : A -> Prop)
    (handlers : list (continuation * A)) : Prop :=
  match handlers with
  | [] => False
  | (_, h) :: handlers => P h ∨ any_handler P handlers
  end.

Definition var_free_in_simple (x : variable) (s : simple) : Prop :=
  match s with
  | Var y => x = y
  | Symbol _ | Const _ => False
  end.

Definition var_free_in_simples (x : variable) (args : list simple) : Prop :=
  Exists (var_free_in_simple x) args.

Definition var_free_in_named (x : variable) (defining_expr : named) : Prop :=
  match defining_expr with
  | Simple s => var_free_in_simple x s
  | Prim _ args => var_free_in_simples x args
  | Set_of_closures _ value_slots =>
    Exists (fun slot => var_free_in_simple x (snd slot)) value_slots
  | Project_value_slot _ closure => var_free_in_simple x closure
  end.

Definition var_free_in_static_const (x : variable) (const : static_const)
    : Prop :=
  match const with
  | Static_const_set_of_closures _ value_slots =>
    Exists (fun slot => var_free_in_simple x (snd slot)) value_slots
  | Static_const_block _ fields => var_free_in_simples x fields
  | Static_const_boxed_number contents => var_free_in_simple x contents
  | Static_const_immutable_string _ => False
  end.

(* Code has no free variable of the term around it, whatever is in it. *)
Definition var_free_in_static_binding (x : variable)
    (binding : static_binding) : Prop :=
  match binding with
  | Bind_code _ _ | Bind_deleted_code _ => False
  | Bind_symbol _ const => var_free_in_static_const x const
  end.

(* A [Let] binds its variable in its body; a handler binds its
   parameters. *)
Fixpoint var_free_in_expr (x : variable) (e : expr) : Prop :=
  match e with
  | Let y defining_expr body =>
    var_free_in_named x defining_expr ∨ (x <> y ∧ var_free_in_expr x body)
  | Let_static bindings body =>
    Exists (var_free_in_static_binding x) bindings ∨ var_free_in_expr x body
  | Let_cont_non_recursive _ handler body =>
    var_free_in_handler x handler ∨ var_free_in_expr x body
  | Let_cont_recursive handlers body =>
    any_handler (var_free_in_handler x) handlers ∨ var_free_in_expr x body
  | Apply ap =>
    var_free_in_simple x (ap_callee ap) ∨ var_free_in_simples x (ap_args ap)
  | Apply_cont ac => var_free_in_simples x (ac_args ac)
  | Switch scrutinee arms =>
    var_free_in_simple x scrutinee
    ∨ Exists (fun arm => var_free_in_simples x (ac_args (snd arm))) arms
  | Invalid => False
  end
with var_free_in_handler (x : variable) (h : continuation_handler) : Prop :=
  match h with
  | Handler params handler => x ∉ params ∧ var_free_in_expr x handler
  end.

(* A non-recursive [Let_cont] binds its continuation in its body; a
   recursive one binds its continuations in its body and its handlers. *)
Fixpoint cont_free_in_expr (k : continuation) (e : expr) : Prop :=
  match e with
  | Let _ _ body | Let_static _ body => cont_free_in_expr k body
  | Let_cont_non_recursive bound handler body =>
    cont_free_in_handler k handler ∨ (k <> bound ∧ cont_free_in_expr k body)
  | Let_cont_recursive handlers body =>
    lookup k handlers = None
    ∧ (any_handler (cont_free_in_handler k) handlers
       ∨ cont_free_in_expr k body)
  | Apply ap => k = ap_continuation ap ∨ k = ap_exn_continuation ap
  | Apply_cont ac => k = ac_continuation ac
  | Switch _ arms => Exists (fun arm => k = ac_continuation (snd arm)) arms
  | Invalid => False
  end
with cont_free_in_handler (k : continuation) (h : continuation_handler)
    : Prop :=
  match h with
  | Handler _ handler => cont_free_in_expr k handler
  end.

(* ======================================================================== *)
(* Binders are name abstractions                                            *)
(* ======================================================================== *)

(* The variable of a [Let]: a renaming that fixes the free names of the
   body other than the bound variable may be applied to the bound variable
   and the body. *)
Definition rename_let_statement : Prop :=
  ∀ (r : renaming) (x : variable) (defining_expr : named) (body : expr),
    (∀ y : variable,
      y <> x -> var_free_in_expr y body -> rename_variable r y = y) ->
    (∀ k : continuation,
      cont_free_in_expr k body -> rename_continuation r k = k) ->
    expr_equivalent (Let x defining_expr body)
      (Let (rename_variable r x) defining_expr (rename_expr r body)).

(* [Name_abstraction.pattern_match] on a [Let]: the bound variable becomes
   one that is not free in the body. *)
Definition freshen_let_statement : Prop :=
  ∀ (x fresh : variable) (defining_expr : named) (body : expr),
    ~ var_free_in_expr fresh body ->
    expr_equivalent (Let x defining_expr body)
      (Let fresh defining_expr
         (rename_expr (Renaming [(x, fresh)] []) body)).

(* The continuation of a non-recursive [Let_cont]. *)
Definition rename_let_cont_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (handler : continuation_handler)
    (body : expr),
    (∀ y : variable, var_free_in_expr y body -> rename_variable r y = y) ->
    (∀ k' : continuation,
      k' <> k -> cont_free_in_expr k' body -> rename_continuation r k' = k')
    ->
    expr_equivalent (Let_cont_non_recursive k handler body)
      (Let_cont_non_recursive (rename_continuation r k) handler
         (rename_expr r body)).

(* The parameters of a continuation handler. *)
Definition rename_handler_params_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (params : list variable)
    (handler body : expr),
    (∀ y : variable,
      y ∉ params -> var_free_in_expr y handler -> rename_variable r y = y) ->
    (∀ k' : continuation,
      cont_free_in_expr k' handler -> rename_continuation r k' = k') ->
    expr_equivalent
      (Let_cont_non_recursive k (Handler params handler) body)
      (Let_cont_non_recursive k (rename_handler r (Handler params handler))
         body).

(* The parameters of one handler of a recursive [Let_cont]. *)
Definition rename_recursive_handler_params_statement : Prop :=
  ∀ (r : renaming) (before : list (continuation * continuation_handler))
    (k : continuation) (params : list variable) (handler : expr)
    (after : list (continuation * continuation_handler)) (body : expr),
    (∀ y : variable,
      y ∉ params -> var_free_in_expr y handler -> rename_variable r y = y) ->
    (∀ k' : continuation,
      cont_free_in_expr k' handler -> rename_continuation r k' = k') ->
    expr_equivalent
      (Let_cont_recursive (before ++ (k, Handler params handler) :: after)
         body)
      (Let_cont_recursive
         (before ++ (k, rename_handler r (Handler params handler)) :: after)
         body).

(* The continuations of a recursive [Let_cont], and the parameters of its
   handlers: a renaming that fixes the free names of the whole may be
   applied throughout. *)
Definition rename_let_cont_recursive_statement : Prop :=
  ∀ (r : renaming) (handlers : list (continuation * continuation_handler))
    (body : expr),
    (∀ y : variable,
      var_free_in_expr y (Let_cont_recursive handlers body) ->
      rename_variable r y = y) ->
    (∀ k : continuation,
      cont_free_in_expr k (Let_cont_recursive handlers body) ->
      rename_continuation r k = k) ->
    expr_equivalent (Let_cont_recursive handlers body)
      (rename_expr r (Let_cont_recursive handlers body)).

(* ======================================================================== *)
(* Bindings that are not used                                               *)
(* ======================================================================== *)

(* A [Let] whose variable is not free in its body may be removed. This is
   a refinement: the defining expression may be undefined. (It has no
   other effect, there being none in this fragment.) *)
Definition unused_let_statement : Prop :=
  ∀ (x : variable) (defining_expr : named) (body : expr),
    ~ var_free_in_expr x body ->
    expr_refines (Let x defining_expr body) body.

Definition unused_let_cont_statement : Prop :=
  ∀ (k : continuation) (handler : continuation_handler) (body : expr),
    ~ cont_free_in_expr k body ->
    expr_equivalent (Let_cont_non_recursive k handler body) body.

Definition unused_let_cont_recursive_statement : Prop :=
  ∀ (handlers : list (continuation * continuation_handler)) (body : expr),
    handlers_bind_statics handlers = false ->
    (∀ k : continuation,
      cont_free_in_expr k body -> lookup k handlers = None) ->
    expr_equivalent (Let_cont_recursive handlers body) body.
