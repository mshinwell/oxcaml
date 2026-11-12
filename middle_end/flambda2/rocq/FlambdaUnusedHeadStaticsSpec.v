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

(* Removing, from the head of a unit, static bindings that are not used:
   the unit with them refines the unit without.

   This file is to be reviewed: [head_statics_removable] and what it
   is made of ([head_bindings], [under_head], [static_const_total],
   [removed_binding_total], [kept_code_binds_only_kept]), which are
   extracted and run by the validation of
   middle_end/flambda2/tests/semantics/, and the statement.

   FlambdaUnusedStaticsSpec.drop_statics removes static bindings that
   nothing refers to, and its result refines the term, run on its own:
   that is what a rewrite of the term before Simplify owes. The
   validation also needs the removal on the term after Simplify: once it
   has inlined, in both terms, a call that Simplify left, the term after
   still binds the code and the closure that the call used, and the term
   before, in which Simplify's own removal is followed, does not. A
   rewrite of the term after owes the converse: that the term refines
   its result.

   The converse does not hold of [drop_statics] as it is, for two
   reasons, and [drop_head_statics] is [drop_statics] under the checks
   that answer them.

   - A binding removed may have had no value: the group that binds it
     is then undefined, and the term without it is not. So each constant
     removed must have a value whatever the environment
     ([static_const_total]): its fields, elements or value slots are
     constants and symbols, no variable, and a closure of a set is at a
     slot that its set has.
   - A binding of a name that is bound already is undefined
     (FlambdaSemanticsSpec.eval_static_bindings). So the statement is of
     a term run on its own, from empty environments, and the bindings
     removed are among those of the groups at the head of the term
     ([head_bindings]), which run first; the names that those groups
     bind are pairwise distinct; and nothing under them, and no code
     that they keep, binds a name removed. Under an environment that
     binds a name removed the statement is false, and it is not made:
     this is not an equivalence under all environments.

   Which names to remove is for the caller to find; a wrong guess is
   refused, not believed.

   Read the other way, the statement is that the term with more
   bindings at its head refines the term, where the checks pass of the
   larger term: a binding that nothing uses, with a name that nothing
   else binds and a constant that has a value, may be added there.
   That the term refines the larger one is
   FlambdaUnusedStaticsSpec.drop_statics_program_refines_statement,
   which needs no check beyond those of drop_statics.

   The proofs are in FlambdaUnusedHeadStaticsProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaWellFormedSpec FlambdaNormaliseSpec
  FlambdaUnusedStaticsSpec FlambdaLiftSpec.
Import ListNotations.

(* ======================================================================== *)
(* The head of a unit                                                       *)
(* ======================================================================== *)

(* The bindings of the groups of static bindings that a term begins
   with, in their order, and the term under those groups. *)
Fixpoint head_bindings (e : expr) : list static_binding :=
  match e with
  | Let_static bindings body => bindings ++ head_bindings body
  | Let _ _ _ _ | Let_cont_non_recursive _ _ _ | Let_cont_recursive _ _
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => []
  end.

Fixpoint under_head (e : expr) : expr :=
  match e with
  | Let_static _ body => under_head body
  | Let _ _ _ _ | Let_cont_non_recursive _ _ _ | Let_cont_recursive _ _
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

(* ======================================================================== *)
(* Constants that have a value whatever the environment                     *)
(* ======================================================================== *)

(* A simple that is a symbol or a constant is
   FlambdaLiftSpec.plain_simple. *)
Definition value_slots_plain (slots : list (value_slot * simple)) : bool :=
  forallb (fun slot => plain_simple (snd slot)) slots.

Definition static_const_total (const : static_const) : bool :=
  match const with
  | Static_const_set_of_closures _ slots => value_slots_plain slots
  | Static_const_closure_of_set slot _ decls slots =>
    match lookup slot decls with
    | Some _ => value_slots_plain slots
    | None => false
    end
  | Static_const_block _ fields => forallb plain_simple fields
  | Static_const_immutable_value_array elements =>
    forallb plain_simple elements
  | Static_const_boxed_number contents => plain_simple contents
  | Static_const_immutable_string _ => true
  end.

(* A binding that is kept, or whose constant has a value. *)
Definition removed_binding_total (D : dropped) (binding : static_binding)
    : bool :=
  match binding with
  | Bind_code _ _ | Bind_deleted_code _ => true
  | Bind_symbol s const => symbol_kept D s || static_const_total const
  end.

(* Code that is removed, or whose body binds none of the names removed. *)
Definition kept_code_binds_only_kept (D : dropped) (binding : static_binding)
    : bool :=
  match binding with
  | Bind_code id c => negb (code_kept D id) || code_binds_only_kept D c
  | Bind_deleted_code _ | Bind_symbol _ _ => true
  end.

(* ======================================================================== *)
(* The removal                                                              *)
(* ======================================================================== *)

(* The checks. Nothing in the term refers to a name removed, outside
   the bindings that go (FlambdaUnusedStaticsSpec.expr_avoids). Under
   the groups of the head, nothing binds a name removed, and nor does
   the body of code that those groups bind and keep: so the bindings
   removed are bindings of those groups, and no code that runs binds
   one. The symbols that the groups of the head bind are pairwise
   distinct, and so are the code ids: with the static environment
   empty at the start, each binding of those groups is of a name that
   is not bound yet. Each symbol removed is bound to a constant that
   has a value. *)
Definition head_statics_removable (D : dropped) (e : expr) : bool :=
  expr_avoids D e
  && binds_only_kept D (under_head e)
  && forallb (kept_code_binds_only_kept D) (head_bindings e)
  && distinct (flat_map symbols_of_binding (head_bindings e))
  && distinct (flat_map code_ids_of_binding (head_bindings e))
  && forallb (removed_binding_total D) (head_bindings e).

(* FlambdaUnusedStaticsSpec.drop_statics, under the checks. *)
Definition drop_head_statics (D : dropped) (e : expr) : option expr :=
  if head_statics_removable D e then drop_statics D e else None.

(* ======================================================================== *)
(* The statement                                                            *)
(* ======================================================================== *)

(* The term refines its result, each run on its own. With
   FlambdaUnusedStaticsSpec.drop_statics_program_refines_statement, of
   which [drop_head_statics] is a case, the two behave alike from empty
   environments. *)
Definition drop_head_statics_program_refines_statement : Prop :=
  ∀ (D : dropped) (e e' : expr),
    drop_head_statics D e = Some e' -> program_refines e' e.
