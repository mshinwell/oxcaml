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

(* Removing static bindings that are not used.

   This file is to be reviewed: [expr_avoids] and [erase_expr], which are
   extracted and run by the validation of
   middle_end/flambda2/tests/semantics/; the axiom about the primitives;
   and the statement.

   Simplify removes the code and the symbols that nothing refers to any
   more. Removing a static binding is not sound under every environment:
   a value already there may be a closure of the code, or the symbol, and
   then the term with the binding can call it or look into it and the term
   without cannot. It is sound for a term run on its own, from empty
   environments, and that is what is stated ([program_refines]): nothing
   then refers to the names removed but what the term itself builds.

   [drop_statics] takes the names to remove ([dropped]). It checks that
   nothing in the term refers to any of them, outside the bindings that go
   ([expr_avoids]), and removes those bindings everywhere, in handlers and
   in code too ([erase_expr]). Which names to remove is for the caller to
   find; a wrong guess is refused, not believed. A [Let_static] left with
   no binding stays, to be removed by
   FlambdaNormaliseSpec.drop_deleted_code.

   It is a refinement and not an equivalence: a binding removed may have
   been of a static constant with no value.

   Trusted here: that the primitives introduce no symbols and no code ids
   ([eval_prim_avoids]): a value they return refers only to what their
   arguments refer to. Without it a primitive could return a closure of
   code that has been removed.

   The proofs are in FlambdaUnusedStaticsProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaNormaliseSpec.
Import ListNotations.

(* ======================================================================== *)
(* The names removed, and what refers to none of them                       *)
(* ======================================================================== *)

Record dropped : Type := Dropped {
  dropped_symbols : list symbol;
  dropped_code : list code_id
}.

Definition symbol_kept (D : dropped) (s : symbol) : bool :=
  negb (name_in s (dropped_symbols D)).

Definition code_kept (D : dropped) (id : code_id) : bool :=
  negb (name_in id (dropped_code D)).

Fixpoint value_avoids (D : dropped) (v : value) : bool :=
  match v with
  | Value_const _ => true
  | Value_symbol s => symbol_kept D s
  | Value_closure code slots =>
    code_kept D code && forallb (fun '(_, v) => value_avoids D v) slots
  end.

(* The primitives introduce no symbols and no code ids. *)
Axiom eval_prim_avoids :
  ∀ (D : dropped) (p : prim) (vs : list value) (v : value),
    forallb (value_avoids D) vs = true ->
    eval_prim p vs = Some v ->
    value_avoids D v = true.

Definition simple_avoids (D : dropped) (s : simple) : bool :=
  match s with
  | Symbol sym => symbol_kept D sym
  | Var _ | Const _ => true
  end.

Definition simples_avoid (D : dropped) (args : list simple) : bool :=
  forallb (simple_avoids D) args.

Definition value_slots_avoid (D : dropped)
    (slots : list (value_slot * simple)) : bool :=
  forallb (fun slot => simple_avoids D (snd slot)) slots.

Definition named_avoids (D : dropped) (d : named) : bool :=
  match d with
  | Simple s => simple_avoids D s
  | Prim _ args => simples_avoid D args
  | Set_of_closures code slots => code_kept D code && value_slots_avoid D slots
  | Project_value_slot _ closure => simple_avoids D closure
  end.

Definition static_const_avoids (D : dropped) (const : static_const) : bool :=
  match const with
  | Static_const_set_of_closures code slots =>
    code_kept D code && value_slots_avoid D slots
  | Static_const_block _ fields => simples_avoid D fields
  | Static_const_boxed_number contents => simple_avoids D contents
  | Static_const_immutable_string _ => true
  end.

Definition apply_cont_avoids (D : dropped) (ac : apply_cont) : bool :=
  simples_avoid D (ac_args ac).

Definition apply_avoids (D : dropped) (ap : apply_expr) : bool :=
  simple_avoids D (ap_callee ap)
  && match ap_call_kind ap with
     | Direct code => code_kept D code
     | Indirect => true
     end
  && simples_avoid D (ap_args ap).

(* Nothing in the expression refers to a name removed, outside the
   bindings of those names. *)
Fixpoint expr_avoids (D : dropped) (e : expr) : bool :=
  match e with
  | Let _ d body => named_avoids D d && expr_avoids D body
  | Let_static bindings body =>
    forallb (binding_avoids D) bindings && expr_avoids D body
  | Let_cont_non_recursive _ h body =>
    handler_avoids D h && expr_avoids D body
  | Let_cont_recursive handlers body =>
    forallb (fun '(_, h) => handler_avoids D h) handlers
    && expr_avoids D body
  | Apply ap => apply_avoids D ap
  | Apply_cont ac => apply_cont_avoids D ac
  | Switch scrutinee arms =>
    simple_avoids D scrutinee
    && forallb (fun arm => apply_cont_avoids D (snd arm)) arms
  | Invalid => true
  end
with handler_avoids (D : dropped) (h : continuation_handler) : bool :=
  match h with
  | Handler _ handler => expr_avoids D handler
  end
with binding_avoids (D : dropped) (binding : static_binding) : bool :=
  match binding with
  | Bind_code id c => if code_kept D id then code_avoids D c else true
  | Bind_deleted_code _ => true
  | Bind_symbol s const =>
    if symbol_kept D s then static_const_avoids D const else true
  end
with code_avoids (D : dropped) (c : code) : bool :=
  match c with
  | Code _ _ _ _ body => expr_avoids D body
  end.

(* ======================================================================== *)
(* Removing the bindings                                                    *)
(* ======================================================================== *)

Definition binding_kept (D : dropped) (binding : static_binding) : bool :=
  match binding with
  | Bind_code id _ => code_kept D id
  | Bind_deleted_code _ => true
  | Bind_symbol s _ => symbol_kept D s
  end.

(* The elements kept, each transformed. *)
Fixpoint keep_map {A : Type} (keep : A -> bool) (f : A -> A) (l : list A)
    : list A :=
  match l with
  | [] => []
  | a :: l => if keep a then f a :: keep_map keep f l else keep_map keep f l
  end.

Fixpoint erase_expr (D : dropped) (e : expr) : expr :=
  match e with
  | Let x d body => Let x d (erase_expr D body)
  | Let_static bindings body =>
    Let_static (keep_map (binding_kept D) (erase_binding D) bindings)
      (erase_expr D body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (erase_handler D h) (erase_expr D body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive (map (fun '(k, h) => (k, erase_handler D h)) handlers)
      (erase_expr D body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end
with erase_handler (D : dropped) (h : continuation_handler)
    : continuation_handler :=
  match h with
  | Handler params handler => Handler params (erase_expr D handler)
  end
with erase_binding (D : dropped) (binding : static_binding) : static_binding :=
  match binding with
  | Bind_code id c => Bind_code id (erase_code D c)
  | Bind_deleted_code _ | Bind_symbol _ _ => binding
  end
with erase_code (D : dropped) (c : code) : code :=
  match c with
  | Code params my_closure ret exn body =>
    Code params my_closure ret exn (erase_expr D body)
  end.

Definition drop_statics (D : dropped) (e : expr) : option expr :=
  if expr_avoids D e then Some (erase_expr D e) else None.

(* ======================================================================== *)
(* The statement                                                            *)
(* ======================================================================== *)

(* Refinement of terms run on their own. Refinement under all environments
   ([expr_refines]) implies it. *)
Definition program_refines (source target : expr) : Prop :=
  refines (State source [] [] empty_static_env)
    (State target [] [] empty_static_env).

Definition drop_statics_refines_statement : Prop :=
  ∀ (D : dropped) (e e' : expr),
    drop_statics D e = Some e' -> program_refines e e'.
