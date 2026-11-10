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

(* Comparing two expressions up to their bound names: a decision, and that
   it is sound.

   This file is to be reviewed: [expr_eqb] and what it is made of, against
   middle_end/flambda2/compare/compare.ml, which compares Flambda terms up
   to alpha-equivalence; the axioms about [prim_eqb]; and the statement.

   [expr_eqb] goes through the two expressions together, keeping the pairs
   of bound variables and of bound continuations met so far. A name bound
   on one side must be used where its partner is on the other; a name
   bound on neither must be the same on both. Symbols, code ids and value
   slots must be the same. Code is compared as closed: only its own
   parameters, [my_closure] and continuations are paired.

   It is sound: expressions it says are the same are equivalent
   ([expr_eqb_sound_statement]). It is not said to be complete, and it is
   not: it does not reorder the bindings of a group, for one.

   This is the comparison of the validation of
   middle_end/flambda2/tests/semantics/: where Simplify's output is the
   same as its input up to bound names, or is brought to that by rewrites
   proved elsewhere, the two are equivalent by a theorem and not only by a
   test.

   Trusted here: [prim_eqb], an equality test on the abstract primitives,
   with two axioms saying that it decides equality.

   The proofs are in FlambdaCompareProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec.
Import ListNotations.

(* ======================================================================== *)
(* Names                                                                    *)
(* ======================================================================== *)

(* The pairs of bound names, the most recently bound first. *)
Definition name_map : Type := list (positive * positive).

(* [a] on the one side stands where [a'] does on the other: they were bound
   together, by the most recent binding of either; or neither is bound, and
   they are the same name. *)
Fixpoint names_match (m : name_map) (a a' : positive) : bool :=
  match m with
  | [] => Pos.eqb a a'
  | (b, b') :: m =>
    if Pos.eqb a b
    then Pos.eqb a' b'
    else if Pos.eqb a' b' then false else names_match m a a'
  end.

(* Parameters are bound one after the other, a later one shadowing an
   earlier one of the same name. *)
Fixpoint bind_names (xs xs' : list positive) (m : name_map) : option name_map :=
  match xs, xs' with
  | [], [] => Some m
  | x :: xs, x' :: xs' => bind_names xs xs' ((x, x') :: m)
  | _, _ => None
  end.

(* The continuations of a recursive [Let_cont] are bound together, the
   first of a name counting. *)
Definition combine_names (xs xs' : list positive) (m : name_map)
    : option name_map :=
  if Nat.eqb (length xs) (length xs')
  then Some (combine xs xs' ++ m)
  else None.

(* ======================================================================== *)
(* What has no binder                                                       *)
(* ======================================================================== *)

Definition kind_eq_dec : ∀ k k' : flambda_kind, {k = k'} + {k <> k'}.
Proof. repeat decide equality. Defined.

Definition const_eq_dec : ∀ c c' : const, {c = c'} + {c <> c'}.
Proof. decide equality; try apply Z.eq_dec; apply kind_eq_dec. Defined.

Definition const_eqb (c c' : const) : bool :=
  if const_eq_dec c c' then true else false.

(* An equality test on the primitives, which are abstract. *)
Parameter prim_eqb : prim -> prim -> bool.

Axiom prim_eqb_sound : ∀ p p' : prim, prim_eqb p p' = true -> p = p'.

Axiom prim_eqb_refl : ∀ p : prim, prim_eqb p p = true.

Fixpoint forall2b {A B : Type} (f : A -> B -> bool) (l : list A)
    (l' : list B) : bool :=
  match l, l' with
  | [], [] => true
  | a :: l, b :: l' => f a b && forall2b f l l'
  | _, _ => false
  end.

Definition simple_eqb (vm : name_map) (s s' : simple) : bool :=
  match s, s' with
  | Var x, Var x' => names_match vm x x'
  | Symbol sym, Symbol sym' => Pos.eqb sym sym'
  | Const c, Const c' => const_eqb c c'
  | _, _ => false
  end.

Definition simples_eqb (vm : name_map) (args args' : list simple) : bool :=
  forall2b (simple_eqb vm) args args'.

Definition value_slots_eqb (vm : name_map)
    (slots slots' : list (value_slot * simple)) : bool :=
  forall2b
    (fun slot slot' =>
       Pos.eqb (fst slot) (fst slot') && simple_eqb vm (snd slot) (snd slot'))
    slots slots'.

Definition named_eqb (vm : name_map) (d d' : named) : bool :=
  match d, d' with
  | Simple s, Simple s' => simple_eqb vm s s'
  | Prim p args, Prim p' args' => prim_eqb p p' && simples_eqb vm args args'
  | Set_of_closures code slots, Set_of_closures code' slots' =>
    Pos.eqb code code' && value_slots_eqb vm slots slots'
  | Project_value_slot slot closure, Project_value_slot slot' closure' =>
    Pos.eqb slot slot' && simple_eqb vm closure closure'
  | _, _ => false
  end.

Definition static_const_eqb (vm : name_map) (const const' : static_const)
    : bool :=
  match const, const' with
  | Static_const_set_of_closures code slots,
    Static_const_set_of_closures code' slots' =>
    Pos.eqb code code' && value_slots_eqb vm slots slots'
  | Static_const_block tag fields, Static_const_block tag' fields' =>
    Z.eqb tag tag' && simples_eqb vm fields fields'
  | Static_const_boxed_number contents, Static_const_boxed_number contents' =>
    simple_eqb vm contents contents'
  | Static_const_immutable_string bytes,
    Static_const_immutable_string bytes' =>
    forall2b Z.eqb bytes bytes'
  | _, _ => false
  end.

Definition call_kind_eqb (kind kind' : call_kind) : bool :=
  match kind, kind' with
  | Direct code, Direct code' => Pos.eqb code code'
  | Indirect, Indirect => true
  | _, _ => false
  end.

Definition apply_cont_eqb (vm km : name_map) (ac ac' : apply_cont) : bool :=
  names_match km (ac_continuation ac) (ac_continuation ac')
  && simples_eqb vm (ac_args ac) (ac_args ac').

Definition apply_eqb (vm km : name_map) (ap ap' : apply_expr) : bool :=
  simple_eqb vm (ap_callee ap) (ap_callee ap')
  && call_kind_eqb (ap_call_kind ap) (ap_call_kind ap')
  && simples_eqb vm (ap_args ap) (ap_args ap')
  && names_match km (ap_continuation ap) (ap_continuation ap')
  && names_match km (ap_exn_continuation ap) (ap_exn_continuation ap').

(* ======================================================================== *)
(* Expressions                                                              *)
(* ======================================================================== *)

Fixpoint expr_eqb (vm km : name_map) (e e' : expr) {struct e} : bool :=
  match e, e' with
  | Let x d body, Let x' d' body' =>
    named_eqb vm d d' && expr_eqb ((x, x') :: vm) km body body'
  | Let_static bindings body, Let_static bindings' body' =>
    forall2b (binding_eqb vm) bindings bindings' && expr_eqb vm km body body'
  | Let_cont_non_recursive k h body, Let_cont_non_recursive k' h' body' =>
    handler_eqb vm km h h' && expr_eqb vm ((k, k') :: km) body body'
  | Let_cont_recursive handlers body, Let_cont_recursive handlers' body' =>
    match combine_names (map fst handlers) (map fst handlers') km with
    | Some km' =>
      forall2b (fun '(_, h) '(_, h') => handler_eqb vm km' h h') handlers
        handlers'
      && expr_eqb vm km' body body'
    | None => false
    end
  | Apply ap, Apply ap' => apply_eqb vm km ap ap'
  | Apply_cont ac, Apply_cont ac' => apply_cont_eqb vm km ac ac'
  | Switch scrutinee arms, Switch scrutinee' arms' =>
    simple_eqb vm scrutinee scrutinee'
    && forall2b
         (fun arm arm' =>
            Z.eqb (fst arm) (fst arm')
            && apply_cont_eqb vm km (snd arm) (snd arm'))
         arms arms'
  | Invalid, Invalid => true
  | _, _ => false
  end
with handler_eqb (vm km : name_map) (h h' : continuation_handler) {struct h}
    : bool :=
  match h, h' with
  | Handler params handler, Handler params' handler' =>
    match bind_names params params' vm with
    | Some vm' => expr_eqb vm' km handler handler'
    | None => false
    end
  end
with binding_eqb (vm : name_map) (binding binding' : static_binding)
    {struct binding} : bool :=
  match binding, binding' with
  | Bind_code id c, Bind_code id' c' => Pos.eqb id id' && code_eqb c c'
  | Bind_deleted_code id, Bind_deleted_code id' => Pos.eqb id id'
  | Bind_symbol s const, Bind_symbol s' const' =>
    Pos.eqb s s' && static_const_eqb vm const const'
  | _, _ => false
  end
with code_eqb (c c' : code) {struct c} : bool :=
  match c, c' with
  | Code params my_closure ret exn body,
    Code params' my_closure' ret' exn' body' =>
    match bind_names params params' [(my_closure, my_closure')] with
    | Some vm => expr_eqb vm [(ret, ret'); (exn, exn')] body body'
    | None => false
    end
  end.

Definition expr_eqb_sound_statement : Prop :=
  ∀ e e' : expr, expr_eqb [] [] e e' = true -> expr_equivalent e e'.
