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

(* What the unit binds a symbol to is known wherever the symbol is used:
   a primitive or a projection applied to symbols bound to constants is
   replaced by its value.

   This file is to be reviewed: [known_bindings], [fold_known] and what
   they are made of, against what Simplify does (below); [bound_as], the
   check; [fold_known_unit], which is extracted and run by the validation
   of middle_end/flambda2/tests/semantics/; and the statements.

   What Simplify does. A symbol has a type from where it is bound to the
   end of the unit, in code too, and that type says what it is bound to:
   the closures of a static set with their symbols and what their value
   slots hold, the tag and the fields of a static block, the contents of
   a boxed number (simplify/simplify_static_const.ml and
   simplify/lifting/, which give the symbols of a group their types
   before the rest of the unit is simplified). So, wherever such a
   symbol is an argument: the projection of a function slot from the
   symbol of a closure is the symbol of the other closure of the set
   (simplify/simplify_unary_primitive.ml,
   [simplify_project_function_slot]); the projection of a value slot is
   what the slot holds ([simplify_project_value_slot]); a load from a
   static block is its field, and [Is_int] and [Get_tag] of one are
   their answers ([simplify_immutable_block_load] and the like). In the
   code of a function whose closure is a symbol, [my_closure] is that
   symbol (FlambdaMyClosureSpec.v), so the code of two functions that
   call each other comes to call through the two symbols.

   What is here. [known_bindings e] are the symbols that the unit [e]
   binds, outside code, to a constant with no variable in it: one whose
   fields or value slots are symbols and constants. Such a constant has
   one value whatever the environment ([known_statics]). [fold_known]
   replaces, in the whole unit, in code and in handlers too, the
   defining expression of a [Let] whose arguments are constants and
   such symbols, and which has under [known_statics] a value that is a
   constant or a symbol, by that value ([fold_known_named]). The value
   is computed by the evaluation of the machine itself
   (FlambdaSemanticsSpec.eval_named), so there is no list of primitives
   here, and nothing to keep in step with them. The one primitive that
   the normalisation never folds is not folded here either
   (FlambdaNormaliseSpec.prim_may_fold: [Opaque_identity], which
   Simplify leaves alone). No primitive of the model has an effect;
   one that allocates something with an identity, or reads what may
   change, must be left out too when the model has them.

   It is right where each symbol, if it is bound when the [Let] runs,
   is bound to that constant. Under other environments it may be bound
   to something else, so this is no rewrite under all environments. For
   a unit run on its own it is enough that every static binding of such
   a symbol in the unit binds it to the one constant, which is what
   [bound_as] checks; the symbol is then bound to it or to nothing, and
   where it is bound to nothing the defining expression has no value in
   the unit as it was (every operation on a symbol bound to nothing is
   undefined, decision D8). So the unit folded refines the unit, run on
   its own ([fold_known_unit_program_refines_statement]); it is not an
   equivalence, for that last reason.

   Nothing is guessed: the bindings are read off the unit itself. A
   variable that stands for a symbol is not looked through; following
   aliases is another pass (../types/rocq/FlambdaAliasesSpec.v), to be
   run before this one, and again after it for the symbols and constants
   that it puts in place of projections.

   What is not here: a symbol bound to a constant that has a variable in
   it (a closure with a value slot computed when the unit runs); the
   variable is in scope where the symbol is bound and not in code.

   The proofs are in FlambdaKnownSymbolsProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaValueSpec FlambdaSemanticsSpec FlambdaNominalSpec
  FlambdaNormaliseSpec FlambdaUnusedStaticsSpec.
Import ListNotations.

(* ======================================================================== *)
(* What is known                                                            *)
(* ======================================================================== *)

(* A symbol or a constant. *)
Definition closed_simple (s : simple) : bool :=
  match s with
  | Symbol _ | Const _ => true
  | Var _ => false
  end.

(* A static constant with no variable in it. *)
Definition closed_static_const (const : static_const) : bool :=
  match const with
  | Static_const_set_of_closures _ value_slots
  | Static_const_closure_of_set _ _ _ value_slots =>
    forallb (fun slot => closed_simple (snd slot)) value_slots
  | Static_const_block _ fields => forallb closed_simple fields
  | Static_const_boxed_number contents => closed_simple contents
  | Static_const_immutable_string _ => true
  end.

(* What a binding lets be known: a symbol bound to a constant with no
   variable in it, which has a value. *)
Definition known_of_binding (binding : static_binding)
    : list (symbol * static_const) :=
  match binding with
  | Bind_symbol s const =>
    if closed_static_const const
    then
      match eval_static_const [] const with
      | Some _ => [(s, const)]
      | None => []
      end
    else []
  | Bind_code _ _ | Bind_deleted_code _ => []
  end.

(* The symbols that the expression binds to such constants, outside
   code, with the constants. *)
Fixpoint known_bindings (e : expr) : list (symbol * static_const) :=
  match e with
  | Let _ _ _ body => known_bindings body
  | Let_static bindings body =>
    flat_map known_of_binding bindings ++ known_bindings body
  | Let_cont_non_recursive _ h body =>
    known_bindings_of_handler h ++ known_bindings body
  | Let_cont_recursive handlers body =>
    flat_map (fun '(_, h) => known_bindings_of_handler h) handlers
    ++ known_bindings body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => []
  end
with known_bindings_of_handler (h : continuation_handler)
    : list (symbol * static_const) :=
  match h with
  | Handler _ _ handler => known_bindings handler
  end.

(* What each such symbol is bound to: the value of its constant, which
   needs no environment. There is no code. *)
Definition known_value (binding : symbol * static_const)
    : list (symbol * statically_allocated_value) :=
  match eval_static_const [] (snd binding) with
  | Some allocated => [(fst binding, allocated)]
  | None => []
  end.

Definition known_statics (known : list (symbol * static_const))
    : static_env :=
  Static_env [] (flat_map known_value known).

(* ======================================================================== *)
(* The rewrite                                                              *)
(* ======================================================================== *)

(* A constant, or a symbol that [statics] binds. *)
Definition simple_known (statics : static_env) (s : simple) : bool :=
  match s with
  | Const _ => true
  | Symbol sym => is_some (lookup sym (static_values statics))
  | Var _ => false
  end.

(* A primitive that may be folded, or a projection, all of whose
   arguments are such. *)
Definition named_known (statics : static_env) (d : named) : bool :=
  match d with
  | Prim p args => prim_may_fold p && forallb (simple_known statics) args
  | Project_value_slot _ closure | Project_value_slot_from _ _ closure
  | Project_function_slot _ _ closure =>
    simple_known statics closure
  | Simple _ | Set_of_closures _ _ | Closure_of_set _ _ _ => false
  end.

(* The defining expression, or its value under [statics] if all its
   arguments are known and the value is a constant or a symbol. *)
Definition fold_known_named (statics : static_env) (d : named) : named :=
  if named_known statics d
  then
    match eval_named statics [] d with
    | Some (Value_const c) => Simple (Const c)
    | Some (Value_symbol s) => Simple (Symbol s)
    | _ => d
    end
  else d.

(* Every [Let] of the expression, in handlers and in code too, with its
   defining expression folded. *)
Fixpoint fold_known (statics : static_env) (e : expr) : expr :=
  match e with
  | Let x kind d body =>
    Let x kind (fold_known_named statics d) (fold_known statics body)
  | Let_static bindings body =>
    Let_static (map (fold_known_binding statics) bindings)
      (fold_known statics body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (fold_known_handler statics h)
      (fold_known statics body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive
      (map (fun '(k, h) => (k, fold_known_handler statics h)) handlers)
      (fold_known statics body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end
with fold_known_handler (statics : static_env) (h : continuation_handler)
    : continuation_handler :=
  match h with
  | Handler params metadata handler =>
    Handler params metadata (fold_known statics handler)
  end
with fold_known_binding (statics : static_env) (binding : static_binding)
    : static_binding :=
  match binding with
  | Bind_code id c => Bind_code id (fold_known_code statics c)
  | Bind_deleted_code _ | Bind_symbol _ _ => binding
  end
with fold_known_code (statics : static_env) (c : code) : code :=
  match c with
  | Code params my_closure ret exn metadata body =>
    Code params my_closure ret exn metadata (fold_known statics body)
  end.

(* ======================================================================== *)
(* The check                                                                *)
(* ======================================================================== *)

(* If [known] gives the symbol a constant, the binding binds it to that
   constant, which has no variable in it. *)
Definition binding_bound_as (known : list (symbol * static_const))
    (binding : static_binding) : bool :=
  match binding with
  | Bind_symbol s const =>
    match lookup s known with
    | Some expected =>
      closed_static_const const
      && if static_const_eq_dec const expected then true else false
    | None => true
    end
  | Bind_code _ _ | Bind_deleted_code _ => true
  end.

(* Every static binding of the expression, in handlers and in code too,
   binds a symbol of [known] to the constant that [known] gives it. *)
Fixpoint bound_as (known : list (symbol * static_const)) (e : expr) : bool :=
  match e with
  | Let _ _ _ body => bound_as known body
  | Let_static bindings body =>
    forallb (binding_bound_as known) bindings
    && forallb (code_of_binding_bound_as known) bindings
    && bound_as known body
  | Let_cont_non_recursive _ h body =>
    handler_bound_as known h && bound_as known body
  | Let_cont_recursive handlers body =>
    forallb (fun '(_, h) => handler_bound_as known h) handlers
    && bound_as known body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => true
  end
with handler_bound_as (known : list (symbol * static_const))
    (h : continuation_handler) : bool :=
  match h with
  | Handler _ _ handler => bound_as known handler
  end
with code_of_binding_bound_as (known : list (symbol * static_const))
    (binding : static_binding) : bool :=
  match binding with
  | Bind_code _ c => code_bound_as known c
  | Bind_deleted_code _ | Bind_symbol _ _ => true
  end
with code_bound_as (known : list (symbol * static_const)) (c : code) : bool :=
  match c with
  | Code _ _ _ _ _ body => bound_as known body
  end.

(* The unit with what it binds its symbols to used wherever they are, if
   it binds each of them to one constant. *)
Definition fold_known_unit (e : expr) : option expr :=
  let known := known_bindings e in
  if bound_as known e then Some (fold_known (known_statics known) e) else None.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

(* What [fold_known_unit] gives refines the unit, run on its own. *)
Definition fold_known_unit_program_refines_statement : Prop :=
  ∀ e e' : expr, fold_known_unit e = Some e' -> program_refines e e'.

(* A defining expression is folded to its value: in any static
   environment in which each symbol that [statics] binds is bound to the
   same thing or to nothing, if the expression has a value, the
   expression folded has that value. *)
Definition fold_known_named_sound_statement : Prop :=
  ∀ (statics run_statics : static_env) (vars : env) (d : named) (v : value),
    (∀ (s : symbol) (allocated allocated' : statically_allocated_value),
      lookup s (static_values statics) = Some allocated ->
      lookup s (static_values run_statics) = Some allocated' ->
      allocated' = allocated) ->
    eval_named run_statics vars d = Some v ->
    eval_named run_statics vars (fold_known_named statics d) = Some v.

(* The rewrite commutes with renaming, which renames no symbol: what is
   known is the same, and an expression that is folded has no variable
   in it. *)
Definition fold_known_equivariant_statement : Prop :=
  ∀ (r : renaming) (statics : static_env) (e : expr),
    rename_expr r (fold_known statics e) = fold_known statics (rename_expr r e).
