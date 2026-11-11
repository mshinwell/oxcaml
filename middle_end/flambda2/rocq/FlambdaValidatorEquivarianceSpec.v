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


(* The rewrites and the checks that the validator is made of commute
   with renaming.

   This file is to be reviewed: [rewrite_equivariant], the action of a
   renaming on what a pass carries (the definitions named [rename_...]),
   and the statements.

   FlambdaEquivarianceSpec.v says that execution commutes with the
   renamings of FlambdaNominalSpec.v, and that two of the rewrites that
   the validation applies do ([fold_constants], [inline_calls]). Here are
   the statements for the other rewrites and for the checks of the files
   listed below, in the forms that a function on terms owes (NAMES.md,
   section 7):
   - a rewrite that takes a term and nothing else gives, on the renamed
     term, the renamed result ([rewrite_equivariant]);
   - a rewrite that takes names too, or something that holds names (the
     variables in scope, the code known, what a pass knows of the
     variables of the term), gives the renamed result when those are
     renamed with the term;
   - a check answers the same on the renamed term, the names it is given
     being renamed with it.
   Symbols, code ids and slots are not renamed. A map keyed by them
   keeps its keys; what it holds is renamed where it holds variables or
   continuations (the code known, under its code id; what is known of a
   symbol that is a block), and is as it was where it holds none (the
   names to remove, the code id of a symbol known to be a closure).

   The normalisations that the validation applies to the two terms
   (FlambdaValidateSpec.normalise_before, [normalise_after],
   [without_statics]) are made of these rewrites and commute with
   renaming too. The comparison of the two results answers the same
   when both are renamed
   (FlambdaCompareAlphaSpec.expr_eqb_equivariant_statement). So the
   check as a whole, FlambdaValidateSpec.validate_unit, answers the
   same on a pair of terms and on the pair renamed
   ([validate_unit_equivariant_statement]): whether Simplify is found
   correct on a unit does not depend on the names of the unit.

   So each rewrite and each check below depends on the names of the
   term by their equality only: none goes by the order or the number of
   a name, and none makes a name. The one place where names are made
   from others is the renaming that inlining builds from the four
   continuations of a call and of the code called
   (FlambdaNormaliseSpec.inline_renaming); it is made of swaps of those
   four, and commutes with a renaming of them.

   Every statement here is an equation and holds of every term: nothing
   is asked of the term, its code, its binders or its scopes. Three
   statements have a premise, on an argument that is a function: those
   of [rewrite_code] and of [iterate] ask that the rewrite they are
   given commutes with renaming, and that of [static_names] asks that
   the way it is given of reading the names of a binding does not look
   at variables and continuations.

   Kinds, arities and the metadata of handlers and of code have no
   names in them: a renaming keeps them, and a check that reads them
   answers the same.

   The rewrites and checks of FlambdaNormaliseSpec.v:
   - the checks [expr_in_scope], [inlinable_b] and [var_free_b], and
     the two tests of whether a call is sure to agree with the code
     called ([simple_has_kind_b], [call_agrees_b]);
   - the rewrites [remove_unused_lets], [inline_tail_conts] (with
     [inline_cont_at_tail], which it is made of), [drop_deleted_code],
     [remove_unused_total_lets], [remove_unused_defined_lets],
     [inline_known_calls], [merge_statics], [collapse_switches] and
     [thread_switches];
   - [rewrite_code], which takes a rewrite into the bodies of code: it
     is equivariant when the rewrite it is given is.

   Those of FlambdaUnusedContsSpec.v: the check [cont_free_b] and the
   rewrite [remove_unused_conts].

   Those of FlambdaUnusedStaticsSpec.v, where the names given are
   symbols and code ids: the checks [expr_avoids] and
   [binds_only_kept], the rewrite [erase_expr], and [drop_statics],
   which is the two together; and the condition on the environments
   under which that rewrite is sound ([envs_free_of]).

   Two passes go through a term carrying what they know of its names:
   FlambdaBlockLoadSpec.load_known_blocks, of the variables and symbols
   that are blocks, and FlambdaUnboxSpec.unbox_known_numbers, of those
   that are boxed or tagged numbers. What they carry holds variables,
   so a renaming acts on it ([rename_known_blocks],
   [rename_known_numbers], which are to be reviewed), and each pass
   commutes with renaming when what it knows is renamed with the term.
   As the validation runs them, with nothing known, they are rewrites
   that take a term and nothing else. A third pass is of the same
   kind: FlambdaAliasesSpec.follow_aliases, of the types library, which
   carries a typing environment of the first model of the types
   ([rename_naive_typing_env]).

   The checks of FlambdaWellFormedSpec.v, which say what a well-formed
   unit is: where static bindings may be ([statics_at_toplevel], with
   [raises_to], [handler_at_toplevel] and that file's
   [free_continuations]), the static names bound ([static_names]), the
   sets of closures ([sets_well_formed]), the numbers
   ([numbers_in_range]), and the check itself ([well_formed_unit]),
   given the two continuations of the unit, which are renamed with it
   ([rename_unit_interface]); and the test of the states that the
   machine makes undefined ([static_fault]). The three conditions of
   [well_formed_unit] on binders are those of FlambdaBindersSpec.v,
   which FlambdaAlphaSpec.v says are unchanged by a renaming.

   The check of kinds of FlambdaWellKindedSpec.v, which the test tool
   runs on a unit before and after Simplify: the kind that is found
   for a [Simple] and for a defining expression, the checks of a
   static constant, of an application of a continuation and of a call,
   the check of a term ([well_kinded]) and that of a unit
   ([well_kinded_unit]). The check is given the kinds of the variables
   and the kinds of the parameters of the continuations in scope,
   which hold names, so a renaming acts on them ([rename_kind_env],
   [rename_arity_env], which are to be reviewed).

   The normalisations of FlambdaValidateSpec.v: [iterate] of a rewrite
   that commutes, [normalise_before], [normalise_after] and
   [without_statics]; and the check, [validate_unit].

   Nothing is trusted here. The proofs are in
   FlambdaValidatorEquivarianceProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaNominalSpec FlambdaAlphaSpec
  FlambdaNormaliseSpec FlambdaEquivarianceSpec FlambdaUnusedContsSpec
  FlambdaUnusedStaticsSpec FlambdaBlockLoadSpec FlambdaUnboxSpec
  FlambdaWellFormedSpec FlambdaWellKindedSpec FlambdaValidateSpec.
From OxCamlFlambda2Types Require Import FlambdaTypesSpec FlambdaAliasesSpec.
Import ListNotations.

(* A rewrite of terms that takes nothing but the term commutes with
   renaming. *)
Definition rewrite_equivariant (f : expr -> expr) : Prop :=
  ∀ (r : renaming) (e : expr), f (rename_expr r e) = rename_expr r (f e).

(* ======================================================================== *)
(* The checks of FlambdaNormaliseSpec.v                                     *)
(* ======================================================================== *)

(* The names in scope are renamed with the term. *)
Definition expr_in_scope_equivariant_statement : Prop :=
  ∀ (r : renaming) (vs : list variable) (ks : list continuation) (e : expr),
    expr_in_scope (map (rename_variable r) vs)
      (map (rename_continuation r) ks) (rename_expr r e)
    = expr_in_scope vs ks e.

(* Whether a call may be inlined, the call and the code being renamed
   together. *)
Definition inlinable_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (ap : apply_expr) (c : code),
    inlinable_b (rename_apply r ap) (rename_code r c) = inlinable_b ap c.

Definition var_free_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (x : variable) (e : expr),
    var_free_b (rename_variable r x) (rename_expr r e) = var_free_b x e.

(* ======================================================================== *)
(* The rewrites of FlambdaNormaliseSpec.v                                   *)
(* ======================================================================== *)

Definition remove_unused_lets_equivariant_statement : Prop :=
  rewrite_equivariant remove_unused_lets.

(* The continuation, the parameters and the handler are renamed with the
   body; where there is no result for the one there is none for the
   other. The kinds of the parameters have no names in them and stay. *)
Definition inline_cont_at_tail_equivariant_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler body : expr),
    inline_cont_at_tail (rename_continuation r k)
      (map (rename_variable r) params) metadata (rename_expr r handler)
      (rename_expr r body)
    = option_map (rename_expr r)
        (inline_cont_at_tail k params metadata handler body).

Definition inline_tail_conts_equivariant_statement : Prop :=
  rewrite_equivariant inline_tail_conts.

Definition drop_deleted_code_equivariant_statement : Prop :=
  rewrite_equivariant drop_deleted_code.

Definition remove_unused_total_lets_equivariant_statement : Prop :=
  rewrite_equivariant remove_unused_total_lets.

(* The variables in scope are renamed with the term. *)
Definition remove_unused_defined_lets_equivariant_statement : Prop :=
  ∀ (r : renaming) (vs : list variable) (e : expr),
    remove_unused_defined_lets (map (rename_variable r) vs) (rename_expr r e)
    = rename_expr r (remove_unused_defined_lets vs e).

(* The two tests that decide whether a call is sure to agree with the
   code called: of an argument, that it is sure to have a kind, and of
   the call. They read kinds and arities, which have no names in them,
   and of an argument only whether it is a variable. *)
Definition simple_has_kind_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (s : simple) (kind : flambda_kind),
    simple_has_kind_b (rename_simple r s) kind = simple_has_kind_b s kind.

Definition call_agrees_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (ap : apply_expr) (c : code),
    call_agrees_b (rename_apply r ap) (rename_code r c) = call_agrees_b ap c.

(* The code known is renamed with the term, as for [inline_calls]. What
   is known of the symbols holds no variable and no continuation. *)
Definition inline_known_calls_equivariant_statement : Prop :=
  ∀ (r : renaming) (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (e : expr),
    inline_known_calls (map_values (rename_code r) known_code) known_symbols
      (rename_expr r e)
    = rename_expr r (inline_known_calls known_code known_symbols e).

Definition merge_statics_equivariant_statement : Prop :=
  rewrite_equivariant merge_statics.

Definition collapse_switches_equivariant_statement : Prop :=
  rewrite_equivariant collapse_switches.

Definition thread_switches_equivariant_statement : Prop :=
  rewrite_equivariant thread_switches.

(* A rewrite taken into the bodies of code. *)
Definition rewrite_code_equivariant_statement : Prop :=
  ∀ f : expr -> expr,
    rewrite_equivariant f -> rewrite_equivariant (rewrite_code f).

(* ======================================================================== *)
(* FlambdaUnusedContsSpec.v                                                 *)
(* ======================================================================== *)

Definition cont_free_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (e : expr),
    cont_free_b (rename_continuation r k) (rename_expr r e) = cont_free_b k e.

Definition remove_unused_conts_equivariant_statement : Prop :=
  rewrite_equivariant remove_unused_conts.

(* ======================================================================== *)
(* FlambdaUnusedStaticsSpec.v                                               *)
(* ======================================================================== *)

(* The names removed are symbols and code ids, which no renaming moves:
   the argument that holds them is as it was. *)
Definition expr_avoids_equivariant_statement : Prop :=
  ∀ (r : renaming) (D : dropped) (e : expr),
    expr_avoids D (rename_expr r e) = expr_avoids D e.

Definition erase_expr_equivariant_statement : Prop :=
  ∀ D : dropped, rewrite_equivariant (erase_expr D).

(* Where the names given may not be removed from the one term they may
   not be from the other. *)
Definition drop_statics_equivariant_statement : Prop :=
  ∀ (r : renaming) (D : dropped) (e : expr),
    drop_statics D (rename_expr r e)
    = option_map (rename_expr r) (drop_statics D e).

Definition binds_only_kept_equivariant_statement : Prop :=
  ∀ (r : renaming) (D : dropped) (e : expr),
    binds_only_kept D (rename_expr r e) = binds_only_kept D e.

(* The condition on the environments under which removing static
   bindings is sound (the premise of
   FlambdaUnusedStaticsSpec.drop_statics_refines_statement), with the
   action of FlambdaEquivarianceSpec.v on what a state holds. *)
Definition envs_free_of_equivariant_statement : Prop :=
  ∀ (r : renaming) (D : dropped) (vars : env) (conts : cont_env)
    (statics : static_env),
    envs_free_of D (rename_env r vars) (rename_cont_env r conts)
      (rename_static_env r statics)
    = envs_free_of D vars conts statics.

(* ======================================================================== *)
(* FlambdaBlockLoadSpec.v: what is known of blocks                          *)
(* ======================================================================== *)

(* The pass carries what is known of the blocks of the term, which holds
   variables: those that are known to be blocks, and those that the
   fields of a block are known to hold. A renaming acts on both. The
   symbols that are known to be blocks, the tags and the numbers of
   fields are as they were. *)
Definition rename_known_block (r : renaming) (block : known_block)
    : known_block :=
  (fst block, map (option_map (rename_simple r)) (snd block)).

Definition rename_known_blocks (r : renaming) (known : known_blocks)
    : known_blocks :=
  Known_blocks
    (map
       (fun entry =>
          (rename_variable r (fst entry), rename_known_block r (snd entry)))
       (known_vars known))
    (map_values (rename_known_block r) (known_symbols known)).

(* What is known is renamed with the term. *)
Definition load_blocks_knowing_equivariant_statement : Prop :=
  ∀ (r : renaming) (known : known_blocks) (e : expr),
    load_blocks_knowing (rename_known_blocks r known) (rename_expr r e)
    = rename_expr r (load_blocks_knowing known e).

(* The pass as the validation runs it, with nothing known. *)
Definition load_known_blocks_equivariant_statement : Prop :=
  rewrite_equivariant load_known_blocks.

(* ======================================================================== *)
(* FlambdaUnboxSpec.v: what is known of wrapped numbers                     *)
(* ======================================================================== *)

(* Likewise: the variables that are known to be wrapped numbers are
   renamed, and what each wraps. What is known of a symbol is a
   constant. *)
Definition rename_known_numbers (r : renaming) (known : known_numbers)
    : known_numbers :=
  Known_numbers
    (map
       (fun entry =>
          (rename_variable r (fst entry),
           (fst (snd entry), rename_simple r (snd (snd entry)))))
       (known_wrapped_vars known))
    (known_boxed_symbols known).

Definition unbox_numbers_knowing_equivariant_statement : Prop :=
  ∀ (r : renaming) (known : known_numbers) (e : expr),
    unbox_numbers_knowing (rename_known_numbers r known) (rename_expr r e)
    = rename_expr r (unbox_numbers_knowing known e).

Definition unbox_known_numbers_equivariant_statement : Prop :=
  rewrite_equivariant unbox_known_numbers.

(* ======================================================================== *)
(* The types library: following aliases                                     *)
(* ======================================================================== *)

(* FlambdaAliasesSpec.follow_aliases carries a typing environment of the
   first model of the types (FlambdaTypesSpec.v): variables, each with
   what is known of it, which may hold variables. A renaming acts on
   both. *)
Definition rename_naive_type (r : renaming) (t : flambda_type)
    : flambda_type :=
  match t with
  | Unknown => Unknown
  | Bottom => Bottom
  | Equals s => Equals (rename_simple r s)
  | Closure_of code value_slots =>
    Closure_of code
      (map (fun slot => (fst slot, rename_simple r (snd slot))) value_slots)
  end.

Definition rename_naive_typing_env (r : renaming) (tenv : typing_env)
    : typing_env :=
  map
    (fun entry =>
       (rename_variable r (fst entry), rename_naive_type r (snd entry)))
    tenv.

Definition follow_aliases_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : typing_env) (e : expr),
    follow_aliases (rename_naive_typing_env r tenv) (rename_expr r e)
    = rename_expr r (follow_aliases tenv e).

(* The pass as the validation runs it, with nothing known. *)
Definition follow_aliases_unknowing_equivariant_statement : Prop :=
  rewrite_equivariant (follow_aliases []).

(* ======================================================================== *)
(* The checks of FlambdaWellFormedSpec.v                                    *)
(* ======================================================================== *)

(* The continuations that a term may apply and does not bind, as that
   file computes them: those of the renamed term are the images of
   those of the term, in the same order. *)
Definition well_formed_free_continuations_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    free_continuations (rename_expr r e)
    = map (rename_continuation r) (free_continuations e).

Definition raises_to_equivariant_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (e : expr),
    raises_to (rename_continuation r k) (rename_expr r e) = raises_to k e.

(* Where static bindings may be. The exception continuation of the unit
   is renamed with the term. *)
Definition handler_at_toplevel_equivariant_statement : Prop :=
  ∀ (r : renaming) (unit_exn k : continuation) (body : expr),
    handler_at_toplevel (rename_continuation r unit_exn)
      (rename_continuation r k) (rename_expr r body)
    = handler_at_toplevel unit_exn k body.

Definition statics_at_toplevel_equivariant_statement : Prop :=
  ∀ (r : renaming) (unit_exn : continuation) (toplevel : bool) (e : expr),
    statics_at_toplevel (rename_continuation r unit_exn) toplevel
      (rename_expr r e)
    = statics_at_toplevel unit_exn toplevel e.

(* The static names that a term binds are those of the renamed term,
   for a way of reading the names of a binding that does not look at
   its variables and continuations. *)
Definition static_names_equivariant_statement : Prop :=
  ∀ (r : renaming) (names_of : static_binding -> list positive) (e : expr),
    (∀ binding : static_binding,
      names_of (rename_static_binding r binding) = names_of binding) ->
    static_names names_of (rename_expr r e) = static_names names_of e.

(* So the code ids and the symbols that a term binds, which are the two
   ways used, are those of the renamed term. *)
Definition bound_static_names_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    static_names code_ids_of_binding (rename_expr r e)
    = static_names code_ids_of_binding e
    ∧ static_names symbols_of_binding (rename_expr r e)
      = static_names symbols_of_binding e.

Definition sets_well_formed_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    sets_well_formed (rename_expr r e) = sets_well_formed e.

Definition numbers_in_range_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    numbers_in_range (rename_expr r e) = numbers_in_range e.

(* The action on what a unit is given by where it is run: its two
   continuations are renamed. *)
Definition rename_unit_interface (r : renaming) (u : unit_interface)
    : unit_interface :=
  Unit_interface (rename_continuation r (unit_return u))
    (rename_continuation r (unit_exn u)).

(* A renamed unit is well-formed when the unit is, what it is given
   being renamed with it. Three of the conditions are those of
   FlambdaBindersSpec.v, whose statements are in FlambdaAlphaSpec.v. *)
Definition well_formed_unit_equivariant_statement : Prop :=
  ∀ (r : renaming) (u : unit_interface) (e : expr),
    well_formed_unit (rename_unit_interface r u) (rename_expr r e)
    = well_formed_unit u e.

(* The test of the states that the machine makes undefined to keep a
   static binding from being executed twice, with the action of
   FlambdaEquivarianceSpec.v on states. *)
Definition static_fault_equivariant_statement : Prop :=
  ∀ (r : renaming) (s : state),
    static_fault (rename_state r s) = static_fault s.

(* ======================================================================== *)
(* The normalisations of FlambdaValidateSpec.v                              *)
(* ======================================================================== *)

(* A rewrite that commutes with renaming does so however many times it
   is applied. *)
Definition iterate_equivariant_statement : Prop :=
  ∀ (rounds : nat) (f : expr -> expr),
    rewrite_equivariant f -> rewrite_equivariant (iterate rounds f).

(* The normalisation of the term before Simplify, and that of the term
   after: each is made of the rewrites above, of [fold_constants] and of
   [inline_calls]. *)
Definition normalise_before_equivariant_statement : Prop :=
  ∀ rounds : nat, rewrite_equivariant (normalise_before rounds).

Definition normalise_after_equivariant_statement : Prop :=
  ∀ rounds : nat, rewrite_equivariant (normalise_after rounds).

(* The removal of the static bindings of the names given, where nothing
   refers to them. *)
Definition without_statics_equivariant_statement : Prop :=
  ∀ D : dropped, rewrite_equivariant (without_statics D).

(* ======================================================================== *)
(* The check of kinds of FlambdaWellKindedSpec.v                            *)
(* ======================================================================== *)

(* The check of kinds is given the kinds of the variables in scope and
   the kinds of the parameters of the continuations in scope. The
   action on the two: each name is renamed and keeps what it is bound
   to. The kinds of the value slots are keyed by slots, which no
   renaming changes. *)
Definition rename_kind_env (r : renaming) (kinds : kind_env) : kind_env :=
  Keyed.map_keys (rename_variable r) kinds.

Definition rename_arity_env (r : renaming) (conts : arity_env) : arity_env :=
  Keyed.map_keys (rename_continuation r) conts.

(* The kinds of the parameters of a handler have no names in them. *)
Definition handler_kinds_equivariant_statement : Prop :=
  ∀ (r : renaming) (h : continuation_handler),
    handler_kinds (rename_handler r h) = handler_kinds h.

(* The kind that is found for a [Simple], for the arguments of a
   primitive or of a call, and for a defining expression. *)
Definition kind_of_simple_equivariant_statement : Prop :=
  ∀ (r : renaming) (kinds : kind_env) (s : simple),
    kind_of_simple (rename_kind_env r kinds) (rename_simple r s)
    = kind_of_simple kinds s.

Definition kinds_of_simples_equivariant_statement : Prop :=
  ∀ (r : renaming) (kinds : kind_env) (args : list simple),
    kinds_of_simples (rename_kind_env r kinds) (map (rename_simple r) args)
    = kinds_of_simples kinds args.

Definition kind_of_named_equivariant_statement : Prop :=
  ∀ (r : renaming) (slots : slot_kinds) (kinds : kind_env) (d : named),
    kind_of_named slots (rename_kind_env r kinds) (rename_named r d)
    = kind_of_named slots kinds d.

(* The kinds of parameters are bound for the renamed parameters as for
   the parameters. *)
Definition bind_param_kinds_equivariant_statement : Prop :=
  ∀ (r : renaming) (params : list variable) (params_kinds : list flambda_kind)
    (kinds : kind_env),
    bind_param_kinds (map (rename_variable r) params) params_kinds
      (rename_kind_env r kinds)
    = option_map (rename_kind_env r)
        (bind_param_kinds params params_kinds kinds).

(* The checks of a static constant, of an application of a
   continuation and of a call. *)
Definition static_const_well_kinded_equivariant_statement : Prop :=
  ∀ (r : renaming) (slots : slot_kinds) (kinds : kind_env)
    (const : static_const),
    static_const_well_kinded slots (rename_kind_env r kinds)
      (rename_static_const r const)
    = static_const_well_kinded slots kinds const.

Definition apply_cont_well_kinded_equivariant_statement : Prop :=
  ∀ (r : renaming) (kinds : kind_env) (conts : arity_env) (ac : apply_cont),
    apply_cont_well_kinded (rename_kind_env r kinds) (rename_arity_env r conts)
      (rename_apply_cont r ac)
    = apply_cont_well_kinded kinds conts ac.

Definition apply_well_kinded_equivariant_statement : Prop :=
  ∀ (r : renaming) (kinds : kind_env) (conts : arity_env) (ap : apply_expr),
    apply_well_kinded (rename_kind_env r kinds) (rename_arity_env r conts)
      (rename_apply r ap)
    = apply_well_kinded kinds conts ap.

(* The check of a term, what is in scope being renamed with the term;
   and the check of a unit, its two continuations being renamed with
   it. *)
Definition well_kinded_equivariant_statement : Prop :=
  ∀ (r : renaming) (slots : slot_kinds) (kinds : kind_env) (conts : arity_env)
    (e : expr),
    well_kinded slots (rename_kind_env r kinds) (rename_arity_env r conts)
      (rename_expr r e)
    = well_kinded slots kinds conts e.

Definition well_kinded_unit_equivariant_statement : Prop :=
  ∀ (r : renaming) (slots : slot_kinds) (unit_return unit_exn : continuation)
    (e : expr),
    well_kinded_unit slots (rename_continuation r unit_return)
      (rename_continuation r unit_exn) (rename_expr r e)
    = well_kinded_unit slots unit_return unit_exn e.

(* ======================================================================== *)
(* The check                                                                *)
(* ======================================================================== *)

(* The validation answers the same, and for the same reason, on two
   terms and on the two renamed by one renaming. The number of rounds
   and the names of the static bindings to remove are as they were. *)
Definition validate_unit_equivariant_statement : Prop :=
  ∀ (r : renaming) (rounds : nat) (unused : dropped) (before after : expr),
    validate_unit rounds unused (rename_expr r before) (rename_expr r after)
    = validate_unit rounds unused before after.
