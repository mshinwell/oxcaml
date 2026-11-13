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

(* A [Switch] whose arms all apply one continuation, to an argument
   that is the element of a static table at the number of the arm: a
   normalisation that refines.

   This file is to be reviewed: [merge_tables] and what it is made of,
   and the statements. The rewrite is to be one of the normalisations
   of the term before Simplify that the validation of
   middle_end/flambda2/tests/semantics/ applies, once in a round for a
   whole term; it is not applied yet.

   What Simplify does. Where the arms of a [Switch] all apply the same
   continuation, and an argument is in every arm a constant or a
   symbol, is not the same in every arm and is not computed from the
   number of the arm in one of the ways of
   FlambdaMergeSwitchesSpec.v, Simplify may load it from a table
   ([Lookup_table_argument] of
   middle_end/flambda2/simplify/simplify_switch_expr.ml): the numbers
   of the arms are then [d], [d + 1], and so on with none missing,
   and there are three arms or more ([recognize_mergeable_argument],
   [enough_arms]). The table is a symbol bound to the immutable array
   of the arguments in the order of the arms, a constant that Simplify
   lifts, so that its binding is with the static bindings of the unit
   and not where the [Switch] was. The argument is then computed by
   ([rebuild_mergeable_argument])

     tagged = Tag_immediate scrutinee
     index  = tagged                                 where d = 0
            = Int_arith tagged_immediate Add (tagged, -d)   otherwise
     arg    = Array_load (kind, load kind, Immutable) (table, index)

   where the array kind and the load kind are those of immediates if
   every element is a tagged immediate constant, and those of values
   otherwise. A poison constant in an arm is some number in the table;
   that is not modelled, and such a [Switch] is not merged here.

   What is here. The term before Simplify has no table: the validation
   is to bind, at the head of the term before, the tables that the
   term after has (FlambdaValidateSpec.v; a guess that is checked,
   whose soundness is that of
   FlambdaUnusedHeadStaticsSpec.drop_head_statics read the other
   way). [merge_tables] then merges a [Switch] where a table that is
   in scope has the arguments of its arms. Nothing is guessed here:
   the tables are read off the term.

   The tables in scope ([known_tables], [tables_under_statics]). A
   table is a symbol that a [Let_static] binds to an immutable array
   of values whose elements are constants and symbols, with those
   elements. The rewrite carries the tables of the groups of static
   bindings that it has gone under; the body of code is rewritten
   with the tables of the groups that its binding is under and of its
   own group, as in FlambdaUnboxInScopeSpec.rewrite_code_in_scope.

   How a [Switch] is merged ([merge_switch_with_tables]). Only a
   [Switch] that FlambdaMergeSwitchesSpec.merge_switch leaves is
   merged: an argument that is computed from the number of the arm
   is not loaded from a table by Simplify either. The scrutinee must
   be a variable and there must be three arms or more. The
   application that the [Switch] may become applies the continuation
   of the first arm with no trap action; its arguments are those of
   the first arm where every arm has the same, and the variable of
   the scrutinee where one has not ([merged_across]; the elements of
   a table may be the same in the first two arms, so it is not
   enough to look at those as [merge_switch] does), and the variable
   must be among them. The first table in scope is taken that has as
   many elements as there are arms and of which every arm is that
   application with an element of the table in place of the variable
   ([arm_is_loaded]): the element at the index that the primitives
   compute of the number of the arm ([table_index],
   [table_element]), [d] being the number of the first arm, and that
   element must be one that the load kind takes ([element_taken]).
   The [Switch] becomes the application under the [Let]s of the
   three primitives, the second of which is not made where [d] is 0
   ([bind_table_load]). Each arm is tested on its own, so the
   refinement does not depend on the numbers of the arms being in
   order, on the length of the table or on how the merged arguments
   and the offset were found.

   What it costs where there is no table. The tables are looked at
   before [merge_switch] is computed, and with none in scope nothing
   is computed of a [Switch] but its merged arguments; what is
   computed once for a [Switch] or for a table (the offset, whether
   the elements are all immediates) is not computed again for each
   arm.

   The variable of the scrutinee is bound again by each [Let], as in
   [merge_switch], so the rewrite makes no name, and one table serves
   every argument that differs from arm to arm. A [Switch] two of
   whose arguments are loaded from two tables, or one of whose
   arguments is loaded from a table and another computed, is not
   merged here; Simplify merges it. It is for a way for each argument,
   with the parameters of the continuation as names
   (FlambdaMergeSwitchesSpec.merge_switch_by_arguments), which has no
   table yet.

   Where it goes ([merge_tables_knowing], [merge_tables_in_code]).
   The first goes down a term, into the handlers of continuations,
   recursive ones too, and not into code; the second applies it to
   the body of every piece of code, with the tables in scope there.
   [merge_tables] is the two, with no table known at the start.

   The result refines the term under all environments
   ([merge_tables_refines_statement]): a group of static bindings
   that has a value binds each of its symbols to its constant, a name
   that is bound already being undefined, and no binding is ever
   removed, so a table that is in scope is bound to its elements
   wherever the rewrite reads it, in the body of code too, which runs
   after its group is bound. The two parts are stated where the
   tables are bound ([tables_bound];
   [merge_tables_knowing_refines_statement],
   [merge_tables_in_code_refines_statement]). It is not an
   equivalence, as for [merge_switches]: the [Switch] is undefined
   where the scrutinee is the number of no arm.

   It commutes with renaming ([merge_tables_equivariant_statement]):
   it makes no name, a renaming moves no symbol, and the elements of
   a table have no variable. A term that binds no symbol to an
   immutable array is given back as it is
   ([merge_tables_without_tables_statement]).

   Two terms as checks of the definitions
   ([merge_tables_example_statement], and
   [merge_tables_equal_elements_example_statement], a table whose first
   two elements are the same).

   The proofs are in FlambdaMergeTablesProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel FlambdaMapSpec
  FlambdaPrimitiveModel FlambdaValueSpec FlambdaPrimitiveSpec
  FlambdaSemanticsSpec FlambdaNominalSpec FlambdaNormaliseSpec
  FlambdaMergeSwitchesSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The tables in scope                                                      *)
(* ======================================================================== *)

(* The symbols in scope that are bound to an immutable array of values
   whose elements are constants and symbols, each with its elements. *)
Definition known_tables : Type := list (symbol * list simple).

(* An element that has a value whatever the variables hold: a constant
   or a symbol. *)
Definition element_closed (element : simple) : bool :=
  is_some (eval_simple [] element).

Definition table_of_binding (binding : static_binding) : known_tables :=
  match binding with
  | Bind_symbol s (Static_const_immutable_value_array elements) =>
    if forallb element_closed elements then [(s, elements)] else []
  | Bind_symbol _ _ | Bind_code _ _ | Bind_deleted_code _ => []
  end.

(* The tables in scope under a group of static bindings: those of the
   group, then those that were in scope. *)
Definition tables_under_statics (tables : known_tables)
    (bindings : list static_binding) : known_tables :=
  flat_map table_of_binding bindings ++ tables.

(* ======================================================================== *)
(* The element of a table that an arm gives                                 *)
(* ======================================================================== *)

(* What is added to the tagged scrutinee where the first arm is not
   that of 0: the opposite of the number of the first arm, which
   wraps as that of Simplify does. It is computed once for a [Switch]
   and given to what follows as [offset]; nothing below depends on its
   being this number, as every arm is tested with it. *)
Definition table_offset (first : Z) : Z :=
  wrap (int_width Standard_tagged_immediate) (- first).

(* The index that the primitives compute of the number of an arm:
   [Tag_immediate] has a value on an immediate only, and the addition
   wraps, and has none where the constant is not a tagged immediate. *)
Definition table_index (first offset i : Z) : option Z :=
  let width := int_width Standard_tagged_immediate in
  if in_range (int_width Standard_naked_immediate) i
  then
    if first =? 0 then Some i
    else if in_range width offset
    then Some (wrap width (i + offset))
    else None
  else None.

(* The element that the load gives for the arm of number [i]: there is
   none where the index is not one of the table. *)
Definition table_element (first offset : Z) (elements : list simple) (i : Z)
    : option simple :=
  let* index := table_index first offset i in
  if (0 <=? index) && (index <? Z.of_nat (length elements))
  then nth_error elements (Z.to_nat index)
  else None.

(* The kinds of the load: those of immediates where every element is a
   tagged immediate, those of values otherwise. *)
Definition all_immediates (elements : list simple) : bool :=
  forallb
    (fun element =>
       match eval_simple [] element with
       | Some w => is_tagged_immediate w
       | None => false
       end)
    elements.

Definition table_array_kind (immediates : bool) : array_kind :=
  if immediates then Array_immediates else Array_values.

Definition table_load_kind (immediates : bool) : array_load_kind :=
  if immediates then Load_immediates else Load_values.

(* The load has a value on the element: it is one that the load kind
   takes. Where every element is a tagged immediate, which is where
   [immediates] is to be [true], each is taken by the load of
   immediates; otherwise the element must be of kind [Value]. *)
Definition element_taken (immediates : bool) (element : simple) : bool :=
  immediates
  || match eval_simple [] element with
     | Some w => array_element_ok Array_values w
     | None => false
     end.

(* ======================================================================== *)
(* The application that the arms are merged into                            *)
(* ======================================================================== *)

(* An element in place of a variable. *)
Definition element_for (v : variable) (element : simple) (s : simple)
    : simple :=
  match s with
  | Var x => if Pos.eqb x v then element else s
  | Symbol _ | Const _ => s
  end.

(* The arguments of the arms, merged: an argument that is the same in
   every arm stays, and one that is not becomes the variable. The
   elements of a table need not differ between the first two arms, so
   all the arms are gone through
   ([FlambdaMergeSwitchesSpec.merged_arguments], of each arm in turn
   with what the arms before it give). *)
Fixpoint merged_across (v : variable) (args : list simple)
    (arms : list (Z * apply_cont)) : list simple :=
  match arms with
  | [] => args
  | arm :: arms =>
    merged_across v (merged_arguments v args (ac_args (snd arm))) arms
  end.

(* An arm is the merged application with, in place of the variable, the
   element of the table that the load gives for its number. *)
Definition arm_is_loaded (v : variable) (merged : apply_cont)
    (first offset : Z) (elements : list simple) (immediates : bool)
    (arm : Z * apply_cont) : bool :=
  match table_element first offset elements (fst arm) with
  | Some element =>
    element_taken immediates element
    && (if apply_cont_eq_dec (snd arm)
             (Apply_cont_expr (ac_continuation merged)
                (map (element_for v element) (ac_args merged))
                (ac_trap_action merged))
        then true
        else false)
  | None => false
  end.

(* The variable bound again: to itself plus the offset, where the first
   arm is not that of 0, and to the element of the table at itself. The
   constant is the second argument of the addition, as Simplify has
   it. *)
Definition bind_table_offset (v : variable) (first offset : Z)
    (body : expr) : expr :=
  if first =? 0 then body
  else
    Let v Value
      (Prim (Binary (Int_arith Standard_tagged_immediate Add))
         [Var v; Const (Tagged_immediate offset)])
      body.

Definition bind_table_load (v : variable) (s : symbol) (first offset : Z)
    (immediates : bool) (body : expr) : expr :=
  bind_tagged v
    (bind_table_offset v first offset
       (Let v Value
          (Prim
             (Binary
                (Array_load (table_array_kind immediates)
                   (table_load_kind immediates) Immutable))
             [Symbol s; Var v])
          body)).

(* ======================================================================== *)
(* The rewrite                                                              *)
(* ======================================================================== *)

(* A table has the arguments of the arms: it has as many elements as
   there are arms, and every arm is the merged application with its
   element. *)
Definition table_has_arms (v : variable) (merged : apply_cont)
    (first offset : Z) (arms : list (Z * apply_cont))
    (table : symbol * list simple) : bool :=
  Nat.eqb (length (snd table)) (length arms)
  && (let immediates := all_immediates (snd table) in
      forallb (arm_is_loaded v merged first offset (snd table) immediates)
        arms).

Definition merge_switch_by_table (tables : known_tables) (scrutinee : simple)
    (arms : list (Z * apply_cont)) : option expr :=
  match scrutinee, arms with
  | Var v, (first, ac) :: ((_ :: _ :: _) as others) =>
    let merged :=
      Apply_cont_expr (ac_continuation ac)
        (merged_across v (ac_args ac) others) None
    in
    if var_in_simples v (ac_args merged)
    then
      let offset := table_offset first in
      match find (table_has_arms v merged first offset arms) tables with
      | Some (s, elements) =>
        Some
          (bind_table_load v s first offset (all_immediates elements)
             (Apply_cont merged))
      | None => None
      end
    else None
  | _, _ => None
  end.

(* A [Switch] merged where a table in scope has the arguments of its
   arms, if [merge_switch] leaves it: one that [merge_switch] merges is
   left to it. The tables are looked at first: where none is in scope,
   or none has the arms, [merge_switch] is not computed. *)
Definition merge_switch_with_tables (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) : expr :=
  match merge_switch_by_table tables scrutinee arms with
  | Some merged =>
    match merge_switch scrutinee arms with
    | Switch _ _ => merged
    | Let _ _ _ _ | Let_static _ _ | Let_cont_non_recursive _ _ _
    | Let_cont_recursive _ _ | Apply _ | Apply_cont _ | Invalid =>
      Switch scrutinee arms
    end
  | None => Switch scrutinee arms
  end.

(* Down a term, with the tables in scope: into the handlers of
   continuations, and not into code. *)
Fixpoint merge_tables_knowing (tables : known_tables) (e : expr) : expr :=
  match e with
  | Let x kind d body => Let x kind d (merge_tables_knowing tables body)
  | Let_static bindings body =>
    Let_static bindings
      (merge_tables_knowing (tables_under_statics tables bindings) body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (merge_tables_in_handler tables h)
      (merge_tables_knowing tables body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive
      (map (fun '(k, h) => (k, merge_tables_in_handler tables h)) handlers)
      (merge_tables_knowing tables body)
  | Switch scrutinee arms => merge_switch_with_tables tables scrutinee arms
  | Apply _ | Apply_cont _ | Invalid => e
  end
with merge_tables_in_handler (tables : known_tables)
    (h : continuation_handler) : continuation_handler :=
  match h with
  | Handler params metadata handler =>
    Handler params metadata (merge_tables_knowing tables handler)
  end.

(* [merge_tables_knowing] applied to the body of every piece of code,
   with the tables in scope where the code is bound: those of the groups
   of static bindings that the binding is under and those of its own
   group. As in FlambdaNormaliseSpec.rewrite_code, the body is left
   alone if the rewrite would change whether it binds something static;
   it never does. *)
Fixpoint merge_tables_in_code (tables : known_tables) (e : expr) : expr :=
  match e with
  | Let x kind d body => Let x kind d (merge_tables_in_code tables body)
  | Let_static bindings body =>
    let tables := tables_under_statics tables bindings in
    Let_static
      (map (rewrite_code_in_binding (merge_tables_knowing tables)) bindings)
      (merge_tables_in_code tables body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (merge_tables_in_code_in_handler tables h)
      (merge_tables_in_code tables body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive
      (map (fun '(k, h) => (k, merge_tables_in_code_in_handler tables h))
         handlers)
      (merge_tables_in_code tables body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end
with merge_tables_in_code_in_handler (tables : known_tables)
    (h : continuation_handler) : continuation_handler :=
  match h with
  | Handler params metadata handler =>
    Handler params metadata (merge_tables_in_code tables handler)
  end.

(* The whole rewrite: the term, then the bodies of its code, with no
   table known at the start. *)
Definition merge_tables (e : expr) : expr :=
  merge_tables_in_code [] (merge_tables_knowing [] e).

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

(* The tables are bound: the static environment binds the symbol of each
   to an immutable array of the values of its elements. *)
Definition tables_bound (tables : known_tables) (statics : static_env)
    : Prop :=
  ∀ (s : symbol) (elements : list simple),
    (s, elements) ∈ tables ->
    ∃ vs : list value,
      eval_simples [] elements = Some vs
      ∧ lookup s (static_values statics) = Some (Static_immutable_array vs).

Definition merge_tables_knowing_refines_statement : Prop :=
  ∀ (tables : known_tables) (e : expr) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap),
    tables_bound tables statics ->
    refines (State e vars conts statics hp)
      (State (merge_tables_knowing tables e) vars conts statics hp).

Definition merge_tables_in_code_refines_statement : Prop :=
  ∀ (tables : known_tables) (e : expr) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap),
    tables_bound tables statics ->
    refines (State e vars conts statics hp)
      (State (merge_tables_in_code tables e) vars conts statics hp).

Definition merge_tables_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (merge_tables e).

Definition merge_tables_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    merge_tables (rename_expr r e) = rename_expr r (merge_tables e).

(* A term that binds no symbol to an immutable array, in its code
   either. *)
Fixpoint binds_no_table (e : expr) : bool :=
  match e with
  | Let _ _ _ body => binds_no_table body
  | Let_static bindings body =>
    forallb binding_binds_no_table bindings && binds_no_table body
  | Let_cont_non_recursive _ h body =>
    handler_binds_no_table h && binds_no_table body
  | Let_cont_recursive handlers body =>
    forallb (fun '(_, h) => handler_binds_no_table h) handlers
    && binds_no_table body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => true
  end
with handler_binds_no_table (h : continuation_handler) : bool :=
  match h with
  | Handler _ _ handler => binds_no_table handler
  end
with binding_binds_no_table (binding : static_binding) : bool :=
  match binding with
  | Bind_code _ c => code_binds_no_table c
  | Bind_deleted_code _ => true
  | Bind_symbol _ (Static_const_immutable_value_array _) => false
  | Bind_symbol _ _ => true
  end
with code_binds_no_table (c : code) : bool :=
  match c with
  | Code _ _ _ _ _ body => binds_no_table body
  end.

Definition merge_tables_without_tables_statement : Prop :=
  ∀ e : expr, binds_no_table e = true -> merge_tables e = e.

(* ======================================================================== *)
(* Two terms                                                                *)
(* ======================================================================== *)

Definition scrutinee_of_example : variable := 1%positive.
Definition continuation_of_example : continuation := 1%positive.
Definition table_of_example : symbol := 1%positive.

Definition arm_of_example (n : Z) : apply_cont :=
  Apply_cont_expr continuation_of_example [Const (Tagged_immediate n)] None.

(* Four arms that give 1, 2, 3 and 0, under the binding of a table of
   those: the arms of a function from a variant of four constant
   constructors to the next one. *)
Definition switch_under_table : expr :=
  Let_static
    [Bind_symbol table_of_example
       (Static_const_immutable_value_array
          [Const (Tagged_immediate 1); Const (Tagged_immediate 2);
           Const (Tagged_immediate 3); Const (Tagged_immediate 0)])]
    (Switch (Var scrutinee_of_example)
       [(0, arm_of_example 1); (1, arm_of_example 2); (2, arm_of_example 3);
        (3, arm_of_example 0)]).

Definition load_under_table : expr :=
  Let_static
    [Bind_symbol table_of_example
       (Static_const_immutable_value_array
          [Const (Tagged_immediate 1); Const (Tagged_immediate 2);
           Const (Tagged_immediate 3); Const (Tagged_immediate 0)])]
    (Let scrutinee_of_example Value
       (Prim (Unary Tag_immediate) [Var scrutinee_of_example])
       (Let scrutinee_of_example Value
          (Prim (Binary (Array_load Array_immediates Load_immediates Immutable))
             [Symbol table_of_example; Var scrutinee_of_example])
          (Apply_cont
             (Apply_cont_expr continuation_of_example
                [Var scrutinee_of_example] None)))).

Definition merge_tables_example_statement : Prop :=
  merge_tables switch_under_table = load_under_table.

(* Three arms that give 0, 0 and 1: the first two arms are the same, and
   the argument is still loaded. *)
Definition switch_under_equal_elements : expr :=
  Let_static
    [Bind_symbol table_of_example
       (Static_const_immutable_value_array
          [Const (Tagged_immediate 0); Const (Tagged_immediate 0);
           Const (Tagged_immediate 1)])]
    (Switch (Var scrutinee_of_example)
       [(0, arm_of_example 0); (1, arm_of_example 0); (2, arm_of_example 1)]).

Definition load_under_equal_elements : expr :=
  Let_static
    [Bind_symbol table_of_example
       (Static_const_immutable_value_array
          [Const (Tagged_immediate 0); Const (Tagged_immediate 0);
           Const (Tagged_immediate 1)])]
    (Let scrutinee_of_example Value
       (Prim (Unary Tag_immediate) [Var scrutinee_of_example])
       (Let scrutinee_of_example Value
          (Prim (Binary (Array_load Array_immediates Load_immediates Immutable))
             [Symbol table_of_example; Var scrutinee_of_example])
          (Apply_cont
             (Apply_cont_expr continuation_of_example
                [Var scrutinee_of_example] None)))).

Definition merge_tables_equal_elements_example_statement : Prop :=
  merge_tables switch_under_equal_elements = load_under_equal_elements.
