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


(* A function on terms that carries a typing environment down a term
   and rewrites it from the types: the rewrites of primitives, put
   together.

   This file is to be reviewed: every definition, and the two
   statements. The function is meant to be extracted and run by the
   validation of middle_end/flambda2/tests/semantics/; nothing runs it
   yet, and it has not been extracted.

   [simplify_expr tenv e] goes down the term [e] with the typing
   environment [tenv], which it extends at each binder as Simplify
   does, and at each [Let] asks the provers about the types of the
   arguments, as the statements of FlambdaSimplifyPrimitivesSpec.v,
   FlambdaSimplifyProjectionsSpec.v, FlambdaSimplifyBoxingSpec.v and
   FlambdaSimplifyArithSpec.v say that Simplify may. Its answer refines
   the term under the environment
   ([simplify_expr_refines_under_statement]); from the environment that
   knows nothing, it refines the term outright
   ([simplify_by_types_refines_statement]), with no premise on the
   term.

   It is not Simplify, and is not a definition of what Simplify does.
   It is one function that is right, made of rewrites that Simplify
   makes, for the validator to bring a term before Simplify nearer to
   the term after. What it does:
   - At a [Let] of a [Simple]: the [Simple] is replaced by its
     canonical element, and the variable is made an alias of it
     ([bind_simple]).
   - At a [Let] of a primitive: the arguments are looked up
     ([simplify_simples]); if their types are not of the kinds that
     the primitive takes, the term is [Invalid]; otherwise
     [simplify_unary], [simplify_binary] or [simplify_variadic] asks
     the provers, and the [Let] becomes [Invalid], or a [Let] of a
     [Simple] (a constant, an argument, or what a prover answers),
     which is then treated as above; or the primitive stays, with its
     arguments canonical, and its variable is defined with the type
     that Simplify gives it ([Make_block], [Tag_immediate],
     [Box_number], the arithmetic of tagged immediates) or with the
     kind of its result and nothing more.
   - At a [Let] of a projection of a function slot: the same, with
     the prover of that projection. At a [Let] of a set of closures
     the variable is defined at the kind value. At a [Let] of the
     projection of a value slot it stops (the model's value slots
     have no kind).
   - Under a [Let_static] its symbols are defined, with no types.
     The body of a [Let_cont] is gone into.
   - The arguments of an [Apply_cont] are replaced by their canonical
     elements. A [Switch] whose scrutinee has a constant for
     canonical element becomes the [Apply_cont] of its arm.
   - Where it knows nothing (a [Simple] that the environment does not
     know, a variable that the environment has already, an environment
     that fails its test of well-formedness) it leaves the term from
     there down as it is ([Step_stop]).

   What Simplify does and this does not:
   - Nothing is done in the handler of a continuation or in the body
     of code, and nothing is known of a parameter. (The statements
     for going into them at the kinds of their parameters are to
     come.) So there are no joins of the environments at the uses of
     a continuation.
   - Nothing goes through the meet. Where Simplify meets the type of
     an argument with a shape ([Simplify_common.simplify_projection]:
     the unboxing primitives, the loads and projections that a prover
     does not answer) or adds an equation by a meet (the relational
     primitives [Is_int], [Get_tag], [Is_null]), the function asks
     the provers that the statements are about, in the environment
     before the [Let], and otherwise records the kind of the result
     only. No arm of a [Switch] is removed from the type of the
     scrutinee.
   - Symbols have no types; nothing is lifted; there are no common
     subexpressions, no inlining, no unboxing of parameters; a call
     is left as it is.
   - Of the unary primitives, [Is_int], [Is_null], [Get_tag], a
     [Block_load] that is not marked [Mutable], and the tagging,
     untagging, boxing and unboxing of a number are looked at; of the
     binary ones, the arithmetic and the comparison of tagged
     immediates. For every other primitive only the kind of its
     result is recorded. (Simplify makes a [Block_load] marked
     [Mutable] of a constant [Invalid],
     [simplify_mutable_block_load]; this leaves it.)
   - Of that arithmetic, of the tables for one side known
     ([op_lhs_unknown], [op_rhs_unknown]) the lines that make another
     primitive are left out. The comparison is computed on every
     pair of numbers, however many each argument may be: Simplify
     gives up above ten on a side, as [simplify_int_arith_tagged]
     does here, so this rewrites a comparison that Simplify leaves.
   - The tests that it makes before a rewrite (that the environment
     passes [typing_env_well_formed], that the variable of a [Let] is
     new to it, that the types of the environment are well formed
     where a prover of tagged immediates is asked) are not Simplify's:
     they are the premises of the statements, tested so that the
     function needs none. Where a test fails the function stops, so a
     failure costs rewrites and not correctness; that the tests pass
     on the environments that the function builds, for a term whose
     binders are all different, is not stated here.

   Seven terms on which the function is computed are at the end:
   what it answers is stated as an equation, with no premise.

   What is not here and is owed: that the function commutes with
   renaming ([simplify_expr] of the renamed environment and the
   renamed term is the renamed answer), as the other rewrites of the
   validator do (../../rocq/FlambdaValidatorEquivarianceSpec.v). It
   rests on the same law for the functions of the environment, for
   the provers and for the expansion of the head of a type, and is
   for a file of its own.

   Nothing is assumed: the two statements have no premise.

   The proofs are in FlambdaSimplifyPassProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaValueSpec FlambdaPrimitiveModel FlambdaPrimitiveSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeWellFormedSpec FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaTypingEnv
  FlambdaTypingEnvSpec FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvExamplesSpec FlambdaTypingEnvRefinementSpec
  FlambdaProvers FlambdaProversSpec FlambdaSimplifyPrimitivesSpec
  FlambdaSimplifyProjectionsSpec FlambdaSimplifyBoxingSpec
  FlambdaSimplifyArithSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* A [Simple] of the term                                                   *)
(* ======================================================================== *)

(* [Simplify_simple.simplify_simple] at the normal name mode: the type
   of a [Simple] that occurs in the term, and its canonical element.
   [None] where the environment does not know the [Simple] at that
   name mode, which is a fatal error of the compiler. *)
Definition simplify_simple (tenv : Typing_env.t) (s : simple)
    : option (flambda_type * simple) :=
  if Typing_env.mem_simple (Some Name_mode.normal) tenv s
  then
    match
      Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) s
    with
    | Some (Some answer) => Some answer
    | Some None | None => None
    end
  else None.

Fixpoint simplify_simples (tenv : Typing_env.t) (args : list simple)
    : option (list (flambda_type * simple)) :=
  match args with
  | [] => Some []
  | arg :: args =>
    let* answer := simplify_simple tenv arg in
    let* answers := simplify_simples tenv args in
    Some (answer :: answers)
  end.

(* ======================================================================== *)
(* What is decided of a defining expression                                 *)
(* ======================================================================== *)

Inductive outcome : Type :=
  (* The [Let] is [Invalid]. *)
  | Becomes_invalid
  (* The defining expression becomes this [Simple]. *)
  | Becomes_simple (s : simple)
  (* It stays, and its variable has this type. *)
  | Stays_with_type (ty : flambda_type)
  (* It stays, and its variable is of this kind. *)
  | Stays_with_kind (kind : flambda_kind)
  (* Nothing is known. *)
  | Not_known.

(* A boolean, as the naked immediate that a primitive answers. *)
Definition naked_bool_const (b : bool) : simple :=
  Const (Naked_immediate (if b then 1 else 0)).

(* The outcome on the answer of a meet shortcut. *)
Definition of_bool_shortcut (answer : option (Meet_shortcut.t bool))
    (otherwise : outcome) : outcome :=
  match answer with
  | Some (Meet_shortcut.Known_result b) => Becomes_simple (naked_bool_const b)
  | Some Meet_shortcut.Invalid => Becomes_invalid
  | Some Meet_shortcut.Need_meet | None => otherwise
  end.

Definition of_simple_shortcut (answer : option (Meet_shortcut.t simple))
    (otherwise : outcome) : outcome :=
  match answer with
  | Some (Meet_shortcut.Known_result s) => Becomes_simple s
  | Some Meet_shortcut.Invalid => Becomes_invalid
  | Some Meet_shortcut.Need_meet | None => otherwise
  end.

(* The type asked about and the types of the environment are well
   formed: [well_formed_input] of FlambdaProversSpec.v, as a test. *)
Definition well_formed_input_b (tenv : Typing_env.t) (ty : flambda_type)
    : bool :=
  types_well_formed_b tenv && type_well_formed ty.

(* A unary primitive, on its argument and the type of the argument. A
   primitive that has no line of its own stays, and its variable is of
   the kind of its result. *)
Definition simplify_unary (tenv : Typing_env.t) (p : unary_primitive)
    (arg : simple) (ty : flambda_type) : outcome :=
  let unknown := Stays_with_kind (result_kind_of_unary_primitive p) in
  match p with
  | Is_int false =>
    match Provers.prove_is_int tenv ty with
    | Some (Proof_of_property.Proved b) => Becomes_simple (naked_bool_const b)
    | Some Proof_of_property.Unknown | None => unknown
    end
  | Is_int true =>
    of_bool_shortcut (Provers.meet_is_int_variant_only tenv ty) unknown
  | Is_null => of_bool_shortcut (Provers.meet_is_null tenv ty) unknown
  | Get_tag =>
    match Provers.prove_is_int tenv ty with
    | Some (Proof_of_property.Proved true) => Becomes_invalid
    | Some (Proof_of_property.Proved false)
    | Some Proof_of_property.Unknown | None =>
      match Provers.prove_get_tag tenv ty with
      | Some (Proof_of_property.Proved [tag]) =>
        Becomes_simple (Const (Naked_immediate tag))
      | Some (Proof_of_property.Proved _)
      | Some Proof_of_property.Unknown | None =>
        unknown
      end
    end
  | Block_load _ (Immutable | Immutable_unique) field =>
    of_simple_shortcut
      (Provers.meet_block_field_simple tenv Name_mode.normal Value ty
         (Z.to_nat field))
      unknown
  | Tag_immediate => Stays_with_type (tag_immediate ty)
  | Box_number kind => Stays_with_type (box_number kind ty Alloc_mode.Heap)
  | Untag_immediate =>
    if types_well_formed_b tenv
    then
      of_simple_shortcut
        (Provers.meet_tagging_of_simple tenv Name_mode.normal
           (alias_type_of Value arg))
        unknown
    else unknown
  | Unbox_number kind =>
    of_simple_shortcut
      (Provers.meet_boxed_number_containing_simple kind tenv Name_mode.normal
         (alias_type_of Value arg))
      unknown
  | _ => unknown
  end.

(* ======================================================================== *)
(* The arithmetic of tagged immediates                                      *)
(* ======================================================================== *)

(* [Simplify_binary_primitive.binary_arith_outcome_for_one_side_only],
   without the outcomes that make another primitive: what is known of
   the result from one argument alone. [No_result] is the compiler's
   [Invalid]. *)
Inductive one_side_outcome : Type :=
  | Exactly (result : Z)
  | The_other_side
  | No_result
  | Cannot_simplify.

(* [Int_ops_for_binary_arith.symmetric_op_one_side_unknown]. Where the
   compiler answers the negation or the bitwise complement of the other
   side, this answers [Cannot_simplify]. *)
Definition symmetric_op_one_side_unknown (op : binary_int_arith_op)
    (this_side : Z) : one_side_outcome :=
  match op with
  | Add => if this_side =? 0 then The_other_side else Cannot_simplify
  | Mul =>
    if this_side =? 0 then Exactly 0
    else if this_side =? 1 then The_other_side
    else Cannot_simplify
  | And =>
    if this_side =? -1 then The_other_side
    else if this_side =? 0 then Exactly 0
    else Cannot_simplify
  | Or =>
    if this_side =? -1 then Exactly (-1)
    else if this_side =? 0 then The_other_side
    else Cannot_simplify
  | Xor => if this_side =? 0 then The_other_side else Cannot_simplify
  | Sub | Div _ | Mod _ => Cannot_simplify
  end.

(* [Int_ops_for_binary_arith.op_lhs_unknown]: the right argument is
   known. *)
Definition op_lhs_unknown (op : binary_int_arith_op) (rhs : Z)
    : one_side_outcome :=
  match op with
  | Add | Mul | And | Or | Xor => symmetric_op_one_side_unknown op rhs
  | Sub => if rhs =? 0 then The_other_side else Cannot_simplify
  | Div _ =>
    if rhs =? 0 then No_result
    else if rhs =? 1 then The_other_side
    else Cannot_simplify
  | Mod s =>
    if rhs =? 0 then No_result
    else if rhs =? 1 then Exactly 0
    else
      match s with
      | Signed => if rhs =? -1 then Exactly 0 else Cannot_simplify
      | Unsigned => Cannot_simplify
      end
  end.

(* [Int_ops_for_binary_arith.op_rhs_unknown]: the left argument is
   known. *)
Definition op_rhs_unknown (op : binary_int_arith_op) (lhs : Z)
    : one_side_outcome :=
  match op with
  | Add | Mul | And | Or | Xor => symmetric_op_one_side_unknown op lhs
  | Sub | Div _ | Mod _ => Cannot_simplify
  end.

(* The possible results of [Binary_arith_like.simplify]: a number, or
   the other argument. *)
Inductive possible_result : Type :=
  | Result_exactly (result : Z)
  | Result_other_side.

Definition possible_result_eqb (r r' : possible_result) : bool :=
  match r, r' with
  | Result_exactly i, Result_exactly i' => i =? i'
  | Result_other_side, Result_other_side => true
  | Result_exactly _, Result_other_side
  | Result_other_side, Result_exactly _ =>
    false
  end.

(* The local function [only_one_side_known] of
   [Binary_arith_like.simplify]: the possible results for the numbers
   that one argument may be, or [None] if nothing is known for one of
   them. *)
Fixpoint one_side_results (table : Z -> one_side_outcome) (nums : list Z)
    : option (list possible_result) :=
  match nums with
  | [] => Some []
  | i :: nums =>
    let* results := one_side_results table nums in
    match table i with
    | Exactly result => Some (Result_exactly result :: results)
    | The_other_side => Some (Result_other_side :: results)
    | No_result => Some results
    | Cannot_simplify => None
    end
  end.

(* The results of the operation on every pair of numbers that the two
   arguments may be, where both are known. *)
Definition both_sides_results (op : binary_int_arith_op) (nums1 nums2 : list Z)
    : list possible_result :=
  flat_map
    (fun i1 =>
       flat_map
         (fun i2 =>
            match eval_int_arith tagged_width op i1 i2 with
            | Some result => [Result_exactly result]
            | None => []
            end)
         nums2)
    nums1.

(* The numbers among possible results. *)
Fixpoint exact_results (results : list possible_result) : list Z :=
  match results with
  | [] => []
  | Result_exactly result :: results => result :: exact_results results
  | Result_other_side :: results => exact_results results
  end.

(* The local function [check_possible_results] of
   [Binary_arith_like.simplify]: no result is [Invalid]; one result is
   the constant or the other argument; several numbers are the type of
   those numbers; otherwise the type of the tagged immediates. *)
Definition check_possible_results (results : list possible_result)
    (other_side : simple) : outcome :=
  match results with
  | [] => Becomes_invalid
  | result :: rest =>
    if forallb (possible_result_eqb result) rest
    then
      match result with
      | Result_exactly i => Becomes_simple (Const (Tagged_immediate i))
      | Result_other_side => Becomes_simple other_side
      end
    else if forallb
              (fun r =>
                 match r with
                 | Result_exactly _ => true
                 | Result_other_side => false
                 end)
              results
    then Stays_with_type (these_tagged_immediates (exact_results results))
    else Stays_with_type any_tagged_immediate
  end.

(* [Binary_arith_like.max_num_possible_results]. *)
Definition max_num_possible_results : nat := 10.

(* [Binary_arith_like.simplify] at [Int_ops_for_binary_arith] of the
   tagged immediates. *)
Definition simplify_int_arith_tagged (tenv : Typing_env.t)
    (op : binary_int_arith_op) (arg1 : simple) (ty1 : flambda_type)
    (arg2 : simple) (ty2 : flambda_type) : outcome :=
  let unknown := Stays_with_type any_tagged_immediate in
  if well_formed_input_b tenv ty1 && well_formed_input_b tenv ty2
  then
    match
      Provers.meet_equals_tagged_immediates tenv ty1,
      Provers.meet_equals_tagged_immediates tenv ty2
    with
    | Some (Meet_shortcut.Known_result nums1),
      Some (Meet_shortcut.Known_result nums2) =>
      if (max_num_possible_results <? length nums1)%nat
         || (max_num_possible_results <? length nums2)%nat
      then unknown
      else check_possible_results (both_sides_results op nums1 nums2) arg1
    | Some (Meet_shortcut.Known_result nums1),
      (Some Meet_shortcut.Need_meet | None) =>
      match one_side_results (op_rhs_unknown op) nums1 with
      | Some results => check_possible_results results arg2
      | None => unknown
      end
    | (Some Meet_shortcut.Need_meet | None),
      Some (Meet_shortcut.Known_result nums2) =>
      match one_side_results (op_lhs_unknown op) nums2 with
      | Some results => check_possible_results results arg1
      | None => unknown
      end
    | Some Meet_shortcut.Invalid, _ | _, Some Meet_shortcut.Invalid =>
      Becomes_invalid
    | (Some Meet_shortcut.Need_meet | None),
      (Some Meet_shortcut.Need_meet | None) =>
      unknown
    end
  else unknown.

(* The same functor at [Int_ops_for_binary_comp] of the tagged
   immediates, where both arguments are known: the one result of the
   comparison on every pair, if there is one. *)
Definition simplify_int_comp_tagged (tenv : Typing_env.t)
    (behaviour : int_comparison_behaviour) (ty1 ty2 : flambda_type)
    : outcome :=
  let unknown := Stays_with_kind naked_immediate_kind in
  if well_formed_input_b tenv ty1 && well_formed_input_b tenv ty2
  then
    match
      Provers.meet_equals_tagged_immediates tenv ty1,
      Provers.meet_equals_tagged_immediates tenv ty2
    with
    | Some (Meet_shortcut.Known_result nums1),
      Some (Meet_shortcut.Known_result nums2) =>
      let results :=
        flat_map
          (fun i1 =>
             map (fun i2 => eval_int_comp tagged_width behaviour i1 i2) nums2)
          nums1
      in
      match results with
      | result :: rest =>
        if forallb (Z.eqb result) rest
        then Becomes_simple (Const (Naked_immediate result))
        else unknown
      | [] => unknown
      end
    | Some Meet_shortcut.Invalid, _ | _, Some Meet_shortcut.Invalid =>
      Becomes_invalid
    | _, _ => unknown
    end
  else unknown.

(* A binary primitive: the arithmetic and the comparison of tagged
   immediates; every other stays, at the kind of its result. *)
Definition simplify_binary (tenv : Typing_env.t) (p : binary_primitive)
    (arg1 : simple) (ty1 : flambda_type) (arg2 : simple) (ty2 : flambda_type)
    : outcome :=
  match p with
  | Int_arith Standard_tagged_immediate op =>
    simplify_int_arith_tagged tenv op arg1 ty1 arg2 ty2
  | Int_comp Standard_tagged_immediate behaviour =>
    simplify_int_comp_tagged tenv behaviour ty1 ty2
  | _ => Stays_with_kind (result_kind_of_binary_primitive p)
  end.

(* [Simplify_variadic_primitive.simplify_make_block]. *)
Definition simplify_variadic (p : variadic_primitive)
    (tys : list flambda_type) : outcome :=
  match p with
  | Make_block (Block_kind_values tag) =>
    if tag <? no_scan_tag
    then Stays_with_type (make_block_type tag tys)
    else Stays_with_kind Value
  end.

(* ======================================================================== *)
(* A defining expression                                                    *)
(* ======================================================================== *)

Definition simplify_named (tenv : Typing_env.t) (defining_expr : named)
    : outcome :=
  match defining_expr with
  | Simple s => Becomes_simple s
  | Prim p args =>
    match simplify_simples tenv args with
    | None => Not_known
    | Some answers =>
      let tys := map fst answers in
      if prim_args_well_kinded p (map FlambdaTypeGrammar.kind tys)
      then
        match p, args, tys with
        | Unary p, [arg], [ty] => simplify_unary tenv p arg ty
        | Binary p, [arg1; arg2], [ty1; ty2] =>
          simplify_binary tenv p arg1 ty1 arg2 ty2
        | Variadic p, _, _ => simplify_variadic p tys
        | _, _, _ => Not_known
        end
      else Becomes_invalid
    end
  | Set_of_closures _ _ | Closure_of_set _ _ _ => Stays_with_kind Value
  | Project_function_slot _ move_to closure =>
    match simplify_simple tenv closure with
    | Some (ty, _) =>
      of_simple_shortcut
        (Provers.meet_project_function_slot_simple tenv Name_mode.normal ty
           move_to)
        (Stays_with_kind Value)
    | None => Not_known
    end
  | Project_value_slot _ _ | Project_value_slot_from _ _ _ => Not_known
  end.

(* The arguments of a primitive replaced by their canonical elements. *)
Definition canonical_named (tenv : Typing_env.t) (defining_expr : named)
    : named :=
  match defining_expr with
  | Prim p args =>
    match simplify_simples tenv args with
    | Some answers => Prim p (map snd answers)
    | None => defining_expr
    end
  | Simple _ | Set_of_closures _ _ | Closure_of_set _ _ _
  | Project_value_slot _ _ | Project_value_slot_from _ _ _
  | Project_function_slot _ _ _ =>
    defining_expr
  end.

(* ======================================================================== *)
(* A [Let]                                                                  *)
(* ======================================================================== *)

(* What becomes of a [Let]: it is [Invalid]; or it has this defining
   expression, and its body is rewritten under this environment; or it
   is left as it is, with its body. *)
Inductive let_step : Type :=
  | Step_invalid
  | Step_let (defining_expr : named) (tenv : Typing_env.t)
  | Step_stop.

(* [simple_in_terms] and [simple_of_kind], as tests. *)
Definition simple_in_terms_b (tenv : Typing_env.t) (s : simple) : bool :=
  match s with
  | Var x => Typing_env.mem (Some Name_mode.normal) tenv (Name_var x)
  | Symbol _ | Const _ => true
  end.

Definition simple_of_kind_b (tenv : Typing_env.t) (s : simple)
    (kind : flambda_kind) : bool :=
  match s with
  | Const c => kind_eqb (FlambdaTypeGrammar.kind (type_for_const c)) kind
  | Var x => is_some (Typing_env.find tenv (Name_var x) (Some kind))
  | Symbol sym => is_some (Typing_env.find tenv (Name_symbol sym) (Some kind))
  end.

(* The variable of a [Let] is bound to a [Simple]: the [Simple] is
   replaced by its canonical element, and the variable is defined at
   its kind and made an alias of it. *)
Definition bind_simple (tenv : Typing_env.t) (x : variable) (s : simple)
    : let_step :=
  match simplify_simple tenv s with
  | Some (ty, canonical) =>
    let kind := FlambdaTypeGrammar.kind ty in
    if simple_in_terms_b tenv canonical && simple_of_kind_b tenv canonical kind
    then
      match
        Typing_env.add_alias
          (Typing_env.add_variable_definition tenv x kind Name_mode.normal)
          (Var x) canonical
      with
      | Some (Ok result) =>
        Step_let (Simple canonical) (Typing_env.add_alias_result_t result)
      | Some Unknown | Some Bottom | None => Step_stop
      end
    else Step_stop
  | None => Step_stop
  end.

(* Every variable of a type is in scope. *)
Definition type_in_scope_b (tenv : Typing_env.t) (ty : flambda_type) : bool :=
  forallb
    (fun y => Typing_env.mem (Some Name_mode.normal) tenv (Name_var y))
    (free_variables ty).

Definition simplify_let (tenv : Typing_env.t) (x : variable)
    (defining_expr : named) : let_step :=
  if typing_env_well_formed tenv
     && negb (Typing_env.mem None tenv (Name_var x))
  then
    match simplify_named tenv defining_expr with
    | Becomes_invalid => Step_invalid
    | Becomes_simple s => bind_simple tenv x s
    | Stays_with_type ty =>
      if type_in_scope_b tenv ty
      then
        Step_let (canonical_named tenv defining_expr)
          (Typing_env.replace_equation
             (Typing_env.add_variable_definition tenv x
                (FlambdaTypeGrammar.kind ty) Name_mode.normal)
             (Name_var x) ty)
      else Step_stop
    | Stays_with_kind kind =>
      Step_let (canonical_named tenv defining_expr)
        (Typing_env.add_variable_definition tenv x kind Name_mode.normal)
    | Not_known => Step_stop
    end
  else Step_stop.

(* ======================================================================== *)
(* The other expressions                                                    *)
(* ======================================================================== *)

(* The symbols that static bindings bind. *)
Fixpoint bound_symbols (bindings : list static_binding) : list symbol :=
  match bindings with
  | [] => []
  | Bind_symbol s _ :: bindings => s :: bound_symbols bindings
  | (Bind_code _ _ | Bind_deleted_code _) :: bindings =>
    bound_symbols bindings
  end.

Definition simplify_apply_cont (tenv : Typing_env.t) (ac : apply_cont)
    : apply_cont :=
  match simplify_simples tenv (ac_args ac) with
  | Some answers =>
    Apply_cont_expr (ac_continuation ac) (map snd answers)
      (ac_trap_action ac)
  | None => ac
  end.

(* A [Switch] whose scrutinee has a constant for canonical element is
   the [Apply_cont] of its arm. *)
(* CR mshinwell: no arm is removed here from the type of the scrutinee,
   as Simplify removes the arms whose discriminant the type excludes.
   The law of that rewrite (the workstream on the grammar of types has
   it) rests on the meet, and so holds of the states whose static
   environment is valid; the theorem of this function is of every
   state, which is what the validation asks of a rewrite of the term
   before. The choice made: the pruning stays out of this function,
   and goes into a second one with a theorem about valid static
   environments, which is to come. The other choice is to carry the
   premise into [simplify_by_types_refines_statement], and so into the
   theorem of the validation. *)
Definition simplify_switch (tenv : Typing_env.t) (scrutinee : simple)
    (arms : list (Z * apply_cont)) : expr :=
  match simplify_simple tenv scrutinee with
  | Some (_, Const (Naked_immediate i)) =>
    match find_arm i arms with
    | Some ac => Apply_cont (simplify_apply_cont tenv ac)
    | None => Switch scrutinee arms
    end
  | Some (_, (Const _ | Var _ | Symbol _)) | None => Switch scrutinee arms
  end.

(* ======================================================================== *)
(* A term                                                                   *)
(* ======================================================================== *)

Fixpoint simplify_expr (tenv : Typing_env.t) (e : expr) : expr :=
  match e with
  | Let x declared defining_expr body =>
    match simplify_let tenv x defining_expr with
    | Step_invalid => Invalid
    | Step_let defining_expr' tenv' =>
      Let x declared defining_expr' (simplify_expr tenv' body)
    | Step_stop => e
    end
  | Let_static bindings body =>
    Let_static bindings
      (simplify_expr
         (Typing_env.add_symbol_definitions tenv (bound_symbols bindings))
         body)
  | Let_cont_non_recursive k handler body =>
    Let_cont_non_recursive k handler (simplify_expr tenv body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (simplify_expr tenv body)
  | Apply _ => e
  | Apply_cont ac => Apply_cont (simplify_apply_cont tenv ac)
  | Switch scrutinee arms => simplify_switch tenv scrutinee arms
  | Invalid => Invalid
  end.

(* From the environment that knows nothing. *)
Definition simplify_by_types (e : expr) : expr :=
  simplify_expr Typing_env.create e.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

(* What the function answers refines the term, in every state that
   satisfies the environment. *)
Definition simplify_expr_refines_under_statement : Prop :=
  ∀ (tenv : Typing_env.t) (e : expr),
    expr_refines_under tenv e (simplify_expr tenv e).

(* From the environment that knows nothing, it refines the term. *)
Definition simplify_by_types_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (simplify_by_types e).

(* ======================================================================== *)
(* Examples                                                                 *)
(* ======================================================================== *)

(* What the function answers, computed. The variables are those of
   FlambdaTypingEnvExamplesSpec.v. A variable of which nothing is to be
   known is bound to [Opaque_identity] of a constant. *)

Definition example_tagged_add (arg1 arg2 : simple) : named :=
  Prim (Binary (Int_arith Standard_tagged_immediate Add)) [arg1; arg2].

Definition example_opaque (kind : flambda_kind) (c : const) : named :=
  Prim (Unary (Opaque_identity kind)) [Const c].

(* [let x = 3 in let y = x + 4 in apply_cont k y]. *)
Definition example_pass_add_constants_statement : Prop :=
  ∀ k : continuation,
    simplify_by_types
      (Let example_x Value (Simple (Const (Tagged_immediate 3)))
         (Let example_y Value
            (example_tagged_add (Var example_x) (Const (Tagged_immediate 4)))
            (Apply_cont (Apply_cont_expr k [Var example_y] None))))
    = Let example_x Value (Simple (Const (Tagged_immediate 3)))
        (Let example_y Value (Simple (Const (Tagged_immediate 7)))
           (Apply_cont
              (Apply_cont_expr k [Const (Tagged_immediate 7)] None))).

(* [let x = 5 in let i = Is_int x in switch i with 0 -> k0 | 1 -> k1]. *)
Definition example_pass_is_int_statement : Prop :=
  ∀ k0 k1 : continuation,
    simplify_by_types
      (Let example_x Value (Simple (Const (Tagged_immediate 5)))
         (Let example_i naked_immediate_kind
            (Prim (Unary (Is_int false)) [Var example_x])
            (Switch (Var example_i)
               [(0, Apply_cont_expr k0 [] None);
                (1, Apply_cont_expr k1 [] None)])))
    = Let example_x Value (Simple (Const (Tagged_immediate 5)))
        (Let example_i naked_immediate_kind
           (Simple (Const (Naked_immediate 1)))
           (Apply_cont (Apply_cont_expr k1 [] None))).

(* [let p = Make_block 0 [x; y] in let q = Block_load p 1 in
   apply_cont k q], for [x] and [y] unknown. *)
Definition example_pass_second_of_pair_statement : Prop :=
  ∀ k : continuation,
    let unknown (x : variable) (c : Z) (body : expr) : expr :=
      Let x Value (example_opaque Value (Tagged_immediate c)) body
    in
    let pair :=
      Prim (Variadic (Make_block (Block_kind_values 0)))
        [Var example_x; Var example_y]
    in
    simplify_by_types
      (unknown example_x 5
         (unknown example_y 6
            (Let example_p Value pair
               (Let example_q Value
                  (Prim
                     (Unary
                        (Block_load
                           (Block_access_values (Some 0) (Some 2) Any_value)
                           Immutable 1))
                     [Var example_p])
                  (Apply_cont (Apply_cont_expr k [Var example_q] None))))))
    = unknown example_x 5
        (unknown example_y 6
           (Let example_p Value pair
              (Let example_q Value (Simple (Var example_y))
                 (Apply_cont (Apply_cont_expr k [Var example_y] None))))).

(* [let y = x + 0 in apply_cont k y], for [x] unknown. *)
Definition example_pass_add_zero_statement : Prop :=
  ∀ k : continuation,
    let unknown (body : expr) : expr :=
      Let example_x Value (example_opaque Value (Tagged_immediate 5)) body
    in
    simplify_by_types
      (unknown
         (Let example_y Value
            (example_tagged_add (Var example_x) (Const (Tagged_immediate 0)))
            (Apply_cont (Apply_cont_expr k [Var example_y] None))))
    = unknown
        (Let example_y Value (Simple (Var example_x))
           (Apply_cont (Apply_cont_expr k [Var example_x] None))).

(* [let p = Box_number x in let q = Unbox_number p in apply_cont k q],
   for a naked float [x] unknown. *)
Definition example_pass_unbox_of_box_statement : Prop :=
  ∀ k : continuation,
    let float := Naked_number Kind_naked_float in
    let unknown (body : expr) : expr :=
      Let example_x float (example_opaque float (Naked_float 1)) body
    in
    let boxed := Prim (Unary (Box_number Boxable_naked_float)) [Var example_x]
    in
    simplify_by_types
      (unknown
         (Let example_p Value boxed
            (Let example_q float
               (Prim (Unary (Unbox_number Boxable_naked_float))
                  [Var example_p])
               (Apply_cont (Apply_cont_expr k [Var example_q] None)))))
    = unknown
        (Let example_p Value boxed
           (Let example_q float (Simple (Var example_x))
              (Apply_cont (Apply_cont_expr k [Var example_x] None)))).

(* [let p = Tag_immediate x in let q = Untag_immediate p in
   apply_cont k q], for a naked immediate [x] unknown. *)
Definition example_pass_untag_of_tag_statement : Prop :=
  ∀ k : continuation,
    let unknown (body : expr) : expr :=
      Let example_x naked_immediate_kind
        (example_opaque naked_immediate_kind (Naked_immediate 1)) body
    in
    let tagged := Prim (Unary Tag_immediate) [Var example_x] in
    simplify_by_types
      (unknown
         (Let example_p Value tagged
            (Let example_q naked_immediate_kind
               (Prim (Unary Untag_immediate) [Var example_p])
               (Apply_cont (Apply_cont_expr k [Var example_q] None)))))
    = unknown
        (Let example_p Value tagged
           (Let example_q naked_immediate_kind (Simple (Var example_x))
              (Apply_cont (Apply_cont_expr k [Var example_x] None)))).

(* Under a [Let_static] and in the body of a [Let_cont]: the symbol is
   known to the environment, and the handler is left as it is. *)
Definition example_pass_under_binders_statement : Prop :=
  ∀ k k' : continuation,
    let handler :=
      Handler [example_p] (make_handler_metadata [Value])
        (Let example_q Value
           (example_tagged_add (Var example_p) (Const (Tagged_immediate 0)))
           (Apply_cont (Apply_cont_expr k [Var example_q] None)))
    in
    let bindings :=
      [Bind_symbol example_s
         (Static_const_block 0 [Const (Tagged_immediate 1)])]
    in
    simplify_by_types
      (Let_static bindings
         (Let_cont_non_recursive k' handler
            (Let example_x Value (Simple (Symbol example_s))
               (Let example_y Value
                  (example_tagged_add (Const (Tagged_immediate 1))
                     (Const (Tagged_immediate 2)))
                  (Apply_cont
                     (Apply_cont_expr k' [Var example_y] None))))))
    = Let_static bindings
        (Let_cont_non_recursive k' handler
           (Let example_x Value (Simple (Symbol example_s))
              (Let example_y Value (Simple (Const (Tagged_immediate 3)))
                 (Apply_cont
                    (Apply_cont_expr k' [Const (Tagged_immediate 3)]
                       None))))).
