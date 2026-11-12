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

(* A [Switch] whose arms all apply one continuation, to arguments that
   are computed from the number of the arm: a normalisation that
   refines.

   This file is to be reviewed: [merge_switches] and what it is made
   of, and the statements. The rewrite is one of the normalisations
   of the term before Simplify that the validation of
   middle_end/flambda2/tests/semantics/ applies: in a round of each of
   its two phases it follows [collapse_switches]
   (FlambdaValidateSpec.normalise_expr_before and
   [normalise_expr_params]). It is extracted and run with them.

   What Simplify does. Where the arms of a [Switch] all apply the same
   continuation with no trap action, and each argument is either the
   same in every arm or a constant that is computed from the number of
   the arm, Simplify makes of the [Switch] one application of the
   continuation, under the [Let]s of the primitives that compute those
   arguments from the scrutinee ([rebuild_switch] of
   middle_end/flambda2/simplify/simplify_switch_expr.ml). So
   [switch i with 0 -> k x 0t | 1 -> k x 1t], where [0t] is the tagged
   immediate, becomes [let tagged = Tag_immediate i in k x tagged].
   The model of that function, with what it is given and what is
   stated of it, is ../types/rocq/FlambdaSimplifySwitchMergeSpec.v.

   [merge_switches] does as much to the term before, for four of the
   ways in which Simplify computes an argument:
   - the argument is, in every arm, the number of the arm as a tagged
     immediate: the scrutinee is tagged ([By_tagging]);
   - the argument is the tagged immediate 1 in the arm of 0 and the
     tagged immediate 0 in the arm of 1, and there is no other arm:
     the scrutinee is tagged and the result negated
     ([By_tagging_and_negating]);
   - the argument is, in every arm, the number of the arm as a naked
     immediate: it is the scrutinee, and no primitive is needed
     ([As_it_is]). Simplify takes such an argument for one that is
     the same in every arm, the scrutinee, whatever the number of the
     arms ([recognize_mergeable_argument], where the function of the
     number of the arm is the identity on naked immediates);
   - the argument is, in every arm, an offset plus a slope times the
     number of the arm, as a tagged immediate or as a naked one, and
     there are three arms or more: the scrutinee, tagged first where
     the argument is tagged, is multiplied by the slope and added to
     the offset ([By_arithmetic]; [Affine_argument] and
     [enough_arms] of Simplify). The slope and the offset are those
     of the line through the first two arms.
   The arguments that differ from arm to arm are all computed in the
   same one of these four ways, and for the fourth with one slope and
   one offset. Simplify decides for each argument, so it also merges
   arms whose arguments are computed in several ways, which are not
   merged here. Nor are the arms an argument of which Simplify loads
   from a table of the constants of the arms
   ([Lookup_table_argument]).

   How it decides ([merge_switch]). The scrutinee must be a variable
   and there must be two arms or more. The application that the
   [Switch] may become applies the continuation of the first arm, with
   no trap action; its arguments are those of the first arm where the
   second arm has the same, and the variable of the scrutinee where it
   has not ([merged_arguments]), and the variable must be among them.
   Every arm must then be that application with a constant in place of
   the variable ([arm_is_merged]): the constant that is computed from
   the number of the arm ([constant_of_arm]). Where that is so of all
   the arms the [Switch] becomes the application: for the first way
   under a [Let] of the variable as itself tagged, for the second
   under a second [Let] of the variable as that negated
   ([bind_tagged], [bind_negated]), for the third with no [Let], and
   for the fourth under a [Let] for each primitive of the arithmetic
   ([bind_arithmetic]). Otherwise the [Switch] is left as it is.

   The arithmetic of the fourth way. The slope and the offset are
   computed from the first two arms as Simplify computes them
   ([arithmetic_of_arms], [line_through]); they say which primitives
   there are ([arithmetic_steps]): the multiplication by the slope,
   which is not made by 1, then the addition of the offset, which is
   not made of 0; for a negative slope the multiplication is by its
   opposite and the result is subtracted from the offset. The
   constant of an arm is then what those primitives compute of its
   number ([arithmetic_value]), which wraps as they do, and each arm,
   the first two with the others, is tested to have that constant. So
   the refinement does not depend on how the slope and the offset are
   found: a slope or an offset that is not that of the arms merges
   nothing.

   For the ways that apply a primitive, the variable of the scrutinee
   is bound again, once for each primitive, where Simplify binds a new
   variable each time; for the third nothing is bound. So the
   rewrite makes no name, and needs none to be given; the comparison
   of the validation is up to bound names (FlambdaCompareSpec.v).
   The arguments that are the same in every arm are not captured by
   the new [Let]s: in the merged arguments the variable of the
   scrutinee marks the arguments that are computed, so an argument
   that is that variable in the arms is read as one of them, and then
   no arm is the application with a constant in its place: nothing is
   merged. Nothing is assumed of the numbers of the arms: for the
   first way they are tested to be immediates
   ([in_range]), as [Tag_immediate] has no value on a number that is
   not one and the machine does not ask it of the scrutinee of a
   [Switch]; for the second they are 0 or 1; for the third nothing is
   asked of them, as the variable is passed with the value that the
   machine has for it; for the fourth they are tested to be
   immediates, as for the first, and the constants of the arithmetic
   too, as [Int_arith] has no value on a constant that is not an
   integer of its kind.

   [merge_switches] goes where
   FlambdaNormaliseSpec.collapse_switches goes: into the bodies of
   [Let]s, of static bindings and of the bindings of continuations,
   and into the handlers of non-recursive continuations. It leaves
   the handlers of recursive continuations and the bodies of code as
   they are: a round of the validation takes it there as it takes
   the other rewrites of the round, with
   FlambdaRecHandlersSpec.rewrite_rec_handlers and
   FlambdaNormaliseSpec.rewrite_code. A [Switch] whose arms are all the
   same is left to [collapse_switches].

   The result refines the term ([merge_switches_refines_statement]).
   Where the scrutinee is the number of an arm, the [Switch] goes to
   that arm, and the merged term binds the variable to the constant
   of that arm, in a step for each of its [Let]s (for the third way
   the variable holds it already), and applies the continuation to
   the same values. It is not an equivalence: the [Switch] is
   undefined where the scrutinee is not the number of an arm, and the
   merged term is not.

   The rewrite commutes with renaming
   ([merge_switches_equivariant_statement]): it makes no name, and it
   looks at names only to compare them, which a renaming, being
   injective, keeps true or false. That it keeps scope, which is that
   on a term whose code is closed the code of the result is closed and
   every variable or continuation that is free in the result is free
   in the term, is stated with the same of the other rewrites of a
   round (FlambdaKeepsScopeSpec.merge_switches_keeps_scope_statement).

   Four terms as checks of the definitions
   ([merge_switches_tagging_example_statement],
   [merge_switches_negating_example_statement],
   [merge_switches_as_it_is_example_statement],
   [merge_switches_arithmetic_example_statement]).

   The proofs are in FlambdaMergeSwitchesProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaPrimitiveModel FlambdaPrimitiveSpec FlambdaSemanticsSpec
  FlambdaNominalSpec FlambdaNormaliseSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The arguments that are computed from the number of the arm               *)
(* ======================================================================== *)

(* The immediates that an argument computed by arithmetic is: tagged
   or naked. *)
Inductive arithmetic_kind : Type :=
  | Arithmetic_tagged
  | Arithmetic_naked.

Definition standard_int_of_arithmetic_kind (kind : arithmetic_kind)
    : standard_int :=
  match kind with
  | Arithmetic_tagged => Standard_tagged_immediate
  | Arithmetic_naked => Standard_naked_immediate
  end.

(* How the arguments that differ from arm to arm are computed from the
   scrutinee. For [By_arithmetic] the argument is, at the kind given,
   the offset plus the slope times the number of the arm. *)
Inductive merge_by : Type :=
  | By_tagging
  | By_tagging_and_negating
  | As_it_is
  | By_arithmetic (kind : arithmetic_kind) (offset slope : Z).

(* One step of the arithmetic, on the integer that the variable holds:
   it is multiplied by a constant, or added to one, or subtracted from
   one. *)
Inductive arithmetic_step : Type :=
  | Multiply_by (c : Z)
  | Add_to (c : Z)
  | Subtract_from (c : Z).

(* The steps for an offset and a slope, integers of a width
   ([rebuild_affine_expr] of simplify_switch_expr.ml): the
   multiplication by the slope, or by its opposite where it is
   negative, which is not made where that is 1; then the addition of
   the offset, or for a negative slope the subtraction from the
   offset, which is not made where it is the addition of 0. The
   opposite wraps, as that of Simplify does: the opposite of the
   least integer is itself. *)
Definition arithmetic_steps (width offset slope : Z) : list arithmetic_step :=
  let negative := slope <? 0 in
  let factor := if negative then wrap width (- slope) else slope in
  (if factor =? 1 then [] else [Multiply_by factor])
  ++ (if negative then [Subtract_from offset]
      else if offset =? 0 then [] else [Add_to offset]).

(* What a step makes of an integer of a width, as the primitives of
   [Int_arith] do: the result wraps, and there is none where the
   constant is not an integer of the width. *)
Definition arithmetic_step_value (width : Z) (step : arithmetic_step) (a : Z)
    : option Z :=
  let result (c r : Z) : option Z :=
    if in_range width c then Some (wrap width r) else None
  in
  match step with
  | Multiply_by c => result c (a * c)
  | Add_to c => result c (c + a)
  | Subtract_from c => result c (c - a)
  end.

Fixpoint arithmetic_value (width : Z) (steps : list arithmetic_step) (a : Z)
    : option Z :=
  match steps with
  | [] => Some a
  | step :: steps =>
    let* a := arithmetic_step_value width step a in
    arithmetic_value width steps a
  end.

(* The constant that such an argument is in the arm of number [i]. For
   the ways that apply a primitive, only if the number is one that
   the primitives have a value on; the scrutinee as it is, is the
   number of the arm whatever that is. For [By_arithmetic] it is what
   the steps compute of the number, so the result wraps as the
   primitives do. *)
Definition constant_of_arm (how : merge_by) (i : Z) : option const :=
  match how with
  | By_tagging =>
    if in_range (int_width Standard_naked_immediate) i
    then Some (Tagged_immediate i)
    else None
  | By_tagging_and_negating =>
    if i =? 0 then Some (Tagged_immediate 1)
    else if i =? 1 then Some (Tagged_immediate 0)
    else None
  | As_it_is => Some (Naked_immediate i)
  | By_arithmetic kind offset slope =>
    let standard := standard_int_of_arithmetic_kind kind in
    let width := int_width standard in
    if in_range width i
    then
      option_map (const_of_int standard)
        (arithmetic_value width (arithmetic_steps width offset slope) i)
    else None
  end.

(* ======================================================================== *)
(* The application that the arms are merged into                            *)
(* ======================================================================== *)

(* The arguments of two arms, merged: an argument that is the same in
   the two stays, and one that is not becomes the variable. Where one
   arm has more arguments than the other, those are left out, and no
   arm will be found to be the application ([arm_is_merged]). *)
Fixpoint merged_arguments (v : variable) (args args' : list simple)
    : list simple :=
  match args, args' with
  | s :: args, s' :: args' =>
    (if simple_eq_dec s s' then s else Var v)
    :: merged_arguments v args args'
  | _, _ => []
  end.

(* A constant in place of a variable. *)
Definition constant_for (v : variable) (c : const) (s : simple) : simple :=
  match s with
  | Var x => if Pos.eqb x v then Const c else s
  | Symbol _ | Const _ => s
  end.

(* An arm is the merged application with the constant of its number in
   place of the variable. *)
Definition arm_is_merged (how : merge_by) (v : variable) (merged : apply_cont)
    (arm : Z * apply_cont) : bool :=
  match constant_of_arm how (fst arm) with
  | Some c =>
    if apply_cont_eq_dec (snd arm)
         (Apply_cont_expr (ac_continuation merged)
            (map (constant_for v c) (ac_args merged))
            (ac_trap_action merged))
    then true
    else false
  | None => false
  end.

(* The variable bound again: to itself tagged, where it holds a naked
   immediate, and to itself negated, where it holds a tagged boolean. *)
Definition bind_tagged (v : variable) (body : expr) : expr :=
  Let v Value (Prim (Unary Tag_immediate) [Var v]) body.

Definition bind_negated (v : variable) (body : expr) : expr :=
  Let v Value (Prim (Unary Boolean_not) [Var v]) body.

(* The variable bound again to what a step of the arithmetic makes of
   it, at a kind of integers. The constant is the second argument of
   the multiplication and the first of the two others, as Simplify has
   them. *)
Definition bind_arithmetic_step (standard : standard_int) (v : variable)
    (step : arithmetic_step) (body : expr) : expr :=
  let constant (c : Z) : simple := Const (const_of_int standard c) in
  let arith (op : binary_int_arith_op) (args : list simple) : named :=
    Prim (Binary (Int_arith standard op)) args
  in
  Let v (kind_of_standard_int standard)
    (match step with
     | Multiply_by c => arith Mul [Var v; constant c]
     | Add_to c => arith Add [constant c; Var v]
     | Subtract_from c => arith Sub [constant c; Var v]
     end)
    body.

Fixpoint bind_arithmetic_steps (standard : standard_int) (v : variable)
    (steps : list arithmetic_step) (body : expr) : expr :=
  match steps with
  | [] => body
  | step :: steps =>
    bind_arithmetic_step standard v step
      (bind_arithmetic_steps standard v steps body)
  end.

(* The variable bound to the offset plus the slope times itself, at a
   kind of immediates: it is tagged first where they are tagged. *)
Definition bind_arithmetic (kind : arithmetic_kind) (offset slope : Z)
    (v : variable) (body : expr) : expr :=
  let standard := standard_int_of_arithmetic_kind kind in
  let body :=
    bind_arithmetic_steps standard v
      (arithmetic_steps (int_width standard) offset slope) body
  in
  match kind with
  | Arithmetic_tagged => bind_tagged v body
  | Arithmetic_naked => body
  end.

(* The arithmetic that two arms determine
   ([recognize_affine_argument] of simplify_switch_expr.ml, which
   reads the arms in the order of their numbers and takes the first
   two): the constants that they have where their arguments first
   differ, which are to be immediates of one kind, and the slope and
   the offset of the line through them. There is none where the slope
   is not a whole number. The differences, the slope and the offset
   are integers of the width of the immediates and wrap, as those of
   Simplify do; the quotient and the remainder are those that
   truncate towards zero. Whether the arms are on the line is not
   decided here but by [arm_is_merged], for each of them, the first
   two as the others. *)
Fixpoint first_difference (args args' : list simple)
    : option (const * const) :=
  match args, args' with
  | s :: args, s' :: args' =>
    if simple_eq_dec s s'
    then first_difference args args'
    else
      match s, s' with
      | Const c, Const c' => Some (c, c')
      | _, _ => None
      end
  | _, _ => None
  end.

Definition line_through (width i a i' a' : Z) : option (Z * Z) :=
  let run := wrap width (i' - i) in
  let rise := wrap width (a' - a) in
  if (run =? 0) || negb (Z.rem rise run =? 0)
  then None
  else
    let slope := wrap width (Z.quot rise run) in
    Some (wrap width (a - slope * i), slope).

Definition arithmetic_of_arms (i i' : Z) (args args' : list simple)
    : option (arithmetic_kind * Z * Z) :=
  let line (kind : arithmetic_kind) (a a' : Z)
      : option (arithmetic_kind * Z * Z) :=
    let width := int_width (standard_int_of_arithmetic_kind kind) in
    let* '(offset, slope) := line_through width i a i' a' in
    Some (kind, offset, slope)
  in
  let* '(c, c') := first_difference args args' in
  match c, c' with
  | Tagged_immediate a, Tagged_immediate a' => line Arithmetic_tagged a a'
  | Naked_immediate a, Naked_immediate a' => line Arithmetic_naked a a'
  | _, _ => None
  end.

(* ======================================================================== *)
(* The rewrite                                                              *)
(* ======================================================================== *)

Definition merge_switch (scrutinee : simple) (arms : list (Z * apply_cont))
    : expr :=
  match scrutinee, arms with
  | Var v, (i, ac) :: (i', ac') :: _ =>
    let merged :=
      Apply_cont_expr (ac_continuation ac)
        (merged_arguments v (ac_args ac) (ac_args ac')) None
    in
    if var_in_simples v (ac_args merged)
    then
      if forallb (arm_is_merged By_tagging v merged) arms
      then bind_tagged v (Apply_cont merged)
      else if forallb (arm_is_merged By_tagging_and_negating v merged) arms
      then bind_tagged v (bind_negated v (Apply_cont merged))
      else if forallb (arm_is_merged As_it_is v merged) arms
      then Apply_cont merged
      else
        match arithmetic_of_arms i i' (ac_args ac) (ac_args ac') with
        | Some (kind, offset, slope) =>
          if (3 <=? length arms)%nat
             && forallb
                  (arm_is_merged (By_arithmetic kind offset slope) v merged)
                  arms
          then bind_arithmetic kind offset slope v (Apply_cont merged)
          else Switch scrutinee arms
        | None => Switch scrutinee arms
        end
    else Switch scrutinee arms
  | _, _ => Switch scrutinee arms
  end.

Fixpoint merge_switches (e : expr) : expr :=
  match e with
  | Let x kind d body => Let x kind d (merge_switches body)
  | Let_static bindings body => Let_static bindings (merge_switches body)
  | Let_cont_non_recursive k (Handler params metadata handler) body =>
    Let_cont_non_recursive k
      (Handler params metadata (merge_switches handler))
      (merge_switches body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (merge_switches body)
  | Switch scrutinee arms => merge_switch scrutinee arms
  | Apply _ | Apply_cont _ | Invalid => e
  end.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

Definition merge_switches_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (merge_switches e).

Definition merge_switches_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    merge_switches (rename_expr r e) = rename_expr r (merge_switches e).

(* ======================================================================== *)
(* Four terms                                                               *)
(* ======================================================================== *)

Module Merge_examples.

Definition i : variable := 1%positive.
Definition x : variable := 2%positive.
Definition k : continuation := 1%positive.

Definition apply_k (s : simple) : apply_cont :=
  Apply_cont_expr k [Var x; s] None.

Definition constant (n : Z) : simple := Const (Tagged_immediate n).

(* [switch i with 0 -> k x 0t | 1 -> k x 1t | 2 -> k x 2t] and
   [let i = Tag_immediate i in k x i]. *)
Definition switch_tagging : expr :=
  Switch (Var i)
    [(0, apply_k (constant 0)); (1, apply_k (constant 1));
     (2, apply_k (constant 2))].

Definition merged_tagging : expr :=
  bind_tagged i (Apply_cont (apply_k (Var i))).

(* [switch i with 0 -> k x 1t | 1 -> k x 0t] and
   [let i = Tag_immediate i in let i = Boolean_not i in k x i]. *)
Definition switch_negating : expr :=
  Switch (Var i) [(0, apply_k (constant 1)); (1, apply_k (constant 0))].

Definition merged_negating : expr :=
  bind_tagged i (bind_negated i (Apply_cont (apply_k (Var i)))).

(* [switch i with 0 -> k x #0 | 1 -> k x #1], where [#0] is the naked
   immediate, and [k x i]. *)
Definition switch_as_it_is : expr :=
  Switch (Var i)
    [(0, apply_k (Const (Naked_immediate 0)));
     (1, apply_k (Const (Naked_immediate 1)))].

Definition merged_as_it_is : expr := Apply_cont (apply_k (Var i)).

(* [switch i with 0 -> k x 5t | 1 -> k x 7t | 2 -> k x 9t] and
   [let i = Tag_immediate i in let i = i * 2t in let i = 5t + i in
   k x i]. *)
Definition switch_arithmetic : expr :=
  Switch (Var i)
    [(0, apply_k (constant 5)); (1, apply_k (constant 7));
     (2, apply_k (constant 9))].

Definition merged_arithmetic : expr :=
  bind_tagged i
    (Let i Value
       (Prim (Binary (Int_arith Standard_tagged_immediate Mul))
          [Var i; constant 2])
       (Let i Value
          (Prim (Binary (Int_arith Standard_tagged_immediate Add))
             [constant 5; Var i])
          (Apply_cont (apply_k (Var i))))).

End Merge_examples.

Definition merge_switches_tagging_example_statement : Prop :=
  merge_switches Merge_examples.switch_tagging
  = Merge_examples.merged_tagging.

Definition merge_switches_negating_example_statement : Prop :=
  merge_switches Merge_examples.switch_negating
  = Merge_examples.merged_negating.

Definition merge_switches_as_it_is_example_statement : Prop :=
  merge_switches Merge_examples.switch_as_it_is
  = Merge_examples.merged_as_it_is.

Definition merge_switches_arithmetic_example_statement : Prop :=
  merge_switches Merge_examples.switch_arithmetic
  = Merge_examples.merged_arithmetic.
