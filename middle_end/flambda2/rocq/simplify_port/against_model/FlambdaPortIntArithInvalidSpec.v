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

(* Where the ported Simplify answers [Invalid] for an integer operation on
   tagged immediates of which THE RIGHT ARGUMENT IS KNOWN and the left is
   not, the model's operation has no result: the step of
   [Binary_arith_like.simplify] that looks each known number up in the
   table [op_lhs_unknown], against the model's semantics of the operation.

   This file is to be reviewed: the statement that ties the named copies
   to the port, the reading of an Invalid result, the form of the two new
   contracts, the statement of the step, and the statement of the port's
   [simplify] where it takes that step. The proofs are in
   FlambdaPortIntArithInvalidProofs.v. Read README.md of this folder and
   FlambdaPortIntArithTableSpec.v first: this file uses the map of the
   operation, the four contracts of the table and its theorem as they
   are, and exports that file.

   THE MODEL'S SIDE. simplify/FlambdaSimplifyArithSpec.v,
   [let_int_arith_tagged_statement]: its fourth conclusion says that the
   term is [Invalid] if [results (fun _ _ r => r = None)], that is, if
   the model's [eval_int_arith] has no result on every pair of numbers
   that the two arguments may be. The model's operation has no result in
   one place only: [Div] and [Mod] on a zero divisor. THAT IS A CHOICE OF
   THE MODEL, which the model marks for the human. The comment at
   [eval_int_arith] (semantics/FlambdaPrimitiveSpec.v) says, in these
   words:

     [Div] and [Mod] have no value on a zero divisor. It is what
     Simplify assumes, which makes such a division [Invalid]. It is
     right for a division of the source, which follows a test of the
     divisor. Nothing checks it for the unsafe divisions that the front
     end makes without a test (those of comprehensions), where the
     machine's division traps on x86-64. It would be wrong if a division
     by zero that is reached has to mean something, or if a pass may move
     a division to where its divisor has not been tested. Decision D14.

   The theorem of this file is the first that is proved from the port to
   that choice: it says where the PORTED code answers Invalid, and the
   answer agrees with the model because of that choice, and only under
   it.

   THE PORT'S SIDE. [Binary_arith_like.simplify] of
   Simplify_binary_primitive.v, at the tagged immediates
   ([Binary_int_arith_tagged_immediate]). It asks a prover about the type
   of each argument. Where the right argument has known numbers and the
   left is not known, it runs [only_one_side_known] with the table
   [op_lhs_unknown]: a fold over the known numbers that gathers a set of
   possible results, and then [check_possible_results] on that set, which
   answers Invalid if the set is empty. These two, and [result_unknown]
   and [result_invalid] that they call, are LOCAL to [simplify], in the
   compiler and in the port: Rocq has no name for them.
   Simplify_binary_primitive_named_locals.v has a copy of each, with a
   name, and [simplify_with_named_locals], the body of [simplify] with
   the copies in it.

   WHAT IS STATED.
   1. THE TIE ([simplify_is_its_named_locals_statement]): for all its
      nine arguments, the port's [simplify] at the tagged immediates IS
      [simplify_with_named_locals]. An equation of two computations, with
      no premise: Rocq proves it by computing. Without it a statement
      about a copy would say nothing of the port.
   2. THE STEP ([invalid_only_where_no_result_statement]): the copy of
      [only_one_side_known], with the copies of the three others given to
      it as [simplify_with_named_locals] gives them, the table
      [op_lhs_unknown] and the fold of the known numbers. If it returns a
      result that IS INVALID, then for every known number [c] and every
      number [j] in the range of the model's tagged immediates, the
      model's operation on [j] and the reading of [c] has no result.
   3. THE PORT'S [simplify]
      ([simplify_invalid_is_sound_statement]): the same
      conclusion of [simplify] itself, for the runs that take the step.
      It follows from 1 and 2.
   4. [fold_names_its_elements_statement] and
      [ported_create_is_not_invalid_statement]: two facts about the form
      of the two new contracts (below).

   WHY THE RIGHT ARGUMENT. With the LEFT argument known the table is
   [op_rhs_unknown], and no line of it answers [Invalid]: there the same
   statement would be true and would never apply. With the right
   argument known the table answers [Invalid] for [Div] and [Mod] on a
   known number that reads as 0. (This is a reading of the two tables;
   no statement here says it.)

   AN INVALID RESULT IS DEFINED, not chosen by the reader
   ([is_invalid_result]): decl/ has the type of the results as an
   inductive type and a record, and a result is Invalid if it is
   [Simplified] of a record whose field [simplified_named] is
   [Or_invalid.Invalid]. It is the test of the compiler's own
   [Simplify_primitive_result.is_invalid]. A [Rewritten] result is not
   Invalid.

   WHAT IS ASSUMED. The statement of the step is CONDITIONAL.

   The reader chooses, as in FlambdaPortIntArithTableSpec.v: the machine
   width, [value], [compatible]. And a set [nums] of numbers with a list
   [known] of numbers, of which the two premises below speak.

   CLAIMS ABOUT THE COMPILER THAT ARE NOT PROVED, each a named
   proposition and a premise:
   - the four contracts of the table ([zero_is_0], [one_is_1],
     [minus_one_is_m1], [equal_is_equality]);
   - [fold_visits .. nums known]: THE DECLARED FOLD of the sets of
     numbers ([Num.Set_.fold]), on [nums], visits the numbers of [known]:
     each once, in some order, and no other. It is a rule in the form of
     a loop invariant, for every step function and every invariant; it
     says nothing of this operation, of Invalid or of a result. Nothing
     is said of the state, of an exception or of a run out of fuel. THE
     READER CANNOT CHOOSE [known] SHORTER THAN THE SET: with the step that
     notes what it visits, the rule says that the fold returns the
     numbers of [known], in some order
     ([fold_names_its_elements_statement], proved);
   - [create_is_not_invalid]: the declared [SPR.create], if it returns,
     does not return an Invalid result. [simplify] calls the DECLARED
     function, a parameter of decl/. The port also has that function's
     text (Simplify_primitive_result.v, over a record of its own), and
     the ported text has the claim
     ([ported_create_is_not_invalid_statement], proved). That shows why
     the claim is believed. It does not prove it of the declared
     function.

   A CONDITION ON WHAT THE READER GIVES: every number of [known] is
   compatible.

   FIVE PREMISES THAT CHOOSE THE RUNS, in the statement of [simplify]
   only (THE CASE). [simplify] takes the step when the prover of the
   left argument answers that it does not know, and the prover of the
   right answers the set [nums]. Each of the five premises is about one
   call that [simplify] makes, on the arguments that it gives it: IF THE
   CALL RETURNS, IT RETURNS THE VALUE NAMED ([DA.denv], [DE.typing_env],
   the two provers, [DE.machine_width]). Each is said for every state
   and every fuel, because the statement does not know in which state
   [simplify] makes the call. So they are more than a choice of runs:
   they say that these five calls, on these arguments, answer nothing
   else from another state. They say nothing of what a prover's answer
   means.

   NOTHING IS ASSUMED of the other declared functions that the step
   calls ([T.bottom], [N.unknown], [DA.add_variable], [N.term],
   [Named.create_prim], [Named.create_simple], [List.filter_map],
   [List.length], [N.these], [T.alias_type_of], [DE.machine_width],
   [K.Standard_int.to_kind], [Simple.const_int_of_kind], the
   comparisons of the possible results, [SPR.create_invalid]). The
   conclusion is about a run that returns, and about Invalid only: it
   holds whatever these return.

   WHAT IS NOT SAID.
   - NOT THE MODEL'S PREMISE YET. The conclusion is over the list
     [known] and a reading [value] of the compiler's numbers. The
     model's [results] is over the numbers that the MODEL's prover
     answers for the model's type of the argument. The conclusion is a
     precursor of [results (fun _ _ r => r = None)]. STILL OPEN: that
     every number in range that the model's prover answers is the
     reading of a number of [known]; and how the compiler's terms, types
     and environments are read as the model's.
   - NOT WHICH RUNS OF [simplify] TAKE THIS STEP. That is decided by
     what the two provers answer for the arguments. The statement of
     [simplify] takes those answers as premises; no statement here
     reads a prover. [simplify] answers Invalid in two other places (a
     prover answers that the type has no number; both arguments have
     known numbers and no pair has a result): they are not covered.
   - ONE DIRECTION: if the result is Invalid, the model's operation has
     no result. Not that Simplify answers Invalid wherever it has none.
   - NOTHING of the answers with a term, of the type that the result
     variable gets, or of the state.
   - NOTHING OF A RUN THAT RAISES OR IS OUT OF FUEL, AND NOTHING OF THE
     STATE. The statements of the step and of [simplify] are of the form
     [if_returns]. The table's theorem has a stronger form
     ([pure_if_returns]): no run raises, and the state after a run that
     returns is the state before it. [if_returns] allows what that form
     forbids: a run that raises any exception, and any change of the
     state. The step cannot have the stronger form without a claim about
     every declared function that it calls: nothing here says that
     [DA.add_variable], [T.bottom] or [SPR.create] does not raise, or
     leaves the state as it was. And the port's own text ends some runs
     in an exception: a fatal error where the negation of the other side
     is asked of a float, and, in [simplify], a failed assertion where a
     set of known numbers is empty.
   - Nothing of the extracted OCaml, and nothing new about division by
     zero: see the model's comment above. *)

From Stdlib Require Import ZArith Bool List Permutation.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaPrimitiveModel
  FlambdaPrimitiveSpec.
From OxCamlFlambda2Types Require Import FlambdaSimplifyArithSpec.
From SimplifyPort Require Import Port_monad Kit_laws.
Require SimplifyPort.Simplify_binary_primitive
  SimplifyPort.Simplify_primitive_result.
From SimplifyPort.decl Require Bound_var Debuginfo Downwards_acc
  Downwards_env Flambda Flambda2_types Flambda_kind Flambda_primitive
  Number_adjuncts Or_invalid Simple Simplified_named
  Simplify_primitive_result Target_system.
From SimplifyPortAgainstModel Require Export FlambdaPortIntArithTableSpec.
From SimplifyPortAgainstModel Require Simplify_binary_primitive_named_locals.
Import ListNotations.

Local Open Scope Z_scope.

(* Short names for modules of decl/, those of the port's Simplify_import.
   [P], [Tagged] and [Num] are of FlambdaPortIntArithTableSpec.v. *)
Module DA := SimplifyPort.decl.Downwards_acc.
Module DE := SimplifyPort.decl.Downwards_env.
Module K := SimplifyPort.decl.Flambda_kind.
Module T := SimplifyPort.decl.Flambda2_types.
Module Named := SimplifyPort.decl.Flambda.Named.
Module SPR := SimplifyPort.decl.Simplify_primitive_result.

(* The named copies of the local functions of [simplify], at the tagged
   immediates (Simplify_binary_primitive_named_locals.v). [Locals.B] is
   the port's module [Binary_int_arith_tagged_immediate], and
   [Possible_result] its possible results. *)
Module Locals :=
  SimplifyPortAgainstModel.Simplify_binary_primitive_named_locals
    .Tagged_immediate.
Module Possible_result := Locals.B.Possible_result.

(* ======================================================================== *)
(* The tie: the port's [simplify] is the body with the named copies         *)
(* ======================================================================== *)

(* For all its nine arguments, [simplify] of the port's
   [Binary_int_arith_tagged_immediate] is [simplify_with_named_locals]:
   the two are one computation (the same end for every fuel and every
   state). No premise. *)
Definition simplify_is_its_named_locals_statement : Prop :=
  forall (op : P.binary_int_arith_op) (dacc : DA.t)
    (original_term : Named.t) (dbg : Debuginfo.t)
    (arg1 : Simple.t) (arg1_ty : T.t) (arg2 : Simple.t) (arg2_ty : T.t)
    (result_var : Bound_var.t),
    SimplifyPort.Simplify_binary_primitive.Binary_int_arith_tagged_immediate
      .simplify op dacc original_term dbg arg1 arg1_ty arg2 arg2_ty
      result_var
    = Locals.simplify_with_named_locals op dacc original_term dbg arg1
        arg1_ty arg2 arg2_ty result_var.

(* ======================================================================== *)
(* A computation that, if it returns, returns a value with a property       *)
(* ======================================================================== *)

(* For every fuel and every state: if [m] returns, [Q] holds of the
   value. Nothing is said of the state after it, of an exception, or of a
   run that is out of fuel. *)
Definition if_returns {A : Type} (m : M A) (Q : A -> Prop) : Prop :=
  forall (n : nat) (s : ocaml_state), wp m (fun a _ => Q a) any_exn n s.

(* ======================================================================== *)
(* An Invalid result                                                        *)
(* ======================================================================== *)

(* A result of the simplification of a primitive is Invalid if it is
   [Simplified] of a record whose [simplified_named] is
   [Or_invalid.Invalid]. *)
Definition is_invalid_result (r : SPR.t) : Prop :=
  match r with
  | SimplifyPort.decl.Simplified_named.Simplified simplified =>
    SPR.simplified_named simplified = SimplifyPort.decl.Or_invalid.Invalid
  | SimplifyPort.decl.Simplified_named.Rewritten _ => False
  end.

(* A CLAIM ABOUT THE COMPILER THAT IS NOT PROVED: the declared
   [SPR.create], if it returns, does not return an Invalid result. *)
Definition create_is_not_invalid : Prop :=
  forall (named : Named.t) (try_reify : bool) (dacc : DA.t),
    if_returns (SPR.create named try_reify dacc)
      (fun r => ~ is_invalid_result r).

(* The port's text of the same function (Simplify_primitive_result.v,
   over the record of that file) has the claim: if it returns, the result
   is [Simplified] of a record whose [simplified_named] is [Ok]. *)
Definition ported_create_is_not_invalid_statement : Prop :=
  forall (named : Named.t) (try_reify : bool) (dacc : DA.t),
    if_returns
      (SimplifyPort.Simplify_primitive_result.create named try_reify dacc)
      (fun r =>
         match r with
         | SimplifyPort.decl.Simplified_named.Simplified simplified =>
           exists simplified_named : SimplifyPort.decl.Simplified_named.t,
             SimplifyPort.Simplify_primitive_result.simplified_named
               simplified
             = SimplifyPort.decl.Or_invalid.Ok simplified_named
         | SimplifyPort.decl.Simplified_named.Rewritten _ => False
         end).

(* ======================================================================== *)
(* A fold that visits a list of elements                                    *)
(* ======================================================================== *)

(* Of any function of the type of the fold of a set: [fold A f nums
   init]. [fold_visits fold nums known] is a rule for the fold on the set
   [nums]. For every type of the accumulator, every step [f], every first
   accumulator and every invariant [inv] of the elements visited and the
   accumulator:
   - if [inv] holds of no element visited and the first accumulator,
   - and if each step keeps it: for an element [c] of [known], with
     [inv] of the elements visited before and the accumulator, [f c],
     if it returns, returns an accumulator that has [inv] with [c]
     visited too,
   then the fold, if it returns, returns an accumulator that has [inv]
   of a list of visited elements THAT IS [known] IN SOME ORDER (a
   permutation: each element of [known] once, and no other).
   The step is asked to keep the invariant from every state and for
   every fuel, and only if it returns; the rule says nothing of the
   state, of an exception or of a run that is out of fuel. *)
Section Any_fold.

  Variable elt set : Type.
  Variable fold : forall A : Type, (elt -> A -> M A) -> set -> A -> M A.

  Definition fold_visits (nums : set) (known : list elt) : Prop :=
    forall (A : Type) (f : elt -> A -> M A) (init : A)
      (inv : list elt -> A -> Prop),
      inv [] init ->
      (forall (c : elt) (seen : list elt) (a : A),
         In c known -> inv seen a -> if_returns (f c a) (inv (c :: seen))) ->
      if_returns (fold A f nums init)
        (fun a => exists seen : list elt, Permutation seen known /\ inv seen a).

End Any_fold.

(* THE RULE NAMES THE ELEMENTS. With the step that notes each element
   that it visits, a fold that has the rule for [known] returns, if it
   returns, the elements of [known] in some order. So a reader cannot
   give the rule a list that is not the elements that the fold visits. *)
Definition fold_names_its_elements_statement : Prop :=
  forall (elt set : Type)
    (fold : forall A : Type, (elt -> A -> M A) -> set -> A -> M A)
    (nums : set) (known : list elt),
    fold_visits elt set fold nums known ->
    if_returns (fold (list elt) (fun c visited => ret (c :: visited)) nums [])
      (fun visited => Permutation visited known).

(* ======================================================================== *)
(* The step: Invalid only where the model's operation has no result         *)
(* ======================================================================== *)

(* The copy of [only_one_side_known], as [simplify_with_named_locals]
   runs it where the right argument has the known numbers [nums] and the
   left argument [other_side] is not known: with the copies of
   [check_possible_results] and [result_unknown] for the same variables
   of [simplify], the numbers and the sets of the tagged immediates, the
   table [op_lhs_unknown] at the machine width, and the declared fold of
   those sets. If it returns an Invalid result, the model's operation has
   no result on any number in range and the reading of any known
   number. *)
Definition invalid_only_where_no_result_statement : Prop :=
  forall (machine_width : Target_system.Machine_width.t)
    (value : Num.t -> Z) (compatible : Num.t -> Prop),
    zero_is_0 machine_width value compatible ->
    one_is_1 machine_width value compatible ->
    minus_one_is_m1 machine_width value compatible ->
    equal_is_equality value compatible ->
    create_is_not_invalid ->
    forall (nums : Num.Set_.t) (known : list Num.t),
      fold_visits Num.t Num.Set_.t (@Num.Set_.fold) nums known ->
      (forall c : Num.t, In c known -> compatible c) ->
      forall (denv : DE.t) (dacc : DA.t) (original_term : Named.t)
        (dbg : Debuginfo.t) (op : P.binary_int_arith_op)
        (result_var : Bound_var.t) (kind : K.t) (other_side : Simple.t),
        if_returns
          (Locals.only_one_side_known denv
             (Locals.check_possible_results
                (Locals.result_invalid kind dacc result_var) original_term
                dbg kind denv op dacc result_var)
             (Locals.result_unknown denv op dacc result_var original_term)
             Num.t Num.Set_.t
             (fun i => Tagged.op_lhs_unknown machine_width op i)
             nums
             (@Num.Set_.fold (option Possible_result.Set_.t))
             other_side)
          (fun r =>
             is_invalid_result r ->
             forall c : Num.t,
               In c known ->
               forall j : Z,
                 in_range tagged_width j = true ->
                 eval_int_arith tagged_width (int_arith_op_of_port op) j
                   (value c)
                 = None).

(* ======================================================================== *)
(* The port's [simplify], where it takes the step                           *)
(* ======================================================================== *)

(* [simplify] of the port's [Binary_int_arith_tagged_immediate], for the
   runs in which the prover of the left argument does not know and the
   prover of the right argument answers the set [nums]. If it returns an
   Invalid result, the model's operation has no result on any number in
   range and the reading of any known number. The premises before THE
   CASE are those of the step. The five of THE CASE say what five calls
   of [simplify] return, if they return: its environment, the typing
   environment, the answers of the two provers, the machine width. *)
Definition simplify_invalid_is_sound_statement : Prop :=
  forall (machine_width : Target_system.Machine_width.t)
    (value : Num.t -> Z) (compatible : Num.t -> Prop),
    zero_is_0 machine_width value compatible ->
    one_is_1 machine_width value compatible ->
    minus_one_is_m1 machine_width value compatible ->
    equal_is_equality value compatible ->
    create_is_not_invalid ->
    forall (nums : Num.Set_.t) (known : list Num.t),
      fold_visits Num.t Num.Set_.t (@Num.Set_.fold) nums known ->
      (forall c : Num.t, In c known -> compatible c) ->
      forall (op : P.binary_int_arith_op) (dacc : DA.t)
        (original_term : Named.t) (dbg : Debuginfo.t)
        (arg1 : Simple.t) (arg1_ty : T.t) (arg2 : Simple.t) (arg2_ty : T.t)
        (result_var : Bound_var.t) (denv : DE.t) (tenv : T.Typing_env.t),
        (* THE CASE. *)
        if_returns (DA.denv dacc) (fun d => d = denv) ->
        if_returns (DE.typing_env denv) (fun e => e = tenv) ->
        if_returns (Tagged.prover_lhs tenv arg1_ty)
          (fun answer => answer = T.Need_meet) ->
        if_returns (Tagged.prover_rhs tenv arg2_ty)
          (fun answer => answer = T.Known_result nums) ->
        if_returns (DE.machine_width denv) (fun w => w = machine_width) ->
        if_returns
          (SimplifyPort.Simplify_binary_primitive
             .Binary_int_arith_tagged_immediate.simplify op dacc
             original_term dbg arg1 arg1_ty arg2 arg2_ty result_var)
          (fun r =>
             is_invalid_result r ->
             forall c : Num.t,
               In c known ->
               forall j : Z,
                 in_range tagged_width j = true ->
                 eval_int_arith tagged_width (int_arith_op_of_port op) j
                   (value c)
                 = None).
