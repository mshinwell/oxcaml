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


(* A read of a parameter of a loop made a parameter: a normalisation
   that refines.

   This file is to be reviewed: [unbox_loops_knowing] and what it is
   made of, and the statement. Nothing applies the pass yet.

   Simplify unboxes the parameters of a recursive continuation as it
   does those of a join (simplify/unboxing/), with two differences
   ([Simplify_let_cont_expr.simplify_single_recursive_handler]). The
   decision is taken before any application is seen: the handler is
   gone into with parameters of unknown type
   ([DE.add_parameters_with_unknown_types]), so a parameter is unboxed
   to what its kind says it holds
   ([Optimistic_unboxing_decision.make_optimistic_decision]), and the
   decision is not filtered by what the applications give nor by
   whether it pays ([Unbox_continuation_params.make_decisions] at
   [Recursive]). Each application is then given the new arguments:
   something in scope where the type of its argument shows one
   ([Already_in_scope] of [Unboxing_epa]), and otherwise a read that
   is bound just before it ([New_let_binding]). So for

     let acc = ref 0L in
     for i = 1 to n do acc := Int64.add !acc (Int64.of_int i) done

   where the front end makes the reference a parameter of the loop,
   which holds a boxed number, the loop after Simplify has the number
   for a parameter: the entry gives it the constant, and each turn
   the sum, which the term before boxes on the way round.

   The model has no subkinds, so the pass goes by what the term
   shows, as FlambdaUnboxVariantsSpec.unbox_variant_params does for a
   join. For a recursive continuation that is alone in its [Let_cont]
   ([unbox_loop_reads]), a [Let] of the handler that reads a parameter
   becomes a parameter ([unbox_loop_read]) where:

   - the [Let] is under [Let]s only ([on_spine]), so that every turn
     of the loop comes to it, or goes wrong before it, whatever the
     values;
   - the handler may take the variable of the [Let] as a parameter,
     and that variable is not free in the handler, as for a join;
   - every application of the continuation in the body of the
     [Let_cont] can be given what the read gives of its argument, by
     FlambdaUnboxParamsSpec.extend_args: a constant, or what a [Let]
     or a [Let_static] in scope shows of the box;
   - every application in what is left of the handler can be given
     the same, where one thing more is known: that the new parameter
     is the read of the parameter read. So a turn that passes the box
     on as it was given passes the new parameter on.

   The reads of one parameter are taken in the order of
   FlambdaUnboxVariantsSpec.next_read, and the parameters in the
   order in which they stand ([unbox_loop_params]): the new
   parameters come after those that the continuation had, those read
   from an earlier parameter first. The parameter read stays; where
   nothing else uses it, it is an unused parameter of the loop, which
   FlambdaDeadParamsSpec.drop_dead_params removes.

   Not done, and the term is left as it is: an application that would
   need a read bound just before it (Simplify's [New_let_binding]),
   as where the loop is entered with a box that the term does not
   show, a parameter of the function for one; a read that is under a
   test in the handler; several recursive continuations in one
   [Let_cont].

   The result refines the term, given what is known of the symbols in
   scope ([unbox_loops_knowing_symbols_refines_statement], in the form
   in which the validation takes a rewrite into code and into loops,
   FlambdaUnboxInScopeSpec.refines_where_known). Why it holds, in two
   steps. The handler with the read taken to its head refines the
   handler: under [Let]s only, the run comes to the read or goes
   wrong before it, and where the primitive has no value the handler
   goes wrong either way. Then the loop whose handler begins with the
   read and the loop with the read made a parameter are run together:
   an application gives the new parameter what the primitive has on
   the argument, so the first run, one step later, is where the
   second is, with the same variables; the applications in the
   handler are of the continuation itself, and the two go on in step.
   It is a refinement and not an equivalence: where the read has no
   value of its kind the term goes wrong, and the result, which no
   longer makes the read, may run on.

   That the pass commutes with renaming is stated in
   FlambdaUnboxVariantsRenameSpec.v, and that it keeps scope in
   FlambdaUnboxInScopeRenameSpec.v. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel FlambdaMapSpec
  FlambdaPrimitiveModel FlambdaSemanticsSpec FlambdaNormaliseSpec
  FlambdaBlockLoadSpec FlambdaUnboxSpec FlambdaUnboxParamsSpec
  FlambdaUnboxVariantsSpec FlambdaUnboxInScopeSpec.
Import ListNotations.

(* Whether a [Let] of the variable is under the bodies of [Let]s
   only, so that every run of the expression comes to it or goes
   wrong before it. *)
Fixpoint on_spine (x : variable) (e : expr) : bool :=
  match e with
  | Let y _ _ body => Pos.eqb x y || on_spine x body
  | Let_static _ _ | Let_cont_non_recursive _ _ _ | Let_cont_recursive _ _
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid =>
    false
  end.

(* The recursive [Let_cont] of [k] alone with the read made a
   parameter: the applications in the body are given what the term
   shows that the read gives, and those in what is left of the
   handler the same, knowing there that the new parameter is the read
   of the parameter read. *)
Definition unbox_loop_read (known : facts) (k : continuation)
    (params : list variable) (metadata : handler_metadata)
    (handler body : expr) (r : read)
    : option (list variable * handler_metadata * expr * expr) :=
  let f := read_variable r in
  let p := read_primitive r in
  let i := read_position r in
  let* x := nth_error params i in
  if may_take params metadata f
     && negb (var_free_b f handler)
     && on_spine f handler
  then
    let* body := extend_applications known k i p body in
    let* without :=
      extend_applications
        (facts_under_let (facts_under_params known params) f
           (Prim (Unary p) [Var x]))
        k i p (read_without r)
    in
    Some (params ++ [f], with_one_more metadata (read_kind r), without, body)
  else None.

(* A loop that is being unboxed: its parameters, its metadata, its
   handler, and the body of its [Let_cont]. *)
Definition loop_state : Type :=
  (list variable * handler_metadata * expr * expr)%type.

Definition loop_of (k : continuation) (state : loop_state) : expr :=
  let '(params, metadata, handler, body) := state in
  Let_cont_recursive [(k, Handler params metadata handler)] body.

(* The reads of the parameter at position [i] made parameters one
   after the other, in the order of [next_read], as long as each can
   be. *)
Fixpoint unbox_loop_param (fuel : nat) (known : facts) (k : continuation)
    (i : nat) (state : loop_state) : loop_state :=
  match fuel with
  | 0 => state
  | S fuel =>
    let '(params, metadata, handler, body) := state in
    match
      (let* param := nth_error params i in
       let* r := next_read [param] handler in
       unbox_loop_read known k params metadata handler body
         (Read (read_variable r) (read_kind r) (read_primitive r) i
            (read_without r)))
    with
    | Some state => unbox_loop_param fuel known k i state
    | None => state
    end
  end.

(* The same for each of the positions given, in turn. *)
Fixpoint unbox_loop_params (fuel : nat) (known : facts) (k : continuation)
    (positions : list nat) (state : loop_state) : loop_state :=
  match positions with
  | [] => state
  | i :: positions =>
    unbox_loop_params fuel known k positions
      (unbox_loop_param fuel known k i state)
  end.

Definition unbox_loop_reads (known : facts) (k : continuation)
    (params : list variable) (metadata : handler_metadata)
    (handler body : expr) : expr :=
  loop_of k
    (unbox_loop_params (lets_in handler) known k (seq 0 (length params))
       (params, metadata, handler, body)).

Fixpoint unbox_loops_knowing (known : facts) (e : expr) : expr :=
  match e with
  | Let x kind d body =>
    Let x kind d (unbox_loops_knowing (facts_under_let known x d) body)
  | Let_static bindings body =>
    Let_static bindings
      (unbox_loops_knowing (facts_under_statics known bindings) body)
  | Let_cont_non_recursive k (Handler params metadata handler) body =>
    Let_cont_non_recursive k
      (Handler params metadata
         (unbox_loops_knowing (facts_under_params known params) handler))
      (unbox_loops_knowing known body)
  | Let_cont_recursive [(k, Handler params metadata handler)] body =>
    unbox_loop_reads known k params metadata handler
      (unbox_loops_knowing known body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (unbox_loops_knowing known body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

(* The pass refines, given what is known of the symbols in scope. *)
Definition unbox_loops_knowing_symbols_refines_statement : Prop :=
  refines_where_known unbox_loops_knowing.
