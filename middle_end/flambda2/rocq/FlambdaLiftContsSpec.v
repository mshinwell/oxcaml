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

(* The continuations that a handler binds on its way to its [Switch],
   bound outside the handler: a normalisation that is an equivalence.

   This file is to be reviewed: [lift_handler_conts] and what it is
   made of, and the two statements. Nothing applies the pass yet; the
   validation of middle_end/flambda2/tests/semantics/ is to apply it to
   each of the two terms that it compares, by a later change.

   Where a continuation [k] is given, by each of its applications, a
   constant for one of its parameters, and its handler tests that
   parameter by a [Switch], an application could go at once where the
   arm of its constant goes. It cannot where that arm applies a
   continuation that the handler binds itself, on its way to the
   [Switch]: that continuation is not in scope at the application.

     let_cont k (p, q) =
       let_cont k' (x) = H in
       switch p
         | 0 -> cont k' (a)
         | 1 -> cont j (b)
     in
     body

   The front end leaves this shape where a variant is matched after
   the branches that build it have met, and the unboxing of the
   parameters of [k], Simplify's and the validation's, gives [k] the
   tag as a constant at each application. Simplify, with the join of
   the environments of the applications
   (simplify/join_points.ml, [compute_handler_env]), knows in the
   handler what each application gave, and a parameter that only one
   arm reads is no longer read; the term before of the validation
   still gives [k] that parameter, with a dummy where the application
   has none.

   The pass binds [k'] outside the [Let_cont] of [k]. There the
   parameters of [k] are not in scope, so [k'] takes, in front of its
   own parameters, those of [k] that its handler reads, and each of
   its applications gives it those:

     let_cont k' (q, x) = H in
     let_cont k (p, q) =
       switch p
         | 0 -> cont k' (q, a)
         | 1 -> cont j (b)
     in
     body

   The handler of [k] is then the [Switch] itself, and every arm
   applies a continuation that is in scope where [k] is applied. No
   name is made: [k'] keeps its name and its new parameters have the
   names of the parameters of [k]. Nothing is copied.

   The continuations are moved one at a time, the first bound first
   ([lift_spine]). One that is bound later may apply an earlier one in
   its handler; that application has been given parameters of [k] by
   then, so the later one reads them and takes them too.

   What the pass asks ([lift_conts], [lift_spine]):
   - of [k]: that its parameters are distinct and that it has as many
     kinds as parameters; that its handler is one or more
     non-recursive [Let_cont]s and then a [Switch] on one of its
     parameters ([tested]). And two things that the equivalence does
     not need, which keep the pass to where an application of [k] can
     then go to an arm: that [k] is not an exception handler; and
     that every mention of [k] in the body of its [Let_cont] is an
     application which gives the tested parameter a naked immediate,
     no [Let_cont] there binding [k] again ([all_give_immediate]);
   - of each [k'] that the handler binds: that it is not an exception
     handler; that its parameters and those of [k] are distinct
     together; that it is not free in the body of the [Let_cont] of
     [k], where it comes into scope, nor in its own handler, where it
     would stand for another continuation of its name, bound outside;
     that in the rest of the handler of [k] every mention of it is an
     application, no [Let_cont] binds it again, and no [Let] and no
     parameter of a handler binds, between its binding and an
     application of it, one of the parameters that it takes
     ([only_applied]).
   Where one of these fails for any of them no continuation is moved
   out at that [Let_cont]: it keeps its handler and its body, which
   are those that the pass has made of the handler and the body of
   the term, and may have continuations moved inside them. The
   handlers of recursive continuations and the bodies of code are not
   gone into: FlambdaNormaliseSpec.rewrite_code and
   FlambdaRecHandlersSpec.rewrite_rec_handlers take a pass there.

   The tests of freedom are FlambdaNormaliseSpec.var_free_b and
   FlambdaUnusedContsSpec.cont_free_b, which may say that a name is
   free when it is not, never the reverse. So a continuation may take
   a parameter that it does not read, and the pass may leave a
   [Let_cont] that it could have rewritten.

   The result is equivalent to the term
   ([lift_handler_conts_equivalent_statement]), under all
   environments. The application of [k'] tests the kinds of the
   parameters of [k] that it is given; the application of [k] has
   tested them against the same kinds, and nothing binds them again
   on the way, so the test passes. Nothing else changes in a run.

   Renaming: the functions here compare names by equality only and
   make none, so the pass commutes with the renamings of
   FlambdaNominalSpec.v ([lift_handler_conts_equivariant_statement]).
   That it keeps scope is stated in FlambdaLiftContsScopeSpec.v.

   The proofs are in FlambdaLiftContsProofs.v, with lemmas in
   FlambdaLiftContsNamesProofs.v; neither needs review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaMapSpec FlambdaSemanticsSpec FlambdaNominalSpec
  FlambdaNormaliseSpec FlambdaUnusedContsSpec.
Import ListNotations.

(* ======================================================================== *)
(* The applications of a continuation given more arguments                  *)
(* ======================================================================== *)

(* An [Apply_cont] that applies [j] given the variables [ps] in front
   of its arguments. *)
Definition give_to (j : continuation) (ps : list variable) (ac : apply_cont)
    : apply_cont :=
  if Pos.eqb (ac_continuation ac) j
  then
    {| ac_continuation := ac_continuation ac;
       ac_args := map Var ps ++ ac_args ac;
       ac_trap_action := ac_trap_action ac |}
  else ac.

(* Every application of [j] in a term so. The bodies of code are not
   gone into. *)
Fixpoint give (j : continuation) (ps : list variable) (e : expr) {struct e}
    : expr :=
  match e with
  | Let x kind d body => Let x kind d (give j ps body)
  | Let_static bindings body => Let_static bindings (give j ps body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (give_in_handler j ps h) (give j ps body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive
      (map (fun '(k, h) => (k, give_in_handler j ps h)) handlers)
      (give j ps body)
  | Apply_cont ac => Apply_cont (give_to j ps ac)
  | Switch scrutinee arms =>
    Switch scrutinee (map (fun '(n, ac) => (n, give_to j ps ac)) arms)
  | Apply _ | Invalid => e
  end
with give_in_handler (j : continuation) (ps : list variable)
    (h : continuation_handler) {struct h} : continuation_handler :=
  match h with
  | Handler params metadata handler =>
    Handler params metadata (give j ps handler)
  end.

(* No trap action of the [Apply_cont] names [j]; and if it applies [j],
   none of the variables that [j] is to be given has been bound since
   the binding of [j] ([ok]). An application of [j] may carry a trap
   action that names another continuation. *)
Definition applies_only (j : continuation) (ok : bool) (ac : apply_cont)
    : bool :=
  match ac_trap_action ac with
  | Some action => negb (Pos.eqb (trap_action_handler action) j)
  | None => true
  end
  && (ok || negb (Pos.eqb (ac_continuation ac) j)).

(* Every mention of [j] in a term is such an application, and [j] is
   not bound again. *)
Fixpoint only_applied (j : continuation) (ps : list variable) (ok : bool)
    (e : expr) {struct e} : bool :=
  match e with
  | Let y _ _ body => only_applied j ps (ok && negb (among y ps)) body
  | Let_static _ body => only_applied j ps ok body
  | Let_cont_non_recursive k h body =>
    negb (Pos.eqb k j)
    && handler_only_applied j ps ok h
    && only_applied j ps ok body
  | Let_cont_recursive handlers body =>
    forallb
      (fun '(k, h) => negb (Pos.eqb k j) && handler_only_applied j ps ok h)
      handlers
    && only_applied j ps ok body
  | Apply ap =>
    negb (Pos.eqb (ap_continuation ap) j)
    && negb (Pos.eqb (ap_exn_continuation ap) j)
  | Apply_cont ac => applies_only j ok ac
  | Switch _ arms => forallb (fun '(_, ac) => applies_only j ok ac) arms
  | Invalid => true
  end
with handler_only_applied (j : continuation) (ps : list variable) (ok : bool)
    (h : continuation_handler) {struct h} : bool :=
  match h with
  | Handler params _ handler =>
    only_applied j ps
      (ok && negb (existsb (fun p => among p params) ps))
      handler
  end.

(* ======================================================================== *)
(* The continuations of a handler, moved out                                *)
(* ======================================================================== *)

(* The parameters that may be free in an expression, each with its
   kind, in their order. *)
Fixpoint read_params (params : list variable) (kinds : list flambda_kind)
    (e : expr) : list (variable * flambda_kind) :=
  match params, kinds with
  | p :: params, kind :: kinds =>
    if var_free_b p e
    then (p, kind) :: read_params params kinds e
    else read_params params kinds e
  | _, _ => []
  end.

(* The applications, in a term, of the continuations that have been
   moved, each given the parameters that its continuation takes; the
   one moved last is first in the list. *)
Definition give_all (moved : list (continuation * list variable)) (e : expr)
    : expr :=
  fold_right (fun '(j, ps) e => give j ps e) e moved.

(* The handler of a continuation whose parameters are [params], of
   kinds [kinds], and that is bound around [body]: the continuations
   that it binds on its way to a [Switch] on one of [params], each as
   it is once moved out, the first bound first, and what is left, with
   the applications of the continuations in [moved] and of those given
   their parameters. [None] if the handler is not of that form, or a
   test fails. *)
Fixpoint lift_spine (body : expr) (params : list variable)
    (kinds : list flambda_kind) (moved : list (continuation * list variable))
    (handler : expr) {struct handler}
    : option (list (continuation * continuation_handler) * expr) :=
  match handler with
  | Let_cont_non_recursive j (Handler q metadata h) rest =>
    let h := give_all moved h in
    let read := read_params params kinds h in
    let ps := map fst read in
    if negb (hm_is_exn_handler metadata)
       && distinct (params ++ q)
       && negb (cont_free_b j body)
       && negb (cont_free_b j h)
       && only_applied j ps true (give_all moved rest)
    then
      match lift_spine body params kinds ((j, ps) :: moved) rest with
      | Some (others, switch) =>
        Some
          ((j,
            Handler (ps ++ q)
              {| hm_params_kinds := map snd read ++ hm_params_kinds metadata;
                 hm_is_exn_handler := false |}
              h)
           :: others,
           switch)
      | None => None
      end
    else None
  | Switch (Var p) _ =>
    if among p params then Some ([], give_all moved handler) else None
  | Let _ _ _ _ | Let_static _ _ | Let_cont_recursive _ _ | Apply _
  | Apply_cont _ | Switch _ _ | Invalid =>
    None
  end.

(* The position, among [params], of the variable that the handler
   tests by a [Switch] once it has bound its own continuations. *)
Fixpoint position (p : variable) (params : list variable) : option nat :=
  match params with
  | [] => None
  | p' :: params =>
    if Pos.eqb p p' then Some O else option_map S (position p params)
  end.

Fixpoint tested (params : list variable) (handler : expr) {struct handler}
    : option nat :=
  match handler with
  | Let_cont_non_recursive _ _ rest => tested params rest
  | Switch (Var p) _ => position p params
  | Let _ _ _ _ | Let_static _ _ | Let_cont_recursive _ _ | Apply _
  | Apply_cont _ | Switch _ _ | Invalid =>
    None
  end.

(* No trap action of the [Apply_cont] names [k]; and if it applies [k],
   it gives a naked immediate at the position. *)
Definition gives_immediate (k : continuation) (i : nat) (ac : apply_cont)
    : bool :=
  match ac_trap_action ac with
  | Some action => negb (Pos.eqb (trap_action_handler action) k)
  | None => true
  end
  && (if Pos.eqb (ac_continuation ac) k
      then
        match nth_error (ac_args ac) i with
        | Some (Const (Naked_immediate _)) => true
        | _ => false
        end
      else true).

(* Every mention of [k] in a term is such an application, and [k] is
   not bound again. *)
Fixpoint all_give_immediate (k : continuation) (i : nat) (e : expr)
    {struct e} : bool :=
  match e with
  | Let _ _ _ body | Let_static _ body => all_give_immediate k i body
  | Let_cont_non_recursive k' h body =>
    negb (Pos.eqb k' k)
    && handler_all_give_immediate k i h
    && all_give_immediate k i body
  | Let_cont_recursive handlers body =>
    forallb
      (fun '(k', h) =>
         negb (Pos.eqb k' k) && handler_all_give_immediate k i h)
      handlers
    && all_give_immediate k i body
  | Apply ap =>
    negb (Pos.eqb (ap_continuation ap) k)
    && negb (Pos.eqb (ap_exn_continuation ap) k)
  | Apply_cont ac => gives_immediate k i ac
  | Switch _ arms => forallb (fun '(_, ac) => gives_immediate k i ac) arms
  | Invalid => true
  end
with handler_all_give_immediate (k : continuation) (i : nat)
    (h : continuation_handler) {struct h} : bool :=
  match h with
  | Handler _ _ handler => all_give_immediate k i handler
  end.

(* The continuations moved, bound around a term, the first outermost. *)
Definition bind_lifted (lifted : list (continuation * continuation_handler))
    (e : expr) : expr :=
  fold_right (fun '(j, hj) e => Let_cont_non_recursive j hj e) e lifted.

(* [Let_cont_non_recursive k h body] with the continuations that [h]
   binds on its way to its [Switch] moved out, where there is one and
   the tests pass. *)
Definition lift_conts (k : continuation) (h : continuation_handler)
    (body : expr) : option expr :=
  match h with
  | Handler params metadata handler =>
    match tested params handler with
    | Some i =>
      if negb (hm_is_exn_handler metadata)
         && distinct params
         && Nat.eqb (length (hm_params_kinds metadata)) (length params)
         && all_give_immediate k i body
      then
        match
          lift_spine body params (hm_params_kinds metadata) [] handler
        with
        | Some (j :: others, switch) =>
          Some
            (bind_lifted (j :: others)
               (Let_cont_non_recursive k (Handler params metadata switch)
                  body))
        | Some ([], _) | None => None
        end
      else None
    | None => None
    end
  end.

(* ======================================================================== *)
(* The pass                                                                 *)
(* ======================================================================== *)

(* Every non-recursive [Let_cont] of a term, its handler and its body
   first. *)
Fixpoint lift_handler_conts (e : expr) : expr :=
  match e with
  | Let x kind d body => Let x kind d (lift_handler_conts body)
  | Let_static bindings body => Let_static bindings (lift_handler_conts body)
  | Let_cont_non_recursive k (Handler params metadata handler) body =>
    let h := Handler params metadata (lift_handler_conts handler) in
    let body := lift_handler_conts body in
    match lift_conts k h body with
    | Some lifted => lifted
    | None => Let_cont_non_recursive k h body
    end
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (lift_handler_conts body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition lift_handler_conts_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (lift_handler_conts e).

Definition lift_handler_conts_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    lift_handler_conts (rename_expr r e)
    = rename_expr r (lift_handler_conts e).
