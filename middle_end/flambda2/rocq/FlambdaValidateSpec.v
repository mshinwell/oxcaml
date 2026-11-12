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

(* Validating what Simplify did to a compilation unit.

   This file is to be reviewed: [validate_unit] and the two statements.
   It is extracted and run by the test of
   middle_end/flambda2/tests/semantics/ on the term of a unit before
   Simplify and the term after.

   [validate_unit] is the whole check, so that what it accepts is correct
   by one theorem and not by how a tool puts the proved pieces together.
   It compares the two terms as they are given, up to bound names
   (FlambdaCompareSpec.expr_eqb). Failing that, it makes jumps of the
   self tail calls of the code named, each with the name given for its
   loop (FlambdaLoopifySpec.loopify_unit, which says what a self tail
   call is and leaves alone the code that it may not change), as
   Simplify does for the code that the front end marks; the result is
   the term before for all that follows. It normalises that term by
   rewrites that refine it
   ([normalise_before]) and the term after by rewrites that are
   equivalences ([normalise_after]), each gone round a number of times as
   they enable one another, and compares the results up to bound
   names. The term before is normalised in two
   phases: first what Simplify does to the parameters of the
   continuations of the term as it is ([normalise_params_round]), then
   the rounds that inline the calls of known code
   ([normalise_before_round]), which the term after has too. Failing
   that, it removes from the term
   before the static bindings of the names given
   (FlambdaUnusedStaticsSpec.drop_statics) and compares again. Failing
   that too, it starts again from the term before as it was given. For
   each of the liftings given, in turn ([lifted_in_turn]), it makes the
   [Let]s given static bindings of the symbols given: first those to
   bind at the head of the unit, which mention no variable and may
   stand where no static binding can, in the arm of a test
   (FlambdaLiftFromArmsSpec.lift_to_head_unit); then those in
   the bodies of code, which mention no variable and whose bindings go
   beside the code (FlambdaLiftFromCodeSpec.lift_from_code_unit); then
   those outside code, where they stand (FlambdaLiftSpec.lift_unit,
   which says what is lifted and under which conditions). It
   normalises the result, each round followed by using
   what is known of the static closures whose bindings are in sight
   (FlambdaKnownClosuresSpec.use_known_closures: a value slot is read,
   a call is made direct), by replacing the primitives and the
   projections applied to symbols that the unit binds to constants by
   their values (FlambdaKnownSymbolsSpec.fold_known_unit), and by
   replacing the projection of a value slot that every set of
   closures of the unit gives the same symbol or constant by that
   symbol or constant, where the symbol is in scope
   (FlambdaKnownSlotsSpec.read_known_slots; [normalise_lifted]): in
   the code of a closure that a function makes, the slot that holds a
   function of the unit is the symbol of that function once the
   function is lifted. Every round of that normalisation, after each
   of the liftings, makes no name that is the return or the exception
   continuation of the unit of any of the liftings given, the later
   ones included, whether or not the term mentions them
   ([unit_continuations]; FlambdaRenameApartSpec.rename_apart_avoiding
   takes its new names outside the names of the term and outside
   those): a lifting checks the unit by the names of those two
   continuations, which the term may no longer mention once it is
   normalised, so a binder made in a round must not take one of them.
   Then it removes from the static sets of closures the value slots
   given, if nothing projects them
   (FlambdaUnusedSlotsSpec.drop_unused_slots), removes the static
   bindings of the names given, and compares; in this comparison the
   bindings of code of both terms are first moved up to the head of
   what they are in (FlambdaFloatCodeSpec.float_code), as the two terms
   do not bind the code of a lifted closure in the same place; and
   before that the term after, normalised, has all its code bound at
   its head, where it passes the checks of
   FlambdaHoistCodeSpec.hoist_code ([with_code_first]): Simplify binds
   the code of a closure that it lifts in the handler of a
   continuation in that handler, and the term before binds all the
   code of the unit first. Failing that, it compares the same two
   terms otherwise: each with its static bindings that need nothing
   from around them, the code and the symbols whose constants mention
   no variable, bound first, where it passes the checks of
   FlambdaHoistStaticsSpec.hoist_statics for the unit of the first
   lifting given ([with_statics_first]). Simplify binds a symbol that
   it lifts out of the arm of a test under the last [Let] before the
   test, and the term before binds it at its head; where such a
   binding stands does not matter to a unit whose static names are
   all in scope where they are mentioned. The
   first lifting comes before any normalisation because the
   normalisation unfolds calls: a [Let] in the body of a function would
   be many [Let]s afterwards, and a closure that nothing uses would be
   gone. A later lifting names [Let]s of the term as the liftings before
   it and the normalisation have left it: those that the inlining of a
   call has brought out of a function, which Simplify lifts where it
   inlines the call. What is known of the symbols is used in every
   round because they enable one another: a round puts a symbol where
   a variable stood for it; what is known of the symbol then puts what
   a projection of it gives in place of the projection, and the code of
   the closure in a call of it; and the next round follows the one to
   where it is read in turn, and inlines the other. The value slots
   come last because it is the normalisation that removes the
   projections which the code of a function makes and no longer needs.
   Before each of the comparisons of normalised terms the bindings of
   each group of static bindings of the term before are put in the
   order that the term after has them in
   (FlambdaStaticsOrderSpec.order_statics_as): Simplify builds the group
   of a set of closures again, in an order of its own.

   The normalisation of the term before ends by making ordinary
   continuations of the exception handlers that no call can raise to,
   and removing the trap actions that name them
   (FlambdaDemoteSpec.demote_handlers), as Simplify does to a [try]
   all of whose raises it sees, and then going through its rounds
   again ([demote_and_tidy]): the term after has a jump where the term
   before has a raise, and the comparison tells a trap action from
   none. The same is done after the last of the liftings. The rewrite
   is applied with no name in scope. It takes the names in scope so as
   to leave alone a handler whose name is also that of a continuation
   around the term, and a term that passes the checks of exception
   handlers and of trap actions then still passes them; nothing here
   asks those checks of a normalised term, and the rewrite is an
   equivalence whatever names it is given
   (FlambdaDemoteSpec.demote_handlers_equivalent_statement), which is
   all that the two statements below use. It does not look at the
   kind of a raise. On a unit compiled with debugging information
   Simplify keeps the handler that a raise with a backtrace reaches,
   and the rewrite demotes it: that can leave the two normalised terms
   different, and prevent the validation.

   What it accepts is correct for the unit run as a compilation unit is
   run, on its own from empty environments
   ([validate_unit_sound_statement]): if the term before exits, the term
   after exits alike, and if the term after terminates then it does as
   the term before does, or the term before is undefined. Where no static
   binding had to be removed and nothing lifted, this holds under all
   environments too ([validate_unit_sound_everywhere_statement]). A unit
   in which something was lifted exits with constants and symbols only:
   that is one of the conditions.

   The number of rounds, the names and the value slots to remove, the
   code to loopify with the names of its loops, what to lift and the
   code whose calls are not to be inlined
   (FlambdaNormaliseSpec.inline_calls; the same on the two sides) are
   for the caller to choose; none is trusted. Fewer rounds, the wrong
   names, the wrong value slots, the wrong loops, the wrong [Let]s or
   the wrong code make the check fail, not accept what it should not.
   The names to remove are those of the term that is compared: of the
   term lifted, where something is lifted.

   The proofs are in FlambdaValidateProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaCompareSpec FlambdaNormaliseSpec FlambdaBlockLoadSpec
  FlambdaCodeLetsSpec FlambdaCseSpec FlambdaDeadParamsSpec FlambdaForwardSpec
  FlambdaForwardJumpsSpec
  FlambdaIdentitiesSpec FlambdaMergeSwitchesSpec
  FlambdaInlineSiblingsSpec FlambdaInlineTailSpec FlambdaLoopAliasesSpec
  FlambdaLoopLetsSpec
  FlambdaParamAliasesSpec FlambdaRecHandlersSpec FlambdaRenameApartSpec
  FlambdaShareProjectionsSpec FlambdaShortcutSpec FlambdaSinkContsSpec
  FlambdaStaticsOrderSpec FlambdaUnboxSpec FlambdaUnboxVariantsSpec
  FlambdaUnusedContsSpec
  FlambdaUnusedParamsSpec FlambdaUnusedProjectionsSpec
  FlambdaUnusedStaticsSpec FlambdaWellFormedSpec FlambdaLiftSpec
  FlambdaUnusedSlotsSpec FlambdaKnownSymbolsSpec FlambdaKnownClosuresSpec
  FlambdaFloatCodeSpec FlambdaHoistCodeSpec FlambdaLoopifySpec
  FlambdaLiftFromCodeSpec FlambdaLiftFromArmsSpec FlambdaHoistStaticsSpec.
From OxCamlFlambda2 Require Import FlambdaDemoteSpec.
From OxCamlFlambda2 Require Import FlambdaKnownSlotsSpec.
From OxCamlFlambda2Types Require Import FlambdaAliasesSpec.
Import ListNotations.

(* ======================================================================== *)
(* The normalisations                                                       *)
(* ======================================================================== *)

Fixpoint iterate (rounds : nat) (f : expr -> expr) (e : expr) : expr :=
  match rounds with
  | O => e
  | S rounds => iterate rounds f (f e)
  end.

(* One round for an expression of the term before: the rewrites that
   need to know nothing of where they are applied, and that go into the
   handlers of the non-recursive continuations but not into those of the
   recursive ones, nor into code. First what makes the control flow
   simpler: a [Switch] whose arms all apply one continuation, to
   arguments that are the same or the number of the arm, becomes that
   application where the tests of
   FlambdaMergeSwitchesSpec.merge_switches pass (among them: the
   scrutinee is a variable that no arm passes, no arm has a trap
   action, and the numbers of the arms are immediates), after
   [collapse_switches] for the arms that are all the same; a
   continuation that is applied once is moved to where it is
   applied and inlined there ([sink_let_conts], then [inline_tail_conts]),
   before an arm of a [Switch] is made to go where its continuation
   goes ([shortcut_switches]), as Simplify makes no shortcut to a
   continuation that it inlines. Then what follows the values, into the
   handlers of the recursive continuations too for what is known where
   they are defined ([follow_aliases_in_loops]): among them a primitive
   that was computed, and a value slot that was projected, is not
   computed or projected again ([share_known_primitives],
   [share_known_projections]). Then what removes the bindings and the
   parameters that are left unused. *)
Definition normalise_expr_before (e : expr) : expr :=
  let e :=
    shortcut_switches
      (thread_switches
         (inline_tail_conts
            (sink_let_conts
               (remove_unused_conts
                  (merge_switches (collapse_switches (fold_constants e)))))))
  in
  let e :=
    apply_identities
      (follow_aliases_in_loops []
         (follow_aliases []
            (share_known_projections
               (share_known_primitives
                  (unbox_known_numbers (load_known_blocks e))))))
  in
  drop_unused_params
    (remove_unused_defined_lets [] (remove_unused_lets (fold_constants e))).

(* One round for the body of code in the term before: the round for an
   expression, and the same for the handler of each of its recursive
   continuations, a loop in a loop included. *)
Definition normalise_code_before (body : expr) : expr :=
  rewrite_rec_handlers normalise_expr_before (normalise_expr_before body).

(* One round for the term before, once its calls are inlined and its
   binders have names of their own: the round for the body of code, on
   the term itself; then the static bindings tidied, and that round
   applied to the body of each piece of code. None of these makes a
   name. *)
Definition normalise_before_inlined (e : expr) : expr :=
  rewrite_code normalise_code_before
    (merge_statics (drop_deleted_code (normalise_code_before e))).

(* One round for the term before: the calls of known code inlined, but
   for the code given, in the bodies of code those of the other code of
   its group too (FlambdaInlineSiblingsSpec.inline_sibling_calls); then
   FlambdaRenameApartSpec.rename_apart_avoiding, whose candidate gives
   every binder a name of its own, none of them one of the
   continuations given (the body of a function that is inlined twice
   is copied twice, with the names it binds), and which keeps the
   candidate only where its own comparison finds it the same as the
   term, and the term as it is otherwise; then the round above. Every
   rewrite refines. *)
Definition normalise_before_round_avoiding (avoid : list continuation)
    (kept : list code_id) (e : expr) : expr :=
  normalise_before_inlined
    (rename_apart_avoiding avoid
       (inline_sibling_calls kept (inline_calls kept [] e))).

(* With no continuation to avoid: the round of the comparisons in which
   nothing is lifted, where no check goes by a name that the term does
   not mention. *)
Definition normalise_before_round (kept : list code_id) (e : expr) : expr :=
  normalise_before_round_avoiding [] kept e.

(* One round of the first phase for an expression of the term before:
   [normalise_expr_before] with what Simplify does to the parameters of
   continuations. After an arm of a [Switch] is made to go where its
   continuation goes, every application of a continuation whose handler
   only applies another is, wherever it is ([forward_applications]; the
   continuations that this leaves unused are removed). Once the
   values are followed, a parameter of a continuation that its handler
   reads as a box, where every application gives something that the
   term shows, is unboxed as Simplify unboxes it: each read becomes a
   parameter, and an application that has nothing to read gives a
   constant in its place
   (FlambdaUnboxVariantsSpec.unbox_variant_params); the boxed
   parameter, where nothing else uses it, is then one of the unused
   ones. After the
   bindings that are left unused are removed, a parameter that every
   application gives the same thing is bound to it at the start of the
   handler ([bind_aliased_params]), which leaves it unused as a
   parameter, and the unused ones are removed, those of loops too, and
   with them the parameters of a loop that are only passed round it and
   the [Let]s that only they need ([drop_dead_params]). The next round
   follows the new [Let]s and removes them. *)
Definition normalise_expr_params (e : expr) : expr :=
  let e :=
    shortcut_switches
      (thread_switches
         (inline_tail_conts
            (sink_let_conts
               (remove_unused_conts
                  (merge_switches (collapse_switches (fold_constants e)))))))
  in
  let e := remove_unused_conts (forward_applications e) in
  let e :=
    unbox_variant_params
      (follow_aliases_in_loops []
         (follow_aliases [] (unbox_known_numbers (load_known_blocks e))))
  in
  drop_dead_params
    (bind_aliased_params
       (remove_unused_defined_lets [] (remove_unused_lets (fold_constants e)))).

(* The same for the body of code: the round for the handler of each of
   its recursive continuations, a loop in a loop included, and then for
   the body itself. The handlers come first: [forward_applications] goes
   into the handler of a loop for the continuations bound outside it,
   and must find those bound inside as [sink_let_conts] and
   [inline_tail_conts] leave them there. *)
Definition normalise_code_params (body : expr) : expr :=
  normalise_expr_params (rewrite_rec_handlers normalise_expr_params body).

(* One round of the first phase for the term before: the round above on
   the term itself and on the body of each piece of code. No call is
   inlined. *)
Definition normalise_params_round (e : expr) : expr :=
  rewrite_code normalise_code_params (normalise_code_params e).

(* What ends the normalisation of the term before. The exception
   handlers that no call can raise to are made ordinary continuations
   and the trap actions that name them removed, in the term, its
   handlers and its code (FlambdaDemoteSpec.demote_handlers, with no
   name in scope: see the header). Then the rounds of the first phase
   and those of the second, without the inlining of calls, are gone
   through again. They do to what was a [try] what Simplify does on
   its way up, once it has found that the handler can be demoted. The
   continuation of the body, which was applied with the trap action
   that installed the handler, is put where it is applied. A handler
   that nothing raises to is removed. The exception is no longer a
   parameter of a handler that does not read it, and the [Let]s that
   made it go. The continuation by which the body left the [try],
   which only applies another now that its trap action is gone, is a
   shortcut; so is the handler, if it only applies another. *)
Definition demote_and_tidy (rounds : nat) (e : expr) : expr :=
  iterate rounds normalise_before_inlined
    (iterate rounds normalise_params_round (demote_handlers [] e)).

(* The term before is normalised in two phases. The first is what
   Simplify does to the continuations of the term as it is: the front
   end makes every mutable variable in scope a parameter of a loop and
   of the continuation after an [if], and Simplify removes those that
   are always given the same thing. The second inlines the calls of
   known code, and the term after has that phase too
   ([normalise_after_round]), also for the calls that Simplify did not
   inline. The work on parameters is not in the second phase: where the
   validation inlines a call that Simplify left, the continuation that
   the call returned to becomes one that the inlined body applies, on
   both sides, and the term after has only equivalences to normalise it
   with, which the removal of a parameter is not. The demotion of
   exception handlers comes after both ([demote_and_tidy]). In a round
   it would come too soon. A round first inlines a continuation that
   is applied once, and then takes an arm of a [Switch] to where its
   continuation goes; so a handler demoted before the raises to it
   have been taken to the arms would be inlined in the continuation
   that raises. Simplify, for which an application with a trap action
   is not one to inline, takes the arm to the handler and leaves the
   handler where it is bound; the rounds do the same while the handler
   has its mark and the raise its trap action. *)
Definition normalise_before (rounds : nat) (kept : list code_id) (e : expr)
    : expr :=
  demote_and_tidy rounds
    (iterate rounds (normalise_before_round kept)
       (iterate rounds normalise_params_round e)).

(* For the term after, what [normalise_expr_before] does first for the
   term before, with rewrites that are equivalences. A continuation
   that is not used is removed. One that is applied once is moved to
   where it is applied, where [sink_let_conts] can move it, and its
   handler is put in place of the application where
   FlambdaInlineTailSpec.inline_tail_conts_kinded allows: the
   application ends the run of [Let]s that is the body of the binding,
   and the handler gives one kind for each of its parameters. The
   validation inlines, in the term after too, the calls that Simplify
   left and that are not in the list of code to leave, and the
   continuation that such a call returned to is then applied once; and
   Simplify leaves some continuations that are applied once, the one
   whose handler binds the symbols of the unit among them. The term
   before can have lost both: its rounds have [sink_let_conts] and
   FlambdaNormaliseSpec.inline_tail_conts.

   Then an application of a continuation of no parameters whose handler
   is one [Apply_cont] becomes that [Apply_cont], where
   FlambdaForwardJumpsSpec.forward_jumps allows: among its conditions,
   the handler gives no kinds, neither [Apply_cont] has a trap action,
   and nothing that the [Apply_cont] of the handler names is bound
   again in the body of the [Let_cont]. It is an equivalence. A
   continuation that this leaves unused is removed. Simplify leaves
   such an application where the handler was a [Switch] on a
   parameter that it removed, every application giving it the same
   constant: the handler it has is that [Switch] under the [Let] of
   the parameter. The fold of the round before has made the handler
   one [Apply_cont], in the term before too, where
   FlambdaForwardSpec.forward_applications has then forwarded the
   applications. *)
Definition inline_once_applied_after (e : expr) : expr :=
  remove_unused_conts
    (forward_jumps
       (inline_tail_conts_kinded (sink_let_conts (remove_unused_conts e)))).

(* The same for the term after. Every rewrite is an equivalence. The
   unused [Let]s that are sure to have a value are removed in the
   handlers of recursive continuations too, with what is in scope there
   ([remove_unused_defined_lets_in_loops]): Simplify leaves such a [Let]
   where it has removed a parameter that every application gave the same
   thing. Before that, the [Let] of the projection of a function slot
   that nothing uses is removed
   (FlambdaUnusedProjectionsSpec.remove_unused_projections): the [Let]
   of a closure of a set that is not the first is one in the model
   (FlambdaModel.let_closures), and the term before loses it by a
   refinement. Last in a round, the unused [Let]s that are sure to have
   a value are removed in the bodies of code with the parameters of the
   code in scope
   (FlambdaCodeLetsSpec.remove_unused_defined_lets_in_code): where
   Simplify makes a loop of a function, it leaves such a [Let] of each
   parameter of the function that every self tail call passes on as it
   is. *)
Definition normalise_expr_after (e : expr) : expr :=
  remove_unused_defined_lets_in_loops []
    (remove_unused_projections
       (fold_constants
          (follow_aliases_in_loops []
             (follow_aliases [] (inline_once_applied_after e))))).

Definition normalise_code_after (body : expr) : expr :=
  rewrite_rec_handlers normalise_expr_after (normalise_expr_after body).

Definition normalise_after_round (kept : list code_id) (e : expr) : expr :=
  remove_unused_defined_lets_in_code
    (rewrite_code normalise_code_after
       (merge_statics
          (drop_deleted_code
             (rewrite_rec_handlers normalise_expr_after
                (remove_unused_defined_lets_in_loops []
                   (remove_unused_projections
                      (fold_constants
                         (inline_known_calls kept [] []
                            (follow_aliases_in_loops []
                               (follow_aliases []
                                  (inline_once_applied_after e))))))))))).

Definition normalise_after (rounds : nat) (kept : list code_id) (e : expr)
    : expr :=
  iterate rounds (normalise_after_round kept) e.

(* The static bindings of the names given removed, if nothing refers to
   them, and the groups of bindings tidied again. *)
Definition without_statics (D : dropped) (e : expr) : expr :=
  match drop_statics D e with
  | Some e' => merge_statics (drop_deleted_code e')
  | None => e
  end.

(* The [Let]s given made static bindings of the symbols given: those
   to bind at the head of the unit, if the conditions of
   FlambdaLiftFromArmsSpec.lift_to_head_unit hold; then those in the
   bodies of code, if the conditions of
   FlambdaLiftFromCodeSpec.lift_from_code_unit hold of what that gives;
   then those outside code that are bound where they stand, if the
   conditions of FlambdaLiftSpec.lift_unit hold of what that gives.
   Where the conditions of one do not hold, it is not made. The paths
   of each are paths in the term that it is given: the first puts the
   unit under a group of static bindings, if it lifts anything. *)
Definition with_lifting (L : lifting) (e : expr) : expr :=
  let e :=
    match lift_to_head_unit (lifting_unit L) (lifted_to_head L) e with
    | Some e' => e'
    | None => e
    end
  in
  let e :=
    match lift_from_code_unit (lifting_unit L) (lifted_out_of_code L) e with
    | Some e' => e'
    | None => e
    end
  in
  match lift_unit L e with
  | Some e' => e'
  | None => e
  end.

(* What the unit binds its symbols to used wherever they are, if it
   binds each of them to one constant. *)
Definition with_known (e : expr) : expr :=
  match fold_known_unit e with
  | Some e' => e'
  | None => e
  end.

(* The normalisation of a term in which something was lifted: the first
   phase of that of the term before, then its second phase with each
   round followed by the use of what is known of the static closures in
   sight, of what the unit binds its symbols to, and of the value slots
   that every set of closures of the unit gives one symbol or
   constant. *)
Definition normalise_lifted_round (avoid : list continuation)
    (kept : list code_id) (e : expr) : expr :=
  read_known_slots
    (with_known
       (use_known_closures (normalise_before_round_avoiding avoid kept e))).

Definition normalise_lifted (rounds : nat) (avoid : list continuation)
    (kept : list code_id) (e : expr) : expr :=
  iterate rounds (normalise_lifted_round avoid kept)
    (iterate rounds normalise_params_round e).

(* The return and the exception continuation of the unit of each of
   the liftings given: the names by which a lifting checks the unit
   (FlambdaLiftSpec.lift_unit), which the term need not mention. *)
Definition unit_continuations (Ls : list lifting) : list continuation :=
  flat_map
    (fun L => [unit_return (lifting_unit L); unit_exn (lifting_unit L)]) Ls.

(* The term with each of the liftings given applied in turn, each
   followed by that normalisation. A lifting after the first names
   [Let]s of the term that those before it give. The continuations to
   avoid are the same at every step: [validate_unit] gives those of
   the units of all the liftings, so that no round, before or after
   any of them, makes one. After the last, the exception handlers are
   demoted, as at the end of [normalise_before]; the rounds that
   follow the demotion inline no call and rename nothing apart, so
   they make no name. *)
Fixpoint lifted_in_turn (rounds : nat) (avoid : list continuation)
    (Ls : list lifting) (kept : list code_id) (e : expr) : expr :=
  match Ls with
  | [] => demote_and_tidy rounds e
  | L :: Ls =>
    lifted_in_turn rounds avoid Ls kept
      (normalise_lifted rounds avoid kept (with_lifting L e))
  end.

(* The value slots given removed from the static sets of closures, if
   nothing projects them. *)
Definition without_slots (slots : list value_slot) (e : expr) : expr :=
  match drop_unused_slots slots e with
  | Some e' => e'
  | None => e
  end.

(* The unit with all its code bound first, if the conditions of
   FlambdaHoistCodeSpec.hoist_code hold, and its groups of static
   bindings tidied again. *)
Definition with_code_first (e : expr) : expr :=
  match hoist_code e with
  | Some e' => merge_statics (drop_deleted_code e')
  | None => e
  end.

(* The unit with its static bindings that need nothing from around
   them bound first, the code and the symbols whose constants mention
   no variable, if the conditions of
   FlambdaHoistStaticsSpec.hoist_statics hold for the unit of the first
   of the liftings given; and its groups of static bindings tidied
   again. The term as it is if no lifting is given. *)
Definition with_statics_first (Ls : list lifting) (e : expr) : expr :=
  match Ls with
  | [] => e
  | L :: _ =>
    match hoist_statics (lifting_unit L) e with
    | Some e' => merge_statics (drop_deleted_code e')
    | None => e
    end
  end.

(* ======================================================================== *)
(* The check                                                                *)
(* ======================================================================== *)

(* How a pair of terms was found to be correct, if it was. *)
Inductive validation : Type :=
  | Same_up_to_bound_names
  | Same_once_normalised
  | Same_once_unused_statics_removed
  | Same_once_lifted
  | Not_validated.

Definition validate_unit (rounds : nat) (unused : dropped)
    (slots : list value_slot) (G : loopified) (Ls : list lifting)
    (kept : list code_id) (before after : expr) : validation :=
  if expr_eqb [] [] before after then Same_up_to_bound_names
  else
    let before := loopify_unit G before in
    let normalised := normalise_before rounds kept before in
    let after := normalise_after rounds kept after in
    if expr_eqb [] [] (order_statics_as after normalised) after
    then Same_once_normalised
    else if
      expr_eqb [] []
        (order_statics_as after (without_statics unused normalised)) after
    then Same_once_unused_statics_removed
    else if
      expr_eqb [] []
        (order_statics_as (float_code (with_code_first after))
           (float_code
              (without_statics unused
                 (without_slots slots
                    (lifted_in_turn rounds (unit_continuations Ls) Ls kept
                       before)))))
        (float_code (with_code_first after))
    then Same_once_lifted
    else if
      expr_eqb [] []
        (order_statics_as (with_statics_first Ls after)
           (with_statics_first Ls
              (without_statics unused
                 (without_slots slots
                    (lifted_in_turn rounds (unit_continuations Ls) Ls kept
                       before)))))
        (with_statics_first Ls after)
    then Same_once_lifted
    else Not_validated.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

(* A unit that is validated refines the unit it came from, run on its own
   from empty environments. *)
Definition validate_unit_sound_statement : Prop :=
  ∀ (rounds : nat) (unused : dropped) (slots : list value_slot)
    (G : loopified) (Ls : list lifting) (kept : list code_id)
    (before after : expr),
    validate_unit rounds unused slots G Ls kept before after
    <> Not_validated ->
    program_refines before after.

(* It does so under all environments if no static binding was removed and
   nothing was lifted. *)
Definition validate_unit_sound_everywhere_statement : Prop :=
  ∀ (rounds : nat) (unused : dropped) (slots : list value_slot)
    (G : loopified) (Ls : list lifting) (kept : list code_id)
    (before after : expr),
    validate_unit rounds unused slots G Ls kept before after
    = Same_up_to_bound_names
    ∨ validate_unit rounds unused slots G Ls kept before after
      = Same_once_normalised ->
    expr_refines before after.
