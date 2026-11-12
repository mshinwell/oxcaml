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

(* Proofs of the statements of FlambdaKnownSymbolsSpec.v. Nothing here
   needs review.

   The unit and the unit folded are run side by side, in step, with the
   same values. The second state is the first with its terms folded
   ([fold_state]). Two things are kept along the run of the unit: its
   terms bind the known symbols as the unit says
   (FlambdaClosuresProofs.terms_inv_step), so what the run has bound of
   them is what is known ([agrees]). A defining expression that has a
   value in such a static environment has the same value in the known
   one, by the laws of the primitives about a static environment that
   grows (FlambdaPrimitiveProofs.eval_prim_statics_extend). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaPrimitiveModel FlambdaValueSpec
  FlambdaPrimitiveSpec FlambdaPrimitiveProofs FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaNominalSpec FlambdaNormaliseSpec
  FlambdaClosuresProofs FlambdaUnusedStaticsSpec FlambdaUnusedSlotsProofs
  FlambdaKnownSymbolsSpec.
Import ListNotations.

(* ======================================================================== *)
(* What has no variable in it                                               *)
(* ======================================================================== *)

Lemma eval_closed_simple (vars : env) (s : simple) :
  closed_simple s = true -> eval_simple vars s = eval_simple [] s.
Proof. destruct s; simpl; [ discriminate | reflexivity | reflexivity ]. Qed.

Lemma eval_closed_simples (vars : env) (args : list simple) :
  forallb closed_simple args = true ->
  eval_simples vars args = eval_simples [] args.
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  intros H. apply andb_true_iff in H as [Hs Hargs].
  rewrite (eval_closed_simple vars s Hs), (IH Hargs). reflexivity.
Qed.

Lemma eval_closed_value_slots (vars : env)
    (slots : list (value_slot * simple)) :
  forallb (fun slot => closed_simple (snd slot)) slots = true ->
  eval_value_slots vars slots = eval_value_slots [] slots.
Proof.
  induction slots as [ | [slot s] slots IH]; simpl; [ reflexivity | ].
  intros H. apply andb_true_iff in H as [Hs Hslots].
  rewrite (eval_closed_simple vars s Hs), (IH Hslots). reflexivity.
Qed.

Lemma eval_closed_static_const (vars : env) (const : static_const) :
  closed_static_const const = true ->
  eval_static_const vars const = eval_static_const [] const.
Proof.
  destruct const
    as [code slots | fslot syms decls slots | tag fields | contents | bytes];
    simpl; intros H.
  - rewrite (eval_closed_value_slots vars slots H). reflexivity.
  - rewrite (eval_closed_value_slots vars slots H). reflexivity.
  - rewrite (eval_closed_simples vars fields H). reflexivity.
  - rewrite (eval_closed_simple vars contents H). reflexivity.
  - reflexivity.
Qed.

(* ======================================================================== *)
(* A defining expression is folded to its value                             *)
(* ======================================================================== *)

Section Folded.

Variables statics run_statics : static_env.

(* Each symbol that [statics] binds is bound in [run_statics] to the same
   thing or to nothing. *)
Hypothesis Hagrees :
  ∀ (s : symbol) (allocated allocated' : statically_allocated_value),
    lookup s (static_values statics) = Some allocated ->
    lookup s (static_values run_statics) = Some allocated' ->
    allocated' = allocated.

Lemma known_symbol_bound (s : symbol)
    (allocated : statically_allocated_value) :
  is_some (lookup s (static_values statics)) = true ->
  lookup s (static_values run_statics) = Some allocated ->
  lookup s (static_values statics) = Some allocated.
Proof.
  destruct (lookup s (static_values statics)) as [known | ] eqn:Hs;
    [ | discriminate ].
  intros _ Hrun. rewrite (Hagrees s known allocated Hs Hrun). reflexivity.
Qed.

Lemma eval_known_simple (vars : env) (s : simple) :
  simple_known statics s = true -> eval_simple vars s = eval_simple [] s.
Proof. destruct s; simpl; [ discriminate | reflexivity | reflexivity ]. Qed.

Lemma eval_known_simples (vars : env) (args : list simple) :
  forallb (simple_known statics) args = true ->
  eval_simples vars args = eval_simples [] args.
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  intros H. apply andb_true_iff in H as [Hs Hargs].
  rewrite (eval_known_simple vars s Hs), (IH Hargs). reflexivity.
Qed.

(* The symbols among the values of known arguments are bound. *)
Lemma known_simples_symbols (args : list simple) :
  forallb (simple_known statics) args = true ->
  ∀ (vs : list value) (s : symbol),
    eval_simples [] args = Some vs ->
    Value_symbol s ∈ vs ->
    is_some (lookup s (static_values statics)) = true.
Proof.
  induction args as [ | a args IH]; simpl; intros H vs s.
  - intros [= <-] [].
  - apply andb_true_iff in H as [Ha Hargs].
    destruct (eval_simple [] a) as [v | ] eqn:Hv; simpl; [ | discriminate ].
    destruct (eval_simples [] args) as [rest | ]; simpl; [ | discriminate ].
    intros [= <-] [Hhead | Hrest]; [ | exact (IH Hargs rest s eq_refl Hrest) ].
    subst v. destruct a as [x | sym | c]; simpl in Hv, Ha;
      [ discriminate | | discriminate ].
    injection Hv as <-. exact Ha.
Qed.

(* What is read of a known symbol in the run is read of it in what is
   known. *)
Lemma eval_known_named (vars : env) (d : named) (v : value) :
  named_known statics d = true ->
  eval_named run_statics vars d = Some v ->
  eval_named statics [] d = Some v.
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure]; simpl;
    try discriminate.
  - intros H. apply andb_true_iff in H as [_ Hargs].
    rewrite (eval_known_simples vars args Hargs).
    destruct (eval_simples [] args) as [vs | ] eqn:Hvs; simpl;
      [ | discriminate ].
    apply eval_prim_statics_extend. intros s allocated Hin.
    apply known_symbol_bound.
    exact (known_simples_symbols args Hargs vs s Hvs Hin).
  - intros Hclosure. rewrite (eval_known_simple vars closure Hclosure).
    destruct closure as [x | s | c]; simpl in Hclosure |- *;
      [ discriminate | | discriminate ].
    destruct (lookup s (static_values run_statics)) as [allocated | ] eqn:Hs;
      [ | discriminate ].
    rewrite (known_symbol_bound s allocated Hclosure Hs). exact (fun H => H).
  - intros Hclosure. rewrite (eval_known_simple vars closure Hclosure).
    destruct closure as [x | s | c]; simpl in Hclosure |- *;
      [ discriminate | | discriminate ].
    unfold project_value_slot, closure_in_set.
    destruct (lookup s (static_values run_statics)) as [allocated | ] eqn:Hs;
      [ | discriminate ].
    rewrite (known_symbol_bound s allocated Hclosure Hs). exact (fun H => H).
  - intros Hclosure. rewrite (eval_known_simple vars closure Hclosure).
    destruct closure as [x | s | c]; simpl in Hclosure |- *;
      [ discriminate | | discriminate ].
    destruct (lookup s (static_values run_statics)) as [allocated | ] eqn:Hs;
      [ | discriminate ].
    rewrite (known_symbol_bound s allocated Hclosure Hs). exact (fun H => H).
Qed.

Lemma fold_known_named_sound_here (vars : env) (d : named) (v : value) :
  eval_named run_statics vars d = Some v ->
  eval_named run_statics vars (fold_known_named statics d) = Some v.
Proof.
  intros Hv. unfold fold_known_named.
  destruct (named_known statics d) eqn:Hknown; [ | exact Hv ].
  rewrite (eval_known_named vars d v Hknown Hv).
  destruct v; solve [ exact Hv | reflexivity ].
Qed.

End Folded.

Theorem fold_known_named_sound : fold_known_named_sound_statement.
Proof.
  intros statics run_statics vars d v Hagrees.
  exact (fold_known_named_sound_here statics run_statics Hagrees vars d v).
Qed.

(* ======================================================================== *)
(* The projection of a function slot is folded to its value                 *)
(* ======================================================================== *)

Section Folded_slot.

Variables sets run_statics : static_env.

(* Each symbol that [sets] binds is bound in [run_statics] to a closure
   at the same slot of the same set, or to nothing. *)
Hypothesis Hsets :
  ∀ (s : symbol) (allocated allocated' : statically_allocated_value),
    lookup s (static_values sets) = Some allocated ->
    lookup s (static_values run_statics) = Some allocated' ->
    same_set allocated allocated'.

Lemma fold_function_slot_sound_here (vars : env) (d : named) (v : value) :
  eval_named run_statics vars d = Some v ->
  eval_named run_statics vars (fold_function_slot sets d) = Some v.
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    try exact (fun H => H).
  destruct closure as [x | s | c]; try exact (fun H => H).
  unfold fold_function_slot.
  change
    (eval_named sets [] (Project_function_slot move_from move_to (Symbol s)))
    with (project_function_slot sets move_from move_to (Value_symbol s)).
  change
    (eval_named run_statics vars
       (Project_function_slot move_from move_to (Symbol s)))
    with (project_function_slot run_statics move_from move_to (Value_symbol s))
    at 1.
  intros Hrun.
  destruct (project_function_slot sets move_from move_to (Value_symbol s))
    as [w | ] eqn:Hknown;
    [ | exact Hrun ].
  destruct w; try exact Hrun.
  change (Some (Value_symbol s0) = Some v).
  unfold project_function_slot in Hrun, Hknown.
  destruct (lookup s (static_values sets)) as [allocated | ] eqn:Hs;
    [ | discriminate ].
  destruct (lookup s (static_values run_statics)) as [allocated' | ] eqn:Hs';
    [ | discriminate ].
  pose proof (Hsets s allocated allocated' Hs Hs') as Hsame.
  destruct allocated as [code slots | fslot syms decls slots | | | ],
    allocated' as [code' slots' | fslot' syms' decls' slots' | | | ];
    try contradiction.
  - rewrite Hknown in Hrun. exact Hrun.
  - destruct Hsame as (-> & -> & ->). rewrite Hknown in Hrun. exact Hrun.
Qed.

(* A symbol that [sets] binds to a closure of code is, in the run, a
   closure of that code, or bound to nothing. *)
Lemma closure_of_sets (s : symbol) (code called : code_id)
    (slots slots' : list (value_slot * value)) :
  closure_of sets (Value_symbol s) = Some (code, slots) ->
  closure_of run_statics (Value_symbol s) = Some (called, slots') ->
  called = code.
Proof.
  unfold closure_of.
  destruct (lookup s (static_values sets)) as [allocated | ] eqn:Hs;
    [ | discriminate ].
  destruct (lookup s (static_values run_statics)) as [allocated' | ] eqn:Hs';
    [ | discriminate ].
  pose proof (Hsets s allocated allocated' Hs Hs') as Hsame.
  destruct allocated as [c sl | fslot syms decls sl | | | ],
    allocated' as [c' sl' | fslot' syms' decls' sl' | | | ];
    try contradiction.
  - simpl in Hsame. subst c'. intros [= <- _] [= <- _]. reflexivity.
  - destruct Hsame as (-> & -> & ->).
    destruct (lookup fslot decls) as [c | ]; simpl; [ | discriminate ].
    intros [= <- _] [= <- _]. reflexivity.
Qed.

(* An indirect call of such a symbol and the direct call of that code
   step alike: both are undefined where the symbol is bound to
   nothing. *)
Lemma fold_known_apply_sound_here (vars : env) (conts : cont_env)
    (ap : apply_expr) :
  step (State (Apply (fold_known_apply sets ap)) vars conts run_statics)
  = step (State (Apply ap) vars conts run_statics).
Proof.
  unfold fold_known_apply.
  destruct (ap_call_kind ap) as [named | ] eqn:Hkind; [ reflexivity | ].
  destruct (ap_callee ap) as [x | s | c] eqn:Hcallee; try reflexivity.
  destruct (closure_of sets (Value_symbol s)) as [[code slots] | ] eqn:Hknown;
    [ | reflexivity ].
  rewrite !step_apply. unfold exn_extra_simples.
  cbn [ap_callee ap_call_kind ap_args ap_continuation ap_exn_continuation
       ap_exn_extra_args ap_args_arity ap_return_arity].
  rewrite Hkind, Hcallee. cbn [eval_simple].
  destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | reflexivity ].
  destruct (eval_simples vars (map fst (ap_exn_extra_args ap)))
    as [extra | ];
    [ | reflexivity ].
  unfold call_function.
  rewrite
    !(shape_of_call_closure run_statics (Value_symbol s) _ vs _ _ eq_refl).
  destruct (closure_of run_statics (Value_symbol s))
    as [[called slots'] | ] eqn:Hrun.
  - rewrite
      (shape_of_closure_call_kind run_statics (Value_symbol s) (Direct code)
         vs _ _ called slots' Hrun
         (or_intror
            (f_equal Direct
               (eq_sym (closure_of_sets s code called slots slots' Hknown
                          Hrun))))).
    reflexivity.
  - unfold shape_of_closure_call. rewrite Hrun. reflexivity.
Qed.

End Folded_slot.

Theorem fold_function_slot_sound : fold_function_slot_sound_statement.
Proof.
  intros sets run_statics vars d v Hsets.
  exact (fold_function_slot_sound_here sets run_statics Hsets vars d v).
Qed.

Theorem fold_known_apply_sound : fold_known_apply_sound_statement.
Proof.
  intros sets run_statics vars conts ap Hsets.
  exact (fold_known_apply_sound_here sets run_statics Hsets vars conts ap).
Qed.

(* ======================================================================== *)
(* What is known of a unit                                                  *)
(* ======================================================================== *)

(* Every constant that is known has a value. *)
Definition all_have_values (known : list (symbol * static_const)) : Prop :=
  Forall (fun binding => eval_static_const [] (snd binding) <> None) known.

Lemma known_of_binding_have_values (binding : static_binding) :
  all_have_values (known_of_binding binding).
Proof.
  destruct binding as [id c | id | s const]; simpl; try constructor.
  destruct (closed_static_const const); [ | constructor ].
  destruct (eval_static_const [] const) eqn:Hconst; constructor;
    [ simpl; congruence | constructor ].
Qed.

Fixpoint known_bindings_have_values (e : expr) {struct e} :
  all_have_values (known_bindings e)
with known_bindings_of_handler_have_values (h : continuation_handler)
    {struct h} :
  all_have_values (known_bindings_of_handler h).
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try constructor.
    + apply known_bindings_have_values.
    + apply Forall_app. split; [ | apply known_bindings_have_values ].
      induction bindings as [ | binding bindings IH]; simpl;
        [ constructor | ].
      apply Forall_app. split; [ apply known_of_binding_have_values | ].
      exact IH.
    + apply Forall_app.
      split;
        [ apply known_bindings_of_handler_have_values
        | apply known_bindings_have_values ].
    + apply Forall_app. split; [ | apply known_bindings_have_values ].
      induction handlers as [ | [k h] handlers IH]; simpl; [ constructor | ].
      apply Forall_app.
      split; [ apply known_bindings_of_handler_have_values | exact IH ].
  - destruct h as [params metadata handler]. simpl.
    apply known_bindings_have_values.
Qed.

Lemma set_of_binding_have_values (binding : static_binding) :
  all_have_values (set_of_binding binding).
Proof.
  destruct binding as [id c | id | s const]; try constructor.
  destruct const
    as [code slots | fslot syms decls slots | tag fields | contents | bytes].
  - unfold all_have_values, set_of_binding.
    constructor; [ discriminate | constructor ].
  - unfold all_have_values, set_of_binding. cbv zeta.
    destruct
      (eval_static_const [] (Static_const_closure_of_set fslot syms decls []))
      eqn:Hconst;
      constructor; [ | constructor ].
    cbn [snd]. rewrite Hconst. discriminate.
  - constructor.
  - constructor.
  - constructor.
Qed.

Fixpoint known_sets_have_values (e : expr) {struct e} :
  all_have_values (known_sets e)
with known_sets_of_handler_have_values (h : continuation_handler)
    {struct h} :
  all_have_values (known_sets_of_handler h).
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try constructor.
    + apply known_sets_have_values.
    + apply Forall_app. split; [ | apply known_sets_have_values ].
      induction bindings as [ | binding bindings IH]; simpl;
        [ constructor | ].
      apply Forall_app. split; [ apply set_of_binding_have_values | ].
      exact IH.
    + apply Forall_app.
      split;
        [ apply known_sets_of_handler_have_values
        | apply known_sets_have_values ].
    + apply Forall_app. split; [ | apply known_sets_have_values ].
      induction handlers as [ | [k h] handlers IH]; simpl; [ constructor | ].
      apply Forall_app.
      split; [ apply known_sets_of_handler_have_values | exact IH ].
  - destruct h as [params metadata handler]. simpl.
    apply known_sets_have_values.
Qed.

(* What [known_statics] binds a symbol to is the value of the constant
   that is known of it. *)
Lemma lookup_known_statics (known : list (symbol * static_const))
    (s : symbol) :
  all_have_values known ->
  lookup s (static_values (known_statics known))
  = match lookup s known with
    | Some const => eval_static_const [] const
    | None => None
    end.
Proof.
  unfold known_statics. simpl.
  induction 1 as [ | [s' const] known Hconst _ IH]; simpl; [ reflexivity | ].
  unfold known_value at 1. simpl in Hconst |- *.
  destruct (eval_static_const [] const) as [allocated | ] eqn:Heval;
    [ | contradiction Hconst; reflexivity ].
  simpl. destruct (Pos.eqb s s'); [ symmetry; exact Heval | exact IH ].
Qed.

(* ======================================================================== *)
(* The run of a unit                                                        *)
(* ======================================================================== *)

Section Unit.

Variable known : list (symbol * static_const).
Hypothesis Hknown : all_have_values known.
Variable sets : list (symbol * static_const).
Hypothesis Hsets : all_have_values sets.

Let S : static_env := known_statics known.
Let T : static_env := known_statics sets.

(* What the run has bound of the known symbols is what is known. *)
Definition agrees_known (run_statics : static_env) : Prop :=
  ∀ (s : symbol) (allocated allocated' : statically_allocated_value),
    lookup s (static_values S) = Some allocated ->
    lookup s (static_values run_statics) = Some allocated' ->
    allocated' = allocated.

(* What it has bound of the symbols of closures of sets are closures at
   the slots and of the sets that are known. *)
Definition agrees_sets (run_statics : static_env) : Prop :=
  ∀ (s : symbol) (allocated allocated' : statically_allocated_value),
    lookup s (static_values T) = Some allocated ->
    lookup s (static_values run_statics) = Some allocated' ->
    same_set allocated allocated'.

Definition agrees (run_statics : static_env) : Prop :=
  agrees_known run_statics ∧ agrees_sets run_statics.

Lemma eval_static_bindings_agrees_sets (vars : env)
    (bindings : list static_binding) :
  forallb (binding_bound_as known sets) bindings = true ->
  ∀ statics statics' : static_env,
    agrees_sets statics ->
    eval_static_bindings vars bindings statics = Some statics' ->
    agrees_sets statics'.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH]; simpl;
    intros Hbound statics statics' Hagrees.
  - intros [= <-]. exact Hagrees.
  - destruct (lookup id (static_code statics)); [ discriminate | ].
    apply IH; [ exact Hbound | ]. exact Hagrees.
  - apply IH; assumption.
  - apply andb_true_iff in Hbound as [Hsym Hbound].
    apply andb_true_iff in Hsym as [_ Hsym].
    destruct (lookup sym (static_values statics)); [ discriminate | ].
    destruct (eval_static_const vars const) as [made | ] eqn:Hmade; simpl;
      [ | discriminate ].
    apply IH; [ exact Hbound | ].
    intros s allocated allocated' Hs. simpl.
    destruct (Pos.eqb_spec s sym) as [-> | _];
      [ | exact (Hagrees s allocated allocated' Hs) ].
    intros [= <-]. unfold T in Hs.
    rewrite (lookup_known_statics sets sym Hsets) in Hs.
    destruct (lookup sym sets) as [expected | ]; [ | discriminate ].
    destruct const
      as [code slots | fslot syms decls slots | tag fields | contents
         | bytes];
      try discriminate.
    { cbn -[static_const_eq_dec] in Hsym.
      destruct
        (static_const_eq_dec (Static_const_set_of_closures code []) expected)
        as [<- | ];
        [ | discriminate ].
      simpl in Hs. injection Hs as <-. simpl in Hmade.
      destruct (eval_value_slots vars slots) as [vs | ]; simpl in Hmade;
        [ | discriminate ].
      injection Hmade as <-. reflexivity. }
    simpl in Hmade.
    destruct (lookup fslot decls) as [code | ] eqn:Hcode;
      cbn -[static_const_eq_dec] in Hsym, Hmade;
      [ | discriminate ].
    destruct
      (static_const_eq_dec (Static_const_closure_of_set fslot syms decls [])
         expected)
      as [<- | ];
      [ | discriminate ].
    simpl in Hs. rewrite Hcode in Hs. simpl in Hs. injection Hs as <-.
    destruct (eval_value_slots vars slots) as [vs | ]; simpl in Hmade;
      [ | discriminate ].
    injection Hmade as <-. simpl. auto.
Qed.

Lemma eval_static_bindings_agrees_known (vars : env)
    (bindings : list static_binding) :
  forallb (binding_bound_as known sets) bindings = true ->
  ∀ statics statics' : static_env,
    agrees_known statics ->
    eval_static_bindings vars bindings statics = Some statics' ->
    agrees_known statics'.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH]; simpl;
    intros Hbound statics statics' Hagrees.
  - intros [= <-]. exact Hagrees.
  - destruct (lookup id (static_code statics)); [ discriminate | ].
    apply IH; [ exact Hbound | ]. exact Hagrees.
  - apply IH; assumption.
  - apply andb_true_iff in Hbound as [Hsym Hbound].
    apply andb_true_iff in Hsym as [Hsym _].
    destruct (lookup sym (static_values statics)); [ discriminate | ].
    destruct (eval_static_const vars const) as [made | ] eqn:Hmade; simpl;
      [ | discriminate ].
    apply IH; [ exact Hbound | ].
    intros s allocated allocated' Hs. simpl.
    destruct (Pos.eqb_spec s sym) as [-> | _];
      [ | exact (Hagrees s allocated allocated' Hs) ].
    intros [= <-]. unfold S in Hs.
    rewrite (lookup_known_statics known sym Hknown) in Hs.
    destruct (lookup sym known) as [expected | ]; [ | discriminate ].
    apply andb_true_iff in Hsym as [Hclosed Heq].
    destruct (static_const_eq_dec const expected) as [<- | ];
      [ | discriminate ].
    rewrite (eval_closed_static_const vars const Hclosed) in Hmade.
    congruence.
Qed.

Lemma eval_static_bindings_agrees (vars : env)
    (bindings : list static_binding) :
  forallb (binding_bound_as known sets) bindings = true ->
  ∀ statics statics' : static_env,
    agrees statics ->
    eval_static_bindings vars bindings statics = Some statics' ->
    agrees statics'.
Proof.
  intros Hbound statics statics' [Hknown_agrees Hsets_agrees] Heval.
  split;
    [ exact (eval_static_bindings_agrees_known vars bindings Hbound statics
               statics' Hknown_agrees Heval)
    | exact (eval_static_bindings_agrees_sets vars bindings Hbound statics
               statics' Hsets_agrees Heval) ].
Qed.

(* The second state: the first with its terms folded. *)
Definition fold_statics (statics : static_env) : static_env :=
  Static_env
    (map (fun binding => (fst binding, fold_known_code S T (snd binding)))
       (static_code statics))
    (static_values statics).

Fixpoint fold_cont (c : cont_value) : cont_value :=
  match c with
  | Closure h vars conts recursive =>
    Closure (fold_known_handler S T h) vars
      (map (fun binding => (fst binding, fold_cont (snd binding))) conts)
      (map (fun '(k, h) => (k, fold_known_handler S T h)) recursive)
  | Outer k => Outer k
  | Extra_args c extra => Extra_args (fold_cont c) extra
  | Over_application remaining remaining_arity return_arity return_to exn_to =>
    Over_application remaining remaining_arity return_arity
      (fold_cont return_to) (fold_cont exn_to)
  end.

Definition fold_conts (conts : cont_env) : cont_env :=
  map (fun binding => (fst binding, fold_cont (snd binding))) conts.

Definition fold_state (s : state) : state :=
  State (fold_known S T (state_expr s)) (state_vars s)
    (fold_conts (state_conts s)) (fold_statics (state_statics s)).

Lemma lookup_fold_code (id : code_id) (statics : static_env) :
  lookup id (static_code (fold_statics statics))
  = option_map (fold_known_code S T) (lookup id (static_code statics)).
Proof. unfold fold_statics. apply lookup_map_snd. Qed.

(* The value of a defining expression does not depend on the code. *)
Lemma eval_named_fold_statics (statics : static_env) (vars : env)
    (d : named) :
  eval_named (fold_statics statics) vars d = eval_named statics vars d.
Proof.
  destruct d; simpl; try reflexivity.
  all:
    destruct (eval_simples vars args) as [vs | ]; simpl; [ | reflexivity ];
    apply eval_prim_static_values; intros s _; reflexivity.
Qed.

Lemma eval_static_bindings_fold (vars : env)
    (bindings : list static_binding) :
  ∀ statics statics' : static_env,
    eval_static_bindings vars bindings statics = Some statics' ->
    eval_static_bindings vars (map (fold_known_binding S T) bindings)
      (fold_statics statics)
    = Some (fold_statics statics').
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH];
    intros statics statics'; simpl.
  - intros [= <-]. reflexivity.
  - rewrite lookup_map_snd.
    destruct (lookup id (static_code statics)); simpl; [ discriminate | ].
    intros H. exact (IH _ _ H).
  - apply IH.
  - destruct (lookup sym (static_values statics)); simpl; [ discriminate | ].
    destruct (eval_static_const vars const) as [allocated | ]; simpl;
      [ | discriminate ].
    intros H. exact (IH _ _ H).
Qed.

(* The rewrite keeps whether a term binds something static. *)
Fixpoint fold_known_binds_statics (e : expr) {struct e} :
  binds_statics (fold_known S T e) = binds_statics e
with fold_known_handler_binds_statics (h : continuation_handler)
    {struct h} :
  handler_binds_statics (fold_known_handler S T h) = handler_binds_statics h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + apply fold_known_binds_statics.
    + rewrite fold_known_binds_statics. f_equal.
      induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
      rewrite IH. destruct binding; reflexivity.
    + rewrite fold_known_handler_binds_statics, fold_known_binds_statics.
      reflexivity.
    + rewrite fold_known_binds_statics. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite fold_known_handler_binds_statics, IH. reflexivity.
  - destruct h as [params metadata handler]. simpl.
    apply fold_known_binds_statics.
Qed.

Lemma fold_known_handlers_bind_statics
    (handlers : list (continuation * continuation_handler)) :
  handlers_bind_statics
    (map (fun '(k, h) => (k, fold_known_handler S T h)) handlers)
  = handlers_bind_statics handlers.
Proof.
  unfold handlers_bind_statics.
  induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
  rewrite fold_known_handler_binds_statics, IH. reflexivity.
Qed.

Lemma resolve_fold (k : continuation) (conts : cont_env) :
  resolve k (fold_conts conts) = fold_cont (resolve k conts).
Proof.
  unfold resolve, fold_conts. rewrite lookup_map_snd.
  destruct (lookup k conts); reflexivity.
Qed.

Lemma rec_closures_fold
    (handlers : list (continuation * continuation_handler)) (vars : env)
    (conts : cont_env) :
  rec_closures (map (fun '(k, h) => (k, fold_known_handler S T h)) handlers)
    vars (fold_conts conts)
  = fold_conts (rec_closures handlers vars conts).
Proof.
  unfold rec_closures, fold_conts. rewrite !map_map.
  apply map_ext. intros [k h]. reflexivity.
Qed.

Lemma with_extra_args_fold (c : cont_value) (extra : list value) :
  fold_cont (with_extra_args c extra) = with_extra_args (fold_cont c) extra.
Proof. destruct extra; reflexivity. Qed.

Lemma fold_known_code_parts (c : code) :
  code_params (fold_known_code S T c) = code_params c
  ∧ code_my_closure (fold_known_code S T c) = code_my_closure c
  ∧ code_return_continuation (fold_known_code S T c)
    = code_return_continuation c
  ∧ code_exn_continuation (fold_known_code S T c) = code_exn_continuation c
  ∧ code_params_arity (fold_known_code S T c) = code_params_arity c
  ∧ code_result_arity (fold_known_code S T c) = code_result_arity c
  ∧ code_body (fold_known_code S T c) = fold_known S T (code_body c).
Proof. destruct c. simpl. auto 8. Qed.

(* What the second run does where the first does something: the same
   step, to the second state of the result, or the same exit. *)
Definition result_folded (result result' : step_result) : Prop :=
  match result with
  | Step t => result' = Step (fold_state t)
  | Exit k vs => result' = Exit k vs
  | Undefined => True
  end.

(* A call of the second run has the shape of the call of the first,
   with the same values, of the code folded. *)
Definition fold_shape (shape : call_shape) : call_shape :=
  match shape with
  | Full_call closure c vs args_arity =>
    Full_call closure (fold_known_code S T c) vs args_arity
  | Over_call closure c vs remaining args_arity remaining_arity =>
    Over_call closure (fold_known_code S T c) vs remaining args_arity
      remaining_arity
  | Partial_call partial => Partial_call partial
  end.

Lemma shape_of_closure_call_fold (statics : static_env) (closure : value)
    (kind : call_kind) (vs : list value) (args_arity return_arity : arity)
    (shape : call_shape) :
  shape_of_closure_call statics closure kind vs args_arity return_arity
  = Some shape ->
  shape_of_closure_call (fold_statics statics) closure kind vs args_arity
    return_arity
  = Some (fold_shape shape).
Proof.
  unfold shape_of_closure_call.
  change (closure_of (fold_statics statics) closure)
    with (closure_of statics closure).
  destruct (closure_of statics closure) as [[called slots] | ];
    [ | discriminate ].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | discriminate ].
  rewrite lookup_fold_code.
  destruct (lookup called (static_code statics)) as [c | ]; [ | discriminate ].
  simpl option_map. cbv iota zeta.
  destruct (fold_known_code_parts c)
    as (_ & _ & _ & _ & Hparams_arity & Hresult_arity & _).
  assert (Htupled : code_is_tupled (fold_known_code S T c) = code_is_tupled c)
    by (destruct c; reflexivity).
  destruct (arguments_for_code statics c vs args_arity)
    as [[vs' args_arity'] | ] eqn:Hargs; [ | discriminate ].
  rewrite (arguments_for_code_mono statics (fold_statics statics) c
             (fold_known_code S T c) vs args_arity _ Htupled Hparams_arity
             (fun tuple rest p v _ Hp =>
                eq_trans
                  (eq_sym
                     (eval_prim_same_static_values statics
                        (fold_statics statics) p [tuple] eq_refl))
                  Hp)
             Hargs).
  simpl. unfold shape_of_code_call. cbv zeta.
  rewrite Hparams_arity, Hresult_arity, Htupled.
  destruct (Nat.eqb (length args_arity') (length (code_params_arity c)));
    [ intros [= <-]; reflexivity | ].
  destruct
    (negb
       (kinds_eqb (map kind_of_value vs') (unarize args_arity')
        && partial_or_over_application args_arity' return_arity
             (code_params_arity c) (code_result_arity c)));
    [ discriminate | ].
  destruct (Nat.ltb (length (code_params_arity c)) (length args_arity'));
    [ intros [= <-]; reflexivity | ].
  destruct (code_is_tupled c); [ discriminate | ].
  intros [= <-]. reflexivity.
Qed.

Lemma shape_of_call_fold (statics : static_env) (callee : value)
    (kind : call_kind) (vs : list value) (args_arity return_arity : arity)
    (shape : call_shape) :
  shape_of_call statics callee kind vs args_arity return_arity = Some shape ->
  shape_of_call (fold_statics statics) callee kind vs args_arity return_arity
  = Some (fold_shape shape).
Proof.
  unfold shape_of_call.
  destruct kind as [named | ]; [ apply shape_of_closure_call_fold | ].
  destruct (partial_application_of callee)
    as [[[closure applied] applied_arity] | ];
    [ | apply shape_of_closure_call_fold ].
  destruct args_arity as [ | component args_arity]; [ discriminate | ].
  destruct (kinds_eqb _ _); [ | discriminate ].
  apply shape_of_closure_call_fold.
Qed.

(* A full call. *)
Lemma call_code_fold (closure : value) (c : code) (vs : list value)
    (args_arity return_arity : arity) (return_to exn_to : cont_value)
    (statics : static_env) :
  result_folded
    (call_code closure c vs args_arity return_arity return_to exn_to statics)
    (call_code closure (fold_known_code S T c) vs args_arity return_arity
       (fold_cont return_to) (fold_cont exn_to) (fold_statics statics)).
Proof.
  unfold result_folded, call_code.
  destruct (fold_known_code_parts c)
    as (Hparams & Hmy_closure & Hret & Hexn & Hparams_arity & Hresult_arity
        & Hbody).
  rewrite Hparams, Hmy_closure, Hret, Hexn, Hbody, fold_known_binds_statics.
  destruct (binds_statics (code_body c)); [ exact I | ].
  rewrite Hparams_arity, Hresult_arity.
  match goal with
  | |- context [negb ?agrees] => destruct (negb agrees)
  end;
    [ exact I | ].
  destruct (bind_params (code_params c) vs [(code_my_closure c, closure)]);
    [ | exact I ].
  reflexivity.
Qed.

(* A call of a given shape, given what the two runs do with a partial
   application. *)
Lemma run_call_fold (return_partial return_partial' : value -> step_result)
    (shape : call_shape) (return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) :
  (∀ partial : value,
    result_folded (return_partial partial) (return_partial' partial)) ->
  result_folded
    (run_call return_partial (Some shape) return_arity return_to exn_to
       statics)
    (run_call return_partial' (Some (fold_shape shape)) return_arity
       (fold_cont return_to) (fold_cont exn_to) (fold_statics statics)).
Proof.
  intros Hpartial.
  destruct shape
    as [closure c vs args_arity
       | closure c vs remaining args_arity remaining_arity | partial];
    simpl.
  - apply call_code_fold.
  - destruct (fold_known_code_parts c) as (_ & _ & _ & _ & _ & -> & _).
    exact (call_code_fold closure c vs args_arity (code_result_arity c)
             (Over_application remaining remaining_arity return_arity
                return_to exn_to)
             exn_to statics).
  - apply Hpartial.
Qed.

(* A call, given what the two runs do when the return continuation is
   applied to a partial application. *)
Lemma call_function_fold_from (callee : value) (kind : call_kind)
    (vs : list value) (args_arity return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) :
  (∀ partial : value,
    result_folded (apply_cont_value return_to [partial] statics)
      (apply_cont_value (fold_cont return_to) [partial]
         (fold_statics statics))) ->
  result_folded
    (call_function callee kind vs args_arity return_arity return_to exn_to
       statics)
    (call_function callee kind vs args_arity return_arity
       (fold_cont return_to) (fold_cont exn_to) (fold_statics statics)).
Proof.
  intros Hpartial. unfold call_function.
  destruct (shape_of_call statics callee kind vs args_arity return_arity)
    as [shape | ] eqn:Hshape;
    [ | exact I ].
  rewrite (shape_of_call_fold statics callee kind vs args_arity return_arity
             shape Hshape).
  apply run_call_fold. exact Hpartial.
Qed.

Lemma apply_cont_value_fold (c : cont_value) :
  ∀ (vs : list value) (statics : static_env),
    result_folded (apply_cont_value c vs statics)
      (apply_cont_value (fold_cont c) vs (fold_statics statics)).
Proof.
  induction c
    as [[params metadata handler] def_vars def_conts recursive | k
       | c IH extra
       | remaining remaining_arity return_arity return_to exn_to IHreturn _]
    using cont_value_over_ind;
    intros vs statics.
  - unfold result_folded. simpl.
    destruct (kinds_eqb (map kind_of_value vs) (hm_params_kinds metadata));
      [ | exact I ].
    destruct (bind_params params vs def_vars) as [handler_vars | ];
      [ | exact I ].
    unfold fold_state. simpl_state. f_equal. f_equal.
    fold (fold_conts def_conts). rewrite rec_closures_fold.
    unfold fold_conts. rewrite map_app. reflexivity.
  - reflexivity.
  - apply IH.
  - simpl fold_cont. rewrite !apply_cont_value_over_application.
    destruct vs as [ | v [ | v' vs]]; [ exact I | | exact I ].
    apply call_function_fold_from. intros partial. apply IHreturn.
Qed.

Lemma call_function_fold (callee : value) (kind : call_kind)
    (vs : list value) (args_arity return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) :
  result_folded
    (call_function callee kind vs args_arity return_arity return_to exn_to
       statics)
    (call_function callee kind vs args_arity return_arity
       (fold_cont return_to) (fold_cont exn_to) (fold_statics statics)).
Proof.
  apply call_function_fold_from. intros partial. apply apply_cont_value_fold.
Qed.

(* A step of a state that binds the known symbols as is known, and has
   bound them so, is a step of the second state, to the second state of
   the result, which has bound them so too. *)
Lemma fold_step_components (e : expr) (vars : env) (conts : cont_env)
    (statics : static_env) :
  bound_as known sets e = true ->
  agrees statics ->
  match step (State e vars conts statics) with
  | Step t =>
    step
      (State (fold_known S T e) vars (fold_conts conts) (fold_statics statics))
    = Step (fold_state t)
    ∧ agrees (state_statics t)
  | Exit k vs =>
    step
      (State (fold_known S T e) vars (fold_conts conts) (fold_statics statics))
    = Exit k vs
  | Undefined => True
  end.
Proof.
  intros Hbound Hagrees.
  destruct e
    as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl fold_known;
    try
      rewrite
        (fold_known_apply_sound_here T (fold_statics statics) (proj2 Hagrees));
    autorewrite with step.
  - (* Let *)
    destruct (eval_named statics vars d) as [v | ] eqn:Hv; [ | exact I ].
    destruct (kind_eqb (kind_of_value v) xkind) eqn:Hkind; [ | exact I ].
    rewrite eval_named_fold_statics.
    rewrite (fold_function_slot_sound_here T statics (proj2 Hagrees) vars _ v
               (fold_known_named_sound_here S statics (proj1 Hagrees) vars d
                  v Hv)),
      Hkind.
    split; [ reflexivity | exact Hagrees ].
  - (* Let_static *)
    simpl in Hbound. apply andb_true_iff in Hbound as [Hbound _].
    apply andb_true_iff in Hbound as [Hbindings _].
    destruct (eval_static_bindings vars bindings statics) as [statics' | ]
      eqn:Heval; [ | exact I ].
    rewrite (eval_static_bindings_fold vars bindings statics statics' Heval).
    split; [ reflexivity | ].
    exact (eval_static_bindings_agrees vars bindings Hbindings statics
             statics' Hagrees Heval).
  - (* Let_cont_non_recursive *)
    split; [ reflexivity | exact Hagrees ].
  - (* Let_cont_recursive *)
    rewrite fold_known_handlers_bind_statics.
    destruct (handlers_bind_statics handlers); [ exact I | ].
    split; [ | exact Hagrees ].
    unfold fold_state. simpl_state. rewrite rec_closures_fold.
    unfold fold_conts. rewrite map_app. reflexivity.
  - (* Apply *)
    destruct (eval_simple vars (ap_callee ap)) as [callee | ]; [ | exact I ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | exact I ].
    destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ];
      [ | exact I ].
    rewrite !resolve_fold, <- with_extra_args_fold.
    pose proof
      (call_function_fold callee (ap_call_kind ap) vs (ap_args_arity ap)
         (ap_return_arity ap) (resolve (ap_continuation ap) conts)
         (with_extra_args (resolve (ap_exn_continuation ap) conts) extra)
         statics)
      as Hcall.
    destruct (call_function callee (ap_call_kind ap) vs (ap_args_arity ap)
                (ap_return_arity ap) (resolve (ap_continuation ap) conts)
                (with_extra_args (resolve (ap_exn_continuation ap) conts)
                   extra)
                statics)
      as [t | k exit_vs | ] eqn:Hstep;
      [ | exact Hcall | exact I ].
    split; [ exact Hcall | ].
    rewrite (call_function_statics _ _ _ _ _ _ _ _ t Hstep). exact Hagrees.
  - (* Apply_cont *)
    destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | exact I ].
    unfold apply_continuation. rewrite resolve_fold.
    pose proof
      (apply_cont_value_fold (resolve (ac_continuation ac) conts) vs statics)
      as Happly.
    destruct (apply_cont_value (resolve (ac_continuation ac) conts) vs statics)
      as [t | | ] eqn:Hstep;
      [ | exact Happly | exact I ].
    split; [ exact Happly | ].
    rewrite (apply_cont_value_statics _ _ _ t Hstep). exact Hagrees.
  - (* Switch *)
    destruct (eval_simple vars scrutinee) as [v | ]; [ | exact I ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
    destruct (find_arm i arms) as [ac | ]; [ | exact I ].
    split; [ reflexivity | exact Hagrees ].
  - exact I.
Qed.

(* The terms of a state bind the known symbols as is known. *)
Definition bound_as_inv : state -> Prop :=
  terms_inv (bound_as known sets) (handler_bound_as known sets)
    (code_bound_as known sets).

Lemma bound_as_inv_step (s s' : state) :
  bound_as_inv s -> step s = Step s' -> bound_as_inv s'.
Proof.
  apply terms_inv_step.
  - intros x xkind d body H. exact H.
  - intros bindings body H. simpl in H.
    apply andb_true_iff in H as [H Hbody].
    apply andb_true_iff in H as [_ Hcode].
    split; [ exact Hbody | ]. intros id c Hin.
    exact (proj1 (forallb_forall _ _) Hcode (Bind_code id c) Hin).
  - intros k h body H. simpl in H. apply andb_true_iff in H. tauto.
  - intros handlers body H. simpl in H. apply andb_true_iff in H. tauto.
  - intros ac. reflexivity.
  - intros params metadata handler H. exact H.
  - intros [params my_closure ret exn metadata body] H. exact H.
Qed.

Definition folded_related (s s' : state) : Prop :=
  s' = fold_state s ∧ bound_as_inv s ∧ agrees (state_statics s).

Lemma folded_related_step (s s' : state) :
  folded_related s s' -> result_simulated folded_related (step s) (step s').
Proof.
  intros (-> & Hinv & Hagrees).
  pose proof
    (fold_step_components (state_expr s) (state_vars s) (state_conts s)
       (state_statics s) (proj1 Hinv) Hagrees)
    as Hstep.
  rewrite <- (state_eta s) in Hstep.
  pose proof (bound_as_inv_step s) as Hkept.
  unfold fold_state at 1.
  destruct (step s) as [t | k vs | ]; simpl; [ | | exact I ].
  - destruct Hstep as [Hstep Ht]. rewrite Hstep. simpl.
    split; [ reflexivity | ]. split; [ exact (Hkept t Hinv eq_refl) | ].
    exact Ht.
  - rewrite Hstep. simpl. auto.
Qed.

End Unit.

Theorem fold_known_unit_program_refines :
  fold_known_unit_program_refines_statement.
Proof.
  intros e e'. unfold fold_known_unit. cbv zeta.
  destruct (bound_as (known_bindings e) (known_sets e) e) eqn:Hbound;
    [ | discriminate ].
  intros [= <-]. unfold program_refines.
  apply (simulation_refines
           (folded_related (known_bindings e) (known_sets e))
           (folded_related_step (known_bindings e)
              (known_bindings_have_values e) (known_sets e)
              (known_sets_have_values e))).
  split; [ reflexivity | ].
  split; [ apply terms_inv_initial; exact Hbound | ].
  split; intros s allocated allocated' _ [=].
Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

Lemma rename_known_simple (r : renaming) (statics : static_env) (s : simple) :
  simple_known statics s = true -> rename_simple r s = s.
Proof. destruct s; simpl; [ discriminate | reflexivity | reflexivity ]. Qed.

Lemma simple_known_rename (r : renaming) (statics : static_env) (s : simple) :
  simple_known statics (rename_simple r s) = simple_known statics s.
Proof. destruct s; reflexivity. Qed.

Lemma named_known_rename (r : renaming) (statics : static_env) (d : named) :
  named_known statics (rename_named r d) = named_known statics d.
Proof.
  destruct d; simpl; try reflexivity; try apply simple_known_rename.
  f_equal. induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite simple_known_rename, IH. reflexivity.
Qed.

Lemma rename_known_named (r : renaming) (statics : static_env) (d : named) :
  named_known statics d = true -> rename_named r d = d.
Proof.
  destruct d; simpl; try discriminate.
  - intros H. apply andb_true_iff in H as [_ Hargs]. f_equal.
    induction args as [ | s args IH]; simpl; [ reflexivity | ].
    simpl in Hargs. apply andb_true_iff in Hargs as [Hs Hargs].
    rewrite (rename_known_simple r statics s Hs), (IH Hargs). reflexivity.
  - intros H. rewrite (rename_known_simple r statics _ H). reflexivity.
  - intros H. rewrite (rename_known_simple r statics _ H). reflexivity.
  - intros H. rewrite (rename_known_simple r statics _ H). reflexivity.
Qed.

Lemma fold_known_named_rename (r : renaming) (statics : static_env)
    (d : named) :
  rename_named r (fold_known_named statics d)
  = fold_known_named statics (rename_named r d).
Proof.
  unfold fold_known_named. rewrite named_known_rename.
  destruct (named_known statics d) eqn:Hknown; [ | reflexivity ].
  rewrite (rename_known_named r statics d Hknown).
  destruct (eval_named statics [] d) as [[] | ]; try reflexivity;
    exact (rename_known_named r statics d Hknown).
Qed.

(* The projection of a function slot that is folded is from a symbol. *)
Lemma fold_function_slot_rename (r : renaming) (sets : static_env)
    (d : named) :
  rename_named r (fold_function_slot sets d)
  = fold_function_slot sets (rename_named r d).
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    try reflexivity.
  destruct closure as [x | s | c]; try reflexivity.
  unfold fold_function_slot. cbn [rename_named rename_simple].
  destruct (eval_named sets [] _) as [w | ]; [ | reflexivity ].
  destruct w; reflexivity.
Qed.

Lemma fold_known_apply_rename (r : renaming) (sets : static_env)
    (ap : apply_expr) :
  rename_apply r (fold_known_apply sets ap)
  = fold_known_apply sets (rename_apply r ap).
Proof.
  unfold fold_known_apply.
  replace (ap_call_kind (rename_apply r ap)) with (ap_call_kind ap)
    by reflexivity.
  replace (ap_callee (rename_apply r ap))
    with (rename_simple r (ap_callee ap)) by reflexivity.
  destruct (ap_call_kind ap) as [named | ]; [ reflexivity | ].
  destruct (ap_callee ap) as [x | s | c]; try reflexivity.
  cbn [rename_simple].
  destruct (closure_of sets (Value_symbol s)) as [[code slots] | ];
    reflexivity.
Qed.

Fixpoint fold_known_rename (r : renaming) (statics sets : static_env)
    (e : expr) {struct e} :
  rename_expr r (fold_known statics sets e)
  = fold_known statics sets (rename_expr r e)
with fold_known_handler_rename (r : renaming) (statics sets : static_env)
    (h : continuation_handler) {struct h} :
  rename_handler r (fold_known_handler statics sets h)
  = fold_known_handler statics sets (rename_handler r h)
with fold_known_binding_rename (r : renaming) (statics sets : static_env)
    (binding : static_binding) {struct binding} :
  rename_static_binding r (fold_known_binding statics sets binding)
  = fold_known_binding statics sets (rename_static_binding r binding)
with fold_known_code_rename (r : renaming) (statics sets : static_env)
    (c : code) {struct c} :
  rename_code r (fold_known_code statics sets c)
  = fold_known_code statics sets (rename_code r c).
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite fold_function_slot_rename, fold_known_named_rename,
        fold_known_rename.
      reflexivity.
    + rewrite fold_known_rename. f_equal. rewrite !map_map.
      induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
      rewrite fold_known_binding_rename, IH. reflexivity.
    + rewrite fold_known_handler_rename, fold_known_rename. reflexivity.
    + rewrite fold_known_rename. f_equal. rewrite !map_map.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite fold_known_handler_rename, IH. reflexivity.
    + rewrite fold_known_apply_rename. reflexivity.
  - destruct h as [params metadata handler]. simpl. rewrite fold_known_rename.
    reflexivity.
  - destruct binding as [id c | id | sym const]; simpl; try reflexivity.
    rewrite fold_known_code_rename. reflexivity.
  - destruct c as [params my_closure ret exn metadata body]. simpl.
    rewrite fold_known_rename. reflexivity.
Qed.

Theorem fold_known_equivariant : fold_known_equivariant_statement.
Proof. exact fold_known_rename. Qed.
