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

(* Proofs of the statements of FlambdaEnvAliasesFollowSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec FlambdaMapProofs
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaContextProofs
  FlambdaNormaliseSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesProofs
  FlambdaEnvAliasesRenamingSpec FlambdaEnvAliasesRenamingProofs
  FlambdaEnvAliasesFollowSpec.
Import ListNotations.

(* ======================================================================== *)
(* Binding a variable that is not mentioned                                 *)
(* ======================================================================== *)

Lemma eval_simple_bind (vars : env) (x : variable) (v : value) (s : simple) :
  var_in_simple x s = false ->
  eval_simple ((x, v) :: vars) s = eval_simple vars s.
Proof.
  destruct s as [y | sym | c]; simpl; try reflexivity.
  intros Hx. rewrite Pos.eqb_sym, Hx. reflexivity.
Qed.

Lemma eval_value_slots_bind (vars : env) (x : variable) (v : value)
    (slots : list (value_slot * simple)) :
  var_in_value_slots x slots = false ->
  eval_value_slots ((x, v) :: vars) slots = eval_value_slots vars slots.
Proof.
  unfold var_in_value_slots.
  induction slots as [ | [slot s] slots IH]; simpl; [ reflexivity | ].
  intros Hx. apply orb_false_iff in Hx. destruct Hx as [Hs Hslots].
  rewrite (eval_simple_bind vars x v s Hs), (IH Hslots). reflexivity.
Qed.

Lemma fold_left_invariant {A B : Type} (P : A -> Prop) (f : A -> B -> A)
    (l : list B) :
  ∀ init : A,
    P init ->
    (∀ (a : A) (b : B), b ∈ l -> P a -> P (f a b)) ->
    P (List.fold_left f l init).
Proof.
  induction l as [ | b l IH]; intros init Hinit Hstep; simpl;
    [ exact Hinit | ].
  apply IH; [ apply Hstep; [ left; reflexivity | exact Hinit ] | ].
  intros a b' Hin. apply Hstep. right. exact Hin.
Qed.

(* ======================================================================== *)
(* The aliases                                                              *)
(* ======================================================================== *)

Lemma empty_unmentioned (n : name) : ~ aliases_mention Aliases.empty n.
Proof.
  intros [[c H] | [[n' H] | [[c H] | [n' H]]]].
  - discriminate H.
  - discriminate H.
  - unfold listed_alias in H. destruct c; discriminate H.
  - unfold listed_alias in H. destruct n; discriminate H.
Qed.

(* The canonical element of a simple, if it is a name, is the simple or
   a name that the structure speaks of. *)
Lemma mentioned_canonical_element_of (t : Aliases.t) (e : simple) (n : name) :
  canonical_element_of t e = simple_of_name n ->
  aliases_mention t n ∨ simple_of_name n = e.
Proof.
  intros Hcanonical.
  destruct (canonical_cases t e)
    as [[_ Heq] | (n' & c & -> & Hdemoted & _ & Heq)].
  - right. rewrite <- Hcanonical. exact Heq.
  - left. right. left. exists n'. rewrite Heq in Hcanonical. subst c.
    exact Hdemoted.
Qed.

Lemma add_equal_respected
    (binding_times
      : Keyed.finite_map name (unit * Binding_time.With_name_mode.t))
    (t : Aliases.t) (vars : env) (e e' : simple) :
  aliases_respected t vars ->
  eval_simple vars e = eval_simple vars e' ->
  aliases_respected (Known.add_equal binding_times t e e') vars.
Proof.
  intros Hrespected Hvalues. unfold Known.add_equal.
  destruct (simple_equal _ _); [ exact Hrespected | ].
  destruct (Aliases.add _ _ t _ _) as [[result | ] | ] eqn:Hadd;
    try exact Hrespected.
  apply (add_respected unit Known.binding_time_resolver binding_times t _ _
    result vars Hadd Hrespected).
  rewrite !(respected_canonical_element_of t vars _ Hrespected).
  exact Hvalues.
Qed.

Lemma add_equal_mentioned
    (binding_times
      : Keyed.finite_map name (unit * Binding_time.With_name_mode.t))
    (t : Aliases.t) (e e' : simple) (n : name) :
  aliases_mention (Known.add_equal binding_times t e e') n ->
  aliases_mention t n ∨ simple_of_name n = e ∨ simple_of_name n = e'.
Proof.
  unfold Known.add_equal.
  destruct (simple_equal _ _); [ auto | ].
  destruct (Aliases.add _ _ t _ _) as [[result | ] | ] eqn:Hadd; auto.
  intros Hmentioned.
  destruct (add_mentioned unit Known.binding_time_resolver binding_times t _
              _ result n Hadd Hmentioned)
    as [H | [H | H]]; [ auto | | ].
  - destruct (mentioned_canonical_element_of t e n (eq_sym H)); auto.
  - destruct (mentioned_canonical_element_of t e' n (eq_sym H)); auto.
Qed.

Lemma not_the_variable (n : name) (x : variable) :
  negb (name_eqb n (Name_var x)) = true -> Var x <> simple_of_name n.
Proof.
  intros Hn Heq. apply (simple_of_name_inj (Name_var x) n) in Heq. subst n.
  rewrite name_eqb_refl in Hn. discriminate Hn.
Qed.

(* Forgetting a variable: the same environment respects what is left. *)
Lemma forget_in_aliases_respected
    (binding_times
      : Keyed.finite_map name (unit * Binding_time.With_name_mode.t))
    (t : Aliases.t) (vars : env) (x : variable) :
  aliases_respected t vars ->
  aliases_respected (Known.forget_in_aliases binding_times t x) vars.
Proof.
  intros Hrespected. unfold Known.forget_in_aliases.
  destruct (negb _); [ exact Hrespected | ]. cbv zeta.
  apply fold_left_invariant; [ apply empty_respected | ].
  intros rebuilt n Hin Hrebuilt.
  assert (Hn :
    eval_simple vars (simple_of_name n)
    = eval_simple vars (Aliases.get_canonical_ignoring_name_mode t n)).
  { symmetry. exact (respected_canonical t vars n Hrespected). }
  destruct (simple_equal (Aliases.get_canonical_ignoring_name_mode t n)
              (Var x)) eqn:Hx.
  - destruct (find _ _) as [n' | ] eqn:Hfind; [ | exact Hrebuilt ].
    apply find_some in Hfind. destruct Hfind as [_ Hx'].
    apply add_equal_respected; [ exact Hrebuilt | ].
    apply simple_equal_eq in Hx. apply simple_equal_eq in Hx'.
    rewrite Hn, Hx, <- Hx'.
    exact (respected_canonical t vars n' Hrespected).
  - apply add_equal_respected; assumption.
Qed.

(* ... and what is left does not speak of the variable. *)
Lemma forget_in_aliases_unmentioned
    (binding_times
      : Keyed.finite_map name (unit * Binding_time.With_name_mode.t))
    (t : Aliases.t) (x : variable) :
  ~ aliases_mention (Known.forget_in_aliases binding_times t x) (Name_var x).
Proof.
  unfold Known.forget_in_aliases.
  destruct (among x (aliases_free_variables t)) eqn:Hamong; cbn [negb].
  2: { intros Hmentioned. apply (mentioned_free t x) in Hmentioned.
       congruence. }
  cbv zeta. apply fold_left_invariant; [ apply empty_unmentioned | ].
  intros rebuilt n Hin Hrebuilt.
  apply filter_In in Hin. destruct Hin as [_ Hn].
  destruct (simple_equal (Aliases.get_canonical_ignoring_name_mode t n)
              (Var x)) eqn:Hx.
  - destruct (find _ _) as [n' | ] eqn:Hfind; [ | exact Hrebuilt ].
    apply find_some in Hfind. destruct Hfind as [Hin' _].
    apply filter_In in Hin'. destruct Hin' as [_ Hn'].
    intros Hmentioned. apply add_equal_mentioned in Hmentioned.
    destruct Hmentioned as [H | [H | H]]; [ exact (Hrebuilt H) | | ].
    + exact (not_the_variable n x Hn H).
    + exact (not_the_variable n' x Hn' H).
  - intros Hmentioned. apply add_equal_mentioned in Hmentioned.
    destruct Hmentioned as [H | [H | H]]; [ exact (Hrebuilt H) | | ].
    + exact (not_the_variable n x Hn H).
    + simpl in H. rewrite <- H in Hx. simpl in Hx.
      rewrite Pos.eqb_refl in Hx. discriminate Hx.
Qed.

(* ======================================================================== *)
(* What is known, under binders                                             *)
(* ======================================================================== *)

Theorem empty_known_respected : empty_known_respected_statement.
Proof.
  intros vars. split; [ apply empty_respected | intros x c [] ].
Qed.

Lemma canonical_simple_sound (known : Known.t) (vars : env) (s : simple) :
  known_respected known vars ->
  eval_simple vars (Known.canonical_simple known s) = eval_simple vars s.
Proof.
  intros [Haliases _].
  exact (respected_canonical_element_of _ vars s Haliases).
Qed.

Theorem canonical_simple_respected : canonical_simple_respected_statement.
Proof. exact canonical_simple_sound. Qed.

Lemma closure_respected_bind (vars : env) (x : variable) (v : value)
    (y : variable) (c : Known.closure) :
  closure_respected vars y c ->
  Pos.eqb x y = false ->
  var_in_value_slots x (Known.closure_value_slots c) = false ->
  closure_respected ((x, v) :: vars) y c.
Proof.
  intros [Hcode (slot_values & Hslots & Hlookup)] Hxy Hfree.
  split; [ exact Hcode | ]. exists slot_values. split.
  - rewrite eval_value_slots_bind; assumption.
  - simpl. rewrite Pos.eqb_sym, Hxy. exact Hlookup.
Qed.

Lemma in_closures_forget (known : Known.t) (x y : variable)
    (c : Known.closure) :
  (y, c) ∈ Known.closures (Known.forget known x) ->
  (y, c) ∈ Known.closures known
  ∧ Pos.eqb x y = false
  ∧ var_in_value_slots x (Known.closure_value_slots c) = false.
Proof.
  unfold Known.forget. cbn [Known.closures]. intros Hin.
  apply filter_In in Hin. destruct Hin as [Hin Hkept]. simpl in Hkept.
  apply andb_true_iff in Hkept. destruct Hkept as [Hxy Hfree].
  apply negb_true_iff in Hxy. apply negb_true_iff in Hfree. auto.
Qed.

Theorem forget_respected : forget_respected_statement.
Proof.
  intros known vars x v [Haliases Hclosures]. split.
  - unfold Known.forget. cbn [Known.aliases].
    apply (respected_coincide
      (Known.forget_in_aliases (Known.binding_times known)
         (Known.aliases known) x)
      vars ((x, v) :: vars));
      [ | apply forget_in_aliases_respected, Haliases ].
    intros n Hmentioned. destruct n as [y | sym]; [ | reflexivity ].
    unfold value_of_name. simpl.
    destruct (Pos.eqb_spec y x) as [-> | _]; [ | reflexivity ].
    exfalso. exact (forget_in_aliases_unmentioned _ _ _ Hmentioned).
  - intros y c Hin.
    destruct (in_closures_forget known x y c Hin) as (Hin' & Hxy & Hfree).
    apply closure_respected_bind;
      [ exact (Hclosures y c Hin') | exact Hxy | exact Hfree ].
Qed.

Theorem bind_respected : bind_respected_statement.
Proof.
  intros known vars x v Hrespected.
  exact (forget_respected known vars x v Hrespected).
Qed.

Lemma bind_all_respected (params : list variable) :
  ∀ (known : Known.t) (vs : list value) (vars handler_vars : env),
    known_respected known vars ->
    bind_params params vs vars = Some handler_vars ->
    known_respected (Known.bind_all known params) handler_vars.
Proof.
  induction params as [ | param params IH];
    intros known [ | v vs] vars handler_vars Hrespected; simpl;
    try discriminate.
  - intros [= <-]. exact Hrespected.
  - apply (IH (Known.bind known param)). apply bind_respected, Hrespected.
Qed.

Lemma find_closure_in (known : Known.t) (s : simple) (c : Known.closure) :
  Known.find_closure known s = Some c ->
  ∃ y : variable, s = Var y ∧ (y, c) ∈ Known.closures known.
Proof.
  destruct s as [y | sym | k]; simpl; try discriminate.
  intros Hlookup. exists y.
  split; [ reflexivity | exact (lookup_in y c _ Hlookup) ].
Qed.

Theorem under_let_respected : under_let_respected_statement.
Proof.
  intros known statics vars x d v Hrespected Hd.
  pose proof (bind_respected known vars x v Hrespected) as Hbound.
  unfold Known.under_let. cbv zeta.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    try exact Hbound.
  - (* Simple *)
    destruct (var_in_simple x s) eqn:Hfree; [ exact Hbound | ].
    destruct Hbound as [Haliases Hclosures]. split; [ | exact Hclosures ].
    cbn [Known.aliases Known.with_aliases].
    apply add_equal_respected; [ exact Haliases | ].
    simpl. rewrite Pos.eqb_refl, (eval_simple_bind vars x v s Hfree).
    symmetry. exact Hd.
  - (* Set_of_closures *)
    destruct (var_in_value_slots x slots) eqn:Hfree; [ exact Hbound | ].
    destruct Hbound as [Haliases Hclosures]. split; [ exact Haliases | ].
    intros y c [[= <- <-] | Hin]; [ | exact (Hclosures y c Hin) ].
    simpl in Hd.
    destruct (eval_value_slots vars slots) as [slot_values | ] eqn:Hslots;
      [ | discriminate Hd ].
    simpl in Hd. injection Hd as <-.
    split; [ discriminate | ]. exists slot_values. split.
    + simpl. rewrite eval_value_slots_bind; assumption.
    + simpl. rewrite Pos.eqb_refl. reflexivity.
  - (* Closure_of_set *)
    destruct (var_in_value_slots x slots) eqn:Hfree; [ exact Hbound | ].
    destruct Hbound as [Haliases Hclosures]. split; [ exact Haliases | ].
    intros y c [[= <- <-] | Hin]; [ | exact (Hclosures y c Hin) ].
    simpl in Hd.
    destruct (lookup fslot decls) as [code | ] eqn:Hcode;
      [ | discriminate Hd ].
    simpl in Hd.
    destruct (eval_value_slots vars slots) as [slot_values | ] eqn:Hslots;
      [ | discriminate Hd ].
    simpl in Hd. injection Hd as <-.
    split; [ simpl; rewrite Hcode; discriminate | ].
    exists slot_values. split.
    + simpl. rewrite eval_value_slots_bind; assumption.
    + simpl. rewrite Pos.eqb_refl. reflexivity.
  - (* Project_function_slot *)
    destruct (Known.find_closure (Known.bind known x) closure)
      as [[code slots | slot decls slots] | ] eqn:Hfind;
      try exact Hbound.
    destruct (Pos.eqb_spec slot move_from) as [-> | _]; [ | exact Hbound ].
    destruct (find_closure_in _ _ _ Hfind) as (y & -> & Hin).
    destruct (in_closures_forget known x y _ Hin) as (_ & Hxy & Hfree).
    destruct Hbound as [Haliases Hclosures]. split; [ exact Haliases | ].
    intros z c [[= <- <-] | Hin']; [ | exact (Hclosures z c Hin') ].
    destruct (Hclosures y _ Hin) as [Hcode (slot_values & Hslots & Hlookup)].
    simpl in Hlookup. rewrite Pos.eqb_sym, Hxy in Hlookup.
    simpl in Hd. rewrite Hlookup in Hd. simpl in Hd.
    rewrite Pos.eqb_refl in Hd. simpl in Hcode.
    destruct (lookup move_from decls) as [code | ]; [ | contradiction ].
    simpl in Hd.
    destruct (lookup move_to decls) as [code' | ] eqn:Hcode';
      [ | discriminate Hd ].
    simpl in Hd. injection Hd as <-.
    split; [ simpl; rewrite Hcode'; discriminate | ].
    exists slot_values. split; [ exact Hslots | ].
    simpl. rewrite Pos.eqb_refl. reflexivity.
Qed.

(* ======================================================================== *)
(* Following aliases at the head of a term                                  *)
(* ======================================================================== *)

Lemma canonical_simples_sound (known : Known.t) (vars : env)
    (args : list simple) :
  known_respected known vars ->
  eval_simples vars (map (Known.canonical_simple known) args)
  = eval_simples vars args.
Proof.
  intros Hrespected. induction args as [ | s args IH]; simpl;
    [ reflexivity | ].
  rewrite (canonical_simple_sound known vars s Hrespected), IH. reflexivity.
Qed.

Lemma canonical_value_slots_sound (known : Known.t) (vars : env)
    (slots : list (value_slot * simple)) :
  known_respected known vars ->
  eval_value_slots vars (canonical_value_slots known slots)
  = eval_value_slots vars slots.
Proof.
  intros Hrespected. induction slots as [ | [slot s] slots IH]; simpl;
    [ reflexivity | ].
  rewrite (canonical_simple_sound known vars s Hrespected), IH. reflexivity.
Qed.

(* What a known closure is. *)
Lemma find_closure_sound (known : Known.t) (vars : env) (s : simple)
    (c : Known.closure) :
  known_respected known vars ->
  Known.find_closure known s = Some c ->
  Known.closure_code c <> None
  ∧ ∃ slot_values : list (value_slot * value),
      eval_value_slots vars (Known.closure_value_slots c) = Some slot_values
      ∧ eval_simple vars s = Some (closure_value c slot_values).
Proof.
  intros [_ Hclosures] Hfind.
  destruct (find_closure_in known s c Hfind) as (y & -> & Hin).
  exact (Hclosures y c Hin).
Qed.

Lemma closure_of_closure_value (statics : static_env) (c : Known.closure)
    (slot_values : list (value_slot * value)) :
  closure_of statics (closure_value c slot_values)
  = option_map (fun code => (code, slot_values)) (Known.closure_code c).
Proof.
  destruct c as [code slots | slot decls slots]; simpl; [ reflexivity | ].
  destruct (lookup slot decls); reflexivity.
Qed.

Lemma project_value_slot_closure_value (statics : static_env)
    (project_from : function_slot) (slot : value_slot) (c : Known.closure)
    (slot_values : list (value_slot * value)) :
  Known.closure_code c <> None ->
  project_value_slot statics project_from slot (closure_value c slot_values)
  = if Pos.eqb (Known.closure_slot c) project_from
    then lookup slot slot_values
    else None.
Proof.
  destruct c as [code slots | fslot decls slots]; simpl; [ reflexivity | ].
  intros Hcode. unfold project_value_slot. simpl.
  destruct (lookup fslot decls); [ reflexivity | contradiction ].
Qed.

(* A slot of evaluated value slots has the value of what it held. *)
Lemma eval_value_slots_lookup (vars : env) (slot : value_slot)
    (slots : list (value_slot * simple)) :
  ∀ (slot_values : list (value_slot * value)) (contents : simple),
    eval_value_slots vars slots = Some slot_values ->
    lookup slot slots = Some contents ->
    lookup slot slot_values = eval_simple vars contents.
Proof.
  induction slots as [ | [slot' s] slots IH]; intros slot_values contents;
    simpl; [ discriminate | ].
  destruct (eval_simple vars s) as [v | ] eqn:Hs; [ | discriminate ].
  destruct (eval_value_slots vars slots) as [rest | ]; [ | discriminate ].
  simpl. intros [= <-]. simpl.
  destruct (Pos.eqb slot slot').
  - intros [= <-]. symmetry. exact Hs.
  - apply (IH rest contents eq_refl).
Qed.

Lemma canonical_project_sound (known : Known.t) (vars : env)
    (statics : static_env) (slot : value_slot) (closure : simple) :
  known_respected known vars ->
  eval_named statics vars (canonical_project known slot closure)
  = eval_named statics vars (Project_value_slot slot closure).
Proof.
  intros Hrespected. unfold canonical_project.
  destruct (Known.find_closure known closure) as [c | ] eqn:Hclosure;
    [ | reflexivity ].
  destruct (lookup slot (Known.closure_value_slots c)) as [contents | ]
    eqn:Hslot; [ | reflexivity ].
  destruct (find_closure_sound known vars closure c Hrespected Hclosure)
    as [Hcode (slot_values & Hslots & Heval)].
  simpl. rewrite Heval. simpl. rewrite closure_of_closure_value.
  destruct (Known.closure_code c) as [code | ]; [ | contradiction ].
  simpl. symmetry.
  exact (eval_value_slots_lookup vars slot _ slot_values contents Hslots
    Hslot).
Qed.

Lemma canonical_project_from_sound (known : Known.t) (vars : env)
    (statics : static_env) (project_from : function_slot) (slot : value_slot)
    (closure : simple) :
  known_respected known vars ->
  eval_named statics vars
    (canonical_project_from known project_from slot closure)
  = eval_named statics vars
      (Project_value_slot_from project_from slot closure).
Proof.
  intros Hrespected. unfold canonical_project_from.
  destruct (Known.find_closure known closure) as [c | ] eqn:Hclosure;
    [ | reflexivity ].
  destruct (Pos.eqb (Known.closure_slot c) project_from) eqn:Hat;
    [ | reflexivity ].
  destruct (lookup slot (Known.closure_value_slots c)) as [contents | ]
    eqn:Hslot; [ | reflexivity ].
  destruct (find_closure_sound known vars closure c Hrespected Hclosure)
    as [Hcode (slot_values & Hslots & Heval)].
  simpl. rewrite Heval. simpl.
  rewrite (project_value_slot_closure_value statics project_from slot c
    slot_values Hcode), Hat.
  symmetry.
  exact (eval_value_slots_lookup vars slot _ slot_values contents Hslots
    Hslot).
Qed.

Lemma canonical_named_sound (known : Known.t) (vars : env)
    (statics : static_env) (d : named) :
  known_respected known vars ->
  eval_named statics vars (canonical_named known d)
  = eval_named statics vars d.
Proof.
  intros Hrespected.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure]; simpl.
  - apply canonical_simple_sound, Hrespected.
  - rewrite (canonical_simples_sound known vars args Hrespected).
    reflexivity.
  - rewrite (canonical_value_slots_sound known vars slots Hrespected).
    reflexivity.
  - rewrite (canonical_value_slots_sound known vars slots Hrespected).
    reflexivity.
  - rewrite (canonical_project_sound known vars statics slot _ Hrespected).
    simpl.
    rewrite (canonical_simple_sound known vars closure Hrespected).
    reflexivity.
  - rewrite (canonical_project_from_sound known vars statics pfrom slot _
      Hrespected).
    simpl.
    rewrite (canonical_simple_sound known vars closure Hrespected).
    reflexivity.
  - rewrite (canonical_simple_sound known vars closure Hrespected).
    reflexivity.
Qed.

(* A call and the same call with its aliases followed and, if the callee
   is a known closure, made direct: they take the same step. *)
Lemma canonical_apply_equivalent (known : Known.t) (ap : apply_expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  known_respected known vars ->
  equivalent (State (Apply ap) vars conts statics)
    (State (Apply (canonical_apply known ap)) vars conts statics).
Proof.
  intros Hrespected. apply step_eq_equivalent. rewrite !step_apply.
  assert (Hextras :
    exn_extra_simples (canonical_apply known ap)
    = map (Known.canonical_simple known) (exn_extra_simples ap))
    by (unfold exn_extra_simples; simpl; rewrite !map_map; reflexivity).
  rewrite Hextras. simpl.
  rewrite (canonical_simples_sound known vars (ap_args ap) Hrespected),
    (canonical_simples_sound known vars (exn_extra_simples ap) Hrespected).
  rewrite (canonical_simple_sound known vars (ap_callee ap) Hrespected).
  unfold canonical_call_kind.
  destruct (ap_call_kind ap) as [code | ]; [ reflexivity | ].
  destruct (Known.find_closure known
              (Known.canonical_simple known (ap_callee ap)))
    as [c | ] eqn:Hclosure; [ | reflexivity ].
  destruct (Known.closure_code c) as [code | ] eqn:Hcode; [ | reflexivity ].
  destruct (find_closure_sound known vars _ c Hrespected Hclosure)
    as [_ (slot_values & _ & Heval)].
  rewrite (canonical_simple_sound known vars (ap_callee ap) Hrespected)
    in Heval.
  rewrite Heval.
  destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | reflexivity ].
  destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ];
    [ | reflexivity ].
  unfold call_function. rewrite closure_of_closure_value, Hcode. simpl.
  rewrite Pos.eqb_refl. reflexivity.
Qed.

Lemma canonical_static_bindings_sound (known : Known.t) (vars : env)
    (bindings : list static_binding) :
  known_respected known vars ->
  ∀ statics : static_env,
    eval_static_bindings vars (map (canonical_static_binding known) bindings)
      statics
    = eval_static_bindings vars bindings statics.
Proof.
  intros Hrespected.
  induction bindings as [ | binding bindings IH]; intros statics;
    [ reflexivity | ].
  destruct binding
    as [id c | id
       | sym [code slots | fslot syms decls slots | tag fields | s | bytes]];
    simpl; try apply IH.
  - destruct (lookup id (static_code statics)); [ reflexivity | apply IH ].
  - destruct (lookup sym (static_values statics)); [ reflexivity | ].
    rewrite (canonical_value_slots_sound known vars slots Hrespected).
    destruct (eval_value_slots vars slots); simpl; [ apply IH | reflexivity ].
  - destruct (lookup sym (static_values statics)); [ reflexivity | ].
    rewrite (canonical_value_slots_sound known vars slots Hrespected).
    destruct (lookup fslot decls); simpl; [ | reflexivity ].
    destruct (eval_value_slots vars slots); simpl; [ apply IH | reflexivity ].
  - destruct (lookup sym (static_values statics)); [ reflexivity | ].
    rewrite (canonical_simples_sound known vars fields Hrespected).
    destruct (eval_simples vars fields); simpl; [ apply IH | reflexivity ].
  - destruct (lookup sym (static_values statics)); [ reflexivity | ].
    rewrite (canonical_simple_sound known vars s Hrespected).
    destruct (eval_simple vars s); simpl; [ apply IH | reflexivity ].
  - destruct (lookup sym (static_values statics)); [ reflexivity | ].
    apply IH.
Qed.

Lemma find_arm_canonical (known : Known.t) (i : Z)
    (arms : list (Z * apply_cont)) :
  find_arm i
    (map (fun arm => (fst arm, canonical_apply_cont known (snd arm))) arms)
  = option_map (canonical_apply_cont known) (find_arm i arms).
Proof.
  induction arms as [ | [discriminant ac] arms IH]; simpl; [ reflexivity | ].
  destruct (Z.eqb i discriminant); [ reflexivity | exact IH ].
Qed.

Lemma canonical_apply_cont_equivalent (known : Known.t) (ac : apply_cont)
    (vars : env) (conts : cont_env) (statics : static_env) :
  known_respected known vars ->
  equivalent (State (Apply_cont ac) vars conts statics)
    (State (Apply_cont (canonical_apply_cont known ac)) vars conts statics).
Proof.
  intros Hrespected. apply step_eq_equivalent. rewrite !step_apply_cont.
  simpl.
  rewrite (canonical_simples_sound known vars (ac_args ac) Hrespected).
  reflexivity.
Qed.

(* ======================================================================== *)
(* Under binders                                                            *)
(* ======================================================================== *)

(* Equivalence in the environments that agree with what is known. *)
Definition equivalent_where (known : Known.t) (e e' : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env),
    known_respected known vars ->
    equivalent (State e vars conts statics) (State e' vars conts statics).

Lemma let_equivalent_where (known : Known.t) (x : variable)
    (kind : flambda_kind) (d : named) (body body' : expr) :
  equivalent_where (Known.under_let known x d) body body' ->
  equivalent_where known (Let x kind d body) (Let x kind d body').
Proof.
  intros Hbody vars conts statics Hrespected.
  apply let_equivalent_step; [ reflexivity | intros v Hd ].
  apply Hbody.
  exact (under_let_respected known statics vars x d v Hrespected Hd).
Qed.

Lemma let_static_equivalent_where (known : Known.t)
    (bindings : list static_binding) (body body' : expr) :
  equivalent_where known body body' ->
  equivalent_where known (Let_static bindings body)
    (Let_static bindings body').
Proof.
  intros Hbody vars conts statics Hrespected.
  apply let_static_equivalent_step.
  destruct (eval_static_bindings vars bindings statics) as [extended | ];
    [ apply Hbody, Hrespected | exact I ].
Qed.

(* A handler may be replaced by one equivalent to it under what is known
   where it is defined, with its parameters bound. *)
Lemma let_cont_handler_equivalent_where (known : Known.t) (k : continuation)
    (params : list variable) (metadata : handler_metadata)
    (handler handler' body : expr) :
  equivalent_where (Known.bind_all known params) handler handler' ->
  equivalent_where known
    (Let_cont_non_recursive k (Handler params metadata handler) body)
    (Let_cont_non_recursive k (Handler params metadata handler') body).
Proof.
  intros Hhandler vars conts statics Hrespected.
  apply refines_antisymmetric; apply let_cont_handler_refines_at;
    intros vs handler_vars conts' statics' Hbind; apply equivalent_refines;
    [ | apply equivalent_sym ];
    apply Hhandler,
      (bind_all_respected params known vs vars handler_vars Hrespected Hbind).
Qed.

Lemma equivalent_where_trans (known : Known.t) (e e' e'' : expr) :
  equivalent_where known e e' -> equivalent_where known e' e'' ->
  equivalent_where known e e''.
Proof.
  intros H H' vars conts statics Hrespected.
  exact (equivalent_trans _ _ _ (H vars conts statics Hrespected)
    (H' vars conts statics Hrespected)).
Qed.

(* ======================================================================== *)
(* Following aliases                                                        *)
(* ======================================================================== *)

(* At each node: the head with its aliases followed is equivalent, by
   evaluating the same; then the parts under binders, by the induction. *)
Fixpoint follow_aliases_equivalent_where (e : expr) :
  ∀ known : Known.t, equivalent_where known e (follow_aliases known e)
with follow_aliases_in_handler_equivalent_where (h : continuation_handler) :
  ∀ (known : Known.t) (k : continuation) (body : expr),
    equivalent_where known (Let_cont_non_recursive k h body)
      (Let_cont_non_recursive k (follow_aliases_in_handler known h) body).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros known; simpl.
    + (* Let *)
      apply (equivalent_where_trans known _
        (Let x kind (canonical_named known d) body)).
      * intros vars conts statics Hrespected.
        apply let_equivalent_step;
          [ apply (canonical_named_sound known vars statics d Hrespected)
          | intros v _; apply equivalent_refl ].
      * apply let_equivalent_where, follow_aliases_equivalent_where.
    + (* Let_static *)
      apply (equivalent_where_trans known _
        (Let_static (map (canonical_static_binding known) bindings) body)).
      * intros vars conts statics Hrespected. apply step_eq_equivalent.
        rewrite !step_let_static,
          (canonical_static_bindings_sound known vars bindings Hrespected).
        reflexivity.
      * apply let_static_equivalent_where, follow_aliases_equivalent_where.
    + (* Let_cont_non_recursive *)
      apply (equivalent_where_trans known _
        (Let_cont_non_recursive k (follow_aliases_in_handler known h) body));
        [ apply follow_aliases_in_handler_equivalent_where | ].
      intros vars conts statics Hrespected.
      apply let_cont_non_recursive_equivalent_step.
      apply (follow_aliases_equivalent_where body known), Hrespected.
    + (* Let_cont_recursive *)
      intros vars conts statics Hrespected.
      apply let_cont_recursive_equivalent_step; [ reflexivity | intros _ ].
      apply (follow_aliases_equivalent_where body known), Hrespected.
    + (* Apply *)
      intros vars conts statics Hrespected.
      apply canonical_apply_equivalent, Hrespected.
    + (* Apply_cont *)
      intros vars conts statics Hrespected.
      apply canonical_apply_cont_equivalent, Hrespected.
    + (* Switch *)
      intros vars conts statics Hrespected.
      destruct (eval_simple vars scrutinee) as [v | ] eqn:Hscrutinee;
        [ destruct (naked_immediate_of_value v) as [i | ] eqn:Himmediate;
          [ destruct (find_arm i arms) as [ac | ] eqn:Hfind | ]
        | ].
      * eapply equivalent_step;
          [ rewrite step_switch, Hscrutinee, Himmediate, Hfind; reflexivity
          | rewrite step_switch,
              (canonical_simple_sound known vars scrutinee Hrespected),
              Hscrutinee, Himmediate, find_arm_canonical, Hfind;
            reflexivity
          | ].
        apply canonical_apply_cont_equivalent, Hrespected.
      * apply step_eq_equivalent.
        rewrite !step_switch,
          (canonical_simple_sound known vars scrutinee Hrespected),
          Hscrutinee, Himmediate, find_arm_canonical, Hfind.
        reflexivity.
      * apply step_eq_equivalent.
        rewrite !step_switch,
          (canonical_simple_sound known vars scrutinee Hrespected),
          Hscrutinee, Himmediate.
        reflexivity.
      * apply step_eq_equivalent.
        rewrite !step_switch,
          (canonical_simple_sound known vars scrutinee Hrespected),
          Hscrutinee.
        reflexivity.
    + (* Invalid *)
      intros vars conts statics Hrespected. apply equivalent_refl.
  - destruct h as [params metadata handler]. intros known k body. simpl.
    apply let_cont_handler_equivalent_where, follow_aliases_equivalent_where.
Qed.

Theorem follow_aliases_respected : follow_aliases_respected_statement.
Proof.
  intros known e vars conts statics Hrespected.
  exact (follow_aliases_equivalent_where e known vars conts statics
    Hrespected).
Qed.

Theorem follow_aliases_equivalent : follow_aliases_equivalent_statement.
Proof.
  intros e vars conts statics.
  apply follow_aliases_respected, empty_known_respected.
Qed.

(* ======================================================================== *)
(* Consistency, and what forgetting a variable keeps                        *)
(* ======================================================================== *)

Lemma empty_consistent : aliases_consistent Aliases.empty.
Proof.
  exact (proj1 (empty_well_formed unit Known.binding_time_resolver [])).
Qed.

Lemma add_equal_consistent
    (binding_times
      : Keyed.finite_map name (unit * Binding_time.With_name_mode.t))
    (t : Aliases.t) (e e' : simple) :
  aliases_consistent t ->
  aliases_consistent (Known.add_equal binding_times t e e').
Proof.
  intros Hconsistent. unfold Known.add_equal.
  destruct (simple_equal _ _); [ exact Hconsistent | ].
  destruct (Aliases.add _ _ t _ _) as [[result | ] | ] eqn:Hadd;
    try exact Hconsistent.
  exact (add_consistent unit Known.binding_time_resolver binding_times t _ _
    result Hconsistent (canonical_element_canonical t e Hconsistent)
    (canonical_element_canonical t e' Hconsistent) Hadd).
Qed.

Lemma forget_in_aliases_consistent
    (binding_times
      : Keyed.finite_map name (unit * Binding_time.With_name_mode.t))
    (t : Aliases.t) (x : variable) :
  aliases_consistent t ->
  aliases_consistent (Known.forget_in_aliases binding_times t x).
Proof.
  intros Hconsistent. unfold Known.forget_in_aliases.
  destruct (negb _); [ exact Hconsistent | ]. cbv zeta.
  apply fold_left_invariant; [ exact empty_consistent | ].
  intros rebuilt n _ Hrebuilt.
  destruct (simple_equal _ _);
    [ destruct (find _ _); [ | exact Hrebuilt ] | ];
    apply add_equal_consistent, Hrebuilt.
Qed.

Theorem bind_consistent : bind_consistent_statement.
Proof.
  intros known x Hconsistent.
  exact (forget_in_aliases_consistent _ _ x Hconsistent).
Qed.

Theorem under_let_consistent : under_let_consistent_statement.
Proof.
  intros known x d Hconsistent.
  pose proof (bind_consistent known x Hconsistent) as Hbound.
  unfold Known.under_let. cbv zeta.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    try exact Hbound.
  - destruct (var_in_simple x s); [ exact Hbound | ].
    cbn [Known.aliases Known.with_aliases].
    apply add_equal_consistent, Hbound.
  - destruct (var_in_value_slots x slots); exact Hbound.
  - destruct (var_in_value_slots x slots); exact Hbound.
  - destruct (Known.find_closure _ closure)
      as [[code slots | slot decls slots] | ]; try exact Hbound.
    destruct (Pos.eqb slot move_from); exact Hbound.
Qed.

(* A simple is in the class of its canonical element. *)
Lemma aliased_canonical (t : Aliases.t) (e : simple) :
  aliases_consistent t -> aliased t e (canonical_element_of t e).
Proof.
  intros Hconsistent. unfold aliased. symmetry.
  exact (canonical_element_idempotent t e Hconsistent).
Qed.

Lemma canonical_element_of_empty (e : simple) :
  canonical_element_of Aliases.empty e = e.
Proof. destruct e; reflexivity. Qed.

(* [add_equal] of two simples that a structure [t] knows to be equal, to
   a structure that knows no more than [t] does: the classes of the two
   are made one, and nothing else changes. *)
Lemma add_equal_classes
    (binding_times
      : Keyed.finite_map name (unit * Binding_time.With_name_mode.t))
    (t rebuilt : Aliases.t) (e e' : simple) :
  aliases_consistent rebuilt ->
  (∀ a b : simple, aliased rebuilt a b -> aliased t a b) ->
  aliased t e e' ->
  ∀ a b : simple,
    aliased (Known.add_equal binding_times rebuilt e e') a b
    <-> aliased rebuilt a b
        ∨ (aliased rebuilt a e ∧ aliased rebuilt b e')
        ∨ (aliased rebuilt a e' ∧ aliased rebuilt b e).
Proof.
  intros Hconsistent Hwithin Haliased a b. unfold Known.add_equal.
  pose proof (aliased_canonical rebuilt e Hconsistent) as H1.
  pose proof (aliased_canonical rebuilt e' Hconsistent) as H2.
  pose proof (canonical_element_canonical rebuilt e Hconsistent) as Hc1.
  pose proof (canonical_element_canonical rebuilt e' Hconsistent) as Hc2.
  destruct (simple_equal_spec (canonical_element_of rebuilt e)
              (canonical_element_of rebuilt e')) as [Heq | Hne].
  - unfold aliased in *. split; [ auto | ].
    intros [H | [[Ha Hb] | [Ha Hb]]]; congruence.
  - destruct (Aliases.add _ _ rebuilt _ _) as [[result | ] | ] eqn:Hadd.
    + rewrite (add_aliased unit Known.binding_time_resolver binding_times
                 rebuilt _ _ result a b Hconsistent Hc1 Hc2 Hadd).
      unfold aliased in *.
      split; intros [H | [[Ha Hb] | [Ha Hb]]];
        solve
          [ left; exact H
          | right; left; split; congruence
          | right; right; split; congruence ].
    + exfalso.
      apply (proj1 (add_bottom unit Known.binding_time_resolver binding_times
                      rebuilt _ _)) in Hadd.
      destruct Hadd as (k1 & k2 & Hk1 & Hk2 & Hk). apply Hk.
      rewrite Hk1 in H1. rewrite Hk2 in H2.
      apply Hwithin in H1. apply Hwithin in H2.
      unfold aliased in H1, H2, Haliased.
      assert (Hsame :
        canonical_element_of t (Const k1) = canonical_element_of t (Const k2))
        by congruence.
      injection Hsame. auto.
    + exfalso.
      exact (add_defined unit Known.binding_time_resolver binding_times
        rebuilt _ _ Hconsistent Hc1 Hc2 Hne Hadd).
Qed.

Lemma fold_left_pointwise {A B : Type} (f g : A -> B -> A) (l : list B) :
  (∀ (a : A) (b : B), f a b = g a b) ->
  ∀ init : A, List.fold_left f l init = List.fold_left g l init.
Proof.
  intros Hfg. induction l as [ | b l IH]; intros init; simpl;
    [ reflexivity | ].
  rewrite Hfg. apply IH.
Qed.

Section Forgetting.

Context
  (binding_times
    : Keyed.finite_map name (unit * Binding_time.With_name_mode.t))
  (t : Aliases.t) (x : variable).
Hypothesis t_consistent : aliases_consistent t.

(* The names that [Known.forget_in_aliases] goes through, and what
   stands for [x]. *)
Let demoted_to_x (n : name) : bool :=
  simple_equal (Aliases.get_canonical_ignoring_name_mode t n) (Var x).

Let demoted : list name :=
  filter (fun n => negb (name_eqb n (Name_var x)))
    (Keyed.domain name_eqb (Aliases.canonical_elements t)).

Let in_place_of_x : option name := find demoted_to_x demoted.

(* What each of them is made an alias of. *)
Let target (n : name) : simple :=
  if demoted_to_x n
  then
    match in_place_of_x with
    | Some n' => simple_of_name n'
    | None => simple_of_name n
    end
  else Aliases.get_canonical_ignoring_name_mode t n.

Lemma target_aliased (n : name) : aliased t (simple_of_name n) (target n).
Proof.
  unfold target.
  destruct (demoted_to_x n) eqn:Hx.
  - destruct in_place_of_x as [n' | ] eqn:Hfind; [ | reflexivity ].
    apply find_some in Hfind. destruct Hfind as [_ Hx'].
    apply simple_equal_eq in Hx. apply simple_equal_eq in Hx'.
    unfold aliased.
    rewrite <- !(get_canonical_ignoring_name_mode t). congruence.
  - rewrite (get_canonical_ignoring_name_mode t n).
    apply aliased_canonical, t_consistent.
Qed.

Lemma forget_in_aliases_eq :
  among x (aliases_free_variables t) = true ->
  Known.forget_in_aliases binding_times t x
  = List.fold_left
      (fun rebuilt n =>
         Known.add_equal binding_times rebuilt (simple_of_name n) (target n))
      demoted Aliases.empty.
Proof.
  intros Hamong. unfold Known.forget_in_aliases. rewrite Hamong.
  cbn [negb]. cbv zeta. apply fold_left_pointwise. intros rebuilt n.
  unfold target, demoted_to_x, in_place_of_x, demoted.
  destruct (simple_equal (Aliases.get_canonical_ignoring_name_mode t n)
              (Var x)); [ | reflexivity ].
  destruct (find _ _); [ reflexivity | ].
  unfold Known.add_equal.
  destruct (simple_equal_spec
              (canonical_element_of rebuilt (simple_of_name n))
              (canonical_element_of rebuilt (simple_of_name n)))
    as [_ | Hne]; [ reflexivity | contradiction ].
Qed.

Lemma rebuild_classes (l : list name) :
  ∀ rebuilt : Aliases.t,
    aliases_consistent rebuilt ->
    (∀ a b : simple, aliased rebuilt a b -> aliased t a b) ->
    let rebuilt' :=
      List.fold_left
        (fun rebuilt n =>
           Known.add_equal binding_times rebuilt (simple_of_name n)
             (target n))
        l rebuilt
    in
    (∀ a b : simple, aliased rebuilt a b -> aliased rebuilt' a b)
    ∧ ∀ n : name, n ∈ l -> aliased rebuilt' (simple_of_name n) (target n).
Proof.
  induction l as [ | n l IH]; intros rebuilt Hconsistent Hwithin; simpl.
  - split; [ auto | intros n [] ].
  - pose proof (add_equal_classes binding_times t rebuilt (simple_of_name n)
                  (target n) Hconsistent Hwithin (target_aliased n))
      as Hclasses.
    destruct (IH (Known.add_equal binding_times rebuilt (simple_of_name n)
                    (target n)))
      as [Hkept Htargets].
    + apply add_equal_consistent, Hconsistent.
    + intros a b Hab. apply Hclasses in Hab.
      pose proof (target_aliased n) as Hn. unfold aliased in *.
      destruct Hab as [H | [[Ha Hb] | [Ha Hb]]].
      * exact (Hwithin a b H).
      * pose proof (Hwithin _ _ Ha). pose proof (Hwithin _ _ Hb). congruence.
      * pose proof (Hwithin _ _ Ha). pose proof (Hwithin _ _ Hb). congruence.
    + split.
      * intros a b Hab. apply Hkept, Hclasses. left. exact Hab.
      * intros n' [<- | Hin]; [ | exact (Htargets n' Hin) ].
        apply Hkept, Hclasses. right. left. split; reflexivity.
Qed.

Lemma in_demoted (n : name) (c : simple) :
  demoted_to t n c -> simple_of_name n <> Var x -> n ∈ demoted.
Proof.
  intros Hdemoted Hne. unfold demoted. apply filter_In. split.
  - apply (keyed_among_in name name_eqb name_eqb_eq).
    rewrite (keyed_among_domain name name_eqb name_eqb_eq).
    unfold Keyed.is_bound. unfold demoted_to in Hdemoted.
    rewrite Hdemoted. reflexivity.
  - apply negb_true_iff.
    destruct (keyed_eqb_spec name_eqb name_eqb_eq n (Name_var x))
      as [-> | _]; [ | reflexivity ].
    exfalso. apply Hne. reflexivity.
Qed.

Lemma forget_in_aliases_aliased (e e' : simple) :
  aliased t e e' ->
  e <> Var x ->
  e' <> Var x ->
  aliased (Known.forget_in_aliases binding_times t x) e e'.
Proof.
  intros Haliased He He'.
  destruct (among x (aliases_free_variables t)) eqn:Hamong.
  2: { unfold Known.forget_in_aliases. rewrite Hamong. exact Haliased. }
  rewrite (forget_in_aliases_eq Hamong).
  destruct (rebuild_classes demoted Aliases.empty empty_consistent)
    as [_ Htargets].
  { intros a b Hab. unfold aliased in Hab.
    rewrite !canonical_element_of_empty in Hab. subst b. reflexivity. }
  cbv zeta in Htargets.
  set (rebuilt :=
    List.fold_left
      (fun rebuilt n =>
         Known.add_equal binding_times rebuilt (simple_of_name n) (target n))
      demoted Aliases.empty) in *.
  (* What stands, in what is rebuilt, for a class of [t]. *)
  set (stands_for := fun c : simple =>
    if simple_equal c (Var x)
    then
      match in_place_of_x with
      | Some n' => simple_of_name n'
      | None => c
      end
    else c).
  assert (Hstands :
    ∀ s : simple,
      s <> Var x ->
      aliased rebuilt s (stands_for (canonical_element_of t s))).
  { intros s Hs.
    destruct (canonical_cases t s)
      as [[_ ->] | (n & c & -> & Hdemoted & _ & ->)].
    - unfold stands_for.
      destruct (simple_equal_spec s (Var x)) as [Heq | _];
        [ contradiction | reflexivity ].
    - pose proof (Htargets n (in_demoted n c Hdemoted Hs)) as Hn.
      assert (Htarget : target n = stands_for c).
      { unfold target, stands_for, demoted_to_x.
        rewrite (get_canonical_ignoring_name_mode t n),
          (canonical_element_of_demoted t n c Hdemoted).
        destruct (simple_equal c (Var x)) eqn:Hx; [ | reflexivity ].
        destruct in_place_of_x as [n' | ] eqn:Hfind; [ reflexivity | ].
        exfalso.
        pose proof (find_none _ _ Hfind n (in_demoted n c Hdemoted Hs))
          as Hnone.
        unfold demoted_to_x in Hnone.
        rewrite (get_canonical_ignoring_name_mode t n),
          (canonical_element_of_demoted t n c Hdemoted), Hx in Hnone.
        discriminate Hnone. }
      rewrite <- Htarget. exact Hn. }
  pose proof (Hstands e He) as H1. pose proof (Hstands e' He') as H2.
  unfold aliased in *. congruence.
Qed.

End Forgetting.

Theorem forget_aliased : forget_aliased_statement.
Proof.
  intros binding_times t x e e' Hconsistent.
  exact (forget_in_aliases_aliased binding_times t x Hconsistent e e').
Qed.

(* ======================================================================== *)
(* Examples                                                                 *)
(* ======================================================================== *)

Module Examples.

Definition x : variable := 1%positive.
Definition y : variable := 2%positive.
Definition z : variable := 3%positive.
Definition f : variable := 4%positive.
Definition g : variable := 5%positive.

Definition three : simple := Const (Tagged_immediate 3).

(* A jump to the continuation of the term, with arguments. *)
Definition jump (args : list simple) : expr :=
  Apply_cont (Apply_cont_expr 1%positive args None).

(* A variable bound to a constant: its uses become the constant. *)
Example constant_followed :
  follow_aliases Known.empty (Let x Value (Simple three) (jump [Var x]))
  = Let x Value (Simple three) (jump [three]).
Proof. reflexivity. Qed.

(* A chain of aliases of a variable that the term does not bind: every
   use becomes that variable, which is earlier than those bound here. *)
Example chain_followed :
  follow_aliases Known.empty
    (Let y Value (Simple (Var x))
       (Let z Value (Simple (Var y)) (jump [Var z; Var y])))
  = Let y Value (Simple (Var x))
      (Let z Value (Simple (Var x)) (jump [Var x; Var x])).
Proof. reflexivity. Qed.

(* [x] is bound again where [y] and [z] are known to be aliases of it.
   What is known of the old [x] is forgotten; that [y] and [z] are
   equal is kept, with [y], the earlier, as the canonical element. *)
Example bound_again :
  follow_aliases Known.empty
    (Let y Value (Simple (Var x))
       (Let z Value (Simple (Var x))
          (Let x Value (Simple three) (jump [Var x; Var y; Var z]))))
  = Let y Value (Simple (Var x))
      (Let z Value (Simple (Var x))
         (Let x Value (Simple three) (jump [three; Var y; Var y]))).
Proof. reflexivity. Qed.

(* A set of two closures, bound as the compiler's [Let] of a set is: the
   first closure, and the second as its projection from the first. *)
Definition f_slot : function_slot := 1%positive.
Definition g_slot : function_slot := 2%positive.
Definition f_code : code_id := 1%positive.
Definition g_code : code_id := 2%positive.
Definition v_slot : value_slot := 1%positive.

Definition two_closures (body : expr) : expr :=
  Let f Value
    (Closure_of_set f_slot [(f_slot, f_code); (g_slot, g_code)]
       [(v_slot, three)])
    (Let g Value (Project_function_slot f_slot g_slot (Var f)) body).

Definition call (callee : simple) (kind : call_kind) (args : list simple)
    : expr :=
  Apply
    (Apply_expr callee kind args 1%positive 2%positive []
       (arity_of_kinds [Value]) (arity_of_kinds [Value])).

(* A call of the second closure is a direct call of its code, and the
   value slot projected from it, at its own function slot, is what the
   slot was given. *)
Example second_closure_known :
  follow_aliases Known.empty
    (two_closures
       (Let x Value (Project_value_slot_from g_slot v_slot (Var g))
          (call (Var g) Indirect [Var x])))
  = two_closures
      (Let x Value (Simple three) (call (Var g) (Direct g_code) [three])).
Proof. reflexivity. Qed.

(* A projection that names another function slot than the one its
   closure is at is undefined, and is left as it is. *)
Example wrong_slot_left :
  follow_aliases Known.empty
    (two_closures
       (Let x Value (Project_value_slot_from f_slot v_slot (Var g))
          (jump [Var x])))
  = two_closures
      (Let x Value (Project_value_slot_from f_slot v_slot (Var g))
         (jump [Var x])).
Proof. reflexivity. Qed.

(* What is learnt in the body of a [Let_cont] is not known in the
   handler, and the parameter of the handler is a new variable. *)
Example handler_apart :
  follow_aliases Known.empty
    (Let y Value (Simple three)
       (Let_cont_non_recursive 2%positive
          (Handler [z] (make_handler_metadata [Value]) (jump [Var y; Var z]))
          (Let z Value (Simple (Var y)) (jump [Var z]))))
  = Let y Value (Simple three)
      (Let_cont_non_recursive 2%positive
         (Handler [z] (make_handler_metadata [Value]) (jump [three; Var z]))
         (Let z Value (Simple three) (jump [three]))).
Proof. reflexivity. Qed.

End Examples.
