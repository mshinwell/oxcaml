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

(* Proofs of the statements of FlambdaLiftSpec.v. Nothing here needs
   review.

   The term and the term lifted are run side by side. Where the first
   executes a [Let] that is lifted, the second executes the [Let_static]
   and then the [Let] of the symbol, two steps for one; everywhere else
   they step together. So the simulation is one in which each step of
   the first run is answered by one or more of the second
   (FlambdaSimulationProofs.stuttering_refines). The relation between the
   two states
   ([state_lifted]) is that the second expression is the first lifted,
   the values of the second are those of the first up to
   [value_lifted], and so are what the symbols are bound to
   ([statics_lifted]). The machine cannot tell such values apart: every
   observation answers alike ([closure_of_lifted], ...), and so does
   every primitive (FlambdaPrimitiveProofs.eval_prim_related).

   What keeps a new static binding from failing where the [Let] did not
   is that the second run is that of a well-formed unit, which never
   binds a name twice (FlambdaWellFormedProofs.well_formed_never_faults).

   That the values at the exit are equal, and not only lifted, is from
   an invariant of the first run alone ([plain_state]): the
   continuations in scope never stand for a way out. *)

From Stdlib Require Import ZArith List Bool Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaPrimitiveModel FlambdaPrimitiveProofs
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaSimulationProofs
  FlambdaNominalSpec FlambdaNominalProofs FlambdaWellFormedSpec
  FlambdaWellFormedProofs FlambdaClosuresSpec FlambdaClosuresProofs
  FlambdaUnusedStaticsSpec FlambdaMyClosureSpec FlambdaMyClosureProofs
  FlambdaLiftSpec.
Import ListNotations.

(* ======================================================================== *)
(* Lists and maps                                                           *)
(* ======================================================================== *)

(* Two maps with the same keys in the same order bind the same names. *)
Lemma lookup_same_keys {A B : Type} (name : positive)
    (l : list (positive * A)) :
  ∀ l' : list (positive * B),
    map fst l = map fst l' ->
    ∀ a : A, lookup name l = Some a -> ∃ b : B, lookup name l' = Some b.
Proof.
  induction l as [ | [k a0] l IH]; intros [ | [k' b0] l']; simpl;
    try discriminate.
  intros [= <- Hrest] a.
  destruct (Pos.eqb name k); [ eauto | apply IH; exact Hrest ].
Qed.

(* ======================================================================== *)
(* Lifted values                                                            *)
(* ======================================================================== *)

Ltac lifted_cases H :=
  destruct H
    as [ c | s | c | tag fields fields' Hfields
       | code slots slots' Hslots | fslot decls slots slots' Hslots
       | c s Hlookup | tag fields fields' s Hlookup Hfields
       | fslot decls slots slots' s syms Hsym Hsyms Hbound Hslots
       | code slots slots' s Hlookup Hslots ].

(* A value lifted under a static environment is lifted under one that
   extends it: a symbol stays bound to what it was bound to. *)
Fixpoint value_lifted_extend (statics' statics'' : static_env)
    (Hextend : statics_extend statics' statics'') (v v' : value)
    (H : value_lifted statics' v v') {struct H} :
  value_lifted statics'' v v'.
Proof.
  lifted_cases H.
  - apply Lifted_const.
  - apply Lifted_symbol.
  - apply Lifted_boxed_number.
  - apply Lifted_block.
    revert fields fields' Hfields. fix IH 3.
    intros fields fields' [ | w w' rest rest' Hhead Htail]; constructor;
      [ exact (value_lifted_extend _ _ Hextend _ _ Hhead)
      | exact (IH _ _ Htail) ].
  - apply Lifted_closure.
    revert slots slots' Hslots. fix IH 3.
    intros slots slots' [ | w w' rest rest' [Hkey Hhead] Htail]; constructor;
      [ split;
        [ exact Hkey | exact (value_lifted_extend _ _ Hextend _ _ Hhead) ]
      | exact (IH _ _ Htail) ].
  - apply Lifted_closure_of_set.
    revert slots slots' Hslots. fix IH 3.
    intros slots slots' [ | w w' rest rest' [Hkey Hhead] Htail]; constructor;
      [ split;
        [ exact Hkey | exact (value_lifted_extend _ _ Hextend _ _ Hhead) ]
      | exact (IH _ _ Htail) ].
  - apply Lifted_to_boxed_number. exact (proj2 Hextend s _ Hlookup).
  - apply (Lifted_to_block statics'' tag fields fields' s);
      [ exact (proj2 Hextend s _ Hlookup) | ].
    clear Hlookup. revert fields fields' Hfields. fix IH 3.
    intros fields fields' [ | w w' rest rest' Hhead Htail]; constructor;
      [ exact (value_lifted_extend _ _ Hextend _ _ Hhead)
      | exact (IH _ _ Htail) ].
  - apply (Lifted_to_closure statics'' fslot decls slots slots' s syms Hsym
             Hsyms);
      [ exact (static_set_bound_extend _ _ _ _ _ Hbound Hextend) | ].
    clear Hbound. revert slots slots' Hslots. fix IH 3.
    intros slots slots' [ | w w' rest rest' [Hkey Hhead] Htail]; constructor;
      [ split;
        [ exact Hkey | exact (value_lifted_extend _ _ Hextend _ _ Hhead) ]
      | exact (IH _ _ Htail) ].
  - apply (Lifted_to_unnamed_closure statics'' code slots slots' s);
      [ exact (proj2 Hextend s _ Hlookup) | ].
    clear Hlookup. revert slots slots' Hslots. fix IH 3.
    intros slots slots' [ | w w' rest rest' [Hkey Hhead] Htail]; constructor;
      [ split;
        [ exact Hkey | exact (value_lifted_extend _ _ Hextend _ _ Hhead) ]
      | exact (IH _ _ Htail) ].
Qed.

Lemma values_lifted_extend (statics' statics'' : static_env)
    (vs vs' : list value) :
  statics_extend statics' statics'' ->
  Forall2 (value_lifted statics') vs vs' ->
  Forall2 (value_lifted statics'') vs vs'.
Proof.
  intros Hextend. induction 1 as [ | v v' vs vs' Hv _ IH]; constructor;
    [ exact (value_lifted_extend _ _ Hextend _ _ Hv) | exact IH ].
Qed.

Lemma slots_lifted_extend (statics' statics'' : static_env)
    (slots slots' : list (value_slot * value)) :
  statics_extend statics' statics'' ->
  Forall2 (slot_lifted (value_lifted statics')) slots slots' ->
  Forall2 (slot_lifted (value_lifted statics'')) slots slots'.
Proof.
  intros Hextend.
  induction 1 as [ | slot slot' slots slots' [Hkey Hv] _ IH]; constructor;
    [ split; [ exact Hkey | exact (value_lifted_extend _ _ Hextend _ _ Hv) ]
    | exact IH ].
Qed.

(* A constant or a symbol is lifted to itself only. *)
Lemma plain_value_lifted (statics' : static_env) (v v' : value) :
  plain_value v -> value_lifted statics' v v' -> v' = v.
Proof. intros Hplain H. lifted_cases H; simpl in Hplain; tauto. Qed.

Lemma plain_values_lifted (statics' : static_env) (vs vs' : list value) :
  (∀ v : value, v ∈ vs -> plain_value v) ->
  Forall2 (value_lifted statics') vs vs' ->
  vs' = vs.
Proof.
  intros Hplain. induction 1 as [ | v v' vs vs' Hv _ IH]; [ reflexivity | ].
  rewrite (plain_value_lifted statics' v v' (Hplain v (or_introl eq_refl)) Hv),
    IH;
    [ reflexivity | ].
  intros w Hw. apply Hplain. right. exact Hw.
Qed.

(* A value lifted has the kind of the value: a symbol stands for what is
   allocated, of kind [Value]. *)
Lemma kind_of_value_lifted (statics' : static_env) (v v' : value) :
  value_lifted statics' v v' -> kind_of_value v' = kind_of_value v.
Proof. intros H. lifted_cases H; reflexivity. Qed.

Lemma kinds_of_values_lifted (statics' : static_env) (vs vs' : list value) :
  Forall2 (value_lifted statics') vs vs' ->
  map kind_of_value vs' = map kind_of_value vs.
Proof.
  induction 1 as [ | v v' vs vs' Hv _ IH]; simpl; [ reflexivity | ].
  rewrite (kind_of_value_lifted statics' v v' Hv), IH. reflexivity.
Qed.

(* The value of a slot of lifted value slots is lifted. *)
Lemma lookup_slots_lifted (statics' : static_env) (slot : value_slot)
    (slots slots' : list (value_slot * value)) (v : value) :
  Forall2 (slot_lifted (value_lifted statics')) slots slots' ->
  lookup slot slots = Some v ->
  ∃ v' : value, lookup slot slots' = Some v' ∧ value_lifted statics' v v'.
Proof.
  induction 1 as [ | [k w] [k' w'] slots slots' [Hkey Hw] _ IH]; simpl;
    [ discriminate | ].
  simpl in Hkey, Hw. subst k'.
  destruct (Pos.eqb slot k); [ intros [= <-]; eauto | exact IH ].
Qed.

(* ======================================================================== *)
(* Lifted static environments                                               *)
(* ======================================================================== *)

(* What a symbol is bound to in the first run and in the second: the
   same, with lifted parts. *)
Inductive allocated_lifted (statics' : static_env)
    : statically_allocated_value -> statically_allocated_value -> Prop :=
  | Lifted_static_closure (code : code_id)
      (slots slots' : list (value_slot * value)) :
    Forall2 (slot_lifted (value_lifted statics')) slots slots' ->
    allocated_lifted statics' (Static_closure code slots)
      (Static_closure code slots')
  | Lifted_static_closure_of_set (fslot : function_slot)
      (syms : list (function_slot * symbol))
      (decls : list (function_slot * code_id))
      (slots slots' : list (value_slot * value)) :
    Forall2 (slot_lifted (value_lifted statics')) slots slots' ->
    allocated_lifted statics' (Static_closure_of_set fslot syms decls slots)
      (Static_closure_of_set fslot syms decls slots')
  | Lifted_static_block (tag : Z) (fields fields' : list value) :
    Forall2 (value_lifted statics') fields fields' ->
    allocated_lifted statics' (Static_block tag fields)
      (Static_block tag fields')
  | Lifted_static_boxed_number (v v' : value) :
    value_lifted statics' v v' ->
    allocated_lifted statics' (Static_boxed_number v) (Static_boxed_number v')
  | Lifted_static_string (bytes : list Z) :
    allocated_lifted statics' (Static_string bytes) (Static_string bytes).

Ltac allocated_cases H :=
  destruct H
    as [ acode aslots aslots' Haslots
       | afslot asyms adecls aslots aslots' Haslots
       | atag afields afields' Hafields | av av' Hav | abytes ].

Lemma allocated_lifted_extend (statics' statics'' : static_env)
    (allocated allocated' : statically_allocated_value) :
  statics_extend statics' statics'' ->
  allocated_lifted statics' allocated allocated' ->
  allocated_lifted statics'' allocated allocated'.
Proof.
  intros Hextend H. allocated_cases H; constructor;
    eauto using slots_lifted_extend, values_lifted_extend,
      value_lifted_extend.
Qed.

Section Known.

(* The code ids whose code has [my_closure] bound to a symbol
   (FlambdaMyClosureSpec.bind_my_closures). *)
Variable known : list (code_id * symbol).

(* The second static environment has the code of the first, with
   [my_closure] bound where [known] says, and binds every symbol that
   the first binds to the same thing, lifted. It may bind more symbols:
   those of the [Let]s lifted. *)
Definition statics_lifted (statics statics' : static_env) : Prop :=
  (∀ id : code_id,
    lookup id (static_code statics')
    = option_map (bind_my_closure known id) (lookup id (static_code statics)))
  ∧ ∀ (s : symbol) (allocated : statically_allocated_value),
      lookup s (static_values statics) = Some allocated ->
      ∃ allocated' : statically_allocated_value,
        lookup s (static_values statics') = Some allocated'
        ∧ allocated_lifted statics' allocated allocated'.

(* The second static environment may grow by symbols alone. *)
Lemma statics_lifted_extend (statics statics' statics'' : static_env) :
  statics_lifted statics statics' ->
  statics_extend statics' statics'' ->
  static_code statics'' = static_code statics' ->
  statics_lifted statics statics''.
Proof.
  intros [Hcode Hvalues] Hextend Hcode'.
  split; [ intros id; rewrite Hcode'; apply Hcode | ].
  intros s allocated Hs.
  destruct (Hvalues s allocated Hs) as (allocated' & Hs' & Hallocated).
  exists allocated'.
  split; [ exact (proj2 Hextend s _ Hs') | ].
  exact (allocated_lifted_extend _ _ _ _ Hextend Hallocated).
Qed.

(* ======================================================================== *)
(* The observations answer alike of a value and of the value lifted         *)
(* ======================================================================== *)

Section Observations.

Variables statics statics' : static_env.
Hypothesis Hstatics : statics_lifted statics statics'.

Lemma block_of_lifted (v v' : value) (block_tag : Z)
    (block_fields : list value) :
  value_lifted statics' v v' ->
  block_of statics v = Some (block_tag, block_fields) ->
  ∃ block_fields' : list value,
    block_of statics' v' = Some (block_tag, block_fields')
    ∧ Forall2 (value_lifted statics') block_fields block_fields'.
Proof.
  intros Hv. lifted_cases Hv; simpl; try discriminate.
  - destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hs;
      [ | discriminate ].
    destruct (proj2 Hstatics s allocated Hs) as (allocated' & -> & Hallocated).
    allocated_cases Hallocated; try discriminate.
    intros [= <- <-]. eauto.
  - intros [= <- <-]. eauto.
  - intros [= <- <-]. rewrite Hlookup. eauto.
Qed.

Lemma boxed_number_of_lifted (v v' : value) (number : const) :
  value_lifted statics' v v' ->
  boxed_number_of statics v = Some number ->
  boxed_number_of statics' v' = Some number.
Proof.
  intros Hv. lifted_cases Hv; simpl; try discriminate;
    try exact (fun H => H).
  - destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hs;
      [ | discriminate ].
    destruct (proj2 Hstatics s allocated Hs) as (allocated' & -> & Hallocated).
    allocated_cases Hallocated; try discriminate.
    destruct av; try discriminate. inversion Hav. exact (fun H => H).
  - rewrite Hlookup. exact (fun H => H).
Qed.

Lemma string_of_lifted (v v' : value) (bytes : list Z) :
  value_lifted statics' v v' ->
  string_of statics v = Some bytes ->
  string_of statics' v' = Some bytes.
Proof.
  intros Hv. lifted_cases Hv; simpl; try discriminate.
  destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hs;
    [ | discriminate ].
  destruct (proj2 Hstatics s allocated Hs) as (allocated' & -> & Hallocated).
  allocated_cases Hallocated; try discriminate. exact (fun H => H).
Qed.

Lemma closure_in_set_lifted (v v' : value) (at_slot : function_slot)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * value)) :
  value_lifted statics' v v' ->
  closure_in_set statics v = Some (at_slot, function_decls, value_slots) ->
  ∃ value_slots' : list (value_slot * value),
    closure_in_set statics' v' = Some (at_slot, function_decls, value_slots')
    ∧ Forall2 (slot_lifted (value_lifted statics')) value_slots value_slots'.
Proof.
  intros Hv. lifted_cases Hv; simpl; try discriminate.
  - destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hs;
      [ | discriminate ].
    destruct (proj2 Hstatics s allocated Hs) as (allocated' & -> & Hallocated).
    allocated_cases Hallocated; try discriminate.
    + intros [= <- <- <-]. eauto.
    + destruct (lookup afslot adecls); [ | discriminate ]. simpl.
      intros [= <- <- <-]. eauto.
  - intros [= <- <- <-]. eauto.
  - destruct (lookup fslot decls); [ | discriminate ]. simpl.
    intros [= <- <- <-]. eauto.
  - destruct (lookup fslot decls) as [code0 | ] eqn:Hcode; [ | discriminate ].
    simpl. intros [= <- <- <-].
    rewrite (Hbound fslot s (lookup_in _ _ _ Hsym)), Hcode. simpl. eauto.
  - intros [= <- <- <-]. rewrite Hlookup. eauto.
Qed.

Lemma closure_of_lifted (v v' : value) (called : code_id)
    (value_slots : list (value_slot * value)) :
  value_lifted statics' v v' ->
  closure_of statics v = Some (called, value_slots) ->
  ∃ value_slots' : list (value_slot * value),
    closure_of statics' v' = Some (called, value_slots')
    ∧ Forall2 (slot_lifted (value_lifted statics')) value_slots value_slots'.
Proof.
  intros Hv. lifted_cases Hv; simpl; try discriminate.
  - destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hs;
      [ | discriminate ].
    destruct (proj2 Hstatics s allocated Hs) as (allocated' & -> & Hallocated).
    allocated_cases Hallocated; try discriminate.
    + intros [= <- <-]. eauto.
    + destruct (lookup afslot adecls); [ | discriminate ]. simpl.
      intros [= <- <-]. eauto.
  - intros [= <- <-]. eauto.
  - destruct (lookup fslot decls); [ | discriminate ]. simpl.
    intros [= <- <-]. eauto.
  - destruct (lookup fslot decls) as [code0 | ] eqn:Hcode; [ | discriminate ].
    simpl. intros [= <- <-].
    rewrite (Hbound fslot s (lookup_in _ _ _ Hsym)), Hcode. simpl. eauto.
  - intros [= <- <-]. rewrite Hlookup. eauto.
Qed.

Lemma project_value_slot_lifted (project_from : function_slot)
    (slot : value_slot) (v v' w : value) :
  value_lifted statics' v v' ->
  project_value_slot statics project_from slot v = Some w ->
  ∃ w' : value,
    project_value_slot statics' project_from slot v' = Some w'
    ∧ value_lifted statics' w w'.
Proof.
  intros Hv. unfold project_value_slot.
  destruct (closure_in_set statics v) as [[[at_slot decls] slots] | ] eqn:Hc;
    [ | discriminate ].
  destruct (closure_in_set_lifted v v' at_slot decls slots Hv Hc)
    as (slots' & -> & Hslots).
  destruct (Pos.eqb at_slot project_from); [ | discriminate ].
  exact (lookup_slots_lifted statics' slot slots slots' w Hslots).
Qed.

Lemma project_function_slot_lifted (move_from move_to : function_slot)
    (v v' w : value) :
  value_lifted statics' v v' ->
  project_function_slot statics move_from move_to v = Some w ->
  ∃ w' : value,
    project_function_slot statics' move_from move_to v' = Some w'
    ∧ value_lifted statics' w w'.
Proof.
  intros Hv. unfold project_function_slot.
  lifted_cases Hv; try discriminate.
  - (* A symbol: bound alike in both runs. *)
    destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hs;
      [ | discriminate ].
    destruct (proj2 Hstatics s allocated Hs) as (allocated' & -> & Hallocated).
    allocated_cases Hallocated; try discriminate.
    + destruct (Pos.eqb move_from unnamed_function_slot); [ | discriminate ].
      destruct (Pos.eqb move_to unnamed_function_slot); [ | discriminate ].
      intros [= <-]. eexists. split; [ reflexivity | apply Lifted_symbol ].
    + destruct (Pos.eqb afslot move_from); [ | discriminate ].
      destruct (lookup afslot adecls); [ | discriminate ].
      destruct (lookup move_to adecls); [ | discriminate ]. simpl.
      destruct (lookup move_to asyms) as [s' | ]; [ | discriminate ]. simpl.
      intros [= <-]. eexists. split; [ reflexivity | apply Lifted_symbol ].
  - (* A closure of a set of one function. *)
    destruct (Pos.eqb move_from unnamed_function_slot); [ | discriminate ].
    destruct (Pos.eqb move_to unnamed_function_slot); [ | discriminate ].
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_closure, Hslots.
  - (* A closure of a set, made by a [Let] in both runs. *)
    destruct (Pos.eqb fslot move_from); [ | discriminate ].
    destruct (lookup fslot decls); [ | discriminate ].
    destruct (lookup move_to decls); [ | discriminate ]. simpl.
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_closure_of_set, Hslots.
  - (* A closure of a set, lifted: the second run has the symbol of the
       slot asked for. *)
    rewrite (Hbound fslot s (lookup_in _ _ _ Hsym)).
    destruct (Pos.eqb fslot move_from); [ | discriminate ].
    destruct (lookup fslot decls); [ | discriminate ].
    destruct (lookup move_to decls) as [code' | ] eqn:Hto; [ | discriminate ].
    simpl.
    destruct (lookup_same_keys move_to decls syms (eq_sym Hsyms) code' Hto)
      as [s' Hs'].
    rewrite Hs'. simpl. intros [= <-]. eexists. split; [ reflexivity | ].
    exact (Lifted_to_closure statics' move_to decls slots slots' s' syms Hs'
             Hsyms Hbound Hslots).
  - (* A closure of a set of one function, lifted. *)
    rewrite Hlookup.
    destruct (Pos.eqb move_from unnamed_function_slot); [ | discriminate ].
    destruct (Pos.eqb move_to unnamed_function_slot); [ | discriminate ].
    intros [= <-]. eexists. split; [ reflexivity | ].
    exact (Lifted_to_unnamed_closure statics' code slots slots' s Hlookup
             Hslots).
Qed.

(* The relation is one that the observations cannot tell from equality,
   so no primitive can. *)
Lemma value_lifted_respects :
  respects_observations (value_lifted statics') statics statics'.
Proof.
  split; [ | split ].
  - split.
    + intros c v' Hv. inversion Hv. reflexivity.
    + intros v c Hv. inversion Hv. reflexivity.
  - split.
    + intros c. split; constructor.
    + intros tag fields fields' Hfields. constructor. exact Hfields.
  - intros v v' Hv. split; [ | split; [ | split; [ | split ] ] ].
    + intros tag fields. exact (block_of_lifted v v' tag fields Hv).
    + intros c. exact (boxed_number_of_lifted v v' c Hv).
    + intros bytes. exact (string_of_lifted v v' bytes Hv).
    + intros Hclosure.
      destruct (closure_of statics v) as [[called cslots] | ] eqn:Hc;
        [ | congruence ].
      destruct (closure_of_lifted v v' called cslots Hv Hc)
        as (cslots' & -> & _).
      discriminate.
    + lifted_cases Hv; simpl; try reflexivity.
      * destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hs;
          [ | discriminate ].
        destruct (proj2 Hstatics s allocated Hs) as (allocated' & -> & _).
        reflexivity.
      * rewrite Hlookup. reflexivity.
      * rewrite Hlookup. reflexivity.
      * rewrite (Hbound fslot s (lookup_in _ _ _ Hsym)). reflexivity.
      * rewrite Hlookup. reflexivity.
Qed.

Lemma eval_prim_lifted (p : prim) (vs vs' : list value) (v : value) :
  Forall2 (value_lifted statics') vs vs' ->
  eval_prim statics p vs = Some v ->
  ∃ v' : value, eval_prim statics' p vs' = Some v' ∧ value_lifted statics' v v'.
Proof.
  exact
    (eval_prim_related (value_lifted statics') statics statics' p vs vs' v
       value_lifted_respects).
Qed.

End Observations.

(* ======================================================================== *)
(* Evaluation in lifted environments                                        *)
(* ======================================================================== *)

(* Every variable of the first environment is bound in the second, to
   its value lifted. *)
Definition env_lifted (statics' : static_env) (vars vars' : env) : Prop :=
  ∀ (x : variable) (v : value),
    lookup x vars = Some v ->
    ∃ v' : value, lookup x vars' = Some v' ∧ value_lifted statics' v v'.

Lemma env_lifted_extend (statics' statics'' : static_env) (vars vars' : env) :
  statics_extend statics' statics'' ->
  env_lifted statics' vars vars' ->
  env_lifted statics'' vars vars'.
Proof.
  intros Hextend Hvars x v Hx. destruct (Hvars x v Hx) as (v' & Hx' & Hv).
  exists v'. split; [ exact Hx' | ].
  exact (value_lifted_extend _ _ Hextend _ _ Hv).
Qed.

Lemma env_lifted_cons (statics' : static_env) (x : variable) (v v' : value)
    (vars vars' : env) :
  value_lifted statics' v v' ->
  env_lifted statics' vars vars' ->
  env_lifted statics' ((x, v) :: vars) ((x, v') :: vars').
Proof.
  intros Hv Hvars y w. simpl.
  destruct (Pos.eqb y x); [ intros [= <-]; eauto | apply Hvars ].
Qed.

Lemma bind_params_lifted (statics' : static_env) (params : list variable) :
  ∀ (vs vs' : list value) (vars vars' bound : env),
    Forall2 (value_lifted statics') vs vs' ->
    env_lifted statics' vars vars' ->
    bind_params params vs vars = Some bound ->
    ∃ bound' : env,
      bind_params params vs' vars' = Some bound'
      ∧ env_lifted statics' bound bound'.
Proof.
  induction params as [ | p params IH]; intros vs vs' vars vars' bound Hvs;
    destruct Hvs as [ | v v' vs vs' Hv Hvs]; simpl; try discriminate.
  - intros Hvars [= <-]. eauto.
  - intros Hvars. apply (IH vs vs' _ _ bound Hvs).
    apply env_lifted_cons; assumption.
Qed.

Lemma eval_simple_lifted (statics' : static_env) (vars vars' : env)
    (s : simple) (v : value) :
  env_lifted statics' vars vars' ->
  eval_simple vars s = Some v ->
  ∃ v' : value, eval_simple vars' s = Some v' ∧ value_lifted statics' v v'.
Proof.
  intros Hvars. destruct s as [x | sym | c]; simpl.
  - apply Hvars.
  - intros [= <-]. eexists. split; [ reflexivity | apply Lifted_symbol ].
  - intros [= <-]. eexists. split; [ reflexivity | apply Lifted_const ].
Qed.

Lemma eval_simples_lifted (statics' : static_env) (vars vars' : env)
    (args : list simple) :
  env_lifted statics' vars vars' ->
  ∀ vs : list value,
    eval_simples vars args = Some vs ->
    ∃ vs' : list value,
      eval_simples vars' args = Some vs'
      ∧ Forall2 (value_lifted statics') vs vs'.
Proof.
  intros Hvars. induction args as [ | s args IH]; intros vs; simpl.
  - intros [= <-]. exists []. auto.
  - destruct (eval_simple vars s) as [v | ] eqn:Hs; [ | discriminate ].
    destruct (eval_simples vars args) as [rest | ]; [ | discriminate ].
    intros [= <-].
    destruct (eval_simple_lifted statics' vars vars' s v Hvars Hs)
      as (v' & -> & Hv).
    destruct (IH rest eq_refl) as (rest' & -> & Hrest).
    exists (v' :: rest'). auto.
Qed.

Lemma eval_value_slots_lifted (statics' : static_env) (vars vars' : env)
    (slots : list (value_slot * simple)) :
  env_lifted statics' vars vars' ->
  ∀ evaluated : list (value_slot * value),
    eval_value_slots vars slots = Some evaluated ->
    ∃ evaluated' : list (value_slot * value),
      eval_value_slots vars' slots = Some evaluated'
      ∧ Forall2 (slot_lifted (value_lifted statics')) evaluated evaluated'.
Proof.
  intros Hvars. induction slots as [ | [slot s] slots IH]; intros evaluated;
    simpl.
  - intros [= <-]. exists []. auto.
  - destruct (eval_simple vars s) as [v | ] eqn:Hs; [ | discriminate ].
    destruct (eval_value_slots vars slots) as [rest | ]; [ | discriminate ].
    intros [= <-].
    destruct (eval_simple_lifted statics' vars vars' s v Hvars Hs)
      as (v' & -> & Hv).
    destruct (IH rest eq_refl) as (rest' & -> & Hrest).
    exists ((slot, v') :: rest'). split; [ reflexivity | ].
    constructor; [ split; [ reflexivity | exact Hv ] | exact Hrest ].
Qed.

(* A defining expression that has a value in the first run has one in
   the second, lifted. *)
Lemma eval_named_lifted (statics statics' : static_env) (vars vars' : env)
    (d : named) (v : value) :
  statics_lifted statics statics' ->
  env_lifted statics' vars vars' ->
  eval_named statics vars d = Some v ->
  ∃ v' : value,
    eval_named statics' vars' d = Some v' ∧ value_lifted statics' v v'.
Proof.
  intros Hstatics Hvars.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure]; simpl.
  - exact (eval_simple_lifted statics' vars vars' s v Hvars).
  - destruct (eval_simples vars args) as [vs | ] eqn:Hargs;
      [ | discriminate ].
    destruct (eval_simples_lifted statics' vars vars' args Hvars vs Hargs)
      as (vs' & -> & Hvs).
    exact (eval_prim_lifted statics statics' Hstatics p vs vs' v Hvs).
  - destruct (eval_value_slots vars slots) as [vs | ] eqn:Hslots;
      [ | discriminate ].
    destruct (eval_value_slots_lifted statics' vars vars' slots Hvars vs
                Hslots)
      as (vs' & -> & Hvs).
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_closure, Hvs.
  - destruct (lookup fslot decls); [ | discriminate ]. simpl.
    destruct (eval_value_slots vars slots) as [vs | ] eqn:Hslots;
      [ | discriminate ].
    destruct (eval_value_slots_lifted statics' vars vars' slots Hvars vs
                Hslots)
      as (vs' & -> & Hvs).
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_closure_of_set, Hvs.
  - destruct (eval_simple vars closure) as [w | ] eqn:Hclosure;
      [ | discriminate ].
    destruct (eval_simple_lifted statics' vars vars' closure w Hvars Hclosure)
      as (w' & -> & Hw).
    simpl.
    destruct (closure_of statics w) as [[called cslots] | ] eqn:Hc;
      [ | discriminate ].
    destruct (closure_of_lifted statics statics' Hstatics w w' called cslots
                Hw Hc)
      as (cslots' & -> & Hcslots).
    simpl. exact (lookup_slots_lifted statics' slot cslots cslots' v Hcslots).
  - destruct (eval_simple vars closure) as [w | ] eqn:Hclosure;
      [ | discriminate ].
    destruct (eval_simple_lifted statics' vars vars' closure w Hvars Hclosure)
      as (w' & -> & Hw).
    exact (project_value_slot_lifted statics statics' Hstatics pfrom slot w
             w' v Hw).
  - destruct (eval_simple vars closure) as [w | ] eqn:Hclosure;
      [ | discriminate ].
    destruct (eval_simple_lifted statics' vars vars' closure w Hvars Hclosure)
      as (w' & -> & Hw).
    exact (project_function_slot_lifted statics statics' Hstatics move_from
             move_to w w' v Hw).
Qed.

Lemma eval_static_const_lifted (statics' : static_env) (vars vars' : env)
    (const : static_const) (allocated : statically_allocated_value) :
  env_lifted statics' vars vars' ->
  eval_static_const vars const = Some allocated ->
  ∃ allocated' : statically_allocated_value,
    eval_static_const vars' const = Some allocated'
    ∧ allocated_lifted statics' allocated allocated'.
Proof.
  intros Hvars.
  destruct const
    as [code slots | fslot syms decls slots | tag fields | contents | bytes];
    simpl.
  - destruct (eval_value_slots vars slots) as [vs | ] eqn:Hslots;
      [ | discriminate ].
    destruct (eval_value_slots_lifted statics' vars vars' slots Hvars vs
                Hslots)
      as (vs' & -> & Hvs).
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_static_closure, Hvs.
  - destruct (lookup fslot decls); [ | discriminate ]. simpl.
    destruct (eval_value_slots vars slots) as [vs | ] eqn:Hslots;
      [ | discriminate ].
    destruct (eval_value_slots_lifted statics' vars vars' slots Hvars vs
                Hslots)
      as (vs' & -> & Hvs).
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_static_closure_of_set, Hvs.
  - destruct (eval_simples vars fields) as [vs | ] eqn:Hfields;
      [ | discriminate ].
    destruct (eval_simples_lifted statics' vars vars' fields Hvars vs Hfields)
      as (vs' & -> & Hvs).
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_static_block, Hvs.
  - destruct (eval_simple vars contents) as [w | ] eqn:Hcontents;
      [ | discriminate ].
    destruct (eval_simple_lifted statics' vars vars' contents w Hvars
                Hcontents)
      as (w' & -> & Hw).
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_static_boxed_number, Hw.
  - intros [= <-]. eexists. split; [ reflexivity | ].
    apply Lifted_static_string.
Qed.

(* ======================================================================== *)
(* Static bindings                                                          *)
(* ======================================================================== *)

(* A group that the machine does not refuse for binding a symbol twice:
   its symbols are distinct, and none is bound. *)
Lemma no_rebinding (statics' : static_env) (bindings : list static_binding) :
  rebinds symbols_of_binding (symbol_bound statics') bindings = false ->
  distinct (flat_map symbols_of_binding bindings) = true
  ∧ ∀ s : symbol,
      s ∈ flat_map symbols_of_binding bindings ->
      lookup s (static_values statics') = None.
Proof.
  unfold rebinds. intros Hrebinds.
  apply orb_false_iff in Hrebinds as [Hdistinct Hbound].
  apply negb_false_iff in Hdistinct. split; [ exact Hdistinct | ].
  intros s Hin.
  destruct (lookup s (static_values statics')) eqn:Hs; [ | reflexivity ].
  exfalso.
  assert (Hexists :
    existsb (symbol_bound statics') (flat_map symbols_of_binding bindings)
    = true).
  { apply existsb_exists. exists s. split; [ exact Hin | ].
    unfold symbol_bound. rewrite Hs. reflexivity. }
  exact (eq_true_false_abs _ Hexists Hbound).
Qed.

(* A symbol that is not bound may be bound: what was bound stays so. *)
Lemma statics_extend_symbol (statics' : static_env) (s : symbol)
    (allocated : statically_allocated_value) :
  lookup s (static_values statics') = None ->
  statics_extend statics'
    (Static_env (static_code statics')
       ((s, allocated) :: static_values statics')).
Proof.
  intros Hfresh. split; simpl; [ auto | ].
  intros s0 a Hs0. exact (lookup_fresh s0 s a allocated _ Hfresh Hs0).
Qed.

(* A group of bindings that the first run evaluates, the second does,
   given that it binds none of the symbols already: the same group, in
   lifted environments, gives lifted static environments. *)
Lemma eval_static_bindings_lifted (vars vars' : env) :
  ∀ (bindings : list static_binding) (statics statics' extended : static_env),
    env_lifted statics' vars vars' ->
    statics_lifted statics statics' ->
    distinct (flat_map symbols_of_binding bindings) = true ->
    (∀ s : symbol,
      s ∈ flat_map symbols_of_binding bindings ->
      lookup s (static_values statics') = None) ->
    eval_static_bindings vars bindings statics = Some extended ->
    ∃ extended' : static_env,
      eval_static_bindings vars'
        (map (bind_my_closures_in_binding known) bindings) statics'
      = Some extended'
      ∧ statics_lifted extended extended'.
Proof.
  induction bindings as [ | binding bindings IH];
    intros statics statics' extended Hvars Hstatics Hdistinct Hfresh; simpl.
  - intros [= <-]. eauto.
  - destruct binding as [id c | id | sym const];
      simpl in Hdistinct, Hfresh |- *.
    + (* Code: bound alike in both. *)
      destruct (lookup id (static_code statics)) eqn:Hid; [ discriminate | ].
      assert (Hid' : lookup id (static_code statics') = None)
        by (rewrite (proj1 Hstatics id), Hid; reflexivity).
      rewrite Hid'.
      assert (Hextend :
        statics_extend statics'
          (Static_env
             ((id, bind_my_closure known id c) :: static_code statics')
             (static_values statics'))).
      { split; simpl; [ | auto ]. intros id0 c0 Hid0.
        exact (lookup_fresh id0 id c0 _ _ Hid' Hid0). }
      apply IH;
        [ exact (env_lifted_extend _ _ _ _ Hextend Hvars) |
        | exact Hdistinct | exact Hfresh ].
      split; simpl.
      * intros id0. destruct (Pos.eqb_spec id0 id) as [-> | _];
          [ reflexivity | apply (proj1 Hstatics) ].
      * intros s a Hs. destruct (proj2 Hstatics s a Hs) as (a' & Hs' & Ha).
        exists a'. split; [ exact Hs' | ].
        exact (allocated_lifted_extend _ _ _ _ Hextend Ha).
    + apply IH; assumption.
    + (* A symbol: not bound in the second run either. *)
      destruct (lookup sym (static_values statics)) eqn:Hsym;
        [ discriminate | ].
      destruct (eval_static_const vars const) as [allocated | ] eqn:Hconst;
        [ | discriminate ].
      simpl. rewrite (Hfresh sym (or_introl eq_refl)).
      destruct (eval_static_const_lifted statics' vars vars' const allocated
                  Hvars Hconst)
        as (allocated' & -> & Hallocated).
      simpl. apply andb_true_iff in Hdistinct as [Hnotin Hdistinct].
      pose proof (statics_extend_symbol statics' sym allocated'
        (Hfresh sym (or_introl eq_refl))) as Hextend.
      apply IH;
        [ exact (env_lifted_extend _ _ _ _ Hextend Hvars) |
        | exact Hdistinct | ].
      * split; [ exact (proj1 Hstatics) | ].
        intros s a. cbn [static_values]. rewrite lookup_cons.
        destruct (Pos.eqb_spec s sym) as [-> | Hother].
        -- intros [= <-]. exists allocated'.
           split; [ apply lookup_head | ].
           exact (allocated_lifted_extend _ _ _ _ Hextend Hallocated).
        -- intros Hs. destruct (proj2 Hstatics s a Hs) as (a' & Hs' & Ha).
           exists a'. split; [ rewrite lookup_other; assumption | ].
           exact (allocated_lifted_extend _ _ _ _ Hextend Ha).
      * intros s Hin. cbn [static_values].
        rewrite lookup_other; [ apply Hfresh; right; exact Hin | ].
        intros ->. apply negb_true_iff in Hnotin.
        apply (proj2 (among_In _ _)) in Hin.
        exact (eq_true_false_abs _ Hin Hnotin).
Qed.

(* The bindings of a static set of closures bind its symbols. *)
Lemma bind_closures_symbols (syms : list (function_slot * symbol))
    (decls : list (function_slot * code_id))
    (slots : list (value_slot * simple)) :
  flat_map symbols_of_binding (bind_closures syms decls slots) = map snd syms.
Proof.
  unfold bind_closures. generalize syms at 1 as all.
  intros all. induction syms as [ | [slot s] syms IH]; simpl;
    [ reflexivity | ].
  rewrite IH. reflexivity.
Qed.

(* They are evaluated, where the value slots have values, every function
   slot that has a symbol is one of the set, and the symbols are distinct
   and not bound. Code is not touched. [all] is the whole set, kept apart
   from the symbols still to be bound. *)
Lemma eval_closure_bindings (vars' : env)
    (all : list (function_slot * symbol))
    (decls : list (function_slot * code_id))
    (slots : list (value_slot * simple))
    (slot_values : list (value_slot * value)) :
  eval_value_slots vars' slots = Some slot_values ->
  ∀ (rest : list (function_slot * symbol)) (statics' : static_env),
    (∀ (slot : function_slot) (s : symbol),
      (slot, s) ∈ rest -> lookup slot decls <> None) ->
    distinct (map snd rest) = true ->
    (∀ s : symbol,
      s ∈ map snd rest -> lookup s (static_values statics') = None) ->
    ∃ extended' : static_env,
      eval_static_bindings vars'
        (map
           (fun '(slot, s) =>
              Bind_symbol s
                (Static_const_closure_of_set slot all decls slots))
           rest)
        statics'
      = Some extended'
      ∧ static_code extended' = static_code statics'.
Proof.
  intros Hslots.
  induction rest as [ | [slot s] rest IH]; intros statics' Hdecls Hdistinct
    Hfresh; simpl.
  - eauto.
  - simpl in Hdistinct, Hfresh.
    rewrite (Hfresh s (or_introl eq_refl)).
    destruct (lookup slot decls) as [code | ] eqn:Hcode;
      [ | destruct (Hdecls slot s (or_introl eq_refl) Hcode) ].
    simpl. rewrite Hslots. simpl.
    apply andb_true_iff in Hdistinct as [Hnotin Hdistinct].
    destruct
      (IH
         (Static_env (static_code statics')
            ((s, Static_closure_of_set slot all decls slot_values)
             :: static_values statics')))
      as (extended' & Heval & Hcode');
      [ intros slot' s' Hin; apply (Hdecls slot' s'); right; exact Hin
      | exact Hdistinct | | eauto ].
    intros s' Hin. cbn [static_values].
    rewrite lookup_other; [ apply Hfresh; right; exact Hin | ].
    intros ->. apply negb_true_iff in Hnotin.
    apply (proj2 (among_In _ _)) in Hin.
    exact (eq_true_false_abs _ Hin Hnotin).
Qed.

(* The three [Let]s that are lifted. The second run binds the symbols,
   which it can as none is bound, and the value the first run made is
   the symbol's, lifted. *)
Lemma lift_named_lifted (target : lift_to) (d : named)
    (bindings : list static_binding) (s : symbol)
    (statics statics' : static_env) (vars vars' : env) (v : value) :
  lift_named target d = Some (bindings, s) ->
  statics_lifted statics statics' ->
  env_lifted statics' vars vars' ->
  eval_named statics vars d = Some v ->
  distinct (flat_map symbols_of_binding bindings) = true ->
  (∀ s0 : symbol,
    s0 ∈ flat_map symbols_of_binding bindings ->
    lookup s0 (static_values statics') = None) ->
  ∃ extended' : static_env,
    eval_static_bindings vars' bindings statics' = Some extended'
    ∧ static_code extended' = static_code statics'
    ∧ value_lifted extended' v (Value_symbol s).
Proof.
  intros Hlift Hstatics Hvars Heval Hdistinct Hfresh.
  destruct target as [sym | syms].
  - destruct d as [ | p args | code slots | | | | ]; simpl in Hlift;
      try discriminate.
    2: { (* A closure of a set of one function. *)
      injection Hlift as <- <-. simpl in Heval.
      destruct (eval_value_slots vars slots) as [vs | ] eqn:Hslots;
        [ | discriminate ].
      injection Heval as <-.
      destruct (eval_value_slots_lifted statics' vars vars' slots Hvars vs
                  Hslots)
        as (vs' & Hslots' & Hvs).
      simpl. rewrite (Hfresh sym (or_introl eq_refl)), Hslots'. simpl.
      eexists. split; [ reflexivity | ]. split; [ reflexivity | ].
      apply (Lifted_to_unnamed_closure _ code vs vs' sym);
        [ simpl; apply lookup_head | ].
      refine (slots_lifted_extend _ _ _ _ _ Hvs).
      exact (statics_extend_symbol statics' sym _
               (Hfresh sym (or_introl eq_refl))). }
    destruct p as [p | p | p | p]; simpl in Hlift; try discriminate.
    + (* A boxed number. *)
      destruct p; simpl in Hlift; try discriminate.
      destruct args as [ | contents [ | arg args]]; simpl in Hlift;
        try discriminate.
      injection Hlift as <- <-. simpl in Heval.
      destruct (eval_simple vars contents) as [w | ] eqn:Hcontents;
        [ | discriminate ].
      rewrite eval_prim_unary in Heval. simpl in Heval.
      destruct w as [number | | | | | | ]; try discriminate.
      destruct (is_number_of_kind kind number); [ | discriminate ].
      injection Heval as <-.
      destruct (eval_simple_lifted statics' vars vars' contents _ Hvars
                  Hcontents)
        as (w' & Hcontents' & Hw).
      inversion Hw; subst w'.
      simpl. rewrite (Hfresh sym (or_introl eq_refl)), Hcontents'. simpl.
      eexists. split; [ reflexivity | ]. split; [ reflexivity | ].
      apply Lifted_to_boxed_number. simpl. apply lookup_head.
    + (* A block. *)
      destruct p as [[tag]]. simpl in Hlift. injection Hlift as <- <-.
      simpl in Heval.
      destruct (eval_simples vars args) as [vs | ] eqn:Hargs;
        [ | discriminate ].
      rewrite eval_prim_variadic in Heval. simpl in Heval.
      destruct
        (forallb (fun v => kind_eqb (kind_of_value v) Value) vs
         && forallb (bound_if_symbol statics) vs);
        [ | discriminate ].
      injection Heval as <-.
      destruct (eval_simples_lifted statics' vars vars' args Hvars vs Hargs)
        as (vs' & Hargs' & Hvs).
      simpl. rewrite (Hfresh sym (or_introl eq_refl)), Hargs'. simpl.
      eexists. split; [ reflexivity | ]. split; [ reflexivity | ].
      apply (Lifted_to_block _ tag vs vs' sym); [ simpl; apply lookup_head | ].
      refine (values_lifted_extend _ _ _ _ _ Hvs).
      exact (statics_extend_symbol statics' sym _
               (Hfresh sym (or_introl eq_refl))).
  - (* A closure of a set. *)
    destruct d as [ | | | fslot decls slots | | | ]; simpl in Hlift;
      try discriminate.
    destruct (lookup fslot syms) as [s1 | ] eqn:Hsym; [ | discriminate ].
    destruct (list_eq_dec Pos.eq_dec (map fst syms) (map fst decls))
      as [Hsyms | ];
      [ | discriminate ].
    injection Hlift as <- <-. simpl in Heval.
    destruct (lookup fslot decls) as [code | ]; [ | discriminate ].
    simpl in Heval.
    destruct (eval_value_slots vars slots) as [vs | ] eqn:Hslots;
      [ | discriminate ].
    injection Heval as <-.
    destruct (eval_value_slots_lifted statics' vars vars' slots Hvars vs
                Hslots)
      as (vs' & Hslots' & Hvs).
    rewrite bind_closures_symbols in Hdistinct, Hfresh.
    destruct (eval_closure_bindings vars' syms decls slots vs' Hslots' syms
                statics')
      as (extended' & Hextended & Hcode);
      [ | exact Hdistinct | exact Hfresh | ].
    { intros slot s0 Hin Hnone.
      apply (lookup_none_not_in slot decls Hnone).
      pose proof (in_map fst syms (slot, s0) Hin) as Hslot.
      rewrite Hsyms in Hslot. exact Hslot. }
    exists extended'. split; [ exact Hextended | ]. split; [ exact Hcode | ].
    apply (Lifted_to_closure extended' fslot decls vs vs' s1 syms Hsym Hsyms).
    + exact (bind_closures_binds vars' syms decls slots vs' statics' extended'
               Hslots' Hextended).
    + refine (slots_lifted_extend _ _ _ _ _ Hvs).
      exact (eval_static_bindings_extend vars' _ statics' extended' Hextended).
Qed.

(* The bindings that stand for a lifted [Let] bind symbols only, so
   binding [my_closure] in code changes nothing in them. *)
Lemma lift_named_no_code (target : lift_to) (d : named)
    (bindings : list static_binding) (s : symbol) :
  lift_named target d = Some (bindings, s) ->
  map (bind_my_closures_in_binding known) bindings = bindings.
Proof.
  intros Hlift. destruct target as [sym | syms].
  - destruct d as [ | p args | code slots | | | | ]; simpl in Hlift;
      try discriminate.
    2: { injection Hlift as <- <-. reflexivity. }
    destruct p as [p | p | p | p]; simpl in Hlift; try discriminate.
    + destruct p; simpl in Hlift; try discriminate.
      destruct args as [ | contents [ | arg args]]; simpl in Hlift;
        try discriminate.
      injection Hlift as <- <-. reflexivity.
    + destruct p as [[tag]]. simpl in Hlift. injection Hlift as <- <-.
      reflexivity.
  - destruct d as [ | | | fslot decls slots | | | ]; simpl in Hlift;
      try discriminate.
    destruct (lookup fslot syms) as [s1 | ]; [ | discriminate ].
    destruct (list_eq_dec Pos.eq_dec (map fst syms) (map fst decls));
      [ | discriminate ].
    injection Hlift as <- <-. unfold bind_closures. rewrite map_map.
    apply map_ext. intros [slot' s']. reflexivity.
Qed.

(* ======================================================================== *)
(* Continuations and states                                                 *)
(* ======================================================================== *)

(* With no [Let] to lift, the term is left as it is. So code and the
   handlers of recursive continuations, which [lift_expr] does not go
   into, are themselves lifted. *)
Fixpoint lift_expr_nil (at_path : path) (e : expr) {struct e} :
  lift_expr [] at_path e = e
with lift_handler_nil (at_path : path) (h : continuation_handler)
    {struct h} :
  lift_handler [] at_path h = h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite lift_expr_nil. reflexivity.
    + rewrite lift_expr_nil. reflexivity.
    + rewrite lift_handler_nil, lift_expr_nil. reflexivity.
    + rewrite lift_expr_nil. reflexivity.
  - destruct h as [params metadata handler]. simpl. rewrite lift_expr_nil.
    reflexivity.
Qed.

Definition bind_my_closures_in_handlers
    (handlers : list (continuation * continuation_handler))
    : list (continuation * continuation_handler) :=
  map (fun '(k, h) => (k, bind_my_closures_in_handler known h)) handlers.

(* A continuation of the first run and one of the second: the same way
   out, or closures of a handler and of that handler rewritten, with
   lifted environments. The handlers of a recursive group are not gone
   into for [Let]s to lift. *)
#[local] Set Warnings "-register-all".
Inductive cont_lifted (statics' : static_env)
    : cont_value -> cont_value -> Prop :=
  | Outer_lifted (k : continuation) : cont_lifted statics' (Outer k) (Outer k)
  | Closure_lifted (lets : list (path * lift_to)) (at_path : path)
      (h : continuation_handler) (vars vars' : env) (conts conts' : cont_env)
      (recursive : list (continuation * continuation_handler)) :
    env_lifted statics' vars vars' ->
    Forall2
      (fun kc kc' =>
         fst kc = fst kc' ∧ cont_lifted statics' (snd kc) (snd kc'))
      conts conts' ->
    cont_lifted statics' (Closure h vars conts recursive)
      (Closure
         (bind_my_closures_in_handler known (lift_handler lets at_path h))
         vars' conts' (bind_my_closures_in_handlers recursive))
  | Extra_args_lifted (c c' : cont_value) (extra extra' : list value) :
    cont_lifted statics' c c' ->
    Forall2 (value_lifted statics') extra extra' ->
    cont_lifted statics' (Extra_args c extra) (Extra_args c' extra').

Definition conts_lifted (statics' : static_env) (conts conts' : cont_env)
    : Prop :=
  Forall2
    (fun kc kc' => fst kc = fst kc' ∧ cont_lifted statics' (snd kc) (snd kc'))
    conts conts'.

Fixpoint cont_lifted_extend (statics' statics'' : static_env)
    (Hextend : statics_extend statics' statics'') (c c' : cont_value)
    (H : cont_lifted statics' c c') {struct H} :
  cont_lifted statics'' c c'.
Proof.
  destruct H
    as [ k | lets at_path h vars vars' conts conts' recursive Hvars Hconts
       | c0 c0' extra extra' Hc0 Hextra ].
  - apply Outer_lifted.
  - apply Closure_lifted;
      [ exact (env_lifted_extend _ _ _ _ Hextend Hvars) | ].
    clear Hvars. revert conts conts' Hconts. fix IH 3.
    intros conts conts' [ | kc kc' rest rest' [Hkey Hhead] Htail];
      constructor;
      [ split;
        [ exact Hkey | exact (cont_lifted_extend _ _ Hextend _ _ Hhead) ]
      | exact (IH _ _ Htail) ].
  - apply Extra_args_lifted;
      [ exact (cont_lifted_extend _ _ Hextend _ _ Hc0)
      | exact (values_lifted_extend _ _ _ _ Hextend Hextra) ].
Qed.

Lemma with_extra_args_lifted (statics' : static_env) (c c' : cont_value)
    (extra extra' : list value) :
  cont_lifted statics' c c' ->
  Forall2 (value_lifted statics') extra extra' ->
  cont_lifted statics' (with_extra_args c extra) (with_extra_args c' extra').
Proof.
  intros Hc Hextra.
  destruct Hextra as [ | v v' extra extra' Hv Hextra]; [ exact Hc | ].
  apply Extra_args_lifted; [ exact Hc | constructor; assumption ].
Qed.

Lemma conts_lifted_extend (statics' statics'' : static_env)
    (conts conts' : cont_env) :
  statics_extend statics' statics'' ->
  conts_lifted statics' conts conts' ->
  conts_lifted statics'' conts conts'.
Proof.
  intros Hextend.
  induction 1 as [ | kc kc' conts conts' [Hkey Hc] _ IH]; constructor;
    [ split; [ exact Hkey | exact (cont_lifted_extend _ _ Hextend _ _ Hc) ]
    | exact IH ].
Qed.

Lemma resolve_lifted (statics' : static_env) (k : continuation)
    (conts conts' : cont_env) :
  conts_lifted statics' conts conts' ->
  cont_lifted statics' (resolve k conts) (resolve k conts').
Proof.
  unfold resolve.
  induction 1 as [ | [k1 c] [k1' c'] conts conts' [Hk Hc] _ IH]; simpl;
    [ apply Outer_lifted | ].
  simpl in Hk. subst k1'. destruct (Pos.eqb k k1); [ exact Hc | exact IH ].
Qed.

(* [all] is the whole group, kept apart from the handlers still to be gone
   through. *)
Lemma rec_closures_lifted_aux (statics' : static_env) (vars vars' : env)
    (conts conts' : cont_env)
    (all handlers : list (continuation * continuation_handler)) :
  env_lifted statics' vars vars' ->
  conts_lifted statics' conts conts' ->
  conts_lifted statics'
    (map (fun '(k, h) => (k, Closure h vars conts all)) handlers)
    (map
       (fun '(k, h) =>
          (k, Closure h vars' conts' (bind_my_closures_in_handlers all)))
       (bind_my_closures_in_handlers handlers)).
Proof.
  intros Hvars Hconts.
  induction handlers as [ | [k h] handlers IH]; simpl; constructor;
    [ | exact IH ].
  split; [ reflexivity | ]. simpl.
  pose proof (Closure_lifted statics' [] root h vars vars' conts conts' all
    Hvars Hconts) as Hclosure.
  rewrite lift_handler_nil in Hclosure. exact Hclosure.
Qed.

Lemma rec_closures_lifted (statics' : static_env) (vars vars' : env)
    (conts conts' : cont_env)
    (handlers : list (continuation * continuation_handler)) :
  env_lifted statics' vars vars' ->
  conts_lifted statics' conts conts' ->
  conts_lifted statics' (rec_closures handlers vars conts ++ conts)
    (rec_closures (bind_my_closures_in_handlers handlers) vars' conts'
     ++ conts').
Proof.
  intros Hvars Hconts. apply Forall2_app; [ | exact Hconts ].
  apply rec_closures_lifted_aux; assumption.
Qed.

(* The first state and the second: the second expression is the first
   with [Let]s lifted and [my_closure] bound in code, and the
   environments are lifted. *)
Inductive state_lifted : state -> state -> Prop :=
  | State_lifted (lets : list (path * lift_to)) (at_path : path) (e : expr)
      (vars vars' : env) (conts conts' : cont_env)
      (statics statics' : static_env) :
    env_lifted statics' vars vars' ->
    conts_lifted statics' conts conts' ->
    statics_lifted statics statics' ->
    state_lifted (State e vars conts statics)
      (State (bind_my_closures known (lift_expr lets at_path e)) vars' conts'
         statics').

(* The values at an exit are lifted, under the static environment that
   the second run has reached. *)
Definition exit_lifted (last : state) (vs vs' : list value) : Prop :=
  Forall2 (value_lifted (state_statics last)) vs vs'.

Lemma apply_cont_value_lifted (c c' : cont_value) (vs vs' : list value)
    (statics statics' : static_env) :
  cont_lifted statics' c c' ->
  Forall2 (value_lifted statics') vs vs' ->
  statics_lifted statics statics' ->
  match apply_cont_value c vs statics with
  | Undefined => True
  | Exit k exit_vs =>
    ∃ exit_vs' : list value,
      apply_cont_value c' vs' statics' = Exit k exit_vs'
      ∧ Forall2 (value_lifted statics') exit_vs exit_vs'
  | Step t =>
    ∃ t' : state,
      apply_cont_value c' vs' statics' = Step t' ∧ state_lifted t t'
  end.
Proof.
  intros Hc. revert vs vs'.
  induction Hc
    as [ k | lets at_path [params handler] vars vars' conts conts' recursive
             Hvars Hconts
       | c c' extra extra' Hc IH Hextra ];
    intros vs vs' Hvs Hstatics; simpl.
  - exists vs'. split; [ reflexivity | exact Hvs ].
  - destruct (bind_params params vs vars) as [bound | ] eqn:Hbind;
      [ | exact I ].
    destruct (bind_params_lifted statics' params vs vs' vars vars' bound Hvs
                Hvars Hbind)
      as (bound' & -> & Hbound).
    eexists. split; [ reflexivity | ].
    apply State_lifted;
      [ exact Hbound | apply rec_closures_lifted; assumption
      | exact Hstatics ].
  - apply IH; [ apply Forall2_app; assumption | exact Hstatics ].
Qed.

(* Binding [my_closure] leaves the arities of code as they are. *)
Lemma bind_my_closure_params_arity (id : code_id) (c : code) :
  code_params_arity (bind_my_closure known id c) = code_params_arity c.
Proof.
  destruct c as [params my_closure ret exn metadata body]. simpl.
  destruct (lookup id known); [ destruct (among my_closure params) | ];
    reflexivity.
Qed.

Lemma bind_my_closure_result_arity (id : code_id) (c : code) :
  code_result_arity (bind_my_closure known id c) = code_result_arity c.
Proof.
  destruct c as [params my_closure ret exn metadata body]. simpl.
  destruct (lookup id known); [ destruct (among my_closure params) | ];
    reflexivity.
Qed.

(* A call. Where the code called has [my_closure] bound to a symbol,
   the second run takes one step more, to bind it; the closure called is
   then that symbol, which is what [Hknown] says of the second run. *)
Lemma call_function_lifted (callee callee' : value) (kind : call_kind)
    (vs vs' : list value) (args_arity return_arity : arity)
    (return_to return_to' exn_to exn_to' : cont_value)
    (statics statics' : static_env) :
  value_lifted statics' callee callee' ->
  Forall2 (value_lifted statics') vs vs' ->
  cont_lifted statics' return_to return_to' ->
  cont_lifted statics' exn_to exn_to' ->
  statics_lifted statics statics' ->
  (∀ (id : code_id) (slots : list (value_slot * value)) (sym : symbol),
    closure_of statics' callee' = Some (id, slots) ->
    lookup id known = Some sym ->
    callee' = Value_symbol sym) ->
  match
    call_function callee kind vs args_arity return_arity return_to exn_to
      statics
  with
  | Undefined => True
  | Exit _ _ => False
  | Step t =>
    ∃ (n : nat) (u' t' : state),
      call_function callee' kind vs' args_arity return_arity return_to'
        exn_to' statics'
      = Step u'
      ∧ run n u' = Step t'
      ∧ state_lifted t t'
  end.
Proof.
  intros Hcallee Hvs Hreturn Hexn Hstatics Hknown. unfold call_function.
  destruct (closure_of statics callee) as [[called slots] | ] eqn:Hc;
    [ | exact I ].
  destruct (closure_of_lifted statics statics' Hstatics callee callee' called
              slots Hcallee Hc)
    as (slots' & Hc' & _).
  rewrite Hc'.
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | exact I ].
  rewrite (proj1 Hstatics called).
  destruct (lookup called (static_code statics)) as [c | ]; [ | exact I ].
  simpl option_map. cbv iota.
  destruct (bind_my_closure_code known called c)
    as (Hparams & Hmy_closure & Hret & Hexn_k & Hbody).
  rewrite Hparams, Hmy_closure, Hret, Hexn_k,
    (bind_my_closure_params_arity called c),
    (bind_my_closure_result_arity called c),
    (kinds_of_values_lifted statics' vs vs' Hvs).
  destruct (binds_statics (code_body c)) eqn:Hbinds; [ exact I | ].
  destruct
    (negb
       (kinds_eqb (map kind_of_value vs) (unarize args_arity)
        && kinds_per_parameter_eqb (unarize_per_parameter args_arity)
             (unarize_per_parameter (code_params_arity c))
        && arity_eqb return_arity (code_result_arity c)));
    [ exact I | ].
  destruct (bind_params (code_params c) vs [(code_my_closure c, callee)])
    as [bound | ] eqn:Hbind;
    [ | exact I ].
  destruct (bind_params_lifted statics' (code_params c) vs vs'
              [(code_my_closure c, callee)] [(code_my_closure c, callee')]
              bound Hvs)
    as (bound' & Hbind' & Hbound);
    [ apply env_lifted_cons; [ exact Hcallee | intros x v [=] ]
    | exact Hbind | ].
  assert (Hconts :
    conts_lifted statics'
      [(code_return_continuation c, return_to);
       (code_exn_continuation c, exn_to)]
      [(code_return_continuation c, return_to');
       (code_exn_continuation c, exn_to')]).
  { constructor; [ split; [ reflexivity | exact Hreturn ] | ].
    constructor; [ split; [ reflexivity | exact Hexn ] | ].
    constructor. }
  destruct Hbody as [Hbody | (sym & Hsym & Hparam & Hbody)]; rewrite Hbody.
  - (* [my_closure] is not bound in this code. *)
    rewrite bind_my_closures_binds_statics, Hbinds, Hbind'.
    eexists 0, _, _. split; [ reflexivity | ]. split; [ reflexivity | ].
    pose proof (State_lifted [] root (code_body c) bound bound' _ _ statics
      statics' Hbound Hconts Hstatics) as Hstate.
    rewrite lift_expr_nil in Hstate. exact Hstate.
  - (* It is: one step more, and the closure called is the symbol. *)
    simpl binds_statics.
    rewrite bind_my_closures_binds_statics, Hbinds, Hbind'.
    eexists 1, _,
      (State (bind_my_closures known (code_body c))
         ((code_my_closure c, Value_symbol sym) :: bound')
         [(code_return_continuation c, return_to');
          (code_exn_continuation c, exn_to')]
         statics').
    split; [ reflexivity | ].
    split; [ simpl; rewrite step_let; reflexivity | ].
    pose proof (State_lifted [] root (code_body c) bound
      ((code_my_closure c, Value_symbol sym) :: bound')
      [(code_return_continuation c, return_to);
       (code_exn_continuation c, exn_to)]
      [(code_return_continuation c, return_to');
       (code_exn_continuation c, exn_to')]
      statics statics')
      as Hstate.
    rewrite lift_expr_nil in Hstate. apply Hstate; [ | exact Hconts
                                                   | exact Hstatics ].
    intros x v Hx. simpl.
    destruct (Pos.eqb_spec x (code_my_closure c)) as [-> | _];
      [ | exact (Hbound x v Hx) ].
    rewrite (bind_params_lookup_other (code_my_closure c) (code_params c) vs
               _ bound Hparam Hbind), lookup_head in Hx.
    injection Hx as <-. exists (Value_symbol sym). split; [ reflexivity | ].
    rewrite (Hknown called slots' sym Hc' Hsym) in Hcallee. exact Hcallee.
Qed.

Lemma naked_immediate_lifted (statics' : static_env) (v v' : value) (i : Z) :
  value_lifted statics' v v' ->
  naked_immediate_of_value v = Some i ->
  naked_immediate_of_value v' = Some i.
Proof.
  intros Hv. lifted_cases Hv; simpl; try discriminate. exact (fun H => H).
Qed.

(* At a call, the closure called in the second run is the symbol that
   [known] gives its code, if it gives one. *)
Definition callee_known (s' : state) : Prop :=
  ∀ (ap : apply_expr) (callee : value) (id : code_id)
    (slots : list (value_slot * value)) (sym : symbol),
    state_expr s' = Apply ap ->
    eval_simple (state_vars s') (ap_callee ap) = Some callee ->
    closure_of (state_statics s') callee = Some (id, slots) ->
    lookup id known = Some sym ->
    callee = Value_symbol sym.

(* A step of the first state is answered by the second, which is the
   state of a run that never binds a static name twice and that calls
   the code of [known] through its symbols: in one step, or in two where
   the first executes a [Let] that is lifted or calls code in which
   [my_closure] is bound. *)
Lemma lifted_step (s s' : state) :
  state_lifted s s' ->
  static_fault s' = false ->
  callee_known s' ->
  answered state_lifted exit_lifted (step s) s'.
Proof.
  intros [lets at_path e vars vars' conts conts' statics statics' Hvars
            Hconts Hstatics] Hfault Hknown.
  destruct e
    as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ].
  - (* Let *)
    rewrite step_let.
    destruct (eval_named statics vars d) as [v | ] eqn:Hd; [ | exact I ].
    assert (Hkept :
      answered state_lifted exit_lifted
        (Step (State body ((x, v) :: vars) conts statics))
        (State
           (bind_my_closures known
              (Let x xkind d (lift_expr lets (xO at_path) body)))
           vars' conts' statics')).
    { destruct (eval_named_lifted statics statics' vars vars' d v Hstatics
                  Hvars Hd)
        as (v' & Hd' & Hv).
      exists 0, (State
                   (bind_my_closures known (lift_expr lets (xO at_path) body))
                   ((x, v') :: vars') conts' statics').
      split; [ simpl; rewrite step_let, Hd'; reflexivity | ].
      apply State_lifted;
        [ apply env_lifted_cons; assumption | exact Hconts | exact Hstatics ].
    }
    simpl lift_expr in *.
    destruct (lookup at_path lets) as [target | ]; [ | exact Hkept ].
    destruct (lift_named target d) as [[bindings s0] | ] eqn:Hlift;
      [ | exact Hkept ].
    clear Hkept. simpl bind_my_closures in *.
    rewrite (lift_named_no_code target d bindings s0 Hlift) in *.
    unfold static_fault in Hfault. simpl_state.
    apply orb_false_iff in Hfault as [_ Hfault].
    destruct (no_rebinding statics' bindings Hfault) as [Hdistinct Hfresh].
    destruct (lift_named_lifted target d bindings s0 statics statics' vars
                vars' v Hlift Hstatics Hvars Hd Hdistinct Hfresh)
      as (extended' & Hextended & Hcode & Hv).
    pose proof (eval_static_bindings_extend vars' bindings statics' extended'
      Hextended) as Hextend.
    exists 1, (State
                 (bind_my_closures known (lift_expr lets (xO at_path) body))
                 ((x, Value_symbol s0) :: vars') conts' extended').
    split.
    + simpl. rewrite step_let_static, Hextended, step_let. reflexivity.
    + apply State_lifted.
      * apply env_lifted_cons;
          [ exact Hv | exact (env_lifted_extend _ _ _ _ Hextend Hvars) ].
      * exact (conts_lifted_extend _ _ _ _ Hextend Hconts).
      * exact (statics_lifted_extend _ _ _ Hstatics Hextend Hcode).
  - (* Let_static *)
    simpl lift_expr in *. simpl bind_my_closures in *.
    rewrite step_let_static.
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hbindings;
      [ | exact I ].
    unfold static_fault in Hfault. simpl_state.
    apply orb_false_iff in Hfault as [_ Hfault].
    destruct (no_rebinding statics' _ Hfault) as [Hdistinct Hfresh].
    rewrite bind_my_closures_symbols in Hdistinct, Hfresh.
    destruct (eval_static_bindings_lifted vars vars' bindings statics statics'
                extended Hvars Hstatics Hdistinct Hfresh Hbindings)
      as (extended' & Hextended & Hlifted).
    pose proof (eval_static_bindings_extend vars' _ statics' extended'
      Hextended) as Hextend.
    exists 0, (State
                 (bind_my_closures known (lift_expr lets (xO at_path) body))
                 vars' conts' extended').
    split; [ simpl; rewrite step_let_static, Hextended; reflexivity | ].
    apply State_lifted;
      [ exact (env_lifted_extend _ _ _ _ Hextend Hvars)
      | exact (conts_lifted_extend _ _ _ _ Hextend Hconts) | exact Hlifted ].
  - (* Let_cont_non_recursive *)
    simpl lift_expr. simpl bind_my_closures.
    rewrite step_let_cont_non_recursive.
    eexists 0, _.
    split; [ simpl; rewrite step_let_cont_non_recursive; reflexivity | ].
    apply State_lifted; [ exact Hvars | | exact Hstatics ].
    constructor; [ | exact Hconts ].
    split; [ reflexivity | ].
    exact (Closure_lifted statics' lets (xI at_path) h vars vars' conts conts'
             [] Hvars Hconts).
  - (* Let_cont_recursive *)
    simpl lift_expr. simpl bind_my_closures.
    rewrite step_let_cont_recursive.
    destruct (handlers_bind_statics handlers) eqn:Hbinds; [ exact I | ].
    eexists 0, _.
    split;
      [ simpl;
        rewrite step_let_cont_recursive,
          bind_my_closures_handlers_bind_statics, Hbinds;
        reflexivity
      | ].
    apply State_lifted; [ exact Hvars | | exact Hstatics ].
    apply rec_closures_lifted; assumption.
  - (* Apply *)
    simpl lift_expr in *. simpl bind_my_closures in *. rewrite step_apply.
    destruct (eval_simple vars (ap_callee ap)) as [callee | ] eqn:Hcallee;
      [ | exact I ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ] eqn:Hargs;
      [ | exact I ].
    destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ]
      eqn:Hextra;
      [ | exact I ].
    destruct (eval_simple_lifted statics' vars vars' _ callee Hvars Hcallee)
      as (callee' & Hcallee' & Hlifted).
    destruct (eval_simples_lifted statics' vars vars' _ Hvars vs Hargs)
      as (vs' & Hargs' & Hvs).
    destruct (eval_simples_lifted statics' vars vars' _ Hvars extra Hextra)
      as (extra' & Hextra' & Hextras).
    pose proof (call_function_lifted callee callee' (ap_call_kind ap) vs vs'
      (ap_args_arity ap) (ap_return_arity ap)
      (resolve (ap_continuation ap) conts)
      (resolve (ap_continuation ap) conts')
      (with_extra_args (resolve (ap_exn_continuation ap) conts) extra)
      (with_extra_args (resolve (ap_exn_continuation ap) conts') extra')
      statics statics' Hlifted Hvs
      (resolve_lifted statics' _ conts conts' Hconts)
      (with_extra_args_lifted statics' _ _ extra extra'
         (resolve_lifted statics' _ conts conts' Hconts) Hextras)
      Hstatics
      (fun id slots sym => Hknown ap callee' id slots sym eq_refl Hcallee'))
      as Hcall.
    destruct (call_function callee (ap_call_kind ap) vs (ap_args_arity ap)
                (ap_return_arity ap) (resolve (ap_continuation ap) conts)
                (with_extra_args (resolve (ap_exn_continuation ap) conts)
                   extra)
                statics)
      as [t | k vs0 | ];
      [ | destruct Hcall | exact I ].
    destruct Hcall as (n & u' & t' & Hcall' & Hrun & Ht).
    exists n, t'. split; [ | exact Ht ].
    simpl. rewrite step_apply, Hcallee', Hargs', Hextra', Hcall'. exact Hrun.
  - (* Apply_cont *)
    simpl lift_expr. simpl bind_my_closures. rewrite step_apply_cont.
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hargs;
      [ | exact I ].
    destruct (eval_simples_lifted statics' vars vars' _ Hvars vs Hargs)
      as (vs' & Hargs' & Hvs).
    unfold apply_continuation.
    pose proof (apply_cont_value_lifted (resolve (ac_continuation ac) conts)
      (resolve (ac_continuation ac) conts') vs vs' statics statics'
      (resolve_lifted statics' _ conts conts' Hconts) Hvs Hstatics) as Happly.
    destruct (apply_cont_value (resolve (ac_continuation ac) conts) vs
                statics)
      as [t | k exit_vs | ];
      [ | | exact I ].
    + destruct Happly as (t' & Happly' & Ht).
      exists 0, t'. split; [ | exact Ht ].
      simpl. rewrite step_apply_cont, Hargs'. unfold apply_continuation.
      rewrite Happly'. reflexivity.
    + destruct Happly as (exit_vs' & Happly' & Hexit).
      exists exit_vs'. split; [ | exact Hexit ].
      rewrite step_apply_cont, Hargs'. exact Happly'.
  - (* Switch *)
    simpl lift_expr. simpl bind_my_closures. rewrite step_switch.
    destruct (eval_simple vars scrutinee) as [v | ] eqn:Hscrutinee;
      [ | exact I ].
    destruct (eval_simple_lifted statics' vars vars' _ v Hvars Hscrutinee)
      as (v' & Hscrutinee' & Hv).
    destruct (naked_immediate_of_value v) as [i | ] eqn:Hi; [ | exact I ].
    destruct (find_arm i arms) as [ac | ] eqn:Harm; [ | exact I ].
    exists 0, (State (Apply_cont ac) vars' conts' statics').
    split.
    + simpl.
      rewrite step_switch, Hscrutinee',
        (naked_immediate_lifted statics' v v' i Hv Hi), Harm.
      reflexivity.
    + exact (State_lifted lets at_path (Apply_cont ac) vars vars' conts conts'
               statics statics' Hvars Hconts Hstatics).
  - (* Invalid *)
    rewrite step_invalid. exact I.
Qed.

(* ======================================================================== *)
(* The run of the unit lifted                                               *)
(* ======================================================================== *)

Section Unit.

Variable u : unit_interface.
Variable lets : list (path * lift_to).
Variable e : expr.

(* The unit with its [Let]s lifted and [my_closure] bound in its code. *)
Definition lifted_unit : expr :=
  bind_my_closures known (lift_expr lets root e).

Hypothesis Hwf : well_formed_unit u lifted_unit = true.
Hypothesis Honly : only_closures_of known lifted_unit = true.

(* The second state is one that the run of the unit lifted reaches. *)
Definition reached (s' : state) : Prop :=
  ∃ n : nat, run n (State lifted_unit [] [] empty_static_env) = Step s'.

(* The run of the unit lifted calls the code of [known] through its
   symbols. *)
Lemma reached_callee_known (s' : state) : reached s' -> callee_known s'.
Proof.
  intros [n Hn] ap callee id slots sym Hap Hcallee Hclosure Hsym.
  unfold only_closures_of in Honly. rewrite forallb_forall in Honly.
  exact (only_closure_sound id sym lifted_unit n s' ap callee slots
           (Honly (id, sym) (lookup_in id sym known Hsym)) Hn Hap Hcallee
           Hclosure).
Qed.

Lemma reached_run (m : nat) (s' t' : state) :
  reached s' -> run m s' = Step t' -> reached t'.
Proof.
  intros [n Hn] Hm. exists (n + m). rewrite run_add, Hn. exact Hm.
Qed.

Definition unit_lifted (s s' : state) : Prop :=
  state_lifted s s' ∧ reached s'.

Lemma unit_lifted_step (s s' : state) :
  unit_lifted s s' -> answered unit_lifted exit_lifted (step s) s'.
Proof.
  intros [Hlifted Hreached].
  assert (Hfault : static_fault s' = false).
  { destruct Hreached as [n Hn].
    exact (well_formed_never_faults u _ n s' Hwf Hn). }
  pose proof (lifted_step s s' Hlifted Hfault
    (reached_callee_known s' Hreached)) as Hanswer.
  destruct (step s) as [t | k vs | ]; unfold answered in *;
    [ | exact Hanswer | exact I ].
  destruct Hanswer as (n & t' & Hrun & Ht).
  exists n, t'. split; [ exact Hrun | ].
  split; [ exact Ht | exact (reached_run (S n) s' t' Hreached Hrun) ].
Qed.

Lemma unit_lifted_initial :
  unit_lifted (State e [] [] empty_static_env)
    (State lifted_unit [] [] empty_static_env).
Proof.
  split; [ | exists 0; reflexivity ].
  apply State_lifted;
    [ intros x v [=] | constructor
    | split; [ intros id; reflexivity | intros s a [=] ] ].
Qed.

End Unit.

End Known.

Theorem lift_simulates : lift_simulates_statement.
Proof.
  intros u lets known e. cbv zeta. intros Hwf Honly. split.
  - intros k vs [n Hn].
    exact (stuttering_exit (unit_lifted known lets e) exit_lifted
             (unit_lifted_step known u lets e Hwf Honly) n _ _ k vs
             (unit_lifted_initial known lets e) Hn).
  - intros b Hterm Hb.
    destruct (behaves_ended _ b Hterm Hb) as [m Hended].
    destruct (stuttering_ends (unit_lifted known lets e) exit_lifted
                (unit_lifted_step known u lets e Hwf Honly) m _ _ b
                (unit_lifted_initial known lets e) Hended)
      as [n [Hwrong | (k & vs & Hexit)]].
    + left. exists n. exact Hwrong.
    + right. exists k, vs, n. exact Hexit.
Qed.

(* ======================================================================== *)
(* What a unit may exit with                                                *)
(* ======================================================================== *)

(* The continuations of [scope] are bound to closures: none stands for a
   way out. *)
Definition scope_closed (scope : list continuation) (conts : cont_env)
    : Prop :=
  ∀ k : continuation,
    among k scope = true ->
    ∃ (h : continuation_handler) (vars : env) (cs : cont_env)
      (recursive : list (continuation * continuation_handler)),
      lookup k conts = Some (Closure h vars cs recursive).

(* A continuation whose handler, and whatever it goes on to, gives a
   variable only to continuations that are closures: there is a scope
   which passes the check for the handler, and for the handlers of its
   group, and which its environment closes. *)
#[local] Set Warnings "-register-all".
Inductive cont_plain : cont_value -> Prop :=
  | Outer_plain (k : continuation) : cont_plain (Outer k)
  | Closure_plain (scope : list continuation) (h : continuation_handler)
      (vars : env) (conts : cont_env)
      (recursive : list (continuation * continuation_handler)) :
    handler_exits_plain (map fst recursive ++ scope) h = true ->
    forallb
      (fun '(_, h') => handler_exits_plain (map fst recursive ++ scope) h')
      recursive
    = true ->
    scope_closed scope conts ->
    Forall (fun kc => cont_plain (snd kc)) conts ->
    cont_plain (Closure h vars conts recursive)
  | Extra_args_plain (c : cont_value) (extra : list value) :
    cont_plain c ->
    ((∃ k : continuation, cont_target c = Outer k) ->
     ∀ v : value, v ∈ extra -> plain_value v) ->
    cont_plain (Extra_args c extra).

Definition conts_plain (conts : cont_env) : Prop :=
  Forall (fun kc => cont_plain (snd kc)) conts.

Definition code_plain (statics : static_env) : Prop :=
  ∀ (id : code_id) (c : code),
    lookup id (static_code statics) = Some c -> code_exits_plain c = true.

(* The invariant: the expression passes the check for a scope that the
   continuations in scope close. *)
Definition plain_state (s : state) : Prop :=
  ∃ scope : list continuation,
    exits_plain scope (state_expr s) = true
    ∧ scope_closed scope (state_conts s)
    ∧ conts_plain (state_conts s)
    ∧ code_plain (state_statics s).

Lemma lookup_plain (k : continuation) (conts : cont_env) (c : cont_value) :
  conts_plain conts -> lookup k conts = Some c -> cont_plain c.
Proof.
  induction 1 as [ | [k' c'] conts Hc _ IH]; simpl; [ discriminate | ].
  destruct (Pos.eqb k k'); [ intros [= <-]; exact Hc | exact IH ].
Qed.

Lemma resolve_plain (k : continuation) (conts : cont_env) :
  conts_plain conts -> cont_plain (resolve k conts).
Proof.
  intros Hconts. unfold resolve.
  destruct (lookup k conts) as [c | ] eqn:Hk;
    [ exact (lookup_plain k conts c Hconts Hk) | apply Outer_plain ].
Qed.

(* What a name is bound to among the closures of a recursive group: the
   closure of one of its handlers, or nothing if the group has not got
   the name. [all] is the whole group. *)
Lemma lookup_rec_closures (vars : env) (conts : cont_env)
    (all handlers : list (continuation * continuation_handler))
    (k : continuation) :
  match
    lookup k (map (fun '(k, h) => (k, Closure h vars conts all)) handlers)
  with
  | Some c => ∃ h : continuation_handler, c = Closure h vars conts all
  | None => among k (map fst handlers) = false
  end.
Proof.
  induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
  destruct (Pos.eqb k k'); simpl; [ eauto | exact IH ].
Qed.

Lemma rec_closures_plain (scope : list continuation) (vars : env)
    (conts : cont_env)
    (recursive : list (continuation * continuation_handler)) :
  forallb
    (fun '(_, h) => handler_exits_plain (map fst recursive ++ scope) h)
    recursive
  = true ->
  scope_closed scope conts ->
  conts_plain conts ->
  scope_closed (map fst recursive ++ scope)
    (rec_closures recursive vars conts ++ conts)
  ∧ conts_plain (rec_closures recursive vars conts ++ conts).
Proof.
  intros Hrecursive Hscope Hconts. split.
  - intros k Hk. rewrite lookup_app.
    pose proof (lookup_rec_closures vars conts recursive recursive k)
      as Hlookup.
    unfold rec_closures.
    destruct
      (lookup k
         (map (fun '(k, h) => (k, Closure h vars conts recursive)) recursive))
      as [c | ].
    + destruct Hlookup as [h ->]. eauto.
    + rewrite among_app, Hlookup in Hk. exact (Hscope k Hk).
  - apply Forall_app. split; [ | exact Hconts ].
    unfold rec_closures. apply Forall_forall. intros [k c] Hin.
    apply in_map_iff in Hin as ([k' h] & [= <- <-] & Hin). simpl.
    apply (Closure_plain scope); [ | exact Hrecursive | exact Hscope
                                 | exact Hconts ].
    rewrite forallb_forall in Hrecursive. exact (Hrecursive (k', h) Hin).
Qed.

Lemma eval_static_bindings_plain (vars : env) :
  ∀ (bindings : list static_binding) (statics extended : static_env),
    forallb binding_exits_plain bindings = true ->
    code_plain statics ->
    eval_static_bindings vars bindings statics = Some extended ->
    code_plain extended.
Proof.
  induction bindings as [ | binding bindings IH]; intros statics extended;
    simpl.
  - intros _ Hcode [= <-]. exact Hcode.
  - intros Hbindings Hcode.
    apply andb_true_iff in Hbindings as [Hbinding Hbindings].
    destruct binding as [id c | id | sym const].
    + destruct (lookup id (static_code statics)); [ discriminate | ].
      apply (IH _ _ Hbindings). intros id' c'. simpl.
      destruct (Pos.eqb id' id);
        [ intros [= <-]; exact Hbinding | apply Hcode ].
    + exact (IH _ _ Hbindings Hcode).
    + destruct (lookup sym (static_values statics)); [ discriminate | ].
      destruct (eval_static_const vars const); [ | discriminate ].
      apply (IH _ _ Hbindings). exact Hcode.
Qed.

Lemma eval_simples_plain (vars : env) (args : list simple) :
  forallb plain_simple args = true ->
  ∀ vs : list value,
    eval_simples vars args = Some vs ->
    ∀ v : value, v ∈ vs -> plain_value v.
Proof.
  induction args as [ | s args IH]; simpl.
  - intros _ vs [= <-] v [].
  - intros Hplain vs. apply andb_true_iff in Hplain as [Hs Hargs].
    destruct (eval_simple vars s) as [w | ] eqn:Hw; [ | discriminate ].
    destruct (eval_simples vars args) as [rest | ]; [ | discriminate ].
    intros [= <-] v [<- | Hin]; [ | exact (IH Hargs rest eq_refl v Hin) ].
    destruct s as [x | sym | c]; [ discriminate | | ];
      simpl in Hw; injection Hw as <-; exact I.
Qed.

(* A call steps into code or is undefined: it does not leave the term. *)
Lemma call_function_no_exit (callee : value) (kind : call_kind)
    (vs : list value) (args_arity return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env)
    (k : continuation) (exit_vs : list value) :
  call_function callee kind vs args_arity return_arity return_to exn_to
    statics
  <> Exit k exit_vs.
Proof.
  unfold call_function.
  destruct (closure_of statics callee) as [[called slots] | ];
    [ | discriminate ].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | discriminate ].
  destruct (lookup called (static_code statics)) as [c | ];
    [ | discriminate ].
  destruct (binds_statics (code_body c)); [ discriminate | ].
  match goal with
  | |- context [negb ?agrees] => destruct (negb agrees)
  end;
    [ discriminate | ].
  destruct (bind_params (code_params c) vs [(code_my_closure c, callee)]);
    discriminate.
Qed.

(* The exception continuation that a call gives its callee: its extra
   arguments are constants and symbols if it is a way out. *)
Lemma with_extra_args_plain (c : cont_value) (extra : list value) :
  cont_plain c ->
  ((∃ k : continuation, cont_target c = Outer k) ->
   ∀ v : value, v ∈ extra -> plain_value v) ->
  cont_plain (with_extra_args c extra).
Proof.
  intros Hc Hextra. destruct extra as [ | v extra]; [ exact Hc | ].
  apply Extra_args_plain; assumption.
Qed.

(* Applying a continuation keeps the invariant, and if it is a way out
   and the arguments are constants and symbols, so is what the term
   exits with. *)
Lemma apply_cont_value_plain (c : cont_value) :
  cont_plain c ->
  ∀ (vs : list value) (statics : static_env),
    ((∃ k : continuation, cont_target c = Outer k) ->
     ∀ v : value, v ∈ vs -> plain_value v) ->
    code_plain statics ->
    match apply_cont_value c vs statics with
    | Step t => plain_state t
    | Exit k exit_vs => ∀ v : value, v ∈ exit_vs -> plain_value v
    | Undefined => True
    end.
Proof.
  induction 1
    as [ k | cscope [params metadata handler] dvars dconts recursive Hh
             Hrecursive Hcscope Hdconts
       | c extra Hc IH Hextra ];
    intros vs statics Hvs Hcode; simpl.
  - apply Hvs. exists k. reflexivity.
  - destruct (bind_params params vs dvars); [ | exact I ].
    destruct (rec_closures_plain cscope dvars dconts recursive Hrecursive
                Hcscope Hdconts)
      as [Hscope' Hconts'].
    exists (map fst recursive ++ cscope). simpl. auto.
  - apply IH; [ | exact Hcode ].
    intros Hout v Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | Hin];
      [ exact (Hvs Hout v Hin) | exact (Hextra Hout v Hin) ].
Qed.

(* A step keeps the invariant, and an exit is with constants and symbols
   only: the continuation left through is not of the scope, so it was
   given no variable. *)
Lemma plain_step_components (scope : list continuation) (e : expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  exits_plain scope e = true ->
  scope_closed scope conts ->
  conts_plain conts ->
  code_plain statics ->
  match step (State e vars conts statics) with
  | Step t => plain_state t
  | Exit k vs => ∀ v : value, v ∈ vs -> plain_value v
  | Undefined => True
  end.
Proof.
  intros He Hscope Hconts Hcode.
  destruct e
    as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl in He.
  - (* Let *)
    rewrite step_let. destruct (eval_named statics vars d); [ | exact I ].
    exists scope. simpl. auto.
  - (* Let_static *)
    apply andb_true_iff in He as [Hbindings Hbody]. rewrite step_let_static.
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hextended;
      [ | exact I ].
    exists scope. simpl.
    split; [ exact Hbody | ]. split; [ exact Hscope | ].
    split; [ exact Hconts | ].
    exact (eval_static_bindings_plain vars bindings statics extended Hbindings
             Hcode Hextended).
  - (* Let_cont_non_recursive *)
    apply andb_true_iff in He as [Hh Hbody].
    rewrite step_let_cont_non_recursive.
    exists (k :: scope). simpl.
    split; [ exact Hbody | ]. split; [ | split; [ | exact Hcode ] ].
    + intros k' Hk'. rewrite among_cons in Hk'. simpl.
      destruct (Pos.eqb k' k); [ eauto | exact (Hscope k' Hk') ].
    + constructor; [ | exact Hconts ]. simpl.
      apply (Closure_plain scope);
        [ exact Hh | reflexivity | exact Hscope | exact Hconts ].
  - (* Let_cont_recursive *)
    apply andb_true_iff in He as [Hhandlers Hbody].
    rewrite step_let_cont_recursive.
    destruct (handlers_bind_statics handlers); [ exact I | ].
    destruct (rec_closures_plain scope vars conts handlers Hhandlers Hscope
                Hconts)
      as [Hscope' Hconts'].
    exists (map fst handlers ++ scope). simpl. auto.
  - (* Apply *)
    apply andb_true_iff in He as [He Hexn]. rewrite step_apply.
    destruct (eval_simple vars (ap_callee ap)) as [callee | ]; [ | exact I ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | exact I ].
    destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ]
      eqn:Hextra;
      [ | exact I ].
    destruct (call_function callee (ap_call_kind ap) vs (ap_args_arity ap)
                (ap_return_arity ap) (resolve (ap_continuation ap) conts)
                (with_extra_args (resolve (ap_exn_continuation ap) conts)
                   extra)
                statics)
      as [t | k exit_vs | ] eqn:Hcall;
      [ | destruct (call_function_no_exit _ _ _ _ _ _ _ _ _ _ Hcall)
      | exact I ].
    destruct (call_function_step _ _ _ _ _ _ _ _ _ Hcall)
      as (called & called_slots & c & callee_vars & _ & Hlookup & _ & _ & _
          & _ & ->).
    exists [code_return_continuation c]. simpl.
    split; [ | split; [ | split; [ | exact Hcode ] ] ].
    + pose proof (Hcode called c Hlookup) as Hc. destruct c. exact Hc.
    + intros k' Hk'. rewrite among_cons in Hk'. simpl in Hk'.
      rewrite orb_false_r in Hk'. simpl. rewrite Hk'.
      destruct (Hscope _ He) as (h & hvars & cs & recursive & Hk).
      unfold resolve. rewrite Hk. eauto.
    + constructor; [ exact (resolve_plain _ conts Hconts) | ].
      constructor; [ | constructor ]. simpl.
      apply with_extra_args_plain; [ exact (resolve_plain _ conts Hconts) | ].
      intros [k' Hout].
      destruct (among (ap_exn_continuation ap) scope) eqn:Hin.
      * destruct (Hscope _ Hin) as (h & hvars & cs & recursive & Hk).
        unfold resolve in Hout. rewrite Hk in Hout. discriminate.
      * exact (eval_simples_plain vars _ Hexn extra Hextra).
  - (* Apply_cont *)
    rewrite step_apply_cont.
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hargs;
      [ | exact I ].
    unfold apply_continuation.
    apply (apply_cont_value_plain _
      (resolve_plain (ac_continuation ac) conts Hconts));
      [ | exact Hcode ].
    intros [k' Hout]. unfold apply_cont_exits_plain in He.
    destruct (among (ac_continuation ac) scope) eqn:Hin.
    + destruct (Hscope _ Hin) as (h & hvars & cs & recursive & Hk).
      unfold resolve in Hout. rewrite Hk in Hout. discriminate.
    + exact (eval_simples_plain vars _ He vs Hargs).
  - (* Switch *)
    rewrite step_switch.
    destruct (eval_simple vars scrutinee) as [v | ]; [ | exact I ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
    destruct (find_arm i arms) as [ac | ] eqn:Harm; [ | exact I ].
    exists scope. simpl. split; [ | auto ].
    rewrite forallb_forall in He.
    exact (He (i, ac) (find_arm_in i arms ac Harm)).
  - (* Invalid *)
    rewrite step_invalid. exact I.
Qed.

Lemma plain_step (s : state) :
  plain_state s ->
  match step s with
  | Step t => plain_state t
  | Exit k vs => ∀ v : value, v ∈ vs -> plain_value v
  | Undefined => True
  end.
Proof.
  intros (scope & He & Hscope & Hconts & Hcode). rewrite (state_eta s).
  exact (plain_step_components scope _ _ _ _ He Hscope Hconts Hcode).
Qed.

Lemma plain_run (n : nat) :
  ∀ (s : state) (k : continuation) (vs : list value),
    plain_state s ->
    run n s = Exit k vs ->
    ∀ v : value, v ∈ vs -> plain_value v.
Proof.
  induction n as [ | n IH]; intros s k vs Hplain; simpl; [ discriminate | ].
  pose proof (plain_step s Hplain) as Hstep.
  destruct (step s) as [t | k' vs' | ];
    [ exact (IH t k vs Hstep) | intros [= <- <-]; exact Hstep
    | discriminate ].
Qed.

Lemma plain_initial (e : expr) :
  exits_plain [] e = true -> plain_state (State e [] [] empty_static_env).
Proof.
  intros He. exists []. simpl.
  split; [ exact He | ]. split; [ intros k [=] | ].
  split; [ constructor | intros id c [=] ].
Qed.

Theorem exits_plain_sound : exits_plain_sound_statement.
Proof.
  intros e n k vs He.
  exact (plain_run n _ k vs (plain_initial e He)).
Qed.

(* ======================================================================== *)
(* What [lift_unit] gives refines the unit                                  *)
(* ======================================================================== *)

Section Unit_refines.

Variable known : list (code_id * symbol).
Variable u : unit_interface.
Variable lets : list (path * lift_to).
Variable e : expr.
Hypothesis Hwf :
  well_formed_unit u (lifted_unit known lets e) = true.
Hypothesis Honly : only_closures_of known (lifted_unit known lets e) = true.

Definition unit_lifted_plain (s s' : state) : Prop :=
  unit_lifted known lets e s s' ∧ plain_state s.

(* The values at an exit are lifted, and are constants and symbols: they
   are the same. *)
Lemma unit_lifted_plain_step (s s' : state) :
  unit_lifted_plain s s' ->
  answered unit_lifted_plain (fun _ vs vs' => vs' = vs) (step s) s'.
Proof.
  intros [Hlifted Hplain].
  pose proof (unit_lifted_step known u lets e Hwf Honly s s' Hlifted)
    as Hanswer.
  pose proof (plain_step s Hplain) as Hstep.
  destruct (step s) as [t | k vs | ]; unfold answered in *; [ | | exact I ].
  - destruct Hanswer as (n & t' & Hrun & Ht).
    exists n, t'. split; [ exact Hrun | split; assumption ].
  - destruct Hanswer as (vs' & Hexit & Hvs).
    exists vs'. split; [ exact Hexit | ].
    exact (plain_values_lifted _ vs vs' Hstep Hvs).
Qed.

End Unit_refines.

Theorem lift_unit_program_refines : lift_unit_program_refines_statement.
Proof.
  intros L e e'. unfold lift_unit. cbv zeta.
  destruct (exits_plain [] e) eqn:Hplain; [ | discriminate ].
  fold (lifted_unit (lifted_my_closures L) (lifted_lets L) e).
  destruct
    (well_formed_unit (lifting_unit L)
       (lifted_unit (lifted_my_closures L) (lifted_lets L) e))
    eqn:Hwf;
    [ | discriminate ].
  destruct
    (only_closures_of (lifted_my_closures L)
       (lifted_unit (lifted_my_closures L) (lifted_lets L) e))
    eqn:Honly;
    [ | discriminate ].
  intros [= <-]. unfold program_refines.
  apply
    (stuttering_refines
       (unit_lifted_plain (lifted_my_closures L) (lifted_lets L) e)
       (fun _ vs vs' => vs' = vs)
       (unit_lifted_plain_step (lifted_my_closures L) (lifting_unit L)
          (lifted_lets L) e Hwf Honly)).
  - intros last vs vs' Hsame. exact Hsame.
  - split; [ apply unit_lifted_initial | exact (plain_initial e Hplain) ].
Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

Lemma lift_named_rename (r : renaming) (target : lift_to) (d : named) :
  lift_named target (rename_named r d)
  = option_map
      (fun '(bindings, s) => (map (rename_static_binding r) bindings, s))
      (lift_named target d).
Proof.
  destruct target as [sym | syms];
    destruct d as [s | p args | code slots | fslot decls slots | slot closure
      | pfrom slot closure | move_from move_to closure];
    simpl; try reflexivity.
  - destruct p as [p | p | p | p]; try reflexivity.
    + destruct p; try reflexivity.
      destruct args as [ | contents [ | arg args]]; reflexivity.
    + destruct p as [[tag]]. reflexivity.
  - destruct (lookup fslot syms) as [s | ]; [ | reflexivity ].
    destruct (list_eq_dec Pos.eq_dec (map fst syms) (map fst decls));
      [ | reflexivity ].
    simpl. unfold bind_closures. rewrite map_map. do 2 f_equal.
    apply map_ext. intros [slot' s']. reflexivity.
Qed.

Fixpoint lift_expr_rename (r : renaming) (lets : list (path * lift_to))
    (at_path : path) (e : expr) {struct e} :
  rename_expr r (lift_expr lets at_path e)
  = lift_expr lets at_path (rename_expr r e)
with lift_handler_rename (r : renaming) (lets : list (path * lift_to))
    (at_path : path) (h : continuation_handler) {struct h} :
  rename_handler r (lift_handler lets at_path h)
  = lift_handler lets at_path (rename_handler r h).
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + destruct (lookup at_path lets) as [target | ];
        [ | simpl; rewrite lift_expr_rename; reflexivity ].
      rewrite lift_named_rename.
      destruct (lift_named target d) as [[bindings s] | ]; simpl;
        rewrite lift_expr_rename; reflexivity.
    + rewrite lift_expr_rename. reflexivity.
    + rewrite lift_handler_rename, lift_expr_rename. reflexivity.
    + rewrite lift_expr_rename. reflexivity.
  - destruct h as [params metadata handler]. simpl. rewrite lift_expr_rename.
    reflexivity.
Qed.

Theorem lift_expr_equivariant : lift_expr_equivariant_statement.
Proof. exact lift_expr_rename. Qed.

Lemma among_rename_continuation (r : renaming) (k : continuation)
    (scope : list continuation) :
  among (rename_continuation r k) (map (rename_continuation r) scope)
  = among k scope.
Proof.
  unfold among. induction scope as [ | k' scope IH]; simpl; [ reflexivity | ].
  rewrite rename_continuation_eqb, IH. reflexivity.
Qed.

Lemma apply_cont_exits_plain_rename (r : renaming)
    (scope : list continuation) (ac : apply_cont) :
  apply_cont_exits_plain (map (rename_continuation r) scope)
    (rename_apply_cont r ac)
  = apply_cont_exits_plain scope ac.
Proof.
  unfold apply_cont_exits_plain. simpl.
  rewrite among_rename_continuation. f_equal.
  induction (ac_args ac) as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite IH. destruct s; reflexivity.
Qed.

Fixpoint exits_plain_rename (r : renaming) (scope : list continuation)
    (e : expr) {struct e} :
  exits_plain (map (rename_continuation r) scope) (rename_expr r e)
  = exits_plain scope e
with handler_exits_plain_rename (r : renaming) (scope : list continuation)
    (h : continuation_handler) {struct h} :
  handler_exits_plain (map (rename_continuation r) scope) (rename_handler r h)
  = handler_exits_plain scope h
with binding_exits_plain_rename (r : renaming) (binding : static_binding)
    {struct binding} :
  binding_exits_plain (rename_static_binding r binding)
  = binding_exits_plain binding
with code_exits_plain_rename (r : renaming) (c : code) {struct c} :
  code_exits_plain (rename_code r c) = code_exits_plain c.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl.
    + apply exits_plain_rename.
    + rewrite exits_plain_rename. f_equal.
      induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
      rewrite binding_exits_plain_rename, IH. reflexivity.
    + rewrite handler_exits_plain_rename. f_equal.
      exact (exits_plain_rename r (k :: scope) body).
    + assert (Hscope :
        map fst
          (map (fun '(k, h) => (rename_continuation r k, rename_handler r h))
             handlers)
        ++ map (rename_continuation r) scope
        = map (rename_continuation r) (map fst handlers ++ scope)).
      { rewrite map_app, !map_map. f_equal. apply map_ext.
        intros [k h]. reflexivity. }
      rewrite Hscope, exits_plain_rename. f_equal. clear Hscope.
      generalize (map fst handlers ++ scope) as scope'. intros scope'.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite handler_exits_plain_rename, IH. reflexivity.
    + rewrite !among_rename_continuation. do 2 f_equal.
      unfold exn_extra_simples. simpl.
      induction (ap_exn_extra_args ap) as [ | [arg kind] extra IH]; simpl;
        [ reflexivity | ].
      rewrite IH. destruct arg; reflexivity.
    + apply apply_cont_exits_plain_rename.
    + induction arms as [ | [i ac] arms IH]; simpl; [ reflexivity | ].
      rewrite apply_cont_exits_plain_rename, IH. reflexivity.
    + reflexivity.
  - destruct h as [params metadata handler]. simpl. apply exits_plain_rename.
  - destruct binding as [id c | id | sym const]; simpl; try reflexivity.
    apply code_exits_plain_rename.
  - destruct c as [params my_closure ret exn metadata body]. simpl.
    exact (exits_plain_rename r [ret] body).
Qed.

Theorem exits_plain_equivariant : exits_plain_equivariant_statement.
Proof. exact exits_plain_rename. Qed.
