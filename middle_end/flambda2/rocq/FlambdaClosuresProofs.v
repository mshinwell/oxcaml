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


(* Proofs of the statements of FlambdaClosuresSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Arith Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaWellFormedSpec FlambdaWellFormedProofs FlambdaApplySpec
  FlambdaApplyProofs FlambdaClosuresSpec.
Import ListNotations.

(* ======================================================================== *)
(* Lists                                                                    *)
(* ======================================================================== *)

(* In a list of bindings of distinct names, a binding is the one found. *)
Lemma lookup_NoDup_in {A : Type} (bindings : list (positive * A))
    (name : positive) (a : A) :
  NoDup (map fst bindings) -> (name, a) ∈ bindings ->
  lookup name bindings = Some a.
Proof.
  induction bindings as [ | [bound b] bindings IH]; simpl; [ intros _ [] | ].
  intros Hdistinct [Heq | Hin].
  - injection Heq as -> ->. rewrite Pos.eqb_refl. reflexivity.
  - inversion Hdistinct as [ | ? ? Hfresh Hrest]. subst.
    destruct (Pos.eqb_spec name bound) as [-> | _]; [ | exact (IH Hrest Hin) ].
    exfalso. apply Hfresh. change bound with (fst (bound, a)).
    apply in_map, Hin.
Qed.

(* A name bound in a map has something bound to it. *)
Lemma lookup_bound {A : Type} (name : positive)
    (bindings : list (positive * A)) :
  name ∈ map fst bindings -> ∃ a : A, lookup name bindings = Some a.
Proof.
  intros Hin. destruct (lookup name bindings) as [a | ] eqn:Hlookup;
    [ eauto | ].
  destruct (lookup_none_not_in name bindings Hlookup Hin).
Qed.

Lemma combine_fst_length {A B C : Type} (l : list A) (l' : list (B * C)) :
  length l = length l' -> length (combine l (map fst l')) = length l.
Proof.
  revert l'. induction l as [ | a l IH]; intros [ | b l']; simpl;
    try discriminate; [ reflexivity | ].
  intros [= Hlen]. rewrite (IH l' Hlen). reflexivity.
Qed.

(* ======================================================================== *)
(* A set of closures made by a [Let]                                        *)
(* ======================================================================== *)

Section Let_closures.

Variable decls : list (function_slot * code_id).

Variable slot_values : list (value_slot * value).

(* What [let_projections] binds, the first bound first. *)
Definition projections_bound (bound : list (variable * function_slot)) : env :=
  map (fun '(y, slot) => (y, Value_closure_of_set slot decls slot_values))
    bound.

(* The projections are bound one at a time, each from the closure [base],
   which stays in scope as none of the variables bound is [base]. *)
Lemma let_projections_runs (base : variable) (base_slot : function_slot)
    (code : code_id) (body : expr) (conts : cont_env) (statics : static_env) :
  lookup base_slot decls = Some code ->
  ∀ (bound : list (variable * function_slot)) (vars : env),
    lookup base vars
    = Some (Value_closure_of_set base_slot decls slot_values) ->
    (∀ (y : variable) (slot : function_slot),
      (y, slot) ∈ bound ->
      y <> base ∧ ∃ code' : code_id, lookup slot decls = Some code') ->
    run (length bound)
      (State (let_projections base base_slot bound body) vars conts statics)
    = Step
        (State body (rev (projections_bound bound) ++ vars) conts statics).
Proof.
  intros Hfrom.
  induction bound as [ | [y slot] bound IH]; intros vars Hbase Hbound;
    [ reflexivity | ].
  destruct (Hbound y slot (or_introl eq_refl)) as [Hy [code' Hto]].
  simpl length. rewrite run_succ. simpl let_projections.
  rewrite step_let_project_function_slot. simpl eval_simple. rewrite Hbase.
  rewrite (project_function_slot_of_set statics base_slot slot decls
             slot_values code code' Hfrom Hto).
  rewrite IH.
  - simpl. rewrite <- app_assoc. reflexivity.
  - rewrite lookup_other; [ exact Hbase | congruence ].
  - intros y' slot' Hin. apply Hbound. right. exact Hin.
Qed.

(* The bindings of [closures_bound] for the variables [xs] and the
   functions [ds] of the set, the first bound first. *)
Definition closures_bound_to (xs : list variable)
    (ds : list (function_slot * code_id)) : env :=
  map (fun '(x, (slot, _)) => (x, Value_closure_of_set slot decls slot_values))
    (combine xs ds).

Lemma projections_bound_combine (xs : list variable)
    (ds : list (function_slot * code_id)) :
  projections_bound (combine xs (map fst ds)) = closures_bound_to xs ds.
Proof.
  unfold projections_bound, closures_bound_to. revert ds.
  induction xs as [ | x xs IH]; intros [ | [slot code] ds]; simpl;
    try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma closures_bound_to_names (xs : list variable)
    (ds : list (function_slot * code_id)) (x : variable) :
  x ∈ map fst (closures_bound_to xs ds) -> x ∈ xs.
Proof.
  revert ds. induction xs as [ | x' xs IH]; intros [ | [slot code] ds];
    simpl; try contradiction.
  intros [Heq | Hin]; [ left; exact Heq | right; exact (IH ds Hin) ].
Qed.

Lemma closures_bound_to_distinct (xs : list variable)
    (ds : list (function_slot * code_id)) :
  NoDup xs -> NoDup (map fst (closures_bound_to xs ds)).
Proof.
  revert ds. induction xs as [ | x xs IH]; intros [ | [slot code] ds];
    simpl; try (intros _; apply NoDup_nil).
  intros Hdistinct. inversion Hdistinct as [ | ? ? Hfresh Hrest]. subst.
  apply NoDup_cons; [ | exact (IH ds Hrest) ].
  intros Hin. exact (Hfresh (closures_bound_to_names xs ds x Hin)).
Qed.

Lemma closures_bound_to_nth (xs : list variable)
    (ds : list (function_slot * code_id)) :
  ∀ (i : nat) (x : variable) (slot : function_slot) (code : code_id),
    nth_error xs i = Some x ->
    nth_error ds i = Some (slot, code) ->
    (x, Value_closure_of_set slot decls slot_values)
    ∈ closures_bound_to xs ds.
Proof.
  revert ds. induction xs as [ | x' xs IH]; intros [ | [slot' code'] ds];
    intros [ | i] x slot code; simpl; try discriminate.
  - intros [= <-] [= <- <-]. left. reflexivity.
  - intros Hx Hslot. right. exact (IH ds i x slot code Hx Hslot).
Qed.

(* A variable of a [Let] of a set is bound, in its scope, to the closure
   at the slot of the function in its position. *)
Lemma closures_bound_to_lookup (xs : list variable)
    (ds : list (function_slot * code_id)) (vars : env) (i : nat)
    (x : variable) (slot : function_slot) (code : code_id) :
  NoDup xs ->
  nth_error xs i = Some x ->
  nth_error ds i = Some (slot, code) ->
  lookup x (rev (closures_bound_to xs ds) ++ vars)
  = Some (Value_closure_of_set slot decls slot_values).
Proof.
  intros Hdistinct Hx Hslot. rewrite lookup_app.
  rewrite (lookup_NoDup_in (rev (closures_bound_to xs ds)) x
             (Value_closure_of_set slot decls slot_values));
    [ reflexivity | | ].
  - rewrite map_rev. apply NoDup_rev, closures_bound_to_distinct, Hdistinct.
  - apply -> in_rev. exact (closures_bound_to_nth xs ds i x slot code Hx Hslot).
Qed.

End Let_closures.

(* The function at a position of a set has code. *)
Lemma nth_error_lookup (decls : list (function_slot * code_id)) (i : nat)
    (slot : function_slot) (code : code_id) :
  nth_error decls i = Some (slot, code) ->
  ∃ code' : code_id, lookup slot decls = Some code'.
Proof.
  intros Hnth. apply lookup_bound. change slot with (fst (slot, code)).
  apply in_map. exact (nth_error_In decls i Hnth).
Qed.

Theorem let_closures_runs : let_closures_runs_statement.
Proof.
  intros bound_vars decls value_slots body e vars conts statics slot_values
    Hlet Hdistinct Hslots.
  unfold let_closures in Hlet.
  destruct bound_vars as [ | x xs]; [ discriminate | ].
  destruct decls as [ | [slot code] others]; [ discriminate | ].
  destruct (Nat.eqb (length xs) (length others)) eqn:Hlen; [ | discriminate ].
  injection Hlet as <-. apply Nat.eqb_eq in Hlen.
  apply distinct_NoDup in Hdistinct.
  inversion Hdistinct as [ | ? ? Hfresh Hrest]. subst.
  simpl length. rewrite run_succ, step_let_closure_of_set, lookup_head, Hslots.
  rewrite <- (combine_fst_length xs others Hlen) at 1.
  rewrite (let_projections_runs ((slot, code) :: others) slot_values x slot
             code body conts statics (lookup_head _ _ _)
             (combine xs (map fst others)));
    [ | apply lookup_head | ].
  - rewrite projections_bound_combine. unfold closures_bound. simpl.
    rewrite <- app_assoc. reflexivity.
  - intros y slot' Hin. split.
    + intros ->. apply Hfresh. exact (in_combine_l _ _ _ _ Hin).
    + apply lookup_bound. simpl. right. exact (in_combine_r _ _ _ _ Hin).
Qed.

Theorem let_closures_undefined : let_closures_undefined_statement.
Proof.
  intros bound_vars decls value_slots body e vars conts statics Hlet Hslots.
  unfold let_closures in Hlet.
  destruct bound_vars as [ | x xs]; [ discriminate | ].
  destruct decls as [ | [slot code] others]; [ discriminate | ].
  destruct (Nat.eqb (length xs) (length others)); [ | discriminate ].
  injection Hlet as <-.
  rewrite step_let_closure_of_set, lookup_head, Hslots. reflexivity.
Qed.

(* [closures_bound] is the bindings of [closures_bound_to], the last bound
   first. *)
Lemma closures_bound_rev (bound_vars : list variable)
    (decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)) :
  closures_bound bound_vars decls slot_values
  = rev (closures_bound_to decls slot_values bound_vars decls).
Proof. reflexivity. Qed.

(* Both sides bind the closures of the set, or neither does; then the
   projection is the closure that the variable of its slot is bound to. *)
Theorem project_function_slot_let_closures :
  project_function_slot_let_closures_statement.
Proof.
  intros bound_vars decls value_slots move_from move_to x_from x_to y code
    code' i j body e e' Hdistinct Hx_from Hfrom Hx_to Hto Hlet Hlet' vars
    conts statics.
  destruct (eval_value_slots vars value_slots) as [slot_values | ] eqn:Hslots.
  - pose proof (let_closures_runs bound_vars decls value_slots _ e vars conts
                  statics slot_values Hlet Hdistinct Hslots) as Hrun.
    pose proof (let_closures_runs bound_vars decls value_slots _ e' vars conts
                  statics slot_values Hlet' Hdistinct Hslots) as Hrun'.
    eapply equivalent_trans;
      [ exact (equivalent_of_run (length bound_vars) 0 _ _ Hrun) | ].
    eapply equivalent_trans;
      [ | apply equivalent_sym;
          exact (equivalent_of_run (length bound_vars) 0 _ _ Hrun') ].
    apply let_equivalent_step; [ | intros v _; apply equivalent_refl ].
    apply distinct_NoDup in Hdistinct. rewrite closures_bound_rev. simpl.
    rewrite (closures_bound_to_lookup decls slot_values bound_vars decls vars
               i x_from move_from code Hdistinct Hx_from Hfrom).
    rewrite (closures_bound_to_lookup decls slot_values bound_vars decls vars
               j x_to move_to code' Hdistinct Hx_to Hto).
    destruct (nth_error_lookup decls i move_from code Hfrom) as [c Hc].
    destruct (nth_error_lookup decls j move_to code' Hto) as [c' Hc'].
    symmetry.
    exact (project_function_slot_of_set statics move_from move_to decls
             slot_values c c' Hc Hc').
  - apply step_eq_equivalent.
    rewrite (let_closures_undefined bound_vars decls value_slots _ e vars
               conts statics Hlet Hslots).
    rewrite (let_closures_undefined bound_vars decls value_slots _ e' vars
               conts statics Hlet' Hslots).
    reflexivity.
Qed.

(* The variable is bound to the closure at the slot projected, whose code
   is that of the slot. *)
Theorem apply_sibling : apply_sibling_statement.
Proof.
  intros x move_from move_to closure args k exn decls slot_values code vars
    conts statics Hclosure Hto.
  apply let_equivalent_step; [ reflexivity | ].
  intros v. simpl. rewrite Hclosure. unfold project_function_slot.
  rewrite Pos.eqb_refl, Hto.
  destruct (lookup move_from decls); [ | discriminate ].
  simpl. intros [= <-].
  apply (apply_indirect_known (Var x) args k exn
           (Value_closure_of_set move_to decls slot_values) code slot_values).
  - simpl. rewrite Pos.eqb_refl. reflexivity.
  - simpl. rewrite Hto. reflexivity.
Qed.

(* ======================================================================== *)
(* A static set of closures                                                 *)
(* ======================================================================== *)

(* Each binding of [bind_closures] binds its symbol, which was not bound,
   and the bindings that follow leave it so. [all] is all the symbols of
   the set, and [symbols] those still to bind. *)
Lemma bind_closures_binds_aux (vars : env)
    (all : list (function_slot * symbol))
    (decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple))
    (slot_values : list (value_slot * value)) :
  eval_value_slots vars value_slots = Some slot_values ->
  ∀ (symbols : list (function_slot * symbol)) (statics extended : static_env),
    eval_static_bindings vars
      (map
         (fun '(slot, s) =>
            Bind_symbol s
              (Static_const_closure_of_set slot all decls value_slots))
         symbols)
      statics
    = Some extended ->
    ∀ (slot : function_slot) (s : symbol),
      (slot, s) ∈ symbols ->
      lookup s (static_values extended)
      = Some (Static_closure_of_set slot all decls slot_values).
Proof.
  intros Hslots.
  induction symbols as [ | [slot0 s0] symbols IH]; intros statics extended;
    simpl; [ intros _ slot s [] | ].
  destruct (lookup s0 (static_values statics)); [ discriminate | ].
  destruct (lookup slot0 decls) as [code0 | ]; [ | discriminate ].
  simpl. rewrite Hslots. simpl. intros Heval slot s [Heq | Hin].
  - injection Heq as <- <-.
    apply (proj2 (eval_static_bindings_extend vars _ _ _ Heval)). simpl.
    apply lookup_head.
  - exact (IH _ _ Heval slot s Hin).
Qed.

Theorem bind_closures_binds : bind_closures_binds_statement.
Proof.
  intros vars closure_symbols decls value_slots slot_values statics extended
    Hslots Heval.
  exact (bind_closures_binds_aux vars closure_symbols decls value_slots
           slot_values Hslots closure_symbols statics extended Heval).
Qed.

Theorem static_set_bound_extend : static_set_bound_extend_statement.
Proof.
  intros statics statics' closure_symbols decls slot_values Hbound
    [_ Hvalues] slot s Hin.
  exact (Hvalues s _ (Hbound slot s Hin)).
Qed.

Theorem project_static_set : project_static_set_statement.
Proof.
  intros statics closure_symbols decls slot_values move_from move_to s s' code
    code' Hbound Hin Hsymbol Hfrom Hto.
  pose proof (Hbound move_from s Hin) as Hs.
  pose proof (Hbound move_to s' (lookup_in _ _ _ Hsymbol)) as Hs'.
  split.
  - unfold project_function_slot.
    rewrite Hs, Pos.eqb_refl, Hfrom, Hto, Hsymbol. reflexivity.
  - unfold closure_in_set. rewrite Hs', Hto. reflexivity.
Qed.

(* A set with a symbol is not bound where a value slot has no value. *)
Lemma bind_closures_undefined (vars : env)
    (closure_symbols : list (function_slot * symbol))
    (decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) (statics : static_env)
    (slot : function_slot) (s : symbol) :
  (slot, s) ∈ closure_symbols ->
  eval_value_slots vars value_slots = None ->
  eval_static_bindings vars (bind_closures closure_symbols decls value_slots)
    statics
  = None.
Proof.
  intros Hin Hslots. unfold bind_closures.
  destruct closure_symbols as [ | [slot0 s0] symbols]; [ destruct Hin | ].
  simpl. destruct (lookup s0 (static_values statics)); [ reflexivity | ].
  destruct (lookup slot0 decls); [ | reflexivity ].
  simpl. rewrite Hslots. reflexivity.
Qed.

(* Both sides bind the set, or neither does; once it is bound the
   projection is the symbol. *)
Theorem project_function_slot_static :
  project_function_slot_static_statement.
Proof.
  intros closure_symbols decls value_slots move_from move_to s s' code code' x
    body Hin Hsymbol Hfrom Hto vars conts statics.
  apply let_static_equivalent_step.
  destruct
    (eval_static_bindings vars
       (bind_closures closure_symbols decls value_slots) statics)
    as [extended | ] eqn:Heval; [ | exact I ].
  destruct (eval_value_slots vars value_slots) as [slot_values | ] eqn:Hslots;
    [ | rewrite (bind_closures_undefined vars closure_symbols decls
                   value_slots statics move_from s Hin Hslots) in Heval;
        discriminate ].
  pose proof (bind_closures_binds vars closure_symbols decls value_slots
                slot_values statics extended Hslots Heval) as Hbound.
  destruct (project_static_set extended closure_symbols decls slot_values
              move_from move_to s s' code code' Hbound Hin Hsymbol Hfrom Hto)
    as [Hproject _].
  apply let_equivalent_step; [ | intros v _; apply equivalent_refl ].
  cbn [eval_named eval_simple]. rewrite Hproject. reflexivity.
Qed.

(* The value of a value slot of a set is the value, where the set was
   made, of what the set gives the slot. *)
Lemma eval_value_slots_lookup (vars : env) (slot : value_slot)
    (contents : simple) :
  ∀ (value_slots : list (value_slot * simple))
    (slot_values : list (value_slot * value)),
    eval_value_slots vars value_slots = Some slot_values ->
    lookup slot value_slots = Some contents ->
    lookup slot slot_values = eval_simple vars contents.
Proof.
  induction value_slots as [ | [slot' s] value_slots IH]; intros slot_values;
    simpl; [ discriminate | ].
  destruct (eval_simple vars s) as [v | ] eqn:Hs; [ | discriminate ].
  destruct (eval_value_slots vars value_slots) as [rest | ];
    [ | discriminate ].
  simpl. intros [= <-]. simpl. destruct (Pos.eqb slot slot').
  - intros [= <-]. symmetry. exact Hs.
  - exact (IH rest eq_refl).
Qed.

(* Both sides bind the set, or neither does; once it is bound the slot
   holds the value that its contents had, and still have, the variables
   being the same. *)
Theorem project_value_slot_static : project_value_slot_static_statement.
Proof.
  intros closure_symbols decls value_slots project_from s code slot contents
    x body Hin Hfrom Hslot vars conts statics.
  apply let_static_equivalent_step.
  destruct
    (eval_static_bindings vars
       (bind_closures closure_symbols decls value_slots) statics)
    as [extended | ] eqn:Heval; [ | exact I ].
  destruct (eval_value_slots vars value_slots) as [slot_values | ] eqn:Hslots;
    [ | rewrite (bind_closures_undefined vars closure_symbols decls
                   value_slots statics project_from s Hin Hslots) in Heval;
        discriminate ].
  pose proof (bind_closures_binds vars closure_symbols decls value_slots
                slot_values statics extended Hslots Heval project_from s Hin)
    as Hs.
  apply let_equivalent_step; [ | intros v _; apply equivalent_refl ].
  cbn [eval_named eval_simple]. unfold project_value_slot, closure_in_set.
  rewrite Hs, Hfrom. cbn. rewrite Pos.eqb_refl. symmetry.
  exact (eval_value_slots_lookup vars slot contents value_slots slot_values
           Hslots Hslot).
Qed.

(* Two bindings to one thing, where each thing is bound once, are of one
   name. *)
Lemma in_snd_NoDup {A : Type} (bindings : list (positive * A))
    (name name' : positive) (a : A) :
  NoDup (map snd bindings) ->
  (name, a) ∈ bindings -> (name', a) ∈ bindings -> name = name'.
Proof.
  induction bindings as [ | [bound b] bindings IH]; simpl; [ intros _ [] | ].
  intros Hdistinct. inversion Hdistinct as [ | ? ? Hfresh Hrest]. subst.
  intros [Heq | Hin] [Heq' | Hin'].
  - congruence.
  - injection Heq as -> ->. exfalso. apply Hfresh.
    change a with (snd (name', a)). apply in_map, Hin'.
  - injection Heq' as -> ->. exfalso. apply Hfresh.
    change a with (snd (name, a)). apply in_map, Hin.
  - exact (IH Hrest Hin Hin').
Qed.

Theorem closure_code_determines_slot :
  closure_code_determines_slot_statement.
Proof.
  intros statics v slot slot' decls slots slots' code Hin_set Hdistinct Hof
    Hslot'.
  apply (proj1 (closure_in_set_of statics v code slots')) in Hof
    as (slot0 & decls0 & Hin_set0 & Hslot0).
  rewrite Hin_set in Hin_set0. injection Hin_set0 as <- <- _.
  apply distinct_NoDup in Hdistinct.
  exact (in_snd_NoDup decls slot' slot code Hdistinct
           (lookup_in _ _ _ Hslot') (lookup_in _ _ _ Hslot0)).
Qed.

(* ======================================================================== *)
(* The sets of a well-formed unit                                           *)
(* ======================================================================== *)

(* A symbol bound after a group was bound before it, or the group binds
   it. *)
Lemma eval_static_bindings_symbol (vars : env)
    (bindings : list static_binding) :
  ∀ (statics extended : static_env) (s : symbol)
    (allocated : statically_allocated_value),
    eval_static_bindings vars bindings statics = Some extended ->
    lookup s (static_values extended) = Some allocated ->
    lookup s (static_values statics) = Some allocated
    ∨ ∃ const : static_const,
        Bind_symbol s const ∈ bindings
        ∧ eval_static_const vars const = Some allocated.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH];
    intros statics extended s allocated; simpl.
  - intros [= <-]. auto.
  - destruct (lookup id (static_code statics)); [ discriminate | ].
    intros Heval Hs.
    destruct (IH _ _ s allocated Heval Hs) as [Hold | (const & Hin & Hconst)];
      [ left; exact Hold | right; exists const; auto ].
  - intros Heval Hs.
    destruct (IH _ _ s allocated Heval Hs) as [Hold | (const & Hin & Hconst)];
      [ left; exact Hold | right; exists const; auto ].
  - destruct (lookup sym (static_values statics)); [ discriminate | ].
    destruct (eval_static_const vars const) as [a | ] eqn:Hconst; simpl;
      [ | discriminate ].
    intros Heval Hs.
    destruct (IH _ _ s allocated Heval Hs)
      as [Hold | (const' & Hin & Hconst')];
      [ | right; exists const'; auto ].
    simpl in Hold.
    destruct (Pos.eqb_spec s sym) as [-> | _]; [ | left; exact Hold ].
    injection Hold as <-. right. exists const. auto.
Qed.

(* A group binds each of its symbols to what its constant is. *)
Lemma eval_static_bindings_binds (vars : env)
    (bindings : list static_binding) :
  ∀ (statics extended : static_env) (s : symbol) (const : static_const),
    eval_static_bindings vars bindings statics = Some extended ->
    Bind_symbol s const ∈ bindings ->
    ∃ allocated : statically_allocated_value,
      eval_static_const vars const = Some allocated
      ∧ lookup s (static_values extended) = Some allocated.
Proof.
  induction bindings as [ | [id c | id | sym const0] bindings IH];
    intros statics extended s const; simpl; [ intros _ [] | | | ].
  - destruct (lookup id (static_code statics)); [ discriminate | ].
    intros Heval [[=] | Hin]. exact (IH _ _ s const Heval Hin).
  - intros Heval [[=] | Hin]. exact (IH _ _ s const Heval Hin).
  - destruct (lookup sym (static_values statics)); [ discriminate | ].
    destruct (eval_static_const vars const0) as [a | ] eqn:Hconst; simpl;
      [ | discriminate ].
    intros Heval [Heq | Hin]; [ | exact (IH _ _ s const Heval Hin) ].
    injection Heq as <- <-. exists a. split; [ exact Hconst | ].
    apply (proj2 (eval_static_bindings_extend vars _ _ _ Heval)). simpl.
    apply lookup_head.
Qed.

(* Only the constant of a closure of a static set makes one. *)
Lemma eval_static_const_closure_of_set (vars : env) (const : static_const)
    (slot : function_slot) (symbols : list (function_slot * symbol))
    (decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)) :
  eval_static_const vars const
  = Some (Static_closure_of_set slot symbols decls slot_values) ->
  ∃ value_slots : list (value_slot * simple),
    const = Static_const_closure_of_set slot symbols decls value_slots
    ∧ eval_value_slots vars value_slots = Some slot_values.
Proof.
  destruct const
    as [code slots | fslot syms fdecls slots | tag fields | contents | bytes];
    simpl.
  - destruct (eval_value_slots vars slots); discriminate.
  - destruct (lookup fslot fdecls); [ | discriminate ]. simpl.
    destruct (eval_value_slots vars slots) as [evaluated | ] eqn:Hslots;
      [ | discriminate ].
    simpl. intros [= <- <- <- <-]. exists slots. auto.
  - destruct (eval_simples vars fields); discriminate.
  - destruct (eval_simple vars contents); discriminate.
  - discriminate.
Qed.

Lemma binds_symbol_to_sound (s : symbol) (const : static_const)
    (binding : static_binding) :
  binds_symbol_to s const binding = true -> binding = Bind_symbol s const.
Proof.
  destruct binding as [id c | id | s' const']; simpl; try discriminate.
  intros H. apply andb_true_iff in H as [Hs Hconst].
  apply Pos.eqb_eq in Hs.
  destruct (static_const_eq_dec const const'); [ | discriminate ].
  congruence.
Qed.

(* What [static_set_whole] asks of the binding of a closure of a set. *)
Lemma static_set_whole_facts (bindings : list static_binding) (s : symbol)
    (slot : function_slot) (symbols : list (function_slot * symbol))
    (decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) :
  static_set_whole bindings
    (Bind_symbol s
       (Static_const_closure_of_set slot symbols decls value_slots))
  = true ->
  is_bound slot decls = true
  ∧ lookup slot symbols = Some s
  ∧ ∀ (slot' : function_slot) (s' : symbol),
      (slot', s') ∈ symbols ->
      Bind_symbol s'
        (Static_const_closure_of_set slot' symbols decls value_slots)
      ∈ bindings.
Proof.
  unfold static_set_whole. intros H.
  apply andb_true_iff in H as [H Hall].
  apply andb_true_iff in H as [H Hsymbol].
  apply andb_true_iff in H as [Hset _]. unfold set_well_formed in Hset.
  apply andb_true_iff in Hset as [Hset _].
  apply andb_true_iff in Hset as [Hslot _].
  split; [ exact Hslot | ]. split.
  - destruct (lookup slot symbols) as [s0 | ]; [ | discriminate ].
    apply Pos.eqb_eq in Hsymbol. congruence.
  - intros slot' s' Hin. rewrite forallb_forall in Hall.
    specialize (Hall (slot', s') Hin). simpl in Hall.
    apply existsb_exists in Hall as [binding [Hbinding Hbinds]].
    apply binds_symbol_to_sound in Hbinds. subst binding. exact Hbinding.
Qed.

(* A group every set of which is whole, added to a static environment in
   which the sets are bound: the sets are bound. *)
Lemma eval_static_bindings_sets_bound (vars : env)
    (bindings : list static_binding) (statics extended : static_env) :
  forallb (static_set_whole bindings) bindings = true ->
  static_sets_bound statics ->
  eval_static_bindings vars bindings statics = Some extended ->
  static_sets_bound extended.
Proof.
  intros Hwhole Hbound Heval s slot symbols decls slot_values Hs.
  pose proof (eval_static_bindings_extend vars bindings statics extended
                Heval) as Hextend.
  destruct (eval_static_bindings_symbol vars bindings statics extended s _
              Heval Hs) as [Hold | (const & Hin & Hconst)].
  - destruct (Hbound s slot symbols decls slot_values Hold)
      as [Hsymbol Hset].
    split; [ exact Hsymbol | ].
    exact (static_set_bound_extend statics extended symbols decls slot_values
             Hset Hextend).
  - destruct (eval_static_const_closure_of_set vars const slot symbols decls
                slot_values Hconst) as (value_slots & -> & Hslots).
    rewrite forallb_forall in Hwhole.
    destruct (static_set_whole_facts bindings s slot symbols decls
                value_slots (Hwhole _ Hin)) as (_ & Hsymbol & Hall).
    split; [ exact Hsymbol | ]. intros slot' s' Hin'.
    destruct (eval_static_bindings_binds vars bindings statics extended s' _
                Heval (Hall slot' s' Hin')) as (allocated & Hallocated & Hs').
    rewrite Hs'. f_equal. simpl in Hallocated. rewrite Hslots in Hallocated.
    destruct (lookup slot' decls); [ | discriminate ].
    simpl in Hallocated. congruence.
Qed.

(* The handlers a continuation holds, and those of the continuations it
   holds, have well-formed sets. *)
Fixpoint cont_sets_ok (c : cont_value) : Prop :=
  match c with
  | Outer _ => True
  | Closure h _ conts recursive =>
    handler_sets_well_formed h = true
    ∧ forallb (fun '(_, h) => handler_sets_well_formed h) recursive = true
    ∧ fold_right (fun kc acc => cont_sets_ok (snd kc) ∧ acc) True conts
  end.

Definition conts_sets_ok (conts : cont_env) : Prop :=
  fold_right (fun kc acc => cont_sets_ok (snd kc) ∧ acc) True conts.

Lemma conts_sets_ok_app (conts conts' : cont_env) :
  conts_sets_ok conts -> conts_sets_ok conts' ->
  conts_sets_ok (conts ++ conts').
Proof.
  unfold conts_sets_ok. induction conts as [ | kc conts IH]; simpl; [ auto | ].
  intros [Hc Hrest] H'. split; [ exact Hc | exact (IH Hrest H') ].
Qed.

Lemma resolve_sets_ok (k : continuation) (conts : cont_env) :
  conts_sets_ok conts -> cont_sets_ok (resolve k conts).
Proof.
  unfold resolve, conts_sets_ok.
  induction conts as [ | [k' c] conts IH]; simpl; [ intros _; exact I | ].
  intros [Hc Hrest]. destruct (Pos.eqb k k'); [ exact Hc | exact (IH Hrest) ].
Qed.

Lemma rec_closures_sets_ok (vars : env) (conts : cont_env)
    (all handlers : list (continuation * continuation_handler)) :
  forallb (fun '(_, h) => handler_sets_well_formed h) all = true ->
  conts_sets_ok conts ->
  forallb (fun '(_, h) => handler_sets_well_formed h) handlers = true ->
  conts_sets_ok (map (fun '(k, h) => (k, Closure h vars conts all)) handlers).
Proof.
  intros Hall Hconts. unfold conts_sets_ok.
  induction handlers as [ | [k h] handlers IH]; simpl;
    [ intros _; exact I | ].
  intros H. apply andb_true_iff in H as [Hh Hrest].
  split; [ | exact (IH Hrest) ].
  split; [ exact Hh | ]. split; [ exact Hall | exact Hconts ].
Qed.

Definition code_sets_ok (statics : static_env) : Prop :=
  ∀ (id : code_id) (c : code),
    lookup id (static_code statics) = Some c ->
    code_sets_well_formed c = true.

Lemma eval_static_bindings_code_sets_ok (vars : env)
    (bindings : list static_binding) :
  ∀ statics statics' : static_env,
    forallb binding_sets_well_formed bindings = true ->
    code_sets_ok statics ->
    eval_static_bindings vars bindings statics = Some statics' ->
    code_sets_ok statics'.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH];
    intros statics statics'; simpl.
  - intros _ Hok [= <-]. exact Hok.
  - intros H Hok. apply andb_true_iff in H as [Hc Hrest].
    destruct (lookup id (static_code statics)); [ discriminate | ].
    apply (IH _ _ Hrest). intros id' c'. simpl.
    destruct (Pos.eqb id' id); [ intros [= <-]; exact Hc | apply Hok ].
  - intros H Hok. exact (IH _ _ H Hok).
  - intros H Hok.
    destruct (lookup sym (static_values statics)); [ discriminate | ].
    destruct (eval_static_const vars const); simpl; [ | discriminate ].
    apply (IH _ _ H). exact Hok.
Qed.

(* What holds of every state of the run of a well-formed unit: the sets
   of all the terms it holds are well-formed, and the static sets are
   bound. *)
Definition sets_inv (s : state) : Prop :=
  sets_well_formed (state_expr s) = true
  ∧ conts_sets_ok (state_conts s)
  ∧ code_sets_ok (state_statics s)
  ∧ static_sets_bound (state_statics s).

Lemma sets_inv_step (s s' : state) :
  sets_inv s -> step s = Step s' -> sets_inv s'.
Proof.
  intros (P & C & S & B) Hstep. rewrite (state_eta s) in Hstep.
  set (vars := state_vars s) in *. set (conts := state_conts s) in *.
  set (statics := state_statics s) in *.
  destruct (state_expr s)
    as [ x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    autorewrite with step in Hstep.
  - (* Let *)
    destruct (eval_named statics vars d); [ | discriminate ].
    injection Hstep as <-. unfold sets_inv. simpl_state. simpl in P.
    apply andb_true_iff in P as [_ Pbody].
    exact (conj Pbody (conj C (conj S B))).
  - (* Let_static *)
    destruct (eval_static_bindings vars bindings statics) as [statics' | ]
      eqn:Heval; [ | discriminate ].
    injection Hstep as <-. unfold sets_inv. simpl_state. simpl in P.
    apply andb_true_iff in P as [P Pbody].
    apply andb_true_iff in P as [P Pbindings].
    apply andb_true_iff in P as [Pwhole _].
    refine (conj Pbody (conj C (conj _ _))).
    + exact (eval_static_bindings_code_sets_ok vars bindings statics statics'
               Pbindings S Heval).
    + exact (eval_static_bindings_sets_bound vars bindings statics statics'
               Pwhole B Heval).
  - (* Let_cont_non_recursive *)
    injection Hstep as <-. unfold sets_inv. simpl_state. simpl in P.
    apply andb_true_iff in P as [Ph Pbody].
    refine (conj Pbody (conj (conj _ C) (conj S B))).
    simpl. exact (conj Ph (conj eq_refl C)).
  - (* Let_cont_recursive *)
    destruct (handlers_bind_statics handlers); [ discriminate | ].
    injection Hstep as <-. unfold sets_inv. simpl_state. simpl in P.
    apply andb_true_iff in P as [Phandlers Pbody].
    refine (conj Pbody (conj (conts_sets_ok_app _ _ _ C) (conj S B))).
    exact (rec_closures_sets_ok vars conts handlers handlers Phandlers C
             Phandlers).
  - (* Apply *)
    destruct (eval_simple vars (ap_callee ap)) as [callee | ];
      [ | discriminate ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | discriminate ].
    apply call_function_step in Hstep
      as (called & c & callee_vars & Hlookup & ->).
    unfold sets_inv. simpl_state.
    pose proof (S called c Hlookup) as Hc.
    destruct c as [params my_closure ret exn body]. simpl in Hc |- *.
    refine (conj Hc (conj (conj _ (conj _ I)) (conj S B)));
      apply resolve_sets_ok, C.
  - (* Apply_cont *)
    destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | discriminate ].
    unfold apply_continuation, apply_cont_value in Hstep.
    pose proof (resolve_sets_ok (ac_continuation ac) conts C) as Cr.
    destruct (resolve (ac_continuation ac) conts)
      as [[params handler] def_vars def_conts recursive | k];
      [ | discriminate ].
    destruct (bind_params params vs def_vars); [ | discriminate ].
    injection Hstep as <-. unfold sets_inv. simpl_state. simpl in Cr.
    destruct Cr as (Ph & Hrec & Cdef).
    refine (conj Ph (conj (conts_sets_ok_app _ _ _ Cdef) (conj S B))).
    exact (rec_closures_sets_ok def_vars def_conts recursive recursive Hrec
             Cdef Hrec).
  - (* Switch *)
    destruct (eval_simple vars scrutinee) as [v | ]; [ | discriminate ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | discriminate ].
    destruct (find_arm i arms); [ | discriminate ].
    injection Hstep as <-. unfold sets_inv. simpl_state.
    exact (conj eq_refl (conj C (conj S B))).
  - discriminate.
Qed.

Lemma sets_inv_run (n : nat) :
  ∀ s s' : state, sets_inv s -> run n s = Step s' -> sets_inv s'.
Proof.
  induction n as [ | n IH]; intros s s' Hinv; simpl.
  - intros [= <-]. exact Hinv.
  - destruct (step s) as [next | k vs | ] eqn:Hstep; try discriminate.
    exact (IH next s' (sets_inv_step s next Hinv Hstep)).
Qed.

Lemma well_formed_sets_inv (unit_exn : continuation) (e : expr) (n : nat)
    (s : state) :
  well_formed_unit unit_exn e = true ->
  run n (State e [] [] empty_static_env) = Step s ->
  sets_inv s.
Proof.
  intros Hwf. unfold well_formed_unit in Hwf.
  apply andb_true_iff in Hwf as [_ Hsets].
  apply sets_inv_run. unfold sets_inv. simpl_state.
  refine (conj Hsets (conj I (conj _ _))).
  - intros id c [=].
  - intros sym slot symbols decls slot_values [=].
Qed.

Theorem well_formed_makes_closures : well_formed_makes_closures_statement.
Proof.
  intros unit_exn e n s Hwf Hrun.
  destruct (well_formed_sets_inv unit_exn e n s Hwf Hrun) as (P & _).
  unfold makes_closure_outside_set.
  destruct (state_expr s)
    as [ x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    try reflexivity.
  - simpl in P. apply andb_true_iff in P as [Pd _].
    destruct d as [smp | p args | code slots | fslot decls slots
      | slot closure | pfrom slot closure | move_from move_to closure];
      try reflexivity.
    simpl in Pd. unfold set_well_formed in Pd.
    apply andb_true_iff in Pd as [Pd _].
    apply andb_true_iff in Pd as [-> _]. reflexivity.
  - simpl in P. apply andb_true_iff in P as [P _].
    apply andb_true_iff in P as [P _].
    apply andb_true_iff in P as [Pwhole _].
    match goal with
    | |- existsb ?bad bindings = false =>
      destruct (existsb bad bindings) eqn:Hexists; [ | reflexivity ]
    end.
    apply existsb_exists in Hexists as [binding [Hin Hbad]].
    rewrite forallb_forall in Pwhole. specialize (Pwhole binding Hin).
    destruct binding
      as [id c | id
         | sym
             [code slots | fslot syms decls slots | tag fields | contents
             | bytes]];
      try discriminate.
    destruct (static_set_whole_facts bindings sym fslot syms decls slots
                Pwhole) as (Hslot & _).
    rewrite Hslot in Hbad. discriminate.
Qed.

Theorem well_formed_sets_bound : well_formed_sets_bound_statement.
Proof.
  intros unit_exn e n s Hwf Hrun.
  destruct (well_formed_sets_inv unit_exn e n s Hwf Hrun) as (_ & _ & _ & B).
  exact B.
Qed.

Theorem project_function_slot_bound : project_function_slot_bound_statement.
Proof.
  intros statics move_from move_to v w Hbound.
  unfold project_function_slot.
  destruct v as [c | code slots | slot decls slots | s | tag fields
    | contents];
    [ | | | | discriminate .. ].
  - discriminate.
  - intros Hproject.
    apply project_unnamed_function_slot in Hproject as (-> & -> & ->).
    exists [(unnamed_function_slot, code)], slots. auto.
  - destruct (Pos.eqb_spec slot move_from) as [-> | _]; [ | discriminate ].
    destruct (lookup move_from decls) as [code | ] eqn:Hfrom;
      [ | discriminate ].
    destruct (lookup move_to decls) as [code' | ] eqn:Hto; [ | discriminate ].
    simpl. intros [= <-]. exists decls, slots. simpl. rewrite Hfrom, Hto.
    auto.
  - destruct (lookup s (static_values statics))
      as [[code slots | slot syms decls slots | tag fields | contents
          | bytes] | ] eqn:Hs;
      try discriminate.
    + intros Hproject.
      apply project_unnamed_function_slot in Hproject as (-> & -> & ->).
      exists [(unnamed_function_slot, code)], slots. simpl. rewrite Hs. auto.
    + destruct (Pos.eqb_spec slot move_from) as [-> | _]; [ | discriminate ].
      destruct (lookup move_from decls) as [code | ] eqn:Hfrom;
        [ | discriminate ].
      destruct (lookup move_to decls) as [code' | ] eqn:Hto;
        [ | discriminate ].
      destruct (lookup move_to syms) as [s' | ] eqn:Hsymbol;
        [ | discriminate ].
      simpl. intros [= <-]. exists decls, slots.
      destruct (Hbound s move_from syms decls slots Hs) as [_ Hset].
      pose proof (Hset move_to s' (lookup_in _ _ _ Hsymbol)) as Hs'.
      simpl. rewrite Hs, Hs', Hfrom, Hto. auto.
Qed.

(* ======================================================================== *)
(* The example                                                              *)
(* ======================================================================== *)

(* The two units are run. *)
Theorem parity_let : parity_let_statement.
Proof.
  intros i answer [[= <- <-] | [[= <- <-] | []]]; eexists;
    (split; [ reflexivity | ]); exists 60; vm_compute; reflexivity.
Qed.

Theorem parity_static : parity_static_statement.
Proof.
  intros i answer [[= <- <-] | [[= <- <-] | []]]; exists 60; vm_compute;
    reflexivity.
Qed.

Theorem parity_well_formed : parity_well_formed_statement.
Proof.
  intros i. split; [ vm_compute; reflexivity | ].
  eexists. split; [ reflexivity | vm_compute; reflexivity ].
Qed.

Theorem partial_static_set : partial_static_set_statement.
Proof.
  split; [ exists 10; vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.
