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

(* Proofs for FlambdaLiftFromCodeSpec.v. Nothing here needs review.

   The two runs are in step. The second expression is the first with
   its [Let]s lifted out and its groups of static bindings rewritten;
   values are related by FlambdaLiftSpec.value_lifted, as for the
   lifting at toplevel, and the lemmas of FlambdaLiftProofs.v about the
   observations of such values are used as they are. The second static
   environment has the code of the first, rewritten, and binds every
   symbol that the first binds to the same thing, lifted
   ([statics_lifted_out]); and it has, for the code that the first has
   bound, what the [Let]s lifted out of it need ([aliases_bound]): each
   symbol given is bound to what its [Let] makes, whenever the [Let] is
   executed. That is so from the group that binds the code on, as the
   bindings of the symbols are in that group; and a defining expression
   that mentions no variable is evaluated alike in every environment.

   The second run is that of a well-formed unit, so it never binds a
   symbol twice (FlambdaWellFormedProofs.well_formed_never_faults).
   That the values at the exit are equal is from the invariant of the
   first run that FlambdaLiftProofs.v has for the check of the exits
   ([plain_state]). *)

From Stdlib Require Import ZArith List Bool Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaPrimitiveModel FlambdaPrimitiveProofs
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaSimulationProofs
  FlambdaNominalSpec FlambdaNominalProofs FlambdaWellFormedSpec
  FlambdaWellFormedProofs FlambdaClosuresSpec FlambdaClosuresProofs
  FlambdaStaticProofs FlambdaUnusedStaticsSpec FlambdaLiftSpec
  FlambdaLiftProofs FlambdaLiftFromCodeSpec.
Import ListNotations.

(* ======================================================================== *)
(* Lists of names                                                           *)
(* ======================================================================== *)

Lemma distinct_app_parts (names names' : list positive) :
  distinct (names ++ names') = true ->
  distinct names = true
  ∧ distinct names' = true
  ∧ ∀ name : positive, name ∈ names -> ¬ name ∈ names'.
Proof.
  induction names as [ | first names IH]; simpl; intros Hdistinct.
  - split; [ reflexivity | ]. split; [ exact Hdistinct | intros name [] ].
  - apply andb_true_iff in Hdistinct as [Hfirst Hrest].
    apply negb_true_iff in Hfirst.
    destruct (IH Hrest) as (Hnames & Hnames' & Hapart).
    split; [ | split; [ exact Hnames' | ] ].
    + apply andb_true_iff. split; [ | exact Hnames ].
      apply negb_true_iff.
      destruct (among first names) eqn:Hamong; [ | reflexivity ].
      rewrite <- Hfirst. symmetry. apply among_In. apply in_or_app. left.
      apply among_In. exact Hamong.
    + intros name [<- | Hin] Hin'; [ | exact (Hapart name Hin Hin') ].
      assert (Hamong : among first (names ++ names') = true)
        by (apply among_In; apply in_or_app; right; exact Hin').
      rewrite Hamong in Hfirst. discriminate.
Qed.

(* A symbol that a group does not bind, and that was not bound, is not
   bound after it. *)
Lemma eval_static_bindings_fresh (vars : env)
    (bindings : list static_binding) (statics extended : static_env)
    (s : symbol) :
  eval_static_bindings vars bindings statics = Some extended ->
  lookup s (static_values statics) = None ->
  ¬ s ∈ flat_map symbols_of_binding bindings ->
  lookup s (static_values extended) = None.
Proof.
  intros Heval Hs Hnotin.
  destruct (lookup s (static_values extended)) as [allocated | ] eqn:Hs';
    [ | reflexivity ].
  destruct (eval_static_bindings_symbol vars bindings statics extended s
              allocated Heval Hs')
    as [Hold | (const & Hin & _)].
  - rewrite Hs in Hold. discriminate.
  - exfalso. apply Hnotin. apply in_flat_map.
    exists (Bind_symbol s const). split; [ exact Hin | left; reflexivity ].
Qed.

(* ======================================================================== *)
(* What mentions no variable is evaluated alike in every environment        *)
(* ======================================================================== *)

Lemma eval_plain_simple (vars vars' : env) (s : simple) :
  plain_simple s = true -> eval_simple vars s = eval_simple vars' s.
Proof. destruct s as [x | sym | c]; [ discriminate | | ]; reflexivity. Qed.

Lemma eval_plain_simples (vars vars' : env) (args : list simple) :
  forallb plain_simple args = true ->
  eval_simples vars args = eval_simples vars' args.
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  intros Hplain. apply andb_true_iff in Hplain as [Hs Hargs].
  rewrite (eval_plain_simple vars vars' s Hs), (IH Hargs). reflexivity.
Qed.

Lemma eval_plain_value_slots (vars vars' : env)
    (slots : list (value_slot * simple)) :
  forallb (fun slot => plain_simple (snd slot)) slots = true ->
  eval_value_slots vars slots = eval_value_slots vars' slots.
Proof.
  induction slots as [ | [slot s] slots IH]; simpl; [ reflexivity | ].
  intros Hplain. apply andb_true_iff in Hplain as [Hs Hslots].
  rewrite (eval_plain_simple vars vars' s Hs), (IH Hslots). reflexivity.
Qed.

Lemma closed_eval_named (statics : static_env) (vars vars' : env)
    (d : named) :
  closed_named d = true ->
  eval_named statics vars d = eval_named statics vars' d.
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    simpl; try discriminate; intros Hclosed.
  - rewrite (eval_plain_simples vars vars' args Hclosed). reflexivity.
  - rewrite (eval_plain_value_slots vars vars' slots Hclosed). reflexivity.
  - rewrite (eval_plain_value_slots vars vars' slots Hclosed). reflexivity.
Qed.

(* And it has a value. *)
Lemma eval_plain_simple_some (vars : env) (s : simple) :
  plain_simple s = true -> ∃ v : value, eval_simple vars s = Some v.
Proof. destruct s as [x | sym | c]; [ discriminate | | ]; simpl; eauto. Qed.

Lemma eval_plain_simples_some (vars : env) (args : list simple) :
  forallb plain_simple args = true ->
  ∃ vs : list value, eval_simples vars args = Some vs.
Proof.
  induction args as [ | s args IH]; simpl; [ eauto | ].
  intros Hplain. apply andb_true_iff in Hplain as [Hs Hargs].
  destruct (eval_plain_simple_some vars s Hs) as [v ->].
  destruct (IH Hargs) as [vs ->]. simpl. eauto.
Qed.

Lemma eval_plain_value_slots_some (vars : env)
    (slots : list (value_slot * simple)) :
  forallb (fun slot => plain_simple (snd slot)) slots = true ->
  ∃ vs : list (value_slot * value), eval_value_slots vars slots = Some vs.
Proof.
  induction slots as [ | [slot s] slots IH]; simpl; [ eauto | ].
  intros Hplain. apply andb_true_iff in Hplain as [Hs Hslots].
  destruct (eval_plain_simple_some vars s Hs) as [v ->].
  destruct (IH Hslots) as [vs ->]. simpl. eauto.
Qed.

(* ======================================================================== *)
(* The bindings that stand for a [Let] lifted out                           *)
(* ======================================================================== *)

(* The symbol that stands for a [Let] is bound to what the [Let] makes,
   whenever it is executed. *)
Definition alias_bound (statics' : static_env) (d : named) (s : symbol)
    : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value),
    eval_named statics vars d = Some v ->
    value_lifted statics' v (Value_symbol s).

Lemma alias_bound_extend (statics' statics'' : static_env) (d : named)
    (s : symbol) :
  statics_extend statics' statics'' ->
  alias_bound statics' d s ->
  alias_bound statics'' d s.
Proof.
  intros Hextend Hbound statics vars v Hd.
  exact (value_lifted_extend _ _ Hextend _ _ (Hbound statics vars v Hd)).
Qed.

(* The bindings are evaluated, in any environment, where their symbols
   are distinct and not bound. *)
Lemma lifted_out_evaluates (target : lift_to) (d : named)
    (bindings : list static_binding) (s : symbol) (vars' : env)
    (statics' : static_env) :
  lift_named target d = Some (bindings, s) ->
  closed_named d = true ->
  distinct (flat_map symbols_of_binding bindings) = true ->
  (∀ s0 : symbol,
    s0 ∈ flat_map symbols_of_binding bindings ->
    lookup s0 (static_values statics') = None) ->
  ∃ extended' : static_env,
    eval_static_bindings vars' bindings statics' = Some extended'
    ∧ static_code extended' = static_code statics'.
Proof.
  intros Hlift Hclosed Hdistinct Hfresh.
  destruct target as [sym | syms].
  - destruct d as [ | p args | code slots | | | | ]; simpl in Hlift;
      try discriminate.
    2: { (* A closure of a set of one function. *)
      injection Hlift as <- <-. simpl in Hclosed.
      destruct (eval_plain_value_slots_some vars' slots Hclosed)
        as [vs Hslots].
      simpl. rewrite (Hfresh sym (or_introl eq_refl)), Hslots. simpl.
      eexists. split; reflexivity. }
    destruct p as [p | p | p | p]; simpl in Hlift; try discriminate.
    + (* A boxed number. *)
      destruct p; simpl in Hlift; try discriminate.
      destruct args as [ | contents [ | arg args]]; simpl in Hlift;
        try discriminate.
      injection Hlift as <- <-. simpl in Hclosed.
      apply andb_true_iff in Hclosed as [Hclosed _].
      destruct (eval_plain_simple_some vars' contents Hclosed)
        as [w Hcontents].
      simpl. rewrite (Hfresh sym (or_introl eq_refl)), Hcontents. simpl.
      eexists. split; reflexivity.
    + (* A block. *)
      destruct p as [[tag]]. simpl in Hlift. injection Hlift as <- <-.
      simpl in Hclosed.
      destruct (eval_plain_simples_some vars' args Hclosed) as [vs Hargs].
      simpl. rewrite (Hfresh sym (or_introl eq_refl)), Hargs. simpl.
      eexists. split; reflexivity.
  - (* A closure of a set. *)
    destruct d as [ | | | fslot decls slots | | | ]; simpl in Hlift;
      try discriminate.
    destruct (lookup fslot syms) as [s1 | ] eqn:Hsym; [ | discriminate ].
    destruct (list_eq_dec Pos.eq_dec (map fst syms) (map fst decls))
      as [Hsyms | ];
      [ | discriminate ].
    injection Hlift as <- <-. simpl in Hclosed.
    destruct (eval_plain_value_slots_some vars' slots Hclosed)
      as [vs Hslots].
    rewrite bind_closures_symbols in Hdistinct, Hfresh.
    destruct (eval_closure_bindings vars' syms decls slots vs Hslots syms
                statics')
      as (extended' & Hextended & Hcode);
      [ | exact Hdistinct | exact Hfresh | eauto ].
    intros slot s0 Hin Hnone.
    apply (lookup_none_not_in slot decls Hnone).
    pose proof (in_map fst syms (slot, s0) Hin) as Hslot.
    rewrite Hsyms in Hslot. exact Hslot.
Qed.

(* And they bind the symbol to what the [Let] makes. *)
Lemma lifted_out_bound (target : lift_to) (d : named)
    (bindings : list static_binding) (s : symbol) (vars' : env)
    (statics' : static_env) :
  lift_named target d = Some (bindings, s) ->
  closed_named d = true ->
  distinct (flat_map symbols_of_binding bindings) = true ->
  (∀ s0 : symbol,
    s0 ∈ flat_map symbols_of_binding bindings ->
    lookup s0 (static_values statics') = None) ->
  ∃ extended' : static_env,
    eval_static_bindings vars' bindings statics' = Some extended'
    ∧ static_code extended' = static_code statics'
    ∧ alias_bound extended' d s.
Proof.
  intros Hlift Hclosed Hdistinct Hfresh.
  destruct (lifted_out_evaluates target d bindings s vars' statics' Hlift
              Hclosed Hdistinct Hfresh)
    as (extended' & Hextended & Hcode).
  exists extended'. split; [ exact Hextended | ]. split; [ exact Hcode | ].
  intros statics vars v Hd.
  rewrite (closed_eval_named statics vars [] d Hclosed) in Hd.
  destruct (lift_named_lifted target d bindings s statics statics' [] vars'
              v Hlift)
    as (extended'' & Hextended'' & _ & Hv);
    [ intros x w [=] | exact Hd | exact Hdistinct | exact Hfresh | ].
  rewrite Hextended in Hextended''. injection Hextended'' as <-. exact Hv.
Qed.

(* ======================================================================== *)
(* The symbols of the [Let]s lifted out of an expression are bound          *)
(* ======================================================================== *)

Fixpoint aliases_bound (statics' : static_env) (lets : list (path * lift_to))
    (at_path : path) (e : expr) {struct e} : Prop :=
  match e with
  | Let _ _ d body =>
    match lifted_out lets at_path d with
    | Some (_, s) => alias_bound statics' d s
    | None => True
    end
    ∧ aliases_bound statics' lets (xO at_path) body
  | Let_static _ body => aliases_bound statics' lets (xO at_path) body
  | Let_cont_non_recursive _ h body =>
    handler_aliases_bound statics' lets (xI at_path) h
    ∧ aliases_bound statics' lets (xO at_path) body
  | Let_cont_recursive _ body => aliases_bound statics' lets (xO at_path) body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => True
  end
with handler_aliases_bound (statics' : static_env)
    (lets : list (path * lift_to)) (at_path : path)
    (h : continuation_handler) {struct h} : Prop :=
  match h with
  | Handler _ _ handler => aliases_bound statics' lets at_path handler
  end.

Fixpoint aliases_bound_extend (statics' statics'' : static_env)
    (Hextend : statics_extend statics' statics'')
    (lets : list (path * lift_to)) (at_path : path) (e : expr) {struct e} :
  aliases_bound statics' lets at_path e ->
  aliases_bound statics'' lets at_path e
with handler_aliases_bound_extend (statics' statics'' : static_env)
    (Hextend : statics_extend statics' statics'')
    (lets : list (path * lift_to)) (at_path : path)
    (h : continuation_handler) {struct h} :
  handler_aliases_bound statics' lets at_path h ->
  handler_aliases_bound statics'' lets at_path h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try exact (fun H => H).
    + intros [Hd Hbody].
      split; [ | exact (aliases_bound_extend _ _ Hextend _ _ body Hbody) ].
      destruct (lifted_out lets at_path d) as [[bindings s] | ];
        [ | exact I ].
      exact (alias_bound_extend _ _ d s Hextend Hd).
    + apply aliases_bound_extend. exact Hextend.
    + intros [Hh Hbody].
      split;
        [ exact (handler_aliases_bound_extend _ _ Hextend _ _ h Hh)
        | exact (aliases_bound_extend _ _ Hextend _ _ body Hbody) ].
    + apply aliases_bound_extend. exact Hextend.
  - destruct h as [params metadata handler]. simpl.
    apply aliases_bound_extend. exact Hextend.
Qed.

(* With no [Let] to lift out there is nothing to be bound. *)
Fixpoint aliases_bound_nil (statics' : static_env) (at_path : path)
    (e : expr) {struct e} :
  aliases_bound statics' [] at_path e
with handler_aliases_bound_nil (statics' : static_env) (at_path : path)
    (h : continuation_handler) {struct h} :
  handler_aliases_bound statics' [] at_path h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try exact I.
    + split; [ exact I | apply aliases_bound_nil ].
    + apply aliases_bound_nil.
    + split; [ apply handler_aliases_bound_nil | apply aliases_bound_nil ].
    + apply aliases_bound_nil.
  - destruct h as [params metadata handler]. simpl. apply aliases_bound_nil.
Qed.

(* The bindings that stand for the [Let]s lifted out of an expression
   are evaluated, where their symbols are distinct and not bound, and
   bind what those [Let]s need. *)
Fixpoint eval_lifted_out_bindings (vars' : env)
    (lets : list (path * lift_to)) (at_path : path) (e : expr) {struct e} :
  ∀ statics' : static_env,
    distinct
      (flat_map symbols_of_binding (lifted_out_bindings lets at_path e))
    = true ->
    (∀ s : symbol,
      s ∈ flat_map symbols_of_binding (lifted_out_bindings lets at_path e) ->
      lookup s (static_values statics') = None) ->
    ∃ extended' : static_env,
      eval_static_bindings vars' (lifted_out_bindings lets at_path e) statics'
      = Some extended'
      ∧ static_code extended' = static_code statics'
      ∧ aliases_bound extended' lets at_path e
with eval_handler_lifted_out_bindings (vars' : env)
    (lets : list (path * lift_to)) (at_path : path)
    (h : continuation_handler) {struct h} :
  ∀ statics' : static_env,
    distinct
      (flat_map symbols_of_binding
         (handler_lifted_out_bindings lets at_path h))
    = true ->
    (∀ s : symbol,
      s
      ∈ flat_map symbols_of_binding
          (handler_lifted_out_bindings lets at_path h) ->
      lookup s (static_values statics') = None) ->
    ∃ extended' : static_env,
      eval_static_bindings vars' (handler_lifted_out_bindings lets at_path h)
        statics'
      = Some extended'
      ∧ static_code extended' = static_code statics'
      ∧ handler_aliases_bound extended' lets at_path h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros statics'; simpl;
      try solve [ intros _ _; exists statics'; auto ].
    + (* Let *)
      rewrite flat_map_app. intros Hdistinct Hfresh.
      destruct (distinct_app_parts _ _ Hdistinct)
        as (Hdistinct_d & Hdistinct_body & Hapart).
      destruct (lifted_out lets at_path d) as [[bindings s] | ] eqn:Hout.
      * unfold lifted_out in Hout.
        destruct (lookup at_path lets) as [target | ]; [ | discriminate ].
        destruct (closed_named d) eqn:Hclosed; [ | discriminate ].
        destruct (lifted_out_bound target d bindings s vars' statics' Hout
                    Hclosed Hdistinct_d)
          as (extended1 & Hextended1 & Hcode1 & Hbound);
          [ intros s0 Hin; apply Hfresh; apply in_or_app; left; exact Hin
          | ].
        destruct (eval_lifted_out_bindings vars' lets (xO at_path) body
                    extended1 Hdistinct_body)
          as (extended2 & Hextended2 & Hcode2 & Hbody).
        { intros s0 Hin.
          apply (eval_static_bindings_fresh vars' bindings statics' extended1
                   s0 Hextended1);
            [ apply Hfresh; apply in_or_app; right; exact Hin | ].
          intros Hin'. exact (Hapart s0 Hin' Hin). }
        exists extended2.
        rewrite eval_static_bindings_app, Hextended1.
        split; [ exact Hextended2 | ].
        split; [ rewrite Hcode2; exact Hcode1 | ].
        split; [ | exact Hbody ].
        exact (alias_bound_extend _ _ d s
                 (eval_static_bindings_extend vars' _ extended1 extended2
                    Hextended2)
                 Hbound).
      * simpl in Hdistinct, Hfresh |- *.
        destruct (eval_lifted_out_bindings vars' lets (xO at_path) body
                    statics' Hdistinct Hfresh)
          as (extended' & Hextended & Hcode & Hbody).
        exists extended'. auto.
    + (* Let_static *)
      apply eval_lifted_out_bindings.
    + (* Let_cont_non_recursive *)
      rewrite flat_map_app. intros Hdistinct Hfresh.
      destruct (distinct_app_parts _ _ Hdistinct)
        as (Hdistinct_body & Hdistinct_h & Hapart).
      destruct (eval_lifted_out_bindings vars' lets (xO at_path) body statics'
                  Hdistinct_body)
        as (extended1 & Hextended1 & Hcode1 & Hbody);
        [ intros s0 Hin; apply Hfresh; apply in_or_app; left; exact Hin | ].
      destruct (eval_handler_lifted_out_bindings vars' lets (xI at_path) h
                  extended1 Hdistinct_h)
        as (extended2 & Hextended2 & Hcode2 & Hh).
      { intros s0 Hin.
        apply (eval_static_bindings_fresh vars' _ statics' extended1 s0
                 Hextended1);
          [ apply Hfresh; apply in_or_app; right; exact Hin | ].
        intros Hin'. exact (Hapart s0 Hin' Hin). }
      exists extended2.
      rewrite eval_static_bindings_app, Hextended1.
      split; [ exact Hextended2 | ].
      split; [ rewrite Hcode2; exact Hcode1 | ].
      split; [ exact Hh | ].
      exact (aliases_bound_extend _ _
               (eval_static_bindings_extend vars' _ extended1 extended2
                  Hextended2)
               _ _ body Hbody).
    + (* Let_cont_recursive *)
      apply eval_lifted_out_bindings.
  - destruct h as [params metadata handler]. simpl.
    apply eval_lifted_out_bindings.
Qed.

(* ======================================================================== *)
(* Where nothing is bound statically the rewrite changes nothing            *)
(* ======================================================================== *)

Lemma bindings_lift_from_code_nothing (K : lets_in_code)
    (bindings : list static_binding) :
  existsb binding_binds bindings = false ->
  flat_map (binding_lift_from_code K) bindings = bindings.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH]; simpl;
    try discriminate; [ reflexivity | ].
  intros Hbinds. rewrite (IH Hbinds). reflexivity.
Qed.

Fixpoint lift_from_code_nil (K : lets_in_code) (at_path : path)
    (e : expr) {struct e} :
  binds_statics e = false -> lift_from_code K [] at_path e = e
with handler_lift_from_code_nil (K : lets_in_code) (at_path : path)
    (h : continuation_handler) {struct h} :
  handler_binds_statics h = false -> handler_lift_from_code K [] at_path h = h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + intros Hbinds. rewrite (lift_from_code_nil K _ body Hbinds).
      reflexivity.
    + intros Hbinds. apply orb_false_iff in Hbinds as [Hbindings Hbody].
      rewrite (bindings_lift_from_code_nothing K bindings Hbindings),
        (lift_from_code_nil K _ body Hbody).
      reflexivity.
    + intros Hbinds. apply orb_false_iff in Hbinds as [Hh Hbody].
      rewrite (handler_lift_from_code_nil K _ h Hh),
        (lift_from_code_nil K _ body Hbody).
      reflexivity.
    + intros Hbinds. apply orb_false_iff in Hbinds as [_ Hbody].
      rewrite (lift_from_code_nil K _ body Hbody). reflexivity.
  - destruct h as [params metadata handler]. simpl. intros Hbinds.
    rewrite (lift_from_code_nil K _ handler Hbinds). reflexivity.
Qed.

(* The rewrite binds something statically where the expression does. *)
Lemma bindings_lift_from_code_bind (K : lets_in_code)
    (bindings : list static_binding) :
  existsb binding_binds (flat_map (binding_lift_from_code K) bindings)
  = existsb binding_binds bindings.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH]; simpl;
    [ reflexivity | | exact IH | reflexivity ].
  destruct c as [params my_closure ret exn metadata body].
  rewrite !existsb_app. simpl. rewrite orb_true_r. reflexivity.
Qed.

Fixpoint lift_from_code_binds_statics (K : lets_in_code)
    (lets : list (path * lift_to)) (at_path : path) (e : expr) {struct e} :
  binds_statics (lift_from_code K lets at_path e) = binds_statics e
with handler_lift_from_code_binds_statics (K : lets_in_code)
    (lets : list (path * lift_to)) (at_path : path)
    (h : continuation_handler) {struct h} :
  handler_binds_statics (handler_lift_from_code K lets at_path h)
  = handler_binds_statics h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + destruct (lifted_out lets at_path d) as [[bindings s] | ]; simpl;
        apply lift_from_code_binds_statics.
    + rewrite bindings_lift_from_code_bind, lift_from_code_binds_statics.
      reflexivity.
    + rewrite handler_lift_from_code_binds_statics,
        lift_from_code_binds_statics.
      reflexivity.
    + rewrite lift_from_code_binds_statics. reflexivity.
  - destruct h as [params metadata handler]. simpl.
    apply lift_from_code_binds_statics.
Qed.

(* ======================================================================== *)
(* The two static environments                                              *)
(* ======================================================================== *)

Section From_code.

Variable K : lets_in_code.

(* Code with the [Let]s that [K] gives for it lifted out. *)
Definition code_lifted_out (id : code_id) (c : code) : code :=
  match c with
  | Code params my_closure ret exn metadata body =>
    Code params my_closure ret exn metadata
      (lift_from_code K (lets_of K id) root body)
  end.

Lemma binding_lift_from_code_code (id : code_id) (c : code) :
  binding_lift_from_code K (Bind_code id c)
  = lifted_out_bindings (lets_of K id) root (code_body c)
    ++ [Bind_code id (code_lifted_out id c)].
Proof. destruct c. reflexivity. Qed.

Lemma code_lifted_out_parts (id : code_id) (c : code) :
  code_params (code_lifted_out id c) = code_params c
  ∧ code_my_closure (code_lifted_out id c) = code_my_closure c
  ∧ code_return_continuation (code_lifted_out id c)
    = code_return_continuation c
  ∧ code_exn_continuation (code_lifted_out id c) = code_exn_continuation c
  ∧ code_params_arity (code_lifted_out id c) = code_params_arity c
  ∧ code_result_arity (code_lifted_out id c) = code_result_arity c
  ∧ code_body (code_lifted_out id c)
    = lift_from_code K (lets_of K id) root (code_body c).
Proof. destruct c. repeat split; reflexivity. Qed.

(* The second static environment has the code of the first, rewritten;
   its symbols lifted; and, for the code that the first has, the
   symbols of the [Let]s lifted out of it. *)
Definition statics_lifted_out (statics statics' : static_env) : Prop :=
  (∀ id : code_id,
    lookup id (static_code statics')
    = option_map (code_lifted_out id) (lookup id (static_code statics)))
  ∧ symbols_lifted statics statics'
  ∧ ∀ (id : code_id) (c : code),
      lookup id (static_code statics) = Some c ->
      aliases_bound statics' (lets_of K id) root (code_body c).

Lemma symbols_lifted_extend (statics statics' statics'' : static_env) :
  symbols_lifted statics statics' ->
  statics_extend statics' statics'' ->
  symbols_lifted statics statics''.
Proof.
  intros Hsymbols Hextend s allocated Hs.
  destruct (Hsymbols s allocated Hs) as (allocated' & Hs' & Hallocated).
  exists allocated'.
  split; [ exact (proj2 Hextend s _ Hs') | ].
  exact (allocated_lifted_extend _ _ _ _ Hextend Hallocated).
Qed.

(* The second static environment may grow by symbols alone. *)
Lemma statics_lifted_out_extend (statics statics' statics'' : static_env) :
  statics_lifted_out statics statics' ->
  statics_extend statics' statics'' ->
  static_code statics'' = static_code statics' ->
  statics_lifted_out statics statics''.
Proof.
  intros (Hcode & Hsymbols & Haliases) Hextend Hcode'.
  split; [ intros id; rewrite Hcode'; apply Hcode | ].
  split; [ exact (symbols_lifted_extend _ _ _ Hsymbols Hextend) | ].
  intros id c Hid.
  exact (aliases_bound_extend _ _ Hextend _ _ _ (Haliases id c Hid)).
Qed.

(* A group that the first run evaluates, the second does, rewritten,
   given that it binds none of the symbols already. *)
Lemma eval_static_bindings_lifted_out (vars vars' : env) :
  ∀ (bindings : list static_binding) (statics statics' extended : static_env),
    env_lifted statics' vars vars' ->
    statics_lifted_out statics statics' ->
    distinct
      (flat_map symbols_of_binding
         (flat_map (binding_lift_from_code K) bindings))
    = true ->
    (∀ s : symbol,
      s
      ∈ flat_map symbols_of_binding
          (flat_map (binding_lift_from_code K) bindings) ->
      lookup s (static_values statics') = None) ->
    eval_static_bindings vars bindings statics = Some extended ->
    ∃ extended' : static_env,
      eval_static_bindings vars'
        (flat_map (binding_lift_from_code K) bindings) statics'
      = Some extended'
      ∧ statics_lifted_out extended extended'.
Proof.
  induction bindings as [ | binding bindings IH];
    intros statics statics' extended Hvars Hstatics Hdistinct Hfresh.
  - simpl. intros [= <-]. eauto.
  - destruct binding as [id c | id | sym const].
    + (* Code: the bindings of its [Let]s lifted out, then the code. *)
      cbn [flat_map] in Hdistinct, Hfresh |- *.
      rewrite binding_lift_from_code_code in Hdistinct, Hfresh |- *.
      rewrite <- app_assoc in Hdistinct, Hfresh |- *.
      rewrite flat_map_app in Hdistinct, Hfresh.
      cbn [app flat_map symbols_of_binding] in Hdistinct, Hfresh.
      destruct (distinct_app_parts _ _ Hdistinct)
        as (Hdistinct_out & Hdistinct_rest & Hapart).
      simpl.
      destruct (lookup id (static_code statics)) eqn:Hid; [ discriminate | ].
      intros Hbindings.
      destruct (eval_lifted_out_bindings vars' (lets_of K id) root
                  (code_body c) statics' Hdistinct_out)
        as (extended1 & Hextended1 & Hcode1 & Hbound);
        [ intros s Hin; apply Hfresh; apply in_or_app; left; exact Hin | ].
      pose proof (eval_static_bindings_extend vars' _ statics' extended1
        Hextended1) as Hextend1.
      assert (Hid' : lookup id (static_code extended1) = None)
        by (rewrite Hcode1, (proj1 Hstatics id), Hid; reflexivity).
      assert (Hextend2 :
        statics_extend extended1
          (Static_env
             ((id, code_lifted_out id c) :: static_code extended1)
             (static_values extended1))).
      { split; simpl; [ | auto ]. intros id0 c0 Hid0.
        exact (lookup_fresh id0 id c0 _ _ Hid' Hid0). }
      pose proof (statics_extend_trans _ _ _ Hextend1 Hextend2) as Hextend.
      rewrite eval_static_bindings_app, Hextended1.
      cbn [eval_static_bindings]. rewrite Hid'.
      apply
        (IH
           (Static_env ((id, c) :: static_code statics)
              (static_values statics))
           _ extended);
        [ exact (env_lifted_extend _ _ _ _ Hextend Hvars) |
        | exact Hdistinct_rest | | exact Hbindings ].
      * destruct Hstatics as (Hcode & Hsymbols & Haliases).
        split; [ | split ].
        -- intros id0. simpl. rewrite Hcode1.
           destruct (Pos.eqb_spec id0 id) as [-> | _];
             [ reflexivity | apply Hcode ].
        -- exact (symbols_lifted_extend _ _ _ Hsymbols Hextend).
        -- intros id0 c0. simpl.
           destruct (Pos.eqb_spec id0 id) as [-> | _].
           ++ intros [= <-].
              exact (aliases_bound_extend _ _ Hextend2 _ _ _ Hbound).
           ++ intros Hid0.
              exact (aliases_bound_extend _ _ Hextend _ _ _
                       (Haliases id0 c0 Hid0)).
      * intros s Hin. cbn [static_values].
        apply (eval_static_bindings_fresh vars' _ statics' extended1 s
                 Hextended1);
          [ apply Hfresh; apply in_or_app; right; exact Hin | ].
        intros Hin'. exact (Hapart s Hin' Hin).
    + (* Deleted code. *)
      exact (IH statics statics' extended Hvars Hstatics Hdistinct Hfresh).
    + (* A symbol: not bound in the second run either. *)
      simpl in Hdistinct, Hfresh |- *.
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
      * destruct Hstatics as (Hcode & Hsymbols & Haliases).
        split; [ exact Hcode | split ].
        -- intros s a. cbn [static_values]. rewrite lookup_cons.
           destruct (Pos.eqb_spec s sym) as [-> | Hother].
           ++ intros [= <-]. exists allocated'.
              split; [ apply lookup_head | ].
              exact (allocated_lifted_extend _ _ _ _ Hextend Hallocated).
           ++ intros Hs. destruct (Hsymbols s a Hs) as (a' & Hs' & Ha).
              exists a'. split; [ rewrite lookup_other; assumption | ].
              exact (allocated_lifted_extend _ _ _ _ Hextend Ha).
        -- intros id c Hid.
           exact (aliases_bound_extend _ _ Hextend _ _ _ (Haliases id c Hid)).
      * intros s Hin. cbn [static_values].
        rewrite lookup_other; [ apply Hfresh; right; exact Hin | ].
        intros ->. apply negb_true_iff in Hnotin.
        apply (proj2 (among_In _ _)) in Hin.
        exact (eq_true_false_abs _ Hin Hnotin).
Qed.

(* ======================================================================== *)
(* Continuations and states                                                 *)
(* ======================================================================== *)

(* A continuation of the first run and one of the second: the same way
   out, or closures of a handler and of that handler rewritten, with
   lifted environments, the symbols of the [Let]s lifted out of the
   handler being bound; or what is left of the same over-application.
   The handlers of a recursive group bind nothing statically, and are
   the same in both. *)
#[local] Set Warnings "-register-all".
Inductive cont_lifted_out (statics' : static_env)
    : cont_value -> cont_value -> Prop :=
  | Outer_lifted_out (k : continuation) :
    cont_lifted_out statics' (Outer k) (Outer k)
  | Closure_lifted_out (lets : list (path * lift_to)) (at_path : path)
      (h : continuation_handler) (vars vars' : env) (conts conts' : cont_env)
      (recursive : list (continuation * continuation_handler)) :
    env_lifted statics' vars vars' ->
    Forall2
      (fun kc kc' =>
         fst kc = fst kc' ∧ cont_lifted_out statics' (snd kc) (snd kc'))
      conts conts' ->
    handler_aliases_bound statics' lets at_path h ->
    handlers_bind_statics recursive = false ->
    cont_lifted_out statics' (Closure h vars conts recursive)
      (Closure (handler_lift_from_code K lets at_path h) vars' conts'
         recursive)
  | Extra_args_lifted_out (c c' : cont_value) (extra extra' : list value) :
    cont_lifted_out statics' c c' ->
    Forall2 (value_lifted statics') extra extra' ->
    cont_lifted_out statics' (Extra_args c extra) (Extra_args c' extra')
  | Over_application_lifted_out (remaining remaining' : list value)
      (remaining_arity return_arity : arity)
      (return_to return_to' exn_to exn_to' : cont_value) :
    Forall2 (value_lifted statics') remaining remaining' ->
    cont_lifted_out statics' return_to return_to' ->
    cont_lifted_out statics' exn_to exn_to' ->
    cont_lifted_out statics'
      (Over_application remaining remaining_arity return_arity return_to
         exn_to)
      (Over_application remaining' remaining_arity return_arity return_to'
         exn_to').

Definition conts_lifted_out (statics' : static_env)
    (conts conts' : cont_env) : Prop :=
  Forall2
    (fun kc kc' =>
       fst kc = fst kc' ∧ cont_lifted_out statics' (snd kc) (snd kc'))
    conts conts'.

Fixpoint cont_lifted_out_extend (statics' statics'' : static_env)
    (Hextend : statics_extend statics' statics'') (c c' : cont_value)
    (H : cont_lifted_out statics' c c') {struct H} :
  cont_lifted_out statics'' c c'.
Proof.
  destruct H
    as [ k
       | lets at_path h vars vars' conts conts' recursive Hvars Hconts Hbound
           Hrecursive
       | c0 c0' extra extra' Hc0 Hextra
       | remaining remaining' remaining_arity return_arity return_to
           return_to' exn_to exn_to' Hremaining Hreturn Hexn ].
  - apply Outer_lifted_out.
  - apply Closure_lifted_out;
      [ exact (env_lifted_extend _ _ _ _ Hextend Hvars) |
      | exact (handler_aliases_bound_extend _ _ Hextend _ _ h Hbound)
      | exact Hrecursive ].
    clear Hvars. revert conts conts' Hconts. fix IH 3.
    intros conts conts' [ | kc kc' rest rest' [Hkey Hhead] Htail];
      constructor;
      [ split;
        [ exact Hkey | exact (cont_lifted_out_extend _ _ Hextend _ _ Hhead) ]
      | exact (IH _ _ Htail) ].
  - apply Extra_args_lifted_out;
      [ exact (cont_lifted_out_extend _ _ Hextend _ _ Hc0)
      | exact (values_lifted_extend _ _ _ _ Hextend Hextra) ].
  - apply Over_application_lifted_out;
      [ exact (values_lifted_extend _ _ _ _ Hextend Hremaining)
      | exact (cont_lifted_out_extend _ _ Hextend _ _ Hreturn)
      | exact (cont_lifted_out_extend _ _ Hextend _ _ Hexn) ].
Qed.

Lemma with_extra_args_lifted_out (statics' : static_env)
    (c c' : cont_value) (extra extra' : list value) :
  cont_lifted_out statics' c c' ->
  Forall2 (value_lifted statics') extra extra' ->
  cont_lifted_out statics' (with_extra_args c extra)
    (with_extra_args c' extra').
Proof.
  intros Hc Hextra.
  destruct Hextra as [ | v v' extra extra' Hv Hextra]; [ exact Hc | ].
  apply Extra_args_lifted_out; [ exact Hc | constructor; assumption ].
Qed.

Lemma conts_lifted_out_extend (statics' statics'' : static_env)
    (conts conts' : cont_env) :
  statics_extend statics' statics'' ->
  conts_lifted_out statics' conts conts' ->
  conts_lifted_out statics'' conts conts'.
Proof.
  intros Hextend.
  induction 1 as [ | kc kc' conts conts' [Hkey Hc] _ IH]; constructor;
    [ split; [ exact Hkey | exact (cont_lifted_out_extend _ _ Hextend _ _ Hc) ]
    | exact IH ].
Qed.

Lemma resolve_lifted_out (statics' : static_env) (k : continuation)
    (conts conts' : cont_env) :
  conts_lifted_out statics' conts conts' ->
  cont_lifted_out statics' (resolve k conts) (resolve k conts').
Proof.
  unfold resolve.
  induction 1 as [ | [k1 c] [k1' c'] conts conts' [Hk Hc] _ IH]; simpl;
    [ apply Outer_lifted_out | ].
  simpl in Hk. subst k1'. destruct (Pos.eqb k k1); [ exact Hc | exact IH ].
Qed.

(* [all] is the whole group, kept apart from the handlers still to be gone
   through. *)
Lemma rec_closures_lifted_out_aux (statics' : static_env) (vars vars' : env)
    (conts conts' : cont_env)
    (all handlers : list (continuation * continuation_handler)) :
  env_lifted statics' vars vars' ->
  conts_lifted_out statics' conts conts' ->
  handlers_bind_statics all = false ->
  handlers_bind_statics handlers = false ->
  conts_lifted_out statics'
    (map (fun '(k, h) => (k, Closure h vars conts all)) handlers)
    (map (fun '(k, h) => (k, Closure h vars' conts' all)) handlers).
Proof.
  intros Hvars Hconts Hall.
  induction handlers as [ | [k h] handlers IH]; simpl; intros Hbinds;
    constructor.
  - apply orb_false_iff in Hbinds as [Hh _].
    split; [ reflexivity | ]. simpl.
    pose proof (Closure_lifted_out statics' [] root h vars vars' conts conts'
      all Hvars Hconts (handler_aliases_bound_nil statics' root h) Hall)
      as Hclosure.
    rewrite (handler_lift_from_code_nil K root h Hh) in Hclosure.
    exact Hclosure.
  - apply orb_false_iff in Hbinds as [_ Hhandlers]. exact (IH Hhandlers).
Qed.

Lemma rec_closures_lifted_out (statics' : static_env) (vars vars' : env)
    (conts conts' : cont_env)
    (handlers : list (continuation * continuation_handler)) :
  env_lifted statics' vars vars' ->
  conts_lifted_out statics' conts conts' ->
  handlers_bind_statics handlers = false ->
  conts_lifted_out statics' (rec_closures handlers vars conts ++ conts)
    (rec_closures handlers vars' conts' ++ conts').
Proof.
  intros Hvars Hconts Hbinds. apply Forall2_app; [ | exact Hconts ].
  apply rec_closures_lifted_out_aux; assumption.
Qed.

(* The first state and the second: the second expression is the first
   rewritten, the environments are lifted, and the symbols of the
   [Let]s lifted out of the expression are bound. *)
Inductive state_lifted_out : state -> state -> Prop :=
  | State_lifted_out (lets : list (path * lift_to)) (at_path : path)
      (e : expr) (vars vars' : env) (conts conts' : cont_env)
      (statics statics' : static_env) :
    env_lifted statics' vars vars' ->
    conts_lifted_out statics' conts conts' ->
    statics_lifted_out statics statics' ->
    aliases_bound statics' lets at_path e ->
    state_lifted_out (State e vars conts statics)
      (State (lift_from_code K lets at_path e) vars' conts' statics').

(* The values at an exit are lifted, under the static environment that
   the second run has reached. *)
Definition exit_lifted_out (last : state) (vs vs' : list value) : Prop :=
  Forall2 (value_lifted (state_statics last)) vs vs'.

(* What the second run answers to a result of the first: nothing is
   asked if the first is undefined; an exit is answered by an exit
   through the same continuation, with values lifted; a step, by a
   step, to a state related. *)
Definition result_lifted_out (statics' : static_env)
    (result result' : step_result) : Prop :=
  match result with
  | Undefined => True
  | Exit k exit_vs =>
    ∃ exit_vs' : list value,
      result' = Exit k exit_vs'
      ∧ Forall2 (value_lifted statics') exit_vs exit_vs'
  | Step t => ∃ t' : state, result' = Step t' ∧ state_lifted_out t t'
  end.

(* ======================================================================== *)
(* Calls                                                                    *)
(* ======================================================================== *)

(* Two calls of one shape: the closures called, the arguments and those
   that remain are lifted, and the code of the second is that of the
   first rewritten, with the symbols of its [Let]s lifted out bound. *)
Inductive shape_lifted_out (statics' : static_env)
    : call_shape -> call_shape -> Prop :=
  | Full_call_lifted_out (closure closure' : value) (called : code_id)
      (c : code) (vs vs' : list value) (args_arity : arity) :
    value_lifted statics' closure closure' ->
    Forall2 (value_lifted statics') vs vs' ->
    aliases_bound statics' (lets_of K called) root (code_body c) ->
    shape_lifted_out statics' (Full_call closure c vs args_arity)
      (Full_call closure' (code_lifted_out called c) vs' args_arity)
  | Over_call_lifted_out (closure closure' : value) (called : code_id)
      (c : code) (vs vs' remaining remaining' : list value)
      (args_arity remaining_arity : arity) :
    value_lifted statics' closure closure' ->
    Forall2 (value_lifted statics') vs vs' ->
    Forall2 (value_lifted statics') remaining remaining' ->
    aliases_bound statics' (lets_of K called) root (code_body c) ->
    shape_lifted_out statics'
      (Over_call closure c vs remaining args_arity remaining_arity)
      (Over_call closure' (code_lifted_out called c) vs' remaining'
         args_arity remaining_arity)
  | Partial_call_lifted_out (partial partial' : value) :
    value_lifted statics' partial partial' ->
    shape_lifted_out statics' (Partial_call partial) (Partial_call partial').

(* What the call of a closure is in the first run, the call of the
   closure lifted is in the second. *)
Lemma shape_of_closure_call_lifted_out (statics statics' : static_env)
    (closure closure' : value) (kind : call_kind) (vs vs' : list value)
    (args_arity return_arity : arity) (shape : call_shape) :
  statics_lifted_out statics statics' ->
  value_lifted statics' closure closure' ->
  Forall2 (value_lifted statics') vs vs' ->
  shape_of_closure_call statics closure kind vs args_arity return_arity
  = Some shape ->
  ∃ shape' : call_shape,
    shape_of_closure_call statics' closure' kind vs' args_arity return_arity
    = Some shape'
    ∧ shape_lifted_out statics' shape shape'.
Proof.
  intros (Hcode & Hsymbols & Haliases) Hclosure Hvs.
  unfold shape_of_closure_call.
  destruct (closure_of statics closure) as [[called slots] | ] eqn:Hc;
    [ | discriminate ].
  destruct (closure_of_lifted statics statics' Hsymbols closure closure'
              called slots Hclosure Hc)
    as (slots' & Hc' & _).
  rewrite Hc'.
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | discriminate ].
  rewrite (Hcode called).
  destruct (lookup called (static_code statics)) as [c | ] eqn:Hcalled;
    [ | discriminate ].
  simpl option_map. cbv iota zeta.
  destruct (code_lifted_out_parts called c)
    as (_ & _ & _ & _ & Hparams_arity & Hresult_arity & _).
  assert (Htupled :
    code_is_tupled (code_lifted_out called c) = code_is_tupled c)
    by (destruct c; reflexivity).
  destruct (arguments_for_code statics c vs args_arity)
    as [[ws taken_arity] | ] eqn:Hargs; [ | discriminate ].
  destruct
    (arguments_for_code_related (value_lifted statics') statics statics' c
       (code_lifted_out called c) vs vs' args_arity ws taken_arity
       (value_lifted_respects statics statics' Hsymbols) Htupled
       Hparams_arity Hvs (kinds_of_values_lifted statics' vs vs' Hvs) Hargs)
    as (ws' & -> & Hws).
  simpl. unfold shape_of_code_call. cbv zeta.
  rewrite Hparams_arity, Hresult_arity, Htupled,
    (kinds_of_values_lifted statics' ws ws' Hws).
  pose proof (Haliases called c Hcalled) as Hbound.
  clear Hargs Hvs vs vs'. rename ws into vs, ws' into vs', Hws into Hvs.
  rename args_arity into call_arity, taken_arity into args_arity.
  destruct (Nat.eqb (length args_arity) (length (code_params_arity c))).
  - intros [= <-]. eexists. split; [ reflexivity | ].
    apply Full_call_lifted_out; assumption.
  - destruct
      (negb
         (kinds_eqb (map kind_of_value vs) (unarize args_arity)
          && partial_or_over_application args_arity return_arity
               (code_params_arity c) (code_result_arity c)));
      [ discriminate | ].
    destruct
      (Forall2_firstn_skipn (value_lifted statics')
         (cardinal_unarized (code_params_arity c)) vs vs' Hvs)
      as [Hfirst Hrest].
    destruct (Nat.ltb (length (code_params_arity c)) (length args_arity));
      [ intros [= <-]; eexists; (split; [ reflexivity | ]);
        apply Over_call_lifted_out; assumption
      | ].
    destruct (code_is_tupled c); [ discriminate | ].
    intros [= <-]. eexists. split; [ reflexivity | ].
    apply Partial_call_lifted_out, Lifted_partial_application; assumption.
Qed.

(* The same of a call: the closure that a partial application keeps is
   lifted with it. *)
Lemma shape_of_call_lifted_out (statics statics' : static_env)
    (callee callee' : value) (kind : call_kind) (vs vs' : list value)
    (args_arity return_arity : arity) (shape : call_shape) :
  statics_lifted_out statics statics' ->
  value_lifted statics' callee callee' ->
  Forall2 (value_lifted statics') vs vs' ->
  shape_of_call statics callee kind vs args_arity return_arity = Some shape ->
  ∃ shape' : call_shape,
    shape_of_call statics' callee' kind vs' args_arity return_arity
    = Some shape'
    ∧ shape_lifted_out statics' shape shape'.
Proof.
  intros Hstatics Hcallee Hvs. unfold shape_of_call.
  destruct kind as [named | ];
    [ apply shape_of_closure_call_lifted_out; assumption | ].
  pose proof (partial_application_lifted statics' callee callee' Hcallee)
    as Hpartial.
  destruct (partial_application_of callee)
    as [[[closure applied] applied_arity] | ].
  - destruct Hpartial as (closure' & applied' & -> & Hclosure & Happlied).
    simpl.
    destruct args_arity as [ | component args_arity]; [ discriminate | ].
    rewrite (kinds_of_values_lifted statics' vs vs' Hvs).
    destruct (kinds_eqb _ _); [ | discriminate ].
    apply shape_of_closure_call_lifted_out;
      [ exact Hstatics | exact Hclosure | apply Forall2_app; assumption ].
  - rewrite Hpartial. apply shape_of_closure_call_lifted_out; assumption.
Qed.

(* A full call. *)
Lemma call_code_lifted_out (closure closure' : value) (called : code_id)
    (c : code) (vs vs' : list value) (args_arity return_arity : arity)
    (return_to return_to' exn_to exn_to' : cont_value)
    (statics statics' : static_env) :
  value_lifted statics' closure closure' ->
  Forall2 (value_lifted statics') vs vs' ->
  aliases_bound statics' (lets_of K called) root (code_body c) ->
  cont_lifted_out statics' return_to return_to' ->
  cont_lifted_out statics' exn_to exn_to' ->
  statics_lifted_out statics statics' ->
  result_lifted_out statics'
    (call_code closure c vs args_arity return_arity return_to exn_to statics)
    (call_code closure' (code_lifted_out called c) vs' args_arity
       return_arity return_to' exn_to' statics').
Proof.
  intros Hclosure Hvs Hbound Hreturn Hexn Hstatics.
  unfold result_lifted_out, call_code.
  destruct (code_lifted_out_parts called c)
    as (Hparams & Hmy_closure & Hret & Hexn_k & Hparams_arity
        & Hresult_arity & Hbody).
  rewrite Hparams, Hmy_closure, Hret, Hexn_k, Hparams_arity, Hresult_arity,
    Hbody, lift_from_code_binds_statics,
    (kinds_of_values_lifted statics' vs vs' Hvs).
  destruct (binds_statics (code_body c)); [ exact I | ].
  destruct
    (negb
       (kinds_eqb (map kind_of_value vs) (unarize args_arity)
        && kinds_per_parameter_eqb (unarize_per_parameter args_arity)
             (unarize_per_parameter (code_params_arity c))
        && arity_eqb return_arity (code_result_arity c)));
    [ exact I | ].
  destruct (bind_params (code_params c) vs [(code_my_closure c, closure)])
    as [bound | ] eqn:Hbind;
    [ | exact I ].
  destruct (bind_params_lifted statics' (code_params c) vs vs'
              [(code_my_closure c, closure)] [(code_my_closure c, closure')]
              bound Hvs)
    as (bound' & Hbind' & Hbound_vars);
    [ apply env_lifted_cons; [ exact Hclosure | intros x v [=] ]
    | exact Hbind | ].
  rewrite Hbind'. eexists. split; [ reflexivity | ].
  apply State_lifted_out;
    [ exact Hbound_vars | | exact Hstatics | exact Hbound ].
  constructor; [ split; [ reflexivity | exact Hreturn ] | ].
  constructor; [ split; [ reflexivity | exact Hexn ] | ].
  constructor.
Qed.

(* A call of a given shape, given what the two runs do with a partial
   application. The full call inside an over-application returns to
   what is left of it. *)
Lemma run_call_lifted_out
    (return_partial return_partial' : value -> step_result)
    (shape shape' : call_shape) (return_arity : arity)
    (return_to return_to' exn_to exn_to' : cont_value)
    (statics statics' : static_env) :
  shape_lifted_out statics' shape shape' ->
  cont_lifted_out statics' return_to return_to' ->
  cont_lifted_out statics' exn_to exn_to' ->
  statics_lifted_out statics statics' ->
  (∀ partial partial' : value,
    value_lifted statics' partial partial' ->
    result_lifted_out statics' (return_partial partial)
      (return_partial' partial')) ->
  result_lifted_out statics'
    (run_call return_partial (Some shape) return_arity return_to exn_to
       statics)
    (run_call return_partial' (Some shape') return_arity return_to' exn_to'
       statics').
Proof.
  intros Hshape Hreturn Hexn Hstatics Hpartial.
  destruct Hshape
    as [ closure closure' called c vs vs' args_arity Hclosure Hvs Hbound
       | closure closure' called c vs vs' remaining remaining' args_arity
           remaining_arity Hclosure Hvs Hremaining Hbound
       | partial partial' Hp ];
    simpl.
  - apply call_code_lifted_out; assumption.
  - destruct (code_lifted_out_parts called c)
      as (_ & _ & _ & _ & _ & -> & _).
    apply call_code_lifted_out; try assumption.
    apply Over_application_lifted_out; assumption.
  - exact (Hpartial partial partial' Hp).
Qed.

(* A call, given what the two runs do when the return continuation is
   applied to a partial application. *)
Lemma call_function_lifted_out_from (callee callee' : value)
    (kind : call_kind) (vs vs' : list value) (args_arity return_arity : arity)
    (return_to return_to' exn_to exn_to' : cont_value)
    (statics statics' : static_env) :
  value_lifted statics' callee callee' ->
  Forall2 (value_lifted statics') vs vs' ->
  cont_lifted_out statics' return_to return_to' ->
  cont_lifted_out statics' exn_to exn_to' ->
  statics_lifted_out statics statics' ->
  (∀ partial partial' : value,
    value_lifted statics' partial partial' ->
    result_lifted_out statics' (apply_cont_value return_to [partial] statics)
      (apply_cont_value return_to' [partial'] statics')) ->
  result_lifted_out statics'
    (call_function callee kind vs args_arity return_arity return_to exn_to
       statics)
    (call_function callee' kind vs' args_arity return_arity return_to'
       exn_to' statics').
Proof.
  intros Hcallee Hvs Hreturn Hexn Hstatics Hpartial.
  unfold call_function.
  destruct (shape_of_call statics callee kind vs args_arity return_arity)
    as [shape | ] eqn:Hshape;
    [ | exact I ].
  destruct (shape_of_call_lifted_out statics statics' callee callee' kind vs
              vs' args_arity return_arity shape Hstatics Hcallee Hvs Hshape)
    as (shape' & -> & Hshapes).
  exact (run_call_lifted_out _ _ shape shape' return_arity _ _ _ _ statics
           statics' Hshapes Hreturn Hexn Hstatics Hpartial).
Qed.

(* Applying a continuation. *)
Lemma apply_cont_value_lifted_out (statics' : static_env)
    (c c' : cont_value) :
  cont_lifted_out statics' c c' ->
  ∀ (vs vs' : list value) (statics : static_env),
    Forall2 (value_lifted statics') vs vs' ->
    statics_lifted_out statics statics' ->
    result_lifted_out statics' (apply_cont_value c vs statics)
      (apply_cont_value c' vs' statics').
Proof.
  induction 1
    as [ k
       | lets at_path [params metadata handler] vars vars' conts conts'
           recursive Hvars Hconts Hbound Hrecursive
       | c c' extra extra' Hc IH Hextra
       | remaining remaining' remaining_arity return_arity return_to
           return_to' exn_to exn_to' Hremaining Hreturn IHreturn Hexn _ ];
    intros vs vs' statics Hvs Hstatics.
  - simpl. exists vs'. split; [ reflexivity | exact Hvs ].
  - simpl. rewrite (kinds_of_values_lifted statics' vs vs' Hvs).
    destruct (kinds_eqb (map kind_of_value vs) (hm_params_kinds metadata));
      [ | exact I ].
    destruct (bind_params params vs vars) as [bound | ] eqn:Hbind;
      [ | exact I ].
    destruct (bind_params_lifted statics' params vs vs' vars vars' bound Hvs
                Hvars Hbind)
      as (bound' & -> & Hbound_vars).
    eexists. split; [ reflexivity | ].
    apply State_lifted_out;
      [ exact Hbound_vars | apply rec_closures_lifted_out; assumption
      | exact Hstatics | exact Hbound ].
  - simpl. apply IH; [ apply Forall2_app; assumption | exact Hstatics ].
  - rewrite !apply_cont_value_over_application.
    destruct Hvs as [ | v v' vs vs' Hv Hvs]; [ exact I | ].
    destruct Hvs as [ | w w' vs vs' Hw Hvs]; [ | exact I ].
    apply call_function_lifted_out_from; try assumption.
    intros partial partial' Hpartial.
    apply IHreturn;
      [ constructor; [ exact Hpartial | constructor ] | exact Hstatics ].
Qed.

(* A call. *)
Lemma call_function_lifted_out (callee callee' : value) (kind : call_kind)
    (vs vs' : list value) (args_arity return_arity : arity)
    (return_to return_to' exn_to exn_to' : cont_value)
    (statics statics' : static_env) :
  value_lifted statics' callee callee' ->
  Forall2 (value_lifted statics') vs vs' ->
  cont_lifted_out statics' return_to return_to' ->
  cont_lifted_out statics' exn_to exn_to' ->
  statics_lifted_out statics statics' ->
  result_lifted_out statics'
    (call_function callee kind vs args_arity return_arity return_to exn_to
       statics)
    (call_function callee' kind vs' args_arity return_arity return_to'
       exn_to' statics').
Proof.
  intros Hcallee Hvs Hreturn Hexn Hstatics.
  apply call_function_lifted_out_from; try assumption.
  intros partial partial' Hpartial.
  apply (apply_cont_value_lifted_out statics' return_to return_to' Hreturn);
    [ constructor; [ exact Hpartial | constructor ] | exact Hstatics ].
Qed.

(* ======================================================================== *)
(* One step                                                                 *)
(* ======================================================================== *)

Lemma result_lifted_out_answered (s' : state) (result : step_result) :
  result_lifted_out (state_statics s') result (step s') ->
  answered state_lifted_out exit_lifted_out result s'.
Proof.
  destruct result as [t | k vs | ]; unfold answered; simpl;
    [ | exact (fun H => H) | exact (fun H => H) ].
  intros (t' & Hstep & Ht). exists 0, t'.
  split; [ rewrite Hstep; reflexivity | exact Ht ].
Qed.

(* A step of the first state is answered by a step of the second, which
   is the state of a run that never binds a static name twice. *)
Lemma lifted_out_step (s s' : state) :
  state_lifted_out s s' ->
  static_fault s' = false ->
  answered state_lifted_out exit_lifted_out (step s) s'.
Proof.
  intros [lets at_path e vars vars' conts conts' statics statics' Hvars
            Hconts Hstatics Hbound] Hfault.
  destruct e
    as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ].
  - (* Let *)
    rewrite step_let.
    destruct (eval_named statics vars d) as [v | ] eqn:Hd; [ | exact I ].
    destruct (kind_eqb (kind_of_value v) xkind) eqn:Hkind; [ | exact I ].
    cbn [lift_from_code aliases_bound] in Hbound |- *.
    destruct Hbound as [Hbound_d Hbound_body].
    destruct (lifted_out lets at_path d) as [[bindings s0] | ].
    + (* Lifted out: the symbol is bound to what the [Let] makes. *)
      pose proof (Hbound_d statics vars v Hd) as Hv.
      exists 0, (State (lift_from_code K lets (xO at_path) body)
                   ((x, Value_symbol s0) :: vars') conts' statics').
      split.
      * simpl. rewrite step_let. cbn [eval_named eval_simple].
        rewrite (kind_of_value_lifted _ _ _ Hv), Hkind. reflexivity.
      * apply State_lifted_out;
          [ apply env_lifted_cons; assumption | exact Hconts | exact Hstatics
          | exact Hbound_body ].
    + destruct (eval_named_lifted statics statics' vars vars' d v
                  (proj1 (proj2 Hstatics)) Hvars Hd)
        as (v' & Hd' & Hv).
      exists 0, (State (lift_from_code K lets (xO at_path) body)
                   ((x, v') :: vars') conts' statics').
      split.
      * simpl.
        rewrite step_let, Hd', (kind_of_value_lifted statics' v v' Hv), Hkind.
        reflexivity.
      * apply State_lifted_out;
          [ apply env_lifted_cons; assumption | exact Hconts | exact Hstatics
          | exact Hbound_body ].
  - (* Let_static *)
    cbn [lift_from_code aliases_bound] in Hbound, Hfault |- *.
    rewrite step_let_static.
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hbindings;
      [ | exact I ].
    unfold static_fault in Hfault. simpl_state.
    apply orb_false_iff in Hfault as [_ Hfault].
    destruct (no_rebinding statics' _ Hfault) as [Hdistinct Hfresh].
    destruct (eval_static_bindings_lifted_out vars vars' bindings statics
                statics' extended Hvars Hstatics Hdistinct Hfresh Hbindings)
      as (extended' & Hextended & Hlifted).
    pose proof (eval_static_bindings_extend vars' _ statics' extended'
      Hextended) as Hextend.
    exists 0, (State (lift_from_code K lets (xO at_path) body) vars' conts'
                 extended').
    split; [ simpl; rewrite step_let_static, Hextended; reflexivity | ].
    apply State_lifted_out;
      [ exact (env_lifted_extend _ _ _ _ Hextend Hvars)
      | exact (conts_lifted_out_extend _ _ _ _ Hextend Hconts) | exact Hlifted
      | exact (aliases_bound_extend _ _ Hextend _ _ _ Hbound) ].
  - (* Let_cont_non_recursive *)
    cbn [lift_from_code aliases_bound] in Hbound |- *.
    destruct Hbound as [Hbound_h Hbound_body].
    rewrite step_let_cont_non_recursive.
    eexists 0, _.
    split; [ simpl; rewrite step_let_cont_non_recursive; reflexivity | ].
    apply State_lifted_out;
      [ exact Hvars | | exact Hstatics | exact Hbound_body ].
    constructor; [ | exact Hconts ].
    split; [ reflexivity | ].
    exact (Closure_lifted_out statics' lets (xI at_path) h vars vars' conts
             conts' [] Hvars Hconts Hbound_h eq_refl).
  - (* Let_cont_recursive *)
    cbn [lift_from_code aliases_bound] in Hbound |- *.
    rewrite step_let_cont_recursive.
    destruct (handlers_bind_statics handlers) eqn:Hbinds; [ exact I | ].
    eexists 0, _.
    split;
      [ simpl; rewrite step_let_cont_recursive, Hbinds; reflexivity | ].
    apply State_lifted_out; [ exact Hvars | | exact Hstatics | exact Hbound ].
    apply rec_closures_lifted_out; assumption.
  - (* Apply *)
    cbn [lift_from_code]. rewrite step_apply.
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
    apply result_lifted_out_answered. simpl state_statics.
    rewrite step_apply, Hcallee', Hargs', Hextra'.
    apply call_function_lifted_out; try assumption.
    + exact (resolve_lifted_out statics' _ conts conts' Hconts).
    + exact (with_extra_args_lifted_out statics' _ _ extra extra'
               (resolve_lifted_out statics' _ conts conts' Hconts) Hextras).
  - (* Apply_cont *)
    cbn [lift_from_code]. rewrite step_apply_cont.
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hargs;
      [ | exact I ].
    destruct (eval_simples_lifted statics' vars vars' _ Hvars vs Hargs)
      as (vs' & Hargs' & Hvs).
    apply result_lifted_out_answered. simpl state_statics.
    rewrite step_apply_cont, Hargs'. unfold apply_continuation.
    apply (apply_cont_value_lifted_out statics' _ _
             (resolve_lifted_out statics' _ conts conts' Hconts));
      [ exact Hvs | exact Hstatics ].
  - (* Switch *)
    cbn [lift_from_code]. rewrite step_switch.
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
    + exact (State_lifted_out lets at_path (Apply_cont ac) vars vars' conts
               conts' statics statics' Hvars Hconts Hstatics I).
  - (* Invalid *)
    rewrite step_invalid. exact I.
Qed.

(* ======================================================================== *)
(* The run of the unit rewritten                                            *)
(* ======================================================================== *)

Section Unit.

Variable u : unit_interface.
Variable e : expr.

Hypothesis Hwf : well_formed_unit u (lift_from_code K [] root e) = true.

(* The second state is one that the run of the unit rewritten reaches. *)
Definition reached_lifted_out (s' : state) : Prop :=
  ∃ n : nat,
    run n (State (lift_from_code K [] root e) [] [] empty_static_env)
    = Step s'.

(* The states are related, the second is reached, and the first is one
   of a unit that exits with symbols and constants only. *)
Definition unit_lifted_out (s s' : state) : Prop :=
  state_lifted_out s s' ∧ reached_lifted_out s' ∧ plain_state s.

(* The values at an exit are lifted, and are constants and symbols: they
   are the same. *)
Lemma unit_lifted_out_step (s s' : state) :
  unit_lifted_out s s' ->
  answered unit_lifted_out (fun _ vs vs' => vs' = vs) (step s) s'.
Proof.
  intros (Hlifted & [n Hn] & Hplain).
  pose proof (lifted_out_step s s' Hlifted
    (well_formed_never_faults u _ n s' Hwf Hn)) as Hanswer.
  pose proof (plain_step s Hplain) as Hstep.
  destruct (step s) as [t | k vs | ]; unfold answered in *; [ | | exact I ].
  - destruct Hanswer as (m & t' & Hrun & Ht).
    exists m, t'. split; [ exact Hrun | ].
    split; [ exact Ht | ]. split; [ | exact Hstep ].
    exists (n + S m). rewrite run_add, Hn. exact Hrun.
  - destruct Hanswer as (vs' & Hexit & Hvs).
    exists vs'. split; [ exact Hexit | ].
    exact (plain_values_lifted _ vs vs' Hstep Hvs).
Qed.

Lemma unit_lifted_out_initial :
  exits_plain [] e = true ->
  unit_lifted_out (State e [] [] empty_static_env)
    (State (lift_from_code K [] root e) [] [] empty_static_env).
Proof.
  intros Hplain.
  split;
    [ | split; [ exists 0; reflexivity | exact (plain_initial e Hplain) ] ].
  apply State_lifted_out;
    [ intros x v [=] | constructor | | apply aliases_bound_nil ].
  split; [ intros id; reflexivity | ].
  split; [ intros s a [=] | intros id c [=] ].
Qed.

End Unit.

End From_code.

Theorem lift_from_code_unit_program_refines :
  lift_from_code_unit_program_refines_statement.
Proof.
  intros u K e e'. unfold lift_from_code_unit. cbv zeta.
  destruct (exits_plain [] e) eqn:Hplain; [ | discriminate ].
  destruct (well_formed_unit u (lift_from_code K [] root e)) eqn:Hwf;
    [ | discriminate ].
  intros [= <-]. unfold program_refines.
  apply
    (stuttering_refines (unit_lifted_out K e) (fun _ vs vs' => vs' = vs)
       (unit_lifted_out_step K u e Hwf)).
  - intros last vs vs' Hsame. exact Hsame.
  - exact (unit_lifted_out_initial K e Hplain).
Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

Lemma rename_plain_simple (r : renaming) (s : simple) :
  plain_simple s = true -> rename_simple r s = s.
Proof. destruct s as [x | sym | c]; [ discriminate | | ]; reflexivity. Qed.

Lemma plain_simple_renamed (r : renaming) (s : simple) :
  plain_simple (rename_simple r s) = plain_simple s.
Proof. destruct s as [x | sym | c]; reflexivity. Qed.

Lemma rename_plain_simples (r : renaming) (args : list simple) :
  forallb plain_simple args = true -> map (rename_simple r) args = args.
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  intros Hplain. apply andb_true_iff in Hplain as [Hs Hargs].
  rewrite (rename_plain_simple r s Hs), (IH Hargs). reflexivity.
Qed.

Lemma plain_simples_renamed (r : renaming) (args : list simple) :
  forallb plain_simple (map (rename_simple r) args)
  = forallb plain_simple args.
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite plain_simple_renamed, IH. reflexivity.
Qed.

Lemma rename_plain_slots (r : renaming) (slots : list (value_slot * simple)) :
  forallb (fun slot => plain_simple (snd slot)) slots = true ->
  map (fun slot => (fst slot, rename_simple r (snd slot))) slots = slots.
Proof.
  induction slots as [ | [slot s] slots IH]; simpl; [ reflexivity | ].
  intros Hplain. apply andb_true_iff in Hplain as [Hs Hslots].
  rewrite (rename_plain_simple r s Hs), (IH Hslots). reflexivity.
Qed.

Lemma plain_slots_renamed (r : renaming)
    (slots : list (value_slot * simple)) :
  forallb (fun slot => plain_simple (snd slot))
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = forallb (fun slot => plain_simple (snd slot)) slots.
Proof.
  induction slots as [ | [slot s] slots IH]; simpl; [ reflexivity | ].
  rewrite plain_simple_renamed, IH. reflexivity.
Qed.

(* A defining expression that mentions no variable is not changed by a
   renaming, and renaming does not make one. *)
Lemma rename_closed_named (r : renaming) (d : named) :
  closed_named d = true -> rename_named r d = d.
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    simpl; try discriminate; intros Hclosed.
  - rewrite (rename_plain_simples r args Hclosed). reflexivity.
  - rewrite (rename_plain_slots r slots Hclosed). reflexivity.
  - rewrite (rename_plain_slots r slots Hclosed). reflexivity.
Qed.

Lemma closed_named_renamed (r : renaming) (d : named) :
  closed_named (rename_named r d) = closed_named d.
Proof.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    simpl; try reflexivity.
  - apply plain_simples_renamed.
  - apply plain_slots_renamed.
  - apply plain_slots_renamed.
Qed.

Lemma lifted_out_renamed (r : renaming) (lets : list (path * lift_to))
    (at_path : path) (d : named) :
  lifted_out lets at_path (rename_named r d) = lifted_out lets at_path d.
Proof.
  unfold lifted_out.
  destruct (lookup at_path lets) as [target | ]; [ | reflexivity ].
  rewrite closed_named_renamed.
  destruct (closed_named d) eqn:Hclosed; [ | reflexivity ].
  rewrite (rename_closed_named r d Hclosed). reflexivity.
Qed.

(* The bindings that stand for a [Let] lifted out mention no variable. *)
Lemma lifted_out_closed (r : renaming) (lets : list (path * lift_to))
    (at_path : path) (d : named) (bindings : list static_binding)
    (s : symbol) :
  lifted_out lets at_path d = Some (bindings, s) ->
  map (rename_static_binding r) bindings = bindings.
Proof.
  unfold lifted_out.
  destruct (lookup at_path lets) as [target | ]; [ | discriminate ].
  destruct (closed_named d) eqn:Hclosed; [ | discriminate ].
  intros Hlift. pose proof (lift_named_rename r target d) as Hrenamed.
  rewrite (rename_closed_named r d Hclosed), Hlift in Hrenamed.
  simpl in Hrenamed. injection Hrenamed as Hrenamed. symmetry.
  exact Hrenamed.
Qed.

Fixpoint lifted_out_bindings_renamed (r : renaming)
    (lets : list (path * lift_to)) (at_path : path) (e : expr) {struct e} :
  lifted_out_bindings lets at_path (rename_expr r e)
  = lifted_out_bindings lets at_path e
with handler_lifted_out_bindings_renamed (r : renaming)
    (lets : list (path * lift_to)) (at_path : path)
    (h : continuation_handler) {struct h} :
  handler_lifted_out_bindings lets at_path (rename_handler r h)
  = handler_lifted_out_bindings lets at_path h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite lifted_out_renamed, lifted_out_bindings_renamed. reflexivity.
    + apply lifted_out_bindings_renamed.
    + rewrite lifted_out_bindings_renamed,
        handler_lifted_out_bindings_renamed.
      reflexivity.
    + apply lifted_out_bindings_renamed.
  - destruct h as [params metadata handler]. simpl.
    apply lifted_out_bindings_renamed.
Qed.

Theorem lifted_out_bindings_equivariant :
  lifted_out_bindings_equivariant_statement.
Proof. exact lifted_out_bindings_renamed. Qed.

Fixpoint lifted_out_bindings_closed (r : renaming)
    (lets : list (path * lift_to)) (at_path : path) (e : expr) {struct e} :
  map (rename_static_binding r) (lifted_out_bindings lets at_path e)
  = lifted_out_bindings lets at_path e
with handler_lifted_out_bindings_closed (r : renaming)
    (lets : list (path * lift_to)) (at_path : path)
    (h : continuation_handler) {struct h} :
  map (rename_static_binding r) (handler_lifted_out_bindings lets at_path h)
  = handler_lifted_out_bindings lets at_path h.
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite map_app, lifted_out_bindings_closed. f_equal.
      destruct (lifted_out lets at_path d) as [[bindings s] | ] eqn:Hout;
        [ exact (lifted_out_closed r lets at_path d bindings s Hout)
        | reflexivity ].
    + apply lifted_out_bindings_closed.
    + rewrite map_app, lifted_out_bindings_closed,
        handler_lifted_out_bindings_closed.
      reflexivity.
    + apply lifted_out_bindings_closed.
  - destruct h as [params metadata handler]. simpl.
    apply lifted_out_bindings_closed.
Qed.

Fixpoint lift_from_code_renamed (r : renaming) (K : lets_in_code)
    (lets : list (path * lift_to)) (at_path : path) (e : expr) {struct e} :
  rename_expr r (lift_from_code K lets at_path e)
  = lift_from_code K lets at_path (rename_expr r e)
with handler_lift_from_code_renamed (r : renaming) (K : lets_in_code)
    (lets : list (path * lift_to)) (at_path : path)
    (h : continuation_handler) {struct h} :
  rename_handler r (handler_lift_from_code K lets at_path h)
  = handler_lift_from_code K lets at_path (rename_handler r h)
with binding_lift_from_code_renamed (r : renaming) (K : lets_in_code)
    (binding : static_binding) {struct binding} :
  map (rename_static_binding r) (binding_lift_from_code K binding)
  = binding_lift_from_code K (rename_static_binding r binding).
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite lifted_out_renamed.
      destruct (lifted_out lets at_path d) as [[bindings s] | ]; simpl;
        rewrite lift_from_code_renamed; reflexivity.
    + rewrite lift_from_code_renamed. f_equal.
      induction bindings as [ | binding bindings IH]; [ reflexivity | ].
      simpl. rewrite map_app, IH, binding_lift_from_code_renamed.
      reflexivity.
    + rewrite handler_lift_from_code_renamed, lift_from_code_renamed.
      reflexivity.
    + rewrite lift_from_code_renamed. reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite lift_from_code_renamed. reflexivity.
  - destruct binding as [id c | id | sym const]; try reflexivity.
    destruct c as [params my_closure ret exn metadata body]. simpl.
    rewrite map_app, lifted_out_bindings_closed, lifted_out_bindings_renamed.
    simpl. rewrite lift_from_code_renamed. reflexivity.
Qed.

Theorem lift_from_code_equivariant : lift_from_code_equivariant_statement.
Proof. exact lift_from_code_renamed. Qed.
