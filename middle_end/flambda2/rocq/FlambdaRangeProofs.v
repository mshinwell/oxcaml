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

(* Proofs of the statements of FlambdaRangeSpec.v. Nothing here needs
   review.

   The primitives are not looked into: what one does to numbers in range
   is the law FlambdaPrimitiveProofs.eval_prim_in_range. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaWellFormedSpec FlambdaNominalSpec FlambdaRangeSpec.
Import ListNotations.

(* ======================================================================== *)
(* Evaluation                                                               *)
(* ======================================================================== *)

Definition slot_values_in_range (value_slots : list (value_slot * value))
    : bool :=
  forallb (fun '(_, v) => value_in_range v) value_slots.

Section Evaluation.

Variable vars : env.
Hypothesis Hvars : env_in_range vars.

Lemma eval_simple_in_range (s : simple) (v : value) :
  simple_in_range s = true ->
  eval_simple vars s = Some v ->
  value_in_range v = true.
Proof.
  destruct s as [x | sym | c]; simpl.
  - intros _ Hlookup. exact (Hvars x v (lookup_in _ _ _ Hlookup)).
  - intros _ [= <-]. reflexivity.
  - intros Hc [= <-]. exact Hc.
Qed.

Lemma eval_simples_in_range (args : list simple) :
  ∀ vs : list value,
    forallb simple_in_range args = true ->
    eval_simples vars args = Some vs ->
    forallb value_in_range vs = true.
Proof.
  induction args as [ | s args IH]; intros vs; simpl.
  - intros _ [= <-]. reflexivity.
  - intros Hargs. apply andb_true_iff in Hargs as [Hs Hargs].
    destruct (eval_simple vars s) as [v | ] eqn:Heval; [ | discriminate ].
    destruct (eval_simples vars args) as [vs' | ]; [ | discriminate ].
    simpl. intros [= <-]. simpl.
    rewrite (eval_simple_in_range s v Hs Heval), (IH vs' Hargs);
      reflexivity.
Qed.

Lemma eval_value_slots_in_range (value_slots : list (value_slot * simple)) :
  ∀ evaluated : list (value_slot * value),
    value_slots_in_range value_slots = true ->
    eval_value_slots vars value_slots = Some evaluated ->
    slot_values_in_range evaluated = true.
Proof.
  unfold value_slots_in_range, slot_values_in_range.
  induction value_slots as [ | [slot s] value_slots IH]; intros evaluated;
    simpl.
  - intros _ [= <-]. reflexivity.
  - intros Hslots. apply andb_true_iff in Hslots as [Hs Hslots].
    destruct (eval_simple vars s) as [v | ] eqn:Heval; [ | discriminate ].
    destruct (eval_value_slots vars value_slots) as [rest | ];
      [ | discriminate ].
    simpl. intros [= <-]. simpl.
    rewrite (eval_simple_in_range s v Hs Heval), (IH rest Hslots);
      reflexivity.
Qed.

End Evaluation.

Lemma lookup_slot_in_range (slot : value_slot)
    (value_slots : list (value_slot * value)) (v : value) :
  slot_values_in_range value_slots = true ->
  lookup slot value_slots = Some v ->
  value_in_range v = true.
Proof.
  intros Hslots Hlookup.
  exact
    (proj1 (forallb_forall _ _) Hslots (slot, v) (lookup_in _ _ _ Hlookup)).
Qed.

(* ======================================================================== *)
(* Closures                                                                 *)
(* ======================================================================== *)

Section Statics.

Variable statics : static_env.
Hypothesis Hstatics : statics_in_range statics.

Lemma lookup_symbol_in_range (s : symbol)
    (allocated : statically_allocated_value) :
  lookup s (static_values statics) = Some allocated ->
  allocated_in_range allocated = true.
Proof.
  intros Hlookup. exact (proj2 Hstatics s allocated (lookup_in _ _ _ Hlookup)).
Qed.

(* The value slots of a closure in range are, whether the closure was
   made by a [Let] or is what a symbol is bound to. *)
Lemma closure_in_set_in_range (v : value) (slot : function_slot)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * value)) :
  value_in_range v = true ->
  closure_in_set statics v = Some (slot, function_decls, value_slots) ->
  slot_values_in_range value_slots = true.
Proof.
  intros Hv. destruct v; simpl; try discriminate.
  - intros [= _ _ <-]. exact Hv.
  - match goal with
    | |- context [lookup ?at_slot ?decls] => destruct (lookup at_slot decls)
    end;
      [ | discriminate ].
    simpl. intros [= _ _ <-]. exact Hv.
  - match goal with
    | |- context [lookup ?s ?values] =>
      destruct (lookup s values) as [allocated | ] eqn:Hlookup;
        [ | discriminate ];
        pose proof (lookup_symbol_in_range s allocated Hlookup)
          as Hallocated
    end.
    destruct allocated; try discriminate.
    + intros [= _ _ <-]. exact Hallocated.
    + match goal with
      | |- context [lookup ?at_slot ?decls] =>
        destruct (lookup at_slot decls)
      end;
        [ | discriminate ].
      simpl. intros [= _ _ <-]. exact Hallocated.
Qed.

(* The closure of the same set at another slot has the same value slots,
   and a symbol is in range. *)
Lemma project_function_slot_in_range (move_from move_to : function_slot)
    (v w : value) :
  value_in_range v = true ->
  project_function_slot statics move_from move_to v = Some w ->
  value_in_range w = true.
Proof.
  intros Hv. unfold project_function_slot.
  destruct v; try discriminate.
  - destruct (Pos.eqb move_from unnamed_function_slot); [ | discriminate ].
    destruct (Pos.eqb move_to unnamed_function_slot); [ | discriminate ].
    intros [= <-]. exact Hv.
  - match goal with
    | |- context [Pos.eqb ?at_slot move_from] =>
      destruct (Pos.eqb at_slot move_from); [ | discriminate ]
    end.
    repeat
      match goal with
      | |- context [lookup ?at_slot ?decls] =>
        destruct (lookup at_slot decls); [ | discriminate ]
      end.
    simpl. intros [= <-]. exact Hv.
  - match goal with
    | |- context [lookup ?s ?values] =>
      destruct (lookup s values) as [allocated | ]; [ | discriminate ]
    end.
    destruct allocated; try discriminate.
    + destruct (Pos.eqb move_from unnamed_function_slot); [ | discriminate ].
      destruct (Pos.eqb move_to unnamed_function_slot); [ | discriminate ].
      intros [= <-]. reflexivity.
    + match goal with
      | |- context [Pos.eqb ?at_slot move_from] =>
        destruct (Pos.eqb at_slot move_from); [ | discriminate ]
      end.
      repeat
        match goal with
        | |- context [lookup ?key ?bindings] =>
          destruct (lookup key bindings); [ | discriminate ]
        end.
      simpl. intros [= <-]. reflexivity.
Qed.

Variable vars : env.
Hypothesis Hvars : env_in_range vars.

Lemma eval_named_in_range (d : named) (v : value) :
  named_in_range d = true ->
  eval_named statics vars d = Some v ->
  value_in_range v = true.
Proof.
  destruct d
    as [s | p args | code slots | fslot decls slots | slot closure
       | pfrom slot closure | move_from move_to closure];
    simpl; intros Hd.
  - exact (eval_simple_in_range vars Hvars s v Hd).
  - apply andb_true_iff in Hd as [Hp Hargs].
    destruct (eval_simples vars args) as [vs | ] eqn:Heval;
      [ | discriminate ].
    simpl.
    pose proof (eval_simples_in_range vars Hvars args vs Hargs Heval) as Hvs.
    apply (eval_prim_in_range statics p vs v Hp).
    + intros sym allocated _. apply lookup_symbol_in_range.
    + apply forallb_forall. exact Hvs.
  - destruct (eval_value_slots vars slots) as [evaluated | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-].
    exact (eval_value_slots_in_range vars Hvars slots evaluated Hd Heval).
  - destruct (lookup fslot decls); [ | discriminate ]. simpl.
    destruct (eval_value_slots vars slots) as [evaluated | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-].
    exact (eval_value_slots_in_range vars Hvars slots evaluated Hd Heval).
  - destruct (eval_simple vars closure) as [w | ] eqn:Hclosure;
      [ | discriminate ].
    simpl.
    destruct (closure_of statics w) as [[called value_slots] | ] eqn:Hof;
      [ | discriminate ].
    simpl. intros Hlookup.
    destruct (proj1 (closure_in_set_of statics w called value_slots) Hof)
      as (at_slot & function_decls & Hin_set & _).
    exact
      (lookup_slot_in_range slot value_slots v
         (closure_in_set_in_range w at_slot function_decls value_slots
            (eval_simple_in_range vars Hvars closure w Hd Hclosure) Hin_set)
         Hlookup).
  - destruct (eval_simple vars closure) as [w | ] eqn:Hclosure;
      [ | discriminate ].
    simpl. intros Hproject.
    destruct (proj1 (project_value_slot_defined statics pfrom slot w v)
                Hproject)
      as (function_decls & value_slots & Hin_set & Hlookup).
    exact
      (lookup_slot_in_range slot value_slots v
         (closure_in_set_in_range w pfrom function_decls value_slots
            (eval_simple_in_range vars Hvars closure w Hd Hclosure) Hin_set)
         Hlookup).
  - destruct (eval_simple vars closure) as [w | ] eqn:Hclosure;
      [ | discriminate ].
    simpl.
    exact
      (project_function_slot_in_range move_from move_to w v
         (eval_simple_in_range vars Hvars closure w Hd Hclosure)).
Qed.

End Statics.

(* ======================================================================== *)
(* Static bindings                                                          *)
(* ======================================================================== *)

Lemma eval_static_const_in_range (vars : env) (const : static_const)
    (allocated : statically_allocated_value) :
  env_in_range vars ->
  static_const_in_range const = true ->
  eval_static_const vars const = Some allocated ->
  allocated_in_range allocated = true.
Proof.
  intros Hvars.
  destruct const
    as [code slots | fslot syms decls slots | tag fields | contents | bytes];
    simpl; intros Hconst.
  - destruct (eval_value_slots vars slots) as [evaluated | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-].
    exact (eval_value_slots_in_range vars Hvars slots evaluated Hconst Heval).
  - destruct (lookup fslot decls); [ | discriminate ]. simpl.
    destruct (eval_value_slots vars slots) as [evaluated | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-].
    exact (eval_value_slots_in_range vars Hvars slots evaluated Hconst Heval).
  - apply andb_true_iff in Hconst as [Htag Hfields].
    destruct (eval_simples vars fields) as [vs | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-]. simpl. rewrite Htag.
    exact (eval_simples_in_range vars Hvars fields vs Hfields Heval).
  - destruct (eval_simple vars contents) as [v | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-].
    exact (eval_simple_in_range vars Hvars contents v Hconst Heval).
  - intros [= <-]. exact Hconst.
Qed.

Lemma eval_static_bindings_in_range (vars : env)
    (bindings : list static_binding) :
  env_in_range vars ->
  ∀ statics statics' : static_env,
    forallb binding_numbers_in_range bindings = true ->
    statics_in_range statics ->
    eval_static_bindings vars bindings statics = Some statics' ->
    statics_in_range statics'.
Proof.
  intros Hvars.
  induction bindings as [ | binding bindings IH]; intros statics statics';
    simpl.
  - intros _ Hstatics [= <-]. exact Hstatics.
  - intros Hbindings. apply andb_true_iff in Hbindings as [Hbinding Hrest].
    intros [Hcode Hvalues].
    destruct binding as [id c | id | s const]; simpl in Hbinding.
    + destruct (lookup id (static_code statics)); [ discriminate | ].
      apply (IH _ _ Hrest). split; [ | exact Hvalues ].
      intros id' c' [[= <- <-] | Hin]; [ exact Hbinding | ].
      exact (Hcode id' c' Hin).
    + apply (IH _ _ Hrest). split; assumption.
    + destruct (lookup s (static_values statics)); [ discriminate | ].
      destruct (eval_static_const vars const) as [allocated | ] eqn:Heval;
        [ | discriminate ].
      simpl. apply (IH _ _ Hrest). split; [ exact Hcode | ].
      intros s' allocated' [[= <- <-] | Hin].
      * exact
          (eval_static_const_in_range vars const allocated Hvars Hbinding
             Heval).
      * exact (Hvalues s' allocated' Hin).
Qed.

(* ======================================================================== *)
(* Continuations and calls                                                  *)
(* ======================================================================== *)

Lemma resolve_in_range (k : continuation) (conts : cont_env) :
  conts_in_range conts -> cont_in_range (resolve k conts).
Proof.
  intros Hconts. unfold resolve.
  destruct (lookup k conts) as [c | ] eqn:Hlookup.
  - exact (Hconts k c (lookup_in _ _ _ Hlookup)).
  - constructor.
Qed.

Lemma handlers_in_range
    (handlers : list (continuation * continuation_handler)) :
  forallb (fun '(_, h) => handler_numbers_in_range h) handlers = true ->
  ∀ (k : continuation) (h : continuation_handler),
    (k, h) ∈ handlers -> handler_numbers_in_range h = true.
Proof.
  intros Hhandlers k h Hin.
  exact (proj1 (forallb_forall _ _) Hhandlers (k, h) Hin).
Qed.

Lemma rec_closures_in_range
    (handlers : list (continuation * continuation_handler)) (vars : env)
    (conts : cont_env) :
  (∀ (k : continuation) (h : continuation_handler),
    (k, h) ∈ handlers -> handler_numbers_in_range h = true) ->
  env_in_range vars ->
  conts_in_range conts ->
  conts_in_range (rec_closures handlers vars conts).
Proof.
  intros Hhandlers Hvars Hconts k c Hin. unfold rec_closures in Hin.
  apply in_map_iff in Hin as ([k' h] & [= <- <-] & Hin).
  constructor; [ exact (Hhandlers k' h Hin) | assumption .. ].
Qed.

Lemma conts_in_range_app (conts conts' : cont_env) :
  conts_in_range conts ->
  conts_in_range conts' ->
  conts_in_range (conts ++ conts').
Proof.
  intros Hconts Hconts' k c Hin.
  apply in_app_or in Hin as [Hin | Hin]; eauto.
Qed.

Lemma bind_params_in_range (params : list variable) :
  ∀ (vs : list value) (vars vars' : env),
    forallb value_in_range vs = true ->
    env_in_range vars ->
    bind_params params vs vars = Some vars' ->
    env_in_range vars'.
Proof.
  induction params as [ | x params IH]; intros [ | v vs] vars vars'; simpl;
    try discriminate.
  - intros _ Hvars [= <-]. exact Hvars.
  - intros Hvs. apply andb_true_iff in Hvs as [Hv Hvs]. intros Hvars.
    apply (IH vs _ _ Hvs).
    intros y w [[= <- <-] | Hin]; [ exact Hv | exact (Hvars y w Hin) ].
Qed.

(* What applying a continuation comes to: a state in range, or a way out
   with values in range. *)
Definition result_in_range (result : step_result) : Prop :=
  match result with
  | Step s => state_in_range s
  | Exit _ vs => forallb value_in_range vs = true
  | Undefined => True
  end.

Lemma apply_cont_value_in_range (c : cont_value) (vs : list value)
    (statics : static_env) :
  cont_in_range c ->
  forallb value_in_range vs = true ->
  statics_in_range statics ->
  result_in_range (apply_cont_value c vs statics).
Proof.
  intros Hc Hvs Hstatics.
  destruct Hc as [k | [params handler] vars conts recursive Hh Hvars Hconts
                        Hrecursive];
    simpl; [ exact Hvs | ].
  destruct (bind_params params vs vars) as [handler_vars | ] eqn:Hbind;
    [ | exact I ].
  repeat split; simpl.
  - exact Hh.
  - exact (bind_params_in_range params vs vars handler_vars Hvs Hvars Hbind).
  - apply conts_in_range_app; [ | exact Hconts ].
    exact (rec_closures_in_range recursive vars conts Hrecursive Hvars Hconts).
  - exact (proj1 Hstatics).
  - exact (proj2 Hstatics).
Qed.

Lemma call_function_in_range (callee : value) (kind : call_kind)
    (vs : list value) (return_to exn_to : cont_value)
    (statics : static_env) :
  value_in_range callee = true ->
  forallb value_in_range vs = true ->
  cont_in_range return_to ->
  cont_in_range exn_to ->
  statics_in_range statics ->
  result_in_range (call_function callee kind vs return_to exn_to statics).
Proof.
  intros Hcallee Hvs Hreturn Hexn Hstatics. unfold call_function.
  destruct (closure_of statics callee) as [[called slots] | ];
    [ | exact I ].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | exact I ].
  destruct (lookup called (static_code statics)) as [c | ] eqn:Hcode;
    [ | exact I ].
  destruct (binds_statics (code_body c)); [ exact I | ].
  destruct (bind_params (code_params c) vs [(code_my_closure c, callee)])
    as [callee_vars | ] eqn:Hbind;
    [ | exact I ].
  pose proof (proj1 Hstatics called c (lookup_in _ _ _ Hcode)) as Hc.
  repeat split; simpl.
  - destruct c. exact Hc.
  - apply (bind_params_in_range _ _ _ _ Hvs) in Hbind; [ exact Hbind | ].
    intros y w [[= <- <-] | []]. exact Hcallee.
  - intros k c' [[= <- <-] | [[= <- <-] | []]]; assumption.
  - exact (proj1 Hstatics).
  - exact (proj2 Hstatics).
Qed.

(* ======================================================================== *)
(* Steps and runs                                                           *)
(* ======================================================================== *)

Lemma step_result_in_range (s : state) :
  state_in_range s -> result_in_range (step s).
Proof.
  intros (Hexpr & Hvars & Hconts & Hstatics). rewrite (state_eta s).
  set (vars := state_vars s) in *. set (conts := state_conts s) in *.
  set (statics := state_statics s) in *.
  destruct (state_expr s)
    as [x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    autorewrite with step; simpl in Hexpr.
  - apply andb_true_iff in Hexpr as [Hd Hbody].
    destruct (eval_named statics vars d) as [v | ] eqn:Heval; [ | exact I ].
    repeat split; simpl; try assumption; try apply Hstatics.
    intros y w [[= <- <-] | Hin]; [ | exact (Hvars y w Hin) ].
    exact (eval_named_in_range statics Hstatics vars Hvars d v Hd Heval).
  - apply andb_true_iff in Hexpr as [Hbindings Hbody].
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Heval;
      [ | exact I ].
    pose proof
      (eval_static_bindings_in_range vars bindings Hvars statics extended
         Hbindings Hstatics Heval)
      as Hextended.
    repeat split; simpl; try assumption; apply Hextended.
  - apply andb_true_iff in Hexpr as [Hh Hbody].
    repeat split; simpl; try assumption; try apply Hstatics.
    intros k' c [[= <- <-] | Hin]; [ | exact (Hconts k' c Hin) ].
    constructor; try assumption. intros k' h' [].
  - apply andb_true_iff in Hexpr as [Hhandlers Hbody].
    destruct (handlers_bind_statics handlers); [ exact I | ].
    repeat split; simpl; try assumption; try apply Hstatics.
    apply conts_in_range_app; [ | exact Hconts ].
    exact
      (rec_closures_in_range handlers vars conts
         (handlers_in_range handlers Hhandlers) Hvars Hconts).
  - apply andb_true_iff in Hexpr as [Hcallee Hargs].
    destruct (eval_simple vars (ap_callee ap)) as [callee | ] eqn:Hc;
      [ | exact I ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ] eqn:Hvs;
      [ | exact I ].
    apply call_function_in_range; try assumption.
    + exact (eval_simple_in_range vars Hvars _ callee Hcallee Hc).
    + exact (eval_simples_in_range vars Hvars _ vs Hargs Hvs).
    + apply resolve_in_range, Hconts.
    + apply resolve_in_range, Hconts.
  - destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hvs;
      [ | exact I ].
    unfold apply_continuation.
    apply apply_cont_value_in_range; try assumption.
    + apply resolve_in_range, Hconts.
    + exact (eval_simples_in_range vars Hvars _ vs Hexpr Hvs).
  - apply andb_true_iff in Hexpr as [_ Harms].
    destruct (eval_simple vars scrutinee) as [v | ]; [ | exact I ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
    destruct (find_arm i arms) as [ac | ] eqn:Hfind; [ | exact I ].
    pose proof
      (proj1 (forallb_forall _ _) Harms (i, ac) (find_arm_in i arms ac Hfind))
      as Harm.
    apply andb_true_iff in Harm as [_ Hac].
    repeat split; simpl; try assumption; apply Hstatics.
  - exact I.
Qed.

Theorem step_in_range : step_in_range_statement.
Proof.
  intros s s' Hs Hstep. pose proof (step_result_in_range s Hs) as Hresult.
  rewrite Hstep in Hresult. exact Hresult.
Qed.

Lemma run_result_in_range (n : nat) :
  ∀ s : state, state_in_range s -> result_in_range (run n s).
Proof.
  induction n as [ | n IH]; intros s Hs; simpl; [ exact Hs | ].
  pose proof (step_result_in_range s Hs) as Hresult.
  destruct (step s) as [next | k vs | ]; [ exact (IH next Hresult) | .. ];
    exact Hresult.
Qed.

Lemma initial_state_in_range (e : expr) :
  numbers_in_range e = true ->
  state_in_range (State e [] [] empty_static_env).
Proof.
  intros He. repeat split; simpl; try exact He; intros ? ? [].
Qed.

Theorem run_in_range : run_in_range_statement.
Proof.
  intros e n s He Hrun.
  pose proof (run_result_in_range n _ (initial_state_in_range e He))
    as Hresult.
  rewrite Hrun in Hresult. exact Hresult.
Qed.

Theorem run_exit_in_range : run_exit_in_range_statement.
Proof.
  intros e n k vs He Hrun.
  pose proof (run_result_in_range n _ (initial_state_in_range e He))
    as Hresult.
  rewrite Hrun in Hresult. apply forallb_forall. exact Hresult.
Qed.

(* ======================================================================== *)
(* What a state in range holds                                              *)
(* ======================================================================== *)

Theorem blocks_in_range : blocks_in_range_statement.
Proof.
  intros s x v tag fields (_ & Hvars & _ & Hstatics) Hlookup Hblock.
  destruct
    (block_of_in_range (state_statics s) v tag fields) as [Htag Hfields];
    [ | exact (Hvars x v (lookup_in _ _ _ Hlookup)) | exact Hblock | ].
  - intros sym allocated _.
    exact (lookup_symbol_in_range (state_statics s) Hstatics sym allocated).
  - split; [ exact Htag | apply forallb_forall; exact Hfields ].
Qed.

Theorem integers_in_range : integers_in_range_statement.
Proof.
  intros s x kind i (_ & Hvars & _) Hlookup.
  apply int_of_value_in_range.
  exact (Hvars x _ (lookup_in _ _ _ Hlookup)).
Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

Lemma rename_simple_in_range (r : renaming) (s : simple) :
  simple_in_range (rename_simple r s) = simple_in_range s.
Proof. destruct s; reflexivity. Qed.

Lemma rename_simples_in_range (r : renaming) (args : list simple) :
  forallb simple_in_range (map (rename_simple r) args)
  = forallb simple_in_range args.
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite rename_simple_in_range, IH. reflexivity.
Qed.

Lemma rename_value_slots_in_range (r : renaming)
    (value_slots : list (value_slot * simple)) :
  value_slots_in_range
    (map (fun slot => (fst slot, rename_simple r (snd slot))) value_slots)
  = value_slots_in_range value_slots.
Proof.
  unfold value_slots_in_range.
  induction value_slots as [ | [slot s] value_slots IH]; simpl;
    [ reflexivity | ].
  rewrite rename_simple_in_range, IH. reflexivity.
Qed.

Lemma rename_named_in_range (r : renaming) (d : named) :
  named_in_range (rename_named r d) = named_in_range d.
Proof.
  destruct d; simpl;
    rewrite ?rename_simples_in_range, ?rename_value_slots_in_range,
      ?rename_simple_in_range;
    reflexivity.
Qed.

Lemma rename_static_const_in_range (r : renaming) (const : static_const) :
  static_const_in_range (rename_static_const r const)
  = static_const_in_range const.
Proof.
  destruct const; simpl;
    rewrite ?rename_simples_in_range, ?rename_value_slots_in_range,
      ?rename_simple_in_range;
    reflexivity.
Qed.

Lemma rename_apply_cont_in_range (r : renaming) (ac : apply_cont) :
  apply_cont_in_range (rename_apply_cont r ac) = apply_cont_in_range ac.
Proof. unfold apply_cont_in_range. simpl. apply rename_simples_in_range. Qed.

Lemma rename_apply_in_range (r : renaming) (ap : apply_expr) :
  apply_in_range (rename_apply r ap) = apply_in_range ap.
Proof.
  unfold apply_in_range. simpl.
  rewrite rename_simple_in_range, rename_simples_in_range. reflexivity.
Qed.

Fixpoint rename_numbers_in_range (r : renaming) (e : expr) :
  numbers_in_range (rename_expr r e) = numbers_in_range e.
Proof.
  destruct e
    as [ x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl.
  - rewrite rename_named_in_range, rename_numbers_in_range. reflexivity.
  - rewrite rename_numbers_in_range. f_equal.
    induction bindings as [ | [id c | id | sym const] bindings IH]; simpl;
      [ reflexivity | rewrite IH; reflexivity .. | ].
    rewrite rename_static_const_in_range, IH. reflexivity.
  - destruct h as [params handler]. simpl.
    rewrite !rename_numbers_in_range. reflexivity.
  - rewrite rename_numbers_in_range. f_equal.
    induction handlers as [ | [k [params handler]] handlers IH]; simpl;
      [ reflexivity | ].
    rewrite rename_numbers_in_range, IH. reflexivity.
  - apply rename_apply_in_range.
  - apply rename_apply_cont_in_range.
  - rewrite rename_simple_in_range. f_equal.
    induction arms as [ | [i ac] arms IH]; simpl; [ reflexivity | ].
    rewrite IH. unfold arm_in_range. simpl.
    rewrite rename_apply_cont_in_range. reflexivity.
  - reflexivity.
Qed.

Theorem numbers_in_range_renamed : numbers_in_range_renamed_statement.
Proof. exact rename_numbers_in_range. Qed.

(* ======================================================================== *)
(* Examples                                                                 *)
(* ======================================================================== *)

Theorem in_range_runs : in_range_runs_statement.
Proof.
  split; [ vm_compute; reflexivity | exists 5%nat; vm_compute; reflexivity ].
Qed.

Theorem tag_out_of_range : tag_out_of_range_statement.
Proof.
  split; [ vm_compute; reflexivity | exists 5%nat; vm_compute; reflexivity ].
Qed.

Theorem constant_out_of_range : constant_out_of_range_statement.
Proof.
  split; [ vm_compute; reflexivity | exists 5%nat; vm_compute; reflexivity ].
Qed.
