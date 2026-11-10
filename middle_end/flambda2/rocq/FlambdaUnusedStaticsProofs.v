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

(* Proofs of the statements of FlambdaUnusedStaticsSpec.v. Nothing here
   needs review.

   A state and the same state with the bindings erased step alike, as long
   as the first is defined (FlambdaSemanticsProofs.simulation_refines).
   The relation ([state_erased]) says that the expression, the values, the
   continuation closures and the static environment of the first refer to
   none of the names removed; so the values of the two are the same, and
   nothing the first looks up has gone from the second. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaNormaliseSpec FlambdaUnusedStaticsSpec.
Import ListNotations.

Section Erasure.

Variable D : dropped.

(* ======================================================================== *)
(* Values that refer to no name removed                                     *)
(* ======================================================================== *)

Definition env_avoids (vars : env) : Prop :=
  ∀ (x : variable) (v : value),
    lookup x vars = Some v -> value_avoids D v = true.

Definition slot_values_avoid (slots : list (value_slot * value)) : bool :=
  forallb (fun '(_, v) => value_avoids D v) slots.

Lemma env_avoids_cons (vars : env) (x : variable) (v : value) :
  value_avoids D v = true -> env_avoids vars -> env_avoids ((x, v) :: vars).
Proof.
  intros Hv Hvars y w. simpl.
  destruct (Pos.eqb y x); [ intros [= <-]; exact Hv | apply Hvars ].
Qed.

Lemma bind_params_avoids (params : list variable) :
  ∀ (vs : list value) (vars bound : env),
    forallb (value_avoids D) vs = true ->
    env_avoids vars ->
    bind_params params vs vars = Some bound ->
    env_avoids bound.
Proof.
  induction params as [ | p params IH]; intros [ | v vs] vars bound; simpl;
    try discriminate.
  - intros _ Hvars [= <-]. exact Hvars.
  - intros Hvs Hvars. apply andb_true_iff in Hvs as [Hv Hvs].
    apply (IH vs _ bound Hvs), env_avoids_cons; assumption.
Qed.

Lemma eval_simple_avoids (vars : env) (s : simple) (v : value) :
  env_avoids vars ->
  simple_avoids D s = true ->
  eval_simple vars s = Some v ->
  value_avoids D v = true.
Proof.
  intros Hvars. destruct s as [x | sym | c]; simpl.
  - intros _. apply Hvars.
  - intros Hkept [= <-]. exact Hkept.
  - intros _ [= <-]. reflexivity.
Qed.

Lemma eval_simples_avoid (vars : env) (args : list simple) :
  env_avoids vars ->
  ∀ vs : list value,
    simples_avoid D args = true ->
    eval_simples vars args = Some vs ->
    forallb (value_avoids D) vs = true.
Proof.
  intros Hvars. unfold simples_avoid.
  induction args as [ | s args IH]; intros vs; simpl.
  - intros _ [= <-]. reflexivity.
  - intros Hav. apply andb_true_iff in Hav as [Hs Hargs].
    destruct (eval_simple vars s) as [v | ] eqn:Heval; [ | discriminate ].
    destruct (eval_simples vars args) as [vs' | ]; [ | discriminate ].
    simpl. intros [= <-]. simpl.
    rewrite (eval_simple_avoids vars s v Hvars Hs Heval), (IH vs' Hargs);
      reflexivity.
Qed.

Lemma eval_value_slots_avoid (vars : env)
    (slots : list (value_slot * simple)) :
  env_avoids vars ->
  ∀ evaluated : list (value_slot * value),
    value_slots_avoid D slots = true ->
    eval_value_slots vars slots = Some evaluated ->
    slot_values_avoid evaluated = true.
Proof.
  intros Hvars. unfold value_slots_avoid, slot_values_avoid.
  induction slots as [ | [slot s] slots IH]; intros evaluated; simpl.
  - intros _ [= <-]. reflexivity.
  - intros Hav. apply andb_true_iff in Hav as [Hs Hslots].
    destruct (eval_simple vars s) as [v | ] eqn:Heval; [ | discriminate ].
    destruct (eval_value_slots vars slots) as [rest | ]; [ | discriminate ].
    simpl. intros [= <-]. simpl.
    rewrite (eval_simple_avoids vars s v Hvars Hs Heval), (IH rest Hslots);
      reflexivity.
Qed.

Lemma lookup_slot_avoids (slot : value_slot)
    (slots : list (value_slot * value)) (v : value) :
  slot_values_avoid slots = true ->
  lookup slot slots = Some v ->
  value_avoids D v = true.
Proof.
  unfold slot_values_avoid.
  induction slots as [ | [slot' w] slots IH]; simpl; [ discriminate | ].
  intros Hav. apply andb_true_iff in Hav as [Hw Hslots].
  destruct (Pos.eqb slot slot');
    [ intros [= <-]; exact Hw | exact (IH Hslots) ].
Qed.

(* ======================================================================== *)
(* Static environments                                                      *)
(* ======================================================================== *)

Definition allocated_avoids (allocated : statically_allocated_value) : bool :=
  match allocated with
  | Static_closure code slots => code_kept D code && slot_values_avoid slots
  | Static_block _ fields => forallb (value_avoids D) fields
  | Static_boxed_number contents => value_avoids D contents
  | Static_string _ => true
  end.

(* The second static environment is the first without the names removed
   and with its code erased; what the first keeps refers to none of the
   names removed. *)
Definition statics_erased (statics statics' : static_env) : Prop :=
  (∀ id : code_id,
    code_kept D id = true ->
    lookup id (static_code statics')
    = option_map (erase_code D) (lookup id (static_code statics)))
  ∧ (∀ (id : code_id) (c : code),
      code_kept D id = true ->
      lookup id (static_code statics) = Some c ->
      code_avoids D c = true)
  ∧ (∀ s : symbol,
      symbol_kept D s = true ->
      lookup s (static_values statics') = lookup s (static_values statics))
  ∧ (∀ (s : symbol) (allocated : statically_allocated_value),
      symbol_kept D s = true ->
      lookup s (static_values statics) = Some allocated ->
      allocated_avoids allocated = true).

Lemma statics_erased_add_code (statics statics' : static_env) (id : code_id)
    (c : code) :
  statics_erased statics statics' ->
  code_avoids D c = true ->
  statics_erased
    (Static_env ((id, c) :: static_code statics) (static_values statics))
    (Static_env ((id, erase_code D c) :: static_code statics')
       (static_values statics')).
Proof.
  intros (Hcode & Hcode_avoids & Hvalues & Hvalues_avoid) Hc.
  split; [ | split; [ | split ] ]; simpl.
  - intros id' Hkept. destruct (Pos.eqb id' id); [ reflexivity | ].
    apply Hcode, Hkept.
  - intros id' c' Hkept. destruct (Pos.eqb id' id);
      [ intros [= <-]; exact Hc | apply Hcode_avoids, Hkept ].
  - exact Hvalues.
  - exact Hvalues_avoid.
Qed.

Lemma statics_erased_drop_code (statics statics' : static_env) (id : code_id)
    (c : code) :
  statics_erased statics statics' ->
  code_kept D id = false ->
  statics_erased
    (Static_env ((id, c) :: static_code statics) (static_values statics))
    statics'.
Proof.
  intros (Hcode & Hcode_avoids & Hvalues & Hvalues_avoid) Hdropped.
  split; [ | split; [ | split ] ]; simpl.
  - intros id' Hkept.
    destruct (Pos.eqb_spec id' id) as [-> | _]; [ congruence | ].
    apply Hcode, Hkept.
  - intros id' c' Hkept.
    destruct (Pos.eqb_spec id' id) as [-> | _]; [ congruence | ].
    apply Hcode_avoids, Hkept.
  - exact Hvalues.
  - exact Hvalues_avoid.
Qed.

Lemma statics_erased_add_value (statics statics' : static_env) (s : symbol)
    (allocated : statically_allocated_value) :
  statics_erased statics statics' ->
  allocated_avoids allocated = true ->
  statics_erased
    (Static_env (static_code statics)
       ((s, allocated) :: static_values statics))
    (Static_env (static_code statics')
       ((s, allocated) :: static_values statics')).
Proof.
  intros (Hcode & Hcode_avoids & Hvalues & Hvalues_avoid) Hallocated.
  split; [ | split; [ | split ] ]; simpl.
  - exact Hcode.
  - exact Hcode_avoids.
  - intros s' Hkept. destruct (Pos.eqb s' s); [ reflexivity | ].
    apply Hvalues, Hkept.
  - intros s' allocated' Hkept. destruct (Pos.eqb s' s);
      [ intros [= <-]; exact Hallocated | apply Hvalues_avoid, Hkept ].
Qed.

Lemma statics_erased_drop_value (statics statics' : static_env) (s : symbol)
    (allocated : statically_allocated_value) :
  statics_erased statics statics' ->
  symbol_kept D s = false ->
  statics_erased
    (Static_env (static_code statics)
       ((s, allocated) :: static_values statics))
    statics'.
Proof.
  intros (Hcode & Hcode_avoids & Hvalues & Hvalues_avoid) Hdropped.
  split; [ | split; [ | split ] ]; simpl.
  - exact Hcode.
  - exact Hcode_avoids.
  - intros s' Hkept.
    destruct (Pos.eqb_spec s' s) as [-> | _]; [ congruence | ].
    apply Hvalues, Hkept.
  - intros s' allocated' Hkept.
    destruct (Pos.eqb_spec s' s) as [-> | _]; [ congruence | ].
    apply Hvalues_avoid, Hkept.
Qed.

(* A value that refers to no name removed is the same closure under both
   static environments, of code that is kept. *)
Lemma closure_of_erased (statics statics' : static_env) (v : value) :
  statics_erased statics statics' ->
  value_avoids D v = true ->
  closure_of statics' v = closure_of statics v
  ∧ (∀ (called : code_id) (slots : list (value_slot * value)),
      closure_of statics v = Some (called, slots) ->
      code_kept D called = true ∧ slot_values_avoid slots = true).
Proof.
  intros (_ & _ & Hvalues & Hvalues_avoid).
  destruct v as [c | code slots | s]; simpl.
  - intros _. split; [ reflexivity | discriminate ].
  - intros Hv. apply andb_true_iff in Hv as [Hcode Hslots].
    split; [ reflexivity | ]. intros called slots' [= <- <-]. auto.
  - intros Hkept. rewrite (Hvalues s Hkept). split; [ reflexivity | ].
    intros called slots.
    destruct (lookup s (static_values statics))
      as [[code slots' | tag fields | contents | bytes] | ] eqn:Hlookup;
      try discriminate.
    intros [= <- <-].
    pose proof (Hvalues_avoid s _ Hkept Hlookup) as Hallocated.
    simpl in Hallocated. apply andb_true_iff in Hallocated. exact Hallocated.
Qed.

Lemma eval_named_erased (statics statics' : static_env) (vars : env)
    (d : named) :
  statics_erased statics statics' ->
  env_avoids vars ->
  named_avoids D d = true ->
  eval_named statics' vars d = eval_named statics vars d
  ∧ (∀ v : value,
      eval_named statics vars d = Some v -> value_avoids D v = true).
Proof.
  intros Hstatics Hvars.
  destruct d as [s | p args | code slots | slot closure]; simpl; intros Hd.
  - split; [ reflexivity | ]. intros v.
    apply eval_simple_avoids; assumption.
  - split; [ reflexivity | ]. intros v.
    destruct (eval_simples vars args) as [vs | ] eqn:Hargs; [ | discriminate ].
    simpl. apply eval_prim_avoids.
    exact (eval_simples_avoid vars args Hvars vs Hd Hargs).
  - apply andb_true_iff in Hd as [Hcode Hslots].
    split; [ reflexivity | ]. intros v.
    destruct (eval_value_slots vars slots) as [evaluated | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-]. simpl. rewrite Hcode. simpl.
    exact (eval_value_slots_avoid vars slots Hvars evaluated Hslots Heval).
  - destruct (eval_simple vars closure) as [v | ] eqn:Hclosure; simpl;
      [ | split; [ reflexivity | discriminate ] ].
    destruct (closure_of_erased statics statics' v Hstatics
                (eval_simple_avoids vars closure v Hvars Hd Hclosure))
      as [Hsame Hslots].
    rewrite Hsame. split; [ reflexivity | ].
    destruct (closure_of statics v) as [[called slots] | ]; simpl;
      [ | discriminate ].
    intros w.
    exact (lookup_slot_avoids slot slots w
      (proj2 (Hslots called slots eq_refl))).
Qed.

Lemma eval_static_const_avoids (vars : env) (const : static_const)
    (allocated : statically_allocated_value) :
  env_avoids vars ->
  static_const_avoids D const = true ->
  eval_static_const vars const = Some allocated ->
  allocated_avoids allocated = true.
Proof.
  intros Hvars.
  destruct const as [code slots | tag fields | contents | bytes]; simpl;
    intros Hconst.
  - apply andb_true_iff in Hconst as [Hcode Hslots].
    destruct (eval_value_slots vars slots) as [evaluated | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-]. simpl. rewrite Hcode. simpl.
    exact (eval_value_slots_avoid vars slots Hvars evaluated Hslots Heval).
  - destruct (eval_simples vars fields) as [vs | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-]. simpl.
    exact (eval_simples_avoid vars fields Hvars vs Hconst Heval).
  - destruct (eval_simple vars contents) as [v | ] eqn:Heval;
      [ | discriminate ].
    simpl. intros [= <-]. simpl.
    exact (eval_simple_avoids vars contents v Hvars Hconst Heval).
  - intros [= <-]. reflexivity.
Qed.

(* A group of bindings and the group erased, added to static environments
   one of which is the other erased: if the first has a result, the second
   has, and it is the first's erased. *)
Lemma eval_static_bindings_erased (vars : env) :
  env_avoids vars ->
  ∀ (bindings : list static_binding) (statics statics' : static_env),
    forallb (binding_avoids D) bindings = true ->
    statics_erased statics statics' ->
    match eval_static_bindings vars bindings statics with
    | Some extended =>
      ∃ extended' : static_env,
        eval_static_bindings vars
          (keep_map (binding_kept D) (erase_binding D) bindings) statics'
        = Some extended'
        ∧ statics_erased extended extended'
    | None => True
    end.
Proof.
  intros Hvars.
  induction bindings as [ | binding bindings IH]; intros statics statics';
    simpl.
  - intros _ Hstatics. exists statics'. auto.
  - intros Hav Hstatics. apply andb_true_iff in Hav as [Hbinding Hrest].
    destruct binding as [id c | id | sym const]; simpl in Hbinding |- *.
    + destruct (code_kept D id) eqn:Hkept; simpl.
      * apply (IH _ _ Hrest), statics_erased_add_code; assumption.
      * apply (IH _ _ Hrest), statics_erased_drop_code; assumption.
    + exact (IH _ _ Hrest Hstatics).
    + destruct (eval_static_const vars const) as [allocated | ] eqn:Hconst;
        simpl; [ | exact I ].
      destruct (symbol_kept D sym) eqn:Hkept; simpl.
      * rewrite Hconst. simpl.
        apply (IH _ _ Hrest), statics_erased_add_value; [ exact Hstatics | ].
        exact (eval_static_const_avoids vars const allocated Hvars Hbinding
          Hconst).
      * apply (IH _ _ Hrest), statics_erased_drop_value; assumption.
Qed.

(* ======================================================================== *)
(* Continuations and states                                                 *)
(* ======================================================================== *)

Definition handlers_avoid
    (handlers : list (continuation * continuation_handler)) : bool :=
  forallb (fun '(_, h) => handler_avoids D h) handlers.

Definition erase_handlers
    (handlers : list (continuation * continuation_handler))
    : list (continuation * continuation_handler) :=
  map (fun '(k, h) => (k, erase_handler D h)) handlers.

#[local] Set Warnings "-register-all".
Inductive cont_erased : cont_value -> cont_value -> Prop :=
  | Outer_erased (k : continuation) : cont_erased (Outer k) (Outer k)
  | Closure_erased (h : continuation_handler) (vars : env)
      (conts conts' : cont_env)
      (recursive : list (continuation * continuation_handler)) :
    handler_avoids D h = true ->
    env_avoids vars ->
    Forall2
      (fun kc kc' => fst kc = fst kc' ∧ cont_erased (snd kc) (snd kc'))
      conts conts' ->
    handlers_avoid recursive = true ->
    cont_erased (Closure h vars conts recursive)
      (Closure (erase_handler D h) vars conts' (erase_handlers recursive)).

Definition conts_erased (conts conts' : cont_env) : Prop :=
  Forall2 (fun kc kc' => fst kc = fst kc' ∧ cont_erased (snd kc) (snd kc'))
    conts conts'.

Lemma resolve_erased (k : continuation) (conts conts' : cont_env) :
  conts_erased conts conts' ->
  cont_erased (resolve k conts) (resolve k conts').
Proof.
  unfold resolve.
  induction 1 as [ | [k1 c] [k1' c'] conts conts' [Hk Hc] _ IH]; simpl;
    [ apply Outer_erased | ].
  simpl in Hk. subst k1'. destruct (Pos.eqb k k1); [ exact Hc | exact IH ].
Qed.

(* [all] is the whole group, kept apart from the handlers still to be gone
   through. *)
Lemma rec_closures_erased_aux (vars : env) (conts conts' : cont_env)
    (all handlers : list (continuation * continuation_handler)) :
  env_avoids vars ->
  conts_erased conts conts' ->
  handlers_avoid all = true ->
  handlers_avoid handlers = true ->
  conts_erased (map (fun '(k, h) => (k, Closure h vars conts all)) handlers)
    (map (fun '(k, h) => (k, Closure h vars conts' (erase_handlers all)))
       (erase_handlers handlers)).
Proof.
  intros Hvars Hconts Hall. unfold handlers_avoid.
  induction handlers as [ | [k h] handlers IH]; simpl;
    [ intros _; apply Forall2_nil | ].
  intros Hav. apply andb_true_iff in Hav as [Hh Hrest].
  apply Forall2_cons; [ | exact (IH Hrest) ].
  split; [ reflexivity | ]. apply Closure_erased; assumption.
Qed.

Lemma rec_closures_erased (vars : env) (conts conts' : cont_env)
    (handlers : list (continuation * continuation_handler)) :
  env_avoids vars ->
  conts_erased conts conts' ->
  handlers_avoid handlers = true ->
  conts_erased (rec_closures handlers vars conts ++ conts)
    (rec_closures (erase_handlers handlers) vars conts' ++ conts').
Proof.
  intros Hvars Hconts Hhandlers. apply Forall2_app; [ | exact Hconts ].
  apply rec_closures_erased_aux; assumption.
Qed.

Inductive state_erased : state -> state -> Prop :=
  | State_erased (e : expr) (vars : env) (conts conts' : cont_env)
      (statics statics' : static_env) :
    expr_avoids D e = true ->
    env_avoids vars ->
    conts_erased conts conts' ->
    statics_erased statics statics' ->
    state_erased (State e vars conts statics)
      (State (erase_expr D e) vars conts' statics').

Lemma apply_cont_value_erased (c c' : cont_value) (vs : list value)
    (statics statics' : static_env) :
  cont_erased c c' ->
  forallb (value_avoids D) vs = true ->
  statics_erased statics statics' ->
  result_simulated state_erased (apply_cont_value c vs statics)
    (apply_cont_value c' vs statics').
Proof.
  intros [k | [params handler] vars conts conts' recursive Hh Hvars Hconts
               Hrec] Hvs Hstatics; simpl.
  - auto.
  - destruct (bind_params params vs vars) as [bound | ] eqn:Hbind; simpl;
      [ | exact I ].
    apply State_erased;
      [ exact Hh
      | exact (bind_params_avoids params vs vars bound Hvs Hvars Hbind)
      | apply rec_closures_erased; assumption | exact Hstatics ].
Qed.

Lemma call_function_erased (callee : value) (kind : call_kind)
    (vs : list value) (return_to return_to' exn_to exn_to' : cont_value)
    (statics statics' : static_env) :
  value_avoids D callee = true ->
  forallb (value_avoids D) vs = true ->
  cont_erased return_to return_to' ->
  cont_erased exn_to exn_to' ->
  statics_erased statics statics' ->
  result_simulated state_erased
    (call_function callee kind vs return_to exn_to statics)
    (call_function callee kind vs return_to' exn_to' statics').
Proof.
  intros Hcallee Hvs Hreturn Hexn Hstatics. unfold call_function.
  destruct (closure_of_erased statics statics' callee Hstatics Hcallee)
    as [Hsame Hslots].
  rewrite Hsame.
  destruct (closure_of statics callee) as [[called slots] | ]; [ | exact I ].
  destruct (Hslots called slots eq_refl) as [Hkept _].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | exact I ].
  destruct Hstatics as (Hcode & Hcode_avoids & Hvalues & Hvalues_avoid).
  rewrite (Hcode called Hkept).
  destruct (lookup called (static_code statics))
    as [[params my_closure ret exn body] | ] eqn:Hlookup;
    simpl; [ | exact I ].
  destruct (bind_params params vs [(my_closure, callee)]) as [bound | ]
    eqn:Hbind; simpl; [ | exact I ].
  apply State_erased.
  - exact (Hcode_avoids called _ Hkept Hlookup).
  - apply (bind_params_avoids params vs [(my_closure, callee)] bound Hvs);
      [ | exact Hbind ].
    apply env_avoids_cons; [ exact Hcallee | ]. intros x v [=].
  - apply Forall2_cons; [ split; [ reflexivity | exact Hreturn ] | ].
    apply Forall2_cons; [ split; [ reflexivity | exact Hexn ] | ].
    apply Forall2_nil.
  - repeat split; assumption.
Qed.

(* A state and the state erased step alike, where the first is defined. *)
Lemma erased_step (s s' : state) :
  state_erased s s' -> result_simulated state_erased (step s) (step s').
Proof.
  intros [e vars conts conts' statics statics' He Hvars Hconts Hstatics].
  destruct e
    as [ x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl in He |- *.
  - (* Let *)
    apply andb_true_iff in He as [Hd Hbody].
    destruct (eval_named_erased statics statics' vars d Hstatics Hvars Hd)
      as [Hsame Hvalue].
    rewrite Hsame.
    destruct (eval_named statics vars d) as [v | ]; simpl; [ | exact I ].
    apply State_erased;
      [ exact Hbody | apply env_avoids_cons; auto | exact Hconts
      | exact Hstatics ].
  - (* Let_static *)
    apply andb_true_iff in He as [Hbindings Hbody].
    pose proof (eval_static_bindings_erased vars Hvars bindings statics
      statics' Hbindings Hstatics) as Hextended.
    destruct (eval_static_bindings vars bindings statics) as [extended | ];
      [ | exact I ].
    destruct Hextended as (extended' & -> & Hextended).
    simpl. apply State_erased; assumption.
  - (* Let_cont_non_recursive *)
    apply andb_true_iff in He as [Hh Hbody].
    apply State_erased; [ exact Hbody | exact Hvars | | exact Hstatics ].
    apply Forall2_cons; [ | exact Hconts ].
    split; [ reflexivity | ].
    exact (Closure_erased h vars conts conts' [] Hh Hvars Hconts eq_refl).
  - (* Let_cont_recursive *)
    apply andb_true_iff in He as [Hhandlers Hbody].
    apply State_erased; [ exact Hbody | exact Hvars | | exact Hstatics ].
    apply rec_closures_erased; assumption.
  - (* Apply *)
    unfold apply_avoids in He.
    apply andb_true_iff in He as [He Hargs].
    apply andb_true_iff in He as [Hcallee _].
    destruct (eval_simple vars (ap_callee ap)) as [callee | ] eqn:Heval;
      [ | exact I ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ] eqn:Hevals;
      [ | exact I ].
    apply call_function_erased;
      [ exact (eval_simple_avoids vars _ callee Hvars Hcallee Heval)
      | exact (eval_simples_avoid vars _ Hvars vs Hargs Hevals)
      | apply resolve_erased, Hconts | apply resolve_erased, Hconts
      | exact Hstatics ].
  - (* Apply_cont *)
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hevals;
      [ | exact I ].
    apply apply_cont_value_erased;
      [ apply resolve_erased, Hconts
      | exact (eval_simples_avoid vars _ Hvars vs He Hevals) | exact Hstatics ].
  - (* Switch *)
    apply andb_true_iff in He as [_ Harms].
    destruct (eval_simple vars scrutinee) as [v | ]; [ | exact I ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
    destruct (find_arm i arms) as [ac | ] eqn:Hfind; simpl; [ | exact I ].
    apply (State_erased (Apply_cont ac));
      [ | exact Hvars | exact Hconts | exact Hstatics ].
    rewrite forallb_forall in Harms.
    exact (Harms (i, ac) (find_arm_in i arms ac Hfind)).
  - (* Invalid *)
    exact I.
Qed.

End Erasure.

Theorem drop_statics_refines : drop_statics_refines_statement.
Proof.
  intros D e e'. unfold drop_statics.
  destruct (expr_avoids D e) eqn:He; [ | discriminate ].
  intros [= <-].
  apply (simulation_refines (state_erased D) (erased_step D)).
  apply State_erased; [ exact He | | apply Forall2_nil | ].
  - intros x v [=].
  - repeat split; simpl; intros; try reflexivity; discriminate.
Qed.
