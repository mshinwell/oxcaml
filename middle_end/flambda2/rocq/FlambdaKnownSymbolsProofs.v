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

Let S : static_env := known_statics known.

(* What the run has bound of the known symbols is what is known. *)
Definition agrees (run_statics : static_env) : Prop :=
  ∀ (s : symbol) (allocated allocated' : statically_allocated_value),
    lookup s (static_values S) = Some allocated ->
    lookup s (static_values run_statics) = Some allocated' ->
    allocated' = allocated.

Lemma eval_static_bindings_agrees (vars : env)
    (bindings : list static_binding) :
  forallb (binding_bound_as known) bindings = true ->
  ∀ statics statics' : static_env,
    agrees statics ->
    eval_static_bindings vars bindings statics = Some statics' ->
    agrees statics'.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH]; simpl;
    intros Hbound statics statics' Hagrees.
  - intros [= <-]. exact Hagrees.
  - destruct (lookup id (static_code statics)); [ discriminate | ].
    apply IH; [ exact Hbound | ]. exact Hagrees.
  - apply IH; assumption.
  - apply andb_true_iff in Hbound as [Hsym Hbound].
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

(* The second state: the first with its terms folded. *)
Definition fold_statics (statics : static_env) : static_env :=
  Static_env
    (map (fun binding => (fst binding, fold_known_code S (snd binding)))
       (static_code statics))
    (static_values statics).

Fixpoint fold_cont (c : cont_value) : cont_value :=
  match c with
  | Closure h vars conts recursive =>
    Closure (fold_known_handler S h) vars
      (map (fun binding => (fst binding, fold_cont (snd binding))) conts)
      (map (fun '(k, h) => (k, fold_known_handler S h)) recursive)
  | Outer k => Outer k
  | Extra_args c extra => Extra_args (fold_cont c) extra
  end.

Definition fold_conts (conts : cont_env) : cont_env :=
  map (fun binding => (fst binding, fold_cont (snd binding))) conts.

Definition fold_state (s : state) : state :=
  State (fold_known S (state_expr s)) (state_vars s)
    (fold_conts (state_conts s)) (fold_statics (state_statics s)).

Lemma lookup_fold_code (id : code_id) (statics : static_env) :
  lookup id (static_code (fold_statics statics))
  = option_map (fold_known_code S) (lookup id (static_code statics)).
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
    eval_static_bindings vars (map (fold_known_binding S) bindings)
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
  binds_statics (fold_known S e) = binds_statics e
with fold_known_handler_binds_statics (h : continuation_handler)
    {struct h} :
  handler_binds_statics (fold_known_handler S h) = handler_binds_statics h.
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
    (map (fun '(k, h) => (k, fold_known_handler S h)) handlers)
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
  rec_closures (map (fun '(k, h) => (k, fold_known_handler S h)) handlers)
    vars (fold_conts conts)
  = fold_conts (rec_closures handlers vars conts).
Proof.
  unfold rec_closures, fold_conts. rewrite !map_map.
  apply map_ext. intros [k h]. reflexivity.
Qed.

Lemma apply_cont_value_fold (c : cont_value) (vs : list value)
    (statics : static_env) :
  match apply_cont_value c vs statics with
  | Step t =>
    apply_cont_value (fold_cont c) vs (fold_statics statics)
    = Step (fold_state t)
    ∧ state_statics t = statics
  | Exit k vs' =>
    apply_cont_value (fold_cont c) vs (fold_statics statics) = Exit k vs'
  | Undefined => True
  end.
Proof.
  revert vs.
  induction c
    as [[params metadata handler] def_vars def_conts recursive | k
       | c IH extra];
    intros vs; simpl; [ | reflexivity | apply IH ].
  destruct (kinds_eqb (map kind_of_value vs) (hm_params_kinds metadata));
    [ | exact I ].
  destruct (bind_params params vs def_vars) as [handler_vars | ];
    [ | exact I ].
  split; [ | reflexivity ].
  unfold fold_state. simpl_state. f_equal. f_equal.
  fold (fold_conts def_conts). rewrite rec_closures_fold.
  unfold fold_conts. rewrite map_app. reflexivity.
Qed.

Lemma with_extra_args_fold (c : cont_value) (extra : list value) :
  fold_cont (with_extra_args c extra) = with_extra_args (fold_cont c) extra.
Proof. destruct extra; reflexivity. Qed.

Lemma fold_known_code_parts (c : code) :
  code_params (fold_known_code S c) = code_params c
  ∧ code_my_closure (fold_known_code S c) = code_my_closure c
  ∧ code_return_continuation (fold_known_code S c)
    = code_return_continuation c
  ∧ code_exn_continuation (fold_known_code S c) = code_exn_continuation c
  ∧ code_params_arity (fold_known_code S c) = code_params_arity c
  ∧ code_result_arity (fold_known_code S c) = code_result_arity c
  ∧ code_body (fold_known_code S c) = fold_known S (code_body c).
Proof. destruct c. simpl. auto 8. Qed.

Lemma call_function_fold (callee : value) (kind : call_kind)
    (vs : list value) (args_arity return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) :
  match
    call_function callee kind vs args_arity return_arity return_to exn_to
      statics
  with
  | Step t =>
    call_function callee kind vs args_arity return_arity (fold_cont return_to)
      (fold_cont exn_to) (fold_statics statics)
    = Step (fold_state t)
    ∧ state_statics t = statics
  | Exit _ _ => False
  | Undefined => True
  end.
Proof.
  unfold call_function.
  change (closure_of (fold_statics statics) callee)
    with (closure_of statics callee).
  destruct (closure_of statics callee) as [[called slots] | ]; [ | exact I ].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | exact I ].
  rewrite lookup_fold_code.
  destruct (lookup called (static_code statics)) as [c | ]; [ | exact I ].
  simpl option_map. cbv iota.
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
  destruct (bind_params (code_params c) vs [(code_my_closure c, callee)]);
    [ | exact I ].
  split; reflexivity.
Qed.

(* A step of a state that binds the known symbols as is known, and has
   bound them so, is a step of the second state, to the second state of
   the result, which has bound them so too. *)
Lemma fold_step_components (e : expr) (vars : env) (conts : cont_env)
    (statics : static_env) :
  bound_as known e = true ->
  agrees statics ->
  match step (State e vars conts statics) with
  | Step t =>
    step (State (fold_known S e) vars (fold_conts conts) (fold_statics statics))
    = Step (fold_state t)
    ∧ agrees (state_statics t)
  | Exit k vs =>
    step (State (fold_known S e) vars (fold_conts conts) (fold_statics statics))
    = Exit k vs
  | Undefined => True
  end.
Proof.
  intros Hbound Hagrees.
  destruct e
    as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl fold_known; autorewrite with step.
  - (* Let *)
    destruct (eval_named statics vars d) as [v | ] eqn:Hv; [ | exact I ].
    destruct (kind_eqb (kind_of_value v) xkind) eqn:Hkind; [ | exact I ].
    rewrite eval_named_fold_statics.
    rewrite (fold_known_named_sound_here S statics Hagrees vars d v Hv),
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
      as [t | | ];
      [ | contradiction | exact I ].
    destruct Hcall as [Hcall ->]. split; [ exact Hcall | exact Hagrees ].
  - (* Apply_cont *)
    destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | exact I ].
    unfold apply_continuation. rewrite resolve_fold.
    pose proof
      (apply_cont_value_fold (resolve (ac_continuation ac) conts) vs statics)
      as Happly.
    destruct (apply_cont_value (resolve (ac_continuation ac) conts) vs statics)
      as [t | | ];
      [ | exact Happly | exact I ].
    destruct Happly as [Happly ->]. split; [ exact Happly | exact Hagrees ].
  - (* Switch *)
    destruct (eval_simple vars scrutinee) as [v | ]; [ | exact I ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
    destruct (find_arm i arms) as [ac | ]; [ | exact I ].
    split; [ reflexivity | exact Hagrees ].
  - exact I.
Qed.

(* The terms of a state bind the known symbols as is known. *)
Definition bound_as_inv : state -> Prop :=
  terms_inv (bound_as known) (handler_bound_as known) (code_bound_as known).

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
  destruct (bound_as (known_bindings e) e) eqn:Hbound; [ | discriminate ].
  intros [= <-]. unfold program_refines.
  apply (simulation_refines (folded_related (known_bindings e))
           (folded_related_step (known_bindings e)
              (known_bindings_have_values e))).
  split; [ reflexivity | ].
  split; [ apply terms_inv_initial; exact Hbound | ].
  intros s allocated allocated' _ [=].
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

Fixpoint fold_known_rename (r : renaming) (statics : static_env) (e : expr)
    {struct e} :
  rename_expr r (fold_known statics e) = fold_known statics (rename_expr r e)
with fold_known_handler_rename (r : renaming) (statics : static_env)
    (h : continuation_handler) {struct h} :
  rename_handler r (fold_known_handler statics h)
  = fold_known_handler statics (rename_handler r h)
with fold_known_binding_rename (r : renaming) (statics : static_env)
    (binding : static_binding) {struct binding} :
  rename_static_binding r (fold_known_binding statics binding)
  = fold_known_binding statics (rename_static_binding r binding)
with fold_known_code_rename (r : renaming) (statics : static_env) (c : code)
    {struct c} :
  rename_code r (fold_known_code statics c)
  = fold_known_code statics (rename_code r c).
Proof.
  - destruct e
      as [ x xkind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl; try reflexivity.
    + rewrite fold_known_named_rename, fold_known_rename. reflexivity.
    + rewrite fold_known_rename. f_equal. rewrite !map_map.
      induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
      rewrite fold_known_binding_rename, IH. reflexivity.
    + rewrite fold_known_handler_rename, fold_known_rename. reflexivity.
    + rewrite fold_known_rename. f_equal. rewrite !map_map.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite fold_known_handler_rename, IH. reflexivity.
  - destruct h as [params metadata handler]. simpl. rewrite fold_known_rename.
    reflexivity.
  - destruct binding as [id c | id | sym const]; simpl; try reflexivity.
    rewrite fold_known_code_rename. reflexivity.
  - destruct c as [params my_closure ret exn metadata body]. simpl.
    rewrite fold_known_rename. reflexivity.
Qed.

Theorem fold_known_equivariant : fold_known_equivariant_statement.
Proof. exact fold_known_rename. Qed.
