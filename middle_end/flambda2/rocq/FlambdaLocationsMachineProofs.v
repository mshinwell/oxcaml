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

(* Proofs of FlambdaLocationsMachineSpec.v. This file needs no review:
   every statement it proves is in the specification. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaNominalSpec FlambdaNominalProofs FlambdaAlphaProofs
  FlambdaNameAbstractionSpec FlambdaNameAbstractionProofs FlambdaHeapSpec
  FlambdaHeapMachineSpec FlambdaLocationsSpec FlambdaLocationsProofs
  FlambdaLocationsPrimitiveSpec FlambdaLocationsPrimitiveProofs
  FlambdaLocationsMachineSpec.
Import ListNotations.

(* ======================================================================== *)
(* What a step is made of commutes with the action                          *)
(* ======================================================================== *)

Definition permute_slots (p : permutation)
    (slots : list (value_slot * value)) : list (value_slot * value) :=
  map (fun slot => (fst slot, permute_value p (snd slot))) slots.

Lemma lookup_permute_slots (p : permutation)
    (slots : list (value_slot * value)) (slot : value_slot) :
  lookup slot (permute_slots p slots)
  = option_map (permute_value p) (lookup slot slots).
Proof. apply lookup_map_values. Qed.

Lemma eval_simple_permuted (p : permutation) (vars : env) (s : simple) :
  eval_simple (permute_env p vars) s
  = option_map (permute_value p) (eval_simple vars s).
Proof.
  destruct s; simpl; [ apply lookup_permute_env | reflexivity | reflexivity ].
Qed.

Lemma eval_simples_permuted (p : permutation) (vars : env)
    (args : list simple) :
  eval_simples (permute_env p vars) args
  = option_map (map (permute_value p)) (eval_simples vars args).
Proof.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite eval_simple_permuted, IH.
  destruct (eval_simple vars s); simpl; [ | reflexivity ].
  destruct (eval_simples vars args); reflexivity.
Qed.

Lemma eval_value_slots_permuted (p : permutation) (vars : env)
    (slots : list (value_slot * simple)) :
  eval_value_slots (permute_env p vars) slots
  = option_map (permute_slots p) (eval_value_slots vars slots).
Proof.
  induction slots as [ | [slot s] slots IH]; simpl; [ reflexivity | ].
  rewrite eval_simple_permuted, IH.
  destruct (eval_simple vars s); simpl; [ | reflexivity ].
  destruct (eval_value_slots vars slots); reflexivity.
Qed.

Lemma closure_of_permuted (p : permutation) (statics : static_env)
    (v : value) :
  closure_of (permute_static_env p statics) (permute_value p v)
  = option_map (fun called => (fst called, permute_slots p (snd called)))
      (closure_of statics v).
Proof.
  destruct v as [c | code slots | fslot decls slots | s | tag fields | c
    | l | callee applied applied_arity];
    simpl; try reflexivity.
  - destruct (lookup fslot decls); reflexivity.
  - rewrite lookup_permute_statics.
    destruct (lookup s (static_values statics))
      as [[code slots | fslot syms decls slots | | | | | ] | ]; simpl;
      try reflexivity.
    destruct (lookup fslot decls); reflexivity.
Qed.

Lemma closure_in_set_permuted (p : permutation) (statics : static_env)
    (v : value) :
  closure_in_set (permute_static_env p statics) (permute_value p v)
  = option_map
      (fun set => (fst (fst set), snd (fst set), permute_slots p (snd set)))
      (closure_in_set statics v).
Proof.
  destruct v as [c | code slots | fslot decls slots | s | tag fields | c
    | l | callee applied applied_arity];
    simpl; try reflexivity.
  - destruct (lookup fslot decls); reflexivity.
  - rewrite lookup_permute_statics.
    destruct (lookup s (static_values statics))
      as [[code slots | fslot syms decls slots | | | | | ] | ]; simpl;
      try reflexivity.
    destruct (lookup fslot decls); reflexivity.
Qed.

Lemma project_value_slot_permuted (p : permutation) (statics : static_env)
    (project_from : function_slot) (slot : value_slot) (v : value) :
  project_value_slot (permute_static_env p statics) project_from slot
    (permute_value p v)
  = option_map (permute_value p)
      (project_value_slot statics project_from slot v).
Proof.
  unfold project_value_slot. rewrite closure_in_set_permuted.
  destruct (closure_in_set statics v) as [[[at_slot decls] slots] | ]; simpl;
    [ | reflexivity ].
  destruct (Pos.eqb at_slot project_from);
    [ apply lookup_permute_slots | reflexivity ].
Qed.

Ltac by_cases :=
  repeat
    first
      [ reflexivity
      | match goal with
        | |- context [match ?x with _ => _ end] => destruct x; simpl
        end ].

Lemma project_function_slot_permuted (p : permutation)
    (statics : static_env) (move_from move_to : function_slot) (v : value) :
  project_function_slot (permute_static_env p statics) move_from move_to
    (permute_value p v)
  = option_map (permute_value p)
      (project_function_slot statics move_from move_to v).
Proof.
  destruct v as [c | code slots | fslot decls slots | s | tag fields | c
    | l | callee applied applied_arity];
    simpl; try reflexivity.
  - by_cases.
  - by_cases.
  - rewrite lookup_permute_statics.
    destruct (lookup s (static_values statics))
      as [[code slots | fslot syms decls slots | | | | | ] | ]; simpl;
      by_cases.
Qed.

Lemma eval_named_permuted (p : permutation) (statics : static_env)
    (vars : env) (d : named) :
  eval_named (permute_static_env p statics) (permute_env p vars) d
  = option_map (permute_value p) (eval_named statics vars d).
Proof.
  destruct d as [s | prim args | code slots | fslot decls slots
    | slot closure | pfrom slot closure | move_from move_to closure];
    simpl.
  - apply eval_simple_permuted.
  - rewrite eval_simples_permuted.
    destruct (eval_simples vars args) as [vs | ]; simpl;
      [ apply eval_prim_permuted | reflexivity ].
  - rewrite eval_value_slots_permuted.
    destruct (eval_value_slots vars slots); reflexivity.
  - destruct (lookup fslot decls); simpl; [ | reflexivity ].
    rewrite eval_value_slots_permuted.
    destruct (eval_value_slots vars slots); reflexivity.
  - rewrite eval_simple_permuted.
    destruct (eval_simple vars closure) as [v | ]; simpl; [ | reflexivity ].
    rewrite closure_of_permuted.
    destruct (closure_of statics v) as [[code slots] | ]; simpl;
      [ apply lookup_permute_slots | reflexivity ].
  - rewrite eval_simple_permuted.
    destruct (eval_simple vars closure) as [v | ]; simpl; [ | reflexivity ].
    apply project_value_slot_permuted.
  - rewrite eval_simple_permuted.
    destruct (eval_simple vars closure) as [v | ]; simpl; [ | reflexivity ].
    apply project_function_slot_permuted.
Qed.

Lemma eval_static_const_permuted (p : permutation) (vars : env)
    (const : static_const) :
  eval_static_const (permute_env p vars) const
  = option_map (permute_static_value p) (eval_static_const vars const).
Proof.
  destruct const as [code slots | fslot syms decls slots | tag fields
    | contents | bytes | elements];
    simpl.
  - rewrite eval_value_slots_permuted.
    destruct (eval_value_slots vars slots); reflexivity.
  - destruct (lookup fslot decls); simpl; [ | reflexivity ].
    rewrite eval_value_slots_permuted.
    destruct (eval_value_slots vars slots); reflexivity.
  - rewrite eval_simples_permuted.
    destruct (eval_simples vars fields); reflexivity.
  - rewrite eval_simple_permuted.
    destruct (eval_simple vars contents); reflexivity.
  - reflexivity.
  - rewrite eval_simples_permuted.
    destruct (eval_simples vars elements); reflexivity.
Qed.

Lemma eval_static_bindings_permuted (p : permutation) (vars : env)
    (bindings : list static_binding) :
  ∀ statics : static_env,
    eval_static_bindings (permute_env p vars) bindings
      (permute_static_env p statics)
    = option_map (permute_static_env p)
        (eval_static_bindings vars bindings statics).
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH];
    intros statics; simpl; [ reflexivity | | apply IH | ].
  - destruct (lookup id (static_code statics)); [ reflexivity | ].
    exact
      (IH (Static_env ((id, c) :: static_code statics)
             (static_values statics))).
  - rewrite lookup_permute_statics.
    destruct (lookup sym (static_values statics)); [ reflexivity | ].
    simpl. rewrite eval_static_const_permuted.
    destruct (eval_static_const vars const) as [allocated | ];
      [ | reflexivity ].
    exact
      (IH (Static_env (static_code statics)
             ((sym, allocated) :: static_values statics))).
Qed.

Lemma bind_params_permuted (p : permutation) (params : list variable) :
  ∀ (vs : list value) (vars : env),
    bind_params params (map (permute_value p) vs) (permute_env p vars)
    = option_map (permute_env p) (bind_params params vs vars).
Proof.
  induction params as [ | x params IH]; intros [ | v vs] vars; simpl;
    try reflexivity.
  exact (IH vs ((x, v) :: vars)).
Qed.

Lemma lookup_permute_cont_env (p : permutation) (k : continuation)
    (conts : cont_env) :
  lookup k (permute_cont_env p conts)
  = option_map (permute_cont_value p) (lookup k conts).
Proof. apply lookup_map_values. Qed.

Lemma resolve_permuted (p : permutation) (k : continuation)
    (conts : cont_env) :
  resolve k (permute_cont_env p conts)
  = permute_cont_value p (resolve k conts).
Proof.
  unfold resolve. rewrite lookup_permute_cont_env.
  destruct (lookup k conts); reflexivity.
Qed.

Lemma permute_cont_env_app (p : permutation) (conts conts' : cont_env) :
  permute_cont_env p (conts ++ conts')
  = permute_cont_env p conts ++ permute_cont_env p conts'.
Proof. apply map_app. Qed.

Lemma rec_closures_permuted (p : permutation)
    (handlers : list (continuation * continuation_handler)) (vars : env)
    (conts : cont_env) :
  rec_closures handlers (permute_env p vars) (permute_cont_env p conts)
  = permute_cont_env p (rec_closures handlers vars conts).
Proof.
  unfold rec_closures, permute_cont_env. rewrite map_map. apply map_ext.
  intros [k h]. reflexivity.
Qed.

Lemma kinds_permuted (p : permutation) (vs : list value) :
  map kind_of_value (map (permute_value p) vs) = map kind_of_value vs.
Proof.
  rewrite map_map. apply map_ext. intros v. apply kind_of_permute_value.
Qed.

Lemma call_code_permuted (p : permutation) (closure : value) (c : code)
    (vs : list value) (args_arity return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) (hp : heap) :
  call_code (permute_value p closure) c (map (permute_value p) vs)
    args_arity return_arity (permute_cont_value p return_to)
    (permute_cont_value p exn_to) (permute_static_env p statics)
    (permute_heap p hp)
  = permute_result p
      (call_code closure c vs args_arity return_arity return_to exn_to
         statics hp).
Proof.
  unfold call_code. destruct (binds_statics (code_body c)); [ reflexivity | ].
  rewrite kinds_permuted. destruct (negb _); [ reflexivity | ].
  change [(code_my_closure c, permute_value p closure)]
    with (permute_env p [(code_my_closure c, closure)]).
  rewrite bind_params_permuted.
  destruct (bind_params (code_params c) vs [(code_my_closure c, closure)]);
    reflexivity.
Qed.

Lemma tuple_fields_from_permuted (p : permutation) (statics : static_env)
    (size : nat) (tuple : value) (count : nat) :
  ∀ field : nat,
    tuple_fields_from (permute_static_env p statics) size
      (permute_value p tuple) field count
    = option_map (map (permute_value p))
        (tuple_fields_from statics size tuple field count).
Proof.
  induction count as [ | count IH]; intros field; simpl; [ reflexivity | ].
  change [permute_value p tuple] with (map (permute_value p) [tuple]).
  rewrite eval_prim_permuted, IH.
  destruct (eval_prim statics _ [tuple]); simpl; [ | reflexivity ].
  destruct (tuple_fields_from statics size tuple (S field) count);
    reflexivity.
Qed.

Definition permute_arguments (p : permutation)
    (arguments : list value * arity) : list value * arity :=
  (map (permute_value p) (fst arguments), snd arguments).

Lemma detuple_permuted (p : permutation) (statics : static_env) (size : nat)
    (vs : list value) (args_arity : arity) :
  detuple (permute_static_env p statics) size (map (permute_value p) vs)
    args_arity
  = option_map (permute_arguments p) (detuple statics size vs args_arity).
Proof.
  unfold detuple.
  destruct vs as [ | tuple rest]; [ reflexivity | ].
  destruct args_arity as [ | first rest_arity]; [ reflexivity | ].
  rewrite kinds_permuted. cbn [map]. destruct (negb _); [ reflexivity | ].
  unfold tuple_fields. rewrite tuple_fields_from_permuted.
  destruct (tuple_fields_from statics size tuple 0 size) as [fields | ];
    simpl; [ | reflexivity ].
  unfold permute_arguments. simpl. rewrite map_app. reflexivity.
Qed.

Lemma arguments_for_code_permuted (p : permutation) (statics : static_env)
    (c : code) (vs : list value) (args_arity : arity) :
  arguments_for_code (permute_static_env p statics) c
    (map (permute_value p) vs) args_arity
  = option_map (permute_arguments p)
      (arguments_for_code statics c vs args_arity).
Proof.
  unfold arguments_for_code.
  destruct (code_is_tupled c); [ apply detuple_permuted | reflexivity ].
Qed.

(* What a call is, with its values moved. *)
Definition permute_shape (p : permutation) (shape : call_shape)
    : call_shape :=
  match shape with
  | Full_call closure c vs args_arity =>
    Full_call (permute_value p closure) c (map (permute_value p) vs)
      args_arity
  | Over_call closure c vs remaining args_arity remaining_arity =>
    Over_call (permute_value p closure) c (map (permute_value p) vs)
      (map (permute_value p) remaining) args_arity remaining_arity
  | Partial_call partial => Partial_call (permute_value p partial)
  end.

Lemma shape_of_code_call_permuted (p : permutation) (closure : value)
    (c : code) (vs : list value) (args_arity return_arity : arity) :
  shape_of_code_call (permute_value p closure) c (map (permute_value p) vs)
    args_arity return_arity
  = option_map (permute_shape p)
      (shape_of_code_call closure c vs args_arity return_arity).
Proof.
  unfold shape_of_code_call. cbv zeta.
  destruct (Nat.eqb _ _); [ reflexivity | ].
  rewrite kinds_permuted. destruct (negb _); [ reflexivity | ].
  destruct (Nat.ltb _ _).
  - simpl. rewrite firstn_map, skipn_map. reflexivity.
  - destruct (code_is_tupled c); reflexivity.
Qed.

Lemma shape_of_closure_call_permuted (p : permutation)
    (statics : static_env) (closure : value) (kind : call_kind)
    (vs : list value) (args_arity return_arity : arity) :
  shape_of_closure_call (permute_static_env p statics)
    (permute_value p closure) kind (map (permute_value p) vs) args_arity
    return_arity
  = option_map (permute_shape p)
      (shape_of_closure_call statics closure kind vs args_arity
         return_arity).
Proof.
  unfold shape_of_closure_call. rewrite closure_of_permuted.
  destruct (closure_of statics closure) as [[called slots] | ]; simpl;
    [ | reflexivity ].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | reflexivity ].
  destruct (lookup called (static_code statics)) as [c | ];
    [ | reflexivity ].
  rewrite arguments_for_code_permuted.
  destruct (arguments_for_code statics c vs args_arity)
    as [[vs' args_arity'] | ]; simpl; [ | reflexivity ].
  apply shape_of_code_call_permuted.
Qed.

Lemma shape_of_call_permuted (p : permutation) (statics : static_env)
    (callee : value) (kind : call_kind) (vs : list value)
    (args_arity return_arity : arity) :
  shape_of_call (permute_static_env p statics) (permute_value p callee) kind
    (map (permute_value p) vs) args_arity return_arity
  = option_map (permute_shape p)
      (shape_of_call statics callee kind vs args_arity return_arity).
Proof.
  unfold shape_of_call.
  destruct kind as [named | ]; [ apply shape_of_closure_call_permuted | ].
  destruct (partial_application_of callee)
    as [[[closure applied] applied_arity] | ] eqn:Hpartial.
  - destruct callee; try discriminate. injection Hpartial as -> -> ->.
    simpl. destruct args_arity; [ reflexivity | ].
    rewrite kinds_permuted. destruct (kinds_eqb _ _); [ | reflexivity ].
    rewrite <- map_app. apply shape_of_closure_call_permuted.
  - replace (partial_application_of (permute_value p callee))
      with (@None (value * list value * arity))
      by (destruct callee; try reflexivity; discriminate).
    apply shape_of_closure_call_permuted.
Qed.

Lemma run_call_permuted (p : permutation)
    (return_partial return_partial' : value -> step_result)
    (shape : option call_shape) (return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) (hp : heap) :
  (∀ partial : value,
    return_partial' (permute_value p partial)
    = permute_result p (return_partial partial)) ->
  run_call return_partial' (option_map (permute_shape p) shape) return_arity
    (permute_cont_value p return_to) (permute_cont_value p exn_to)
    (permute_static_env p statics) (permute_heap p hp)
  = permute_result p
      (run_call return_partial shape return_arity return_to exn_to statics
         hp).
Proof.
  intros Hpartial.
  destruct shape
    as [[closure c vs args_arity
        | closure c vs remaining args_arity remaining_arity | partial] | ];
    simpl.
  - apply call_code_permuted.
  - exact
      (call_code_permuted p closure c vs args_arity (code_result_arity c)
         (Over_application remaining remaining_arity return_arity return_to
            exn_to)
         exn_to statics hp).
  - apply Hpartial.
  - reflexivity.
Qed.

Lemma apply_cont_value_permuted (p : permutation) (c : cont_value) :
  ∀ (vs : list value) (statics : static_env) (hp : heap),
    apply_cont_value (permute_cont_value p c) (map (permute_value p) vs)
      (permute_static_env p statics) (permute_heap p hp)
    = permute_result p (apply_cont_value c vs statics hp).
Proof.
  induction c
    as [[params metadata handler] def_vars def_conts recursive | k
       | c IH extra
       | remaining remaining_arity return_arity return_to exn_to IHreturn _]
    using cont_value_over_ind;
    intros vs statics hp.
  - simpl. rewrite kinds_permuted.
    destruct (kinds_eqb (map kind_of_value vs) (hm_params_kinds metadata));
      [ | reflexivity ].
    rewrite bind_params_permuted.
    destruct (bind_params params vs def_vars) as [handler_vars | ]; simpl;
      [ | reflexivity ].
    unfold permute_state. simpl_state.
    rewrite permute_cont_env_app, <- rec_closures_permuted. reflexivity.
  - reflexivity.
  - simpl. rewrite <- map_app. apply IH.
  - destruct vs as [ | v [ | v' vs]]; try reflexivity.
    cbn [permute_cont_value apply_cont_value map].
    rewrite shape_of_call_permuted.
    apply run_call_permuted. intros partial.
    exact (IHreturn [partial] statics hp).
Qed.

Lemma with_extra_args_permuted (p : permutation) (c : cont_value)
    (extra : list value) :
  with_extra_args (permute_cont_value p c) (map (permute_value p) extra)
  = permute_cont_value p (with_extra_args c extra).
Proof. destruct extra; reflexivity. Qed.

Lemma call_function_permuted (p : permutation) (callee : value)
    (kind : call_kind) (vs : list value) (args_arity return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) (hp : heap) :
  call_function (permute_value p callee) kind (map (permute_value p) vs)
    args_arity return_arity (permute_cont_value p return_to)
    (permute_cont_value p exn_to) (permute_static_env p statics)
    (permute_heap p hp)
  = permute_result p
      (call_function callee kind vs args_arity return_arity return_to exn_to
         statics hp).
Proof.
  unfold call_function. rewrite shape_of_call_permuted.
  apply run_call_permuted. intros partial.
  exact (apply_cont_value_permuted p return_to [partial] statics hp).
Qed.

Lemma naked_immediate_of_permute_value (p : permutation) (v : value) :
  naked_immediate_of_value (permute_value p v) = naked_immediate_of_value v.
Proof. destruct v; reflexivity. Qed.

(* ======================================================================== *)
(* A step that does not allocate                                            *)
(* ======================================================================== *)

(* Today no step allocates, and this is an equation of every state. *)
Lemma step_permuted_exactly (p : permutation) (s : state) :
  step (permute_state p s) = permute_result p (step s).
Proof.
  rewrite (state_eta s). unfold permute_state. simpl_state.
  destruct (state_expr s)
    as [ x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    autorewrite with step.
  - (* Let *)
    rewrite eval_named_permuted.
    destruct (eval_named (state_statics s) (state_vars s) d) as [v | ];
      simpl; [ | reflexivity ].
    rewrite kind_of_permute_value.
    destruct (kind_eqb (kind_of_value v) kind); reflexivity.
  - (* Let_static *)
    rewrite eval_static_bindings_permuted.
    destruct
      (eval_static_bindings (state_vars s) bindings (state_statics s));
      reflexivity.
  - (* Let_cont_non_recursive *)
    reflexivity.
  - (* Let_cont_recursive *)
    destruct (handlers_bind_statics handlers); [ reflexivity | ].
    rewrite rec_closures_permuted, <- permute_cont_env_app. reflexivity.
  - (* Apply *)
    rewrite eval_simple_permuted, !eval_simples_permuted.
    destruct (eval_simple (state_vars s) (ap_callee ap)) as [callee | ];
      simpl; [ | reflexivity ].
    destruct (eval_simples (state_vars s) (ap_args ap)) as [vs | ]; simpl;
      [ | reflexivity ].
    destruct (eval_simples (state_vars s) (exn_extra_simples ap))
      as [extra | ]; simpl;
      [ | reflexivity ].
    rewrite !resolve_permuted, with_extra_args_permuted.
    apply call_function_permuted.
  - (* Apply_cont *)
    rewrite eval_simples_permuted.
    destruct (eval_simples (state_vars s) (ac_args ac)) as [vs | ]; simpl;
      [ | reflexivity ].
    unfold apply_continuation. rewrite resolve_permuted.
    apply apply_cont_value_permuted.
  - (* Switch *)
    rewrite eval_simple_permuted.
    destruct (eval_simple (state_vars s) scrutinee) as [v | ]; simpl;
      [ | reflexivity ].
    rewrite naked_immediate_of_permute_value.
    destruct (naked_immediate_of_value v) as [i | ]; [ | reflexivity ].
    destruct (find_arm i arms); reflexivity.
  - (* Invalid *)
    reflexivity.
Qed.

(* ======================================================================== *)
(* What an equivariant function makes holds no new name                     *)
(* ======================================================================== *)

(* The names of the value of an equivariant function are among those of
   its argument: a name that is in the value and not in the argument
   could be exchanged for a fresh one, which would change the value
   and not the argument. *)
Lemma equivariant_support {A B : Type} (actA : permutation -> A -> A)
    (namesA : A -> list positive) (actB : permutation -> B -> B)
    (namesB : B -> list positive) (f : A -> option B) :
  action_laws actA namesA ->
  action_laws actB namesB ->
  (∀ (p : permutation) (a : A), f (actA p a) = option_map (actB p) (f a)) ->
  ∀ (a : A) (b : B) (name : positive),
    f a = Some b -> name ∈ namesB b -> name ∈ namesA a.
Proof.
  intros HA HB Hf a b name Hfa Hname.
  destruct (in_dec Pos.eq_dec name (namesA a)) as [Hin | Hout];
    [ exact Hin | exfalso ].
  set (other := fresh_name (name :: namesA a ++ namesB b)).
  assert (Hother : ¬ other ∈ (name :: namesA a ++ namesB b)).
  { intros Hin. apply among_In in Hin. unfold other in Hin.
    rewrite fresh_name_fresh in Hin. discriminate. }
  set (p := [(name, other)]).
  assert (Hfixed : actA p a = a).
  { rewrite <- (act_identity _ _ HA a) at 2. apply (act_ext _ _ HA).
    intros x Hx. simpl. apply swap_other; intros ->.
    - exact (Hout Hx).
    - apply Hother. right. apply in_or_app. left. exact Hx. }
  pose proof (Hf p a) as Hmoved. rewrite Hfixed, Hfa in Hmoved.
  simpl in Hmoved. injection Hmoved as Hb.
  pose proof (act_names _ _ HB p b) as Hnames. rewrite <- Hb in Hnames.
  apply Hother. right. apply in_or_app. right. rewrite Hnames.
  apply in_map_iff. exists name.
  split; [ simpl; apply swap_first | exact Hname ].
Qed.

(* ======================================================================== *)
(* What a step comes to, as a thing that holds locations                    *)
(* ======================================================================== *)

Definition locations_of_result (result : step_result) : list location :=
  match result with
  | Step s => locations_of_state s
  | Exit _ vs hp => locations_of_values vs ++ locations_of_heap hp
  | Undefined => []
  end.

Lemma result_laws : action_laws permute_result locations_of_result.
Proof.
  pose proof state_laws as Hstate. pose proof values_laws as Hvalues.
  pose proof heap_laws as Hheap.
  constructor.
  - intros [s | k vs hp | ]; simpl; [ | | reflexivity ].
    + rewrite (act_identity _ _ Hstate). reflexivity.
    + rewrite (act_identity _ _ Hvalues vs), (act_identity _ _ Hheap).
      reflexivity.
  - intros second first [s | k vs hp | ]; simpl; [ | | reflexivity ].
    + rewrite (act_compose _ _ Hstate). reflexivity.
    + rewrite (act_compose _ _ Hvalues second first vs),
        (act_compose _ _ Hheap).
      reflexivity.
  - intros p [s | k vs hp | ]; simpl; [ | | reflexivity ].
    + apply (act_names _ _ Hstate).
    + rewrite map_app. unfold locations_of_values.
      rewrite (act_names _ _ Hvalues p vs), (act_names _ _ Hheap).
      reflexivity.
  - intros p p' [s | k vs hp | ] Hagree; simpl; [ | | reflexivity ].
    + rewrite (act_ext _ _ Hstate p p' s Hagree). reflexivity.
    + simpl in Hagree.
      rewrite (act_ext _ _ Hvalues p p' vs),
        (act_ext _ _ Hheap p p' hp);
        [ reflexivity | | ];
        intros name Hname; apply Hagree, in_or_app; auto.
Qed.

(* ======================================================================== *)
(* A step leaves the heap as it is                                          *)
(* ======================================================================== *)

Definition result_heap_is (hp : heap) (result : step_result) : Prop :=
  match result with
  | Step s => state_heap s = hp
  | Exit _ _ hp' => hp' = hp
  | Undefined => True
  end.

Lemma call_code_heap (closure : value) (c : code) (vs : list value)
    (args_arity return_arity : arity) (return_to exn_to : cont_value)
    (statics : static_env) (hp : heap) :
  result_heap_is hp
    (call_code closure c vs args_arity return_arity return_to exn_to statics
       hp).
Proof.
  unfold call_code. destruct (binds_statics (code_body c)); [ exact I | ].
  destruct (negb _); [ exact I | ].
  destruct (bind_params (code_params c) vs [(code_my_closure c, closure)]);
    [ reflexivity | exact I ].
Qed.

Lemma run_call_heap (return_partial : value -> step_result)
    (shape : option call_shape) (return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) (hp : heap) :
  (∀ partial : value, result_heap_is hp (return_partial partial)) ->
  result_heap_is hp
    (run_call return_partial shape return_arity return_to exn_to statics hp).
Proof.
  intros Hpartial.
  destruct shape
    as [[closure c vs args_arity
        | closure c vs remaining args_arity remaining_arity | partial] | ];
    simpl;
    [ apply call_code_heap | apply call_code_heap | apply Hpartial
    | exact I ].
Qed.

Lemma apply_cont_value_heap (c : cont_value) :
  ∀ (vs : list value) (statics : static_env) (hp : heap),
    result_heap_is hp (apply_cont_value c vs statics hp).
Proof.
  induction c
    as [[params metadata handler] def_vars def_conts recursive | k
       | c IH extra
       | remaining remaining_arity return_arity return_to exn_to IHreturn _]
    using cont_value_over_ind;
    intros vs statics hp.
  - simpl.
    destruct (kinds_eqb (map kind_of_value vs) (hm_params_kinds metadata));
      [ | exact I ].
    destruct (bind_params params vs def_vars); [ reflexivity | exact I ].
  - reflexivity.
  - simpl. apply IH.
  - destruct vs as [ | v [ | v' vs]]; try exact I.
    cbn [apply_cont_value]. apply run_call_heap. intros partial.
    apply IHreturn.
Qed.

Lemma step_heap (s : state) : result_heap_is (state_heap s) (step s).
Proof.
  rewrite (state_eta s) at 2.
  destruct (state_expr s)
    as [ x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    autorewrite with step.
  - destruct (eval_named (state_statics s) (state_vars s) d) as [v | ];
      [ | exact I ].
    destruct (kind_eqb (kind_of_value v) kind); [ reflexivity | exact I ].
  - destruct
      (eval_static_bindings (state_vars s) bindings (state_statics s));
      [ reflexivity | exact I ].
  - reflexivity.
  - destruct (handlers_bind_statics handlers); [ exact I | reflexivity ].
  - destruct (eval_simple (state_vars s) (ap_callee ap)) as [callee | ];
      [ | exact I ].
    destruct (eval_simples (state_vars s) (ap_args ap)) as [vs | ];
      [ | exact I ].
    destruct (eval_simples (state_vars s) (exn_extra_simples ap))
      as [extra | ];
      [ | exact I ].
    unfold call_function. apply run_call_heap. intros partial.
    apply apply_cont_value_heap.
  - destruct (eval_simples (state_vars s) (ac_args ac)) as [vs | ];
      [ | exact I ].
    apply apply_cont_value_heap.
  - destruct (eval_simple (state_vars s) scrutinee) as [v | ];
      [ | exact I ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
    destruct (find_arm i arms); [ reflexivity | exact I ].
  - exact I.
Qed.

(* ======================================================================== *)
(* The premise                                                              *)
(* ======================================================================== *)

Theorem no_location_bound : no_location_bound_statement.
Proof.
  intros s Hnone l Hl. rewrite Hnone in Hl. destruct Hl.
Qed.

Theorem permute_state_locations_bound :
  permute_state_locations_bound_statement.
Proof.
  intros p s Hbound l Hl. unfold state_locations_bound in Hbound.
  rewrite (act_names _ _ state_laws) in Hl.
  apply in_map_iff in Hl as (l0 & <- & Hl0).
  change (state_heap (permute_state p s)) with (permute_heap p (state_heap s)).
  rewrite is_bound_permute_heap. exact (Hbound l0 Hl0).
Qed.

Theorem step_keeps_locations_bound : step_keeps_locations_bound_statement.
Proof.
  intros s Hbound.
  assert (Hsupport :
            ∀ l : location,
              l ∈ locations_of_result (step s) -> l ∈ locations_of_state s).
  { intros l Hl.
    exact
      (equivariant_support permute_state locations_of_state permute_result
         locations_of_result (fun s0 => Some (step s0)) state_laws
         result_laws
         (fun p s0 => f_equal Some (step_permuted_exactly p s0)) s (step s)
         l eq_refl Hl). }
  pose proof (step_heap s) as Hheap.
  destruct (step s) as [s' | k vs hp | ]; simpl in *; [ | | exact I ].
  - split.
    + intros l Hl. unfold state_locations_bound. rewrite Hheap.
      exact (Hbound l (Hsupport l Hl)).
    + intros l Hl. rewrite Hheap. exact Hl.
  - subst hp. split; [ | split ].
    + intros l Hl. apply Hbound, Hsupport, in_or_app. right. exact Hl.
    + intros l Hl. apply Hbound, Hsupport, in_or_app. left. exact Hl.
    + intros l Hl. exact Hl.
Qed.

Theorem run_keeps_locations_bound : run_keeps_locations_bound_statement.
Proof.
  intros fuel. induction fuel as [ | fuel IH]; intros s Hbound; simpl.
  - split; [ exact Hbound | intros l Hl; exact Hl ].
  - pose proof (step_keeps_locations_bound s Hbound) as Hstep.
    destruct (step s) as [s' | k vs hp | ]; simpl in Hstep;
      [ | exact Hstep | exact I ].
    destruct Hstep as [Hbound' Hkept].
    specialize (IH s' Hbound').
    destruct (run fuel s') as [s'' | k vs hp | ]; simpl in IH |- *;
      [ | | exact I ].
    + destruct IH as [Hbound'' Hkept'].
      split; [ exact Hbound'' | intros l Hl; exact (Hkept' l (Hkept l Hl)) ].
    + destruct IH as (Hhp & Hvs & Hkept').
      split; [ exact Hhp | ].
      split; [ exact Hvs | intros l Hl; exact (Hkept' l (Hkept l Hl)) ].
Qed.

(* ======================================================================== *)
(* A step, a run and a behaviour                                            *)
(* ======================================================================== *)

Theorem step_permuted : step_permuted_statement.
Proof.
  intros p s _. exists p.
  split; [ reflexivity | apply step_permuted_exactly ].
Qed.

Theorem run_permuted : run_permuted_statement.
Proof.
  intros p fuel. revert p.
  induction fuel as [ | fuel IH]; intros p s Hbound; simpl.
  - exists p. split; reflexivity.
  - destruct (step_permuted p s Hbound) as (p1 & Hagree1 & Hstep).
    rewrite Hstep.
    pose proof (step_keeps_locations_bound s Hbound) as Hkeeps.
    destruct (step s) as [s' | k vs hp | ]; simpl in Hkeeps |- *.
    + destruct Hkeeps as [Hbound' Hkept].
      destruct (IH p1 s' Hbound') as (p2 & Hagree2 & Hrun).
      exists p2. split; [ | exact Hrun ].
      intros l Hl. rewrite (Hagree2 l (Hkept l Hl)). exact (Hagree1 l Hl).
    + exists p1. split; [ exact Hagree1 | reflexivity ].
    + exists p1. split; [ exact Hagree1 | reflexivity ].
Qed.

Theorem behaves_permuted : behaves_permuted_statement.
Proof.
  intros p s [k vs hp | | ] Hbound Hbehaves; simpl in Hbehaves.
  - destruct Hbehaves as [fuel Hrun].
    destruct (run_permuted p fuel s Hbound) as (p' & Hagree & Hmoved).
    exists p'. split; [ exact Hagree | ].
    exists fuel. rewrite Hmoved, Hrun. reflexivity.
  - destruct Hbehaves as [fuel Hrun].
    destruct (run_permuted p fuel s Hbound) as (p' & Hagree & Hmoved).
    exists p'. split; [ exact Hagree | ].
    exists fuel. rewrite Hmoved, Hrun. reflexivity.
  - exists p. split; [ reflexivity | ].
    intros fuel. destruct (Hbehaves fuel) as [s' Hrun].
    destruct (run_permuted p fuel s Hbound) as (p' & _ & Hmoved).
    exists (permute_state p' s'). rewrite Hmoved, Hrun. reflexivity.
Qed.

(* ======================================================================== *)
(* What a [Let] is to run                                                   *)
(* ======================================================================== *)

Lemma eval_simples_locations (vars : env) (args : list simple)
    (vs : list value) (l : location) :
  eval_simples vars args = Some vs ->
  l ∈ locations_of_values vs ->
  l ∈ locations_of_env vars.
Proof.
  intros Heval Hl.
  exact
    (equivariant_support permute_env locations_of_env
       (fun p => map (permute_value p)) locations_of_values
       (fun vars0 => eval_simples vars0 args) env_laws values_laws
       (fun p vars0 => eval_simples_permuted p vars0 args) vars vs l Heval
       Hl).
Qed.

Lemma eval_named_locations (statics : static_env) (vars : env) (d : named)
    (v : value) (l : location) :
  eval_named statics vars d = Some v ->
  l ∈ locations_of_value v ->
  l ∈ locations_of_static_env statics ++ locations_of_env vars.
Proof.
  intros Heval Hl.
  exact
    (equivariant_support
       (fun p (a : static_env * env) =>
          (permute_static_env p (fst a), permute_env p (snd a)))
       (fun a => locations_of_static_env (fst a) ++ locations_of_env (snd a))
       permute_value locations_of_value
       (fun a => eval_named (fst a) (snd a) d)
       (laws_of_pair _ _ _ _ static_env_laws env_laws) value_laws
       (fun p a => eval_named_permuted p (fst a) (snd a) d) (statics, vars)
       v l Heval Hl).
Qed.

Theorem heap_exec_named_permuted : heap_exec_named_permuted_statement.
Proof.
  intros p statics h vars d Hheap Hvars.
  destruct d as [s | prim args | code slots | fslot decls slots
    | slot closure | pfrom slot closure | move_from move_to closure];
    try
      (exists p; split; [ reflexivity | ]; unfold heap_exec_named;
       rewrite eval_named_permuted;
       match goal with
       | |- context [eval_named statics vars ?d] =>
         destruct (eval_named statics vars d)
       end;
       reflexivity).
  unfold heap_exec_named. rewrite eval_simples_permuted.
  destruct (eval_simples vars args) as [vs | ] eqn:Hargs; simpl.
  - apply exec_prim_permuted; [ exact Hheap | ].
    intros l Hl. apply Hvars.
    exact (eval_simples_locations vars args vs l Hargs Hl).
  - exists p. split; reflexivity.
Qed.

Theorem heap_exec_named_keeps_locations_bound :
  heap_exec_named_keeps_locations_bound_statement.
Proof.
  intros statics h h' vars d v Hheap Hvars Hstatics Hexec.
  destruct d as [s | prim args | code slots | fslot decls slots
    | slot closure | pfrom slot closure | move_from move_to closure];
    try
      (unfold heap_exec_named in Hexec;
       match type of Hexec with
       | context [eval_named statics vars ?d] =>
         destruct (eval_named statics vars d) as [v0 | ] eqn:Heval;
         [ | discriminate ]
       end;
       injection Hexec as <- <-;
       split; [ exact Hheap | ];
       split; [ | intros l Hl; exact Hl ];
       intros l Hl;
       destruct
         (in_app_or _ _ _
            (eval_named_locations statics vars _ v0 l Heval Hl))
         as [Hin | Hin];
       [ exact (Hstatics l Hin) | exact (Hvars l Hin) ]).
  unfold heap_exec_named in Hexec.
  destruct (eval_simples vars args) as [vs | ] eqn:Hargs; [ | discriminate ].
  apply (exec_prim_keeps_locations_bound statics h h' prim vs v Hheap);
    [ | exact Hstatics | exact Hexec ].
  intros l Hl. apply Hvars.
  exact (eval_simples_locations vars args vs l Hargs Hl).
Qed.
