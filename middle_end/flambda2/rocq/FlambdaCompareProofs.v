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

(* Proofs of the statements of FlambdaCompareSpec.v. Nothing here needs
   review.

   Two expressions that [expr_eqb] accepts under some pairs of names, run
   under environments that give paired names the same things, stay in step
   ([matched_step]): a bisimulation
   (FlambdaSemanticsProofs.bisimulation_equivalent). The values of the two
   runs are the same; the continuation closures and the code are not, as
   their bound names differ, so those are related ([cont_matches],
   [statics_match]). The runs start under one pair of environments, which
   needs [expr_eqb] to be reflexive ([expr_eqb_refl]). *)

From Stdlib Require Import ZArith List Bool Arith.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaCompareSpec.
Import ListNotations.

(* ======================================================================== *)
(* Names                                                                    *)
(* ======================================================================== *)

Lemma names_match_nil (a a' : positive) : names_match [] a a' = true -> a = a'.
Proof. apply Pos.eqb_eq. Qed.

Definition reflexive_map (m : name_map) : Prop :=
  ∀ a : positive, names_match m a a = true.

Lemma reflexive_map_nil : reflexive_map [].
Proof. intros a. apply Pos.eqb_refl. Qed.

Lemma reflexive_map_cons (m : name_map) (b : positive) :
  reflexive_map m -> reflexive_map ((b, b) :: m).
Proof.
  intros Hm a. simpl. destruct (Pos.eqb a b); [ reflexivity | apply Hm ].
Qed.

Lemma bind_names_refl (xs : list positive) :
  ∀ m : name_map,
    reflexive_map m ->
    ∃ m' : name_map, bind_names xs xs m = Some m' ∧ reflexive_map m'.
Proof.
  induction xs as [ | x xs IH]; intros m Hm; simpl; [ eauto | ].
  apply IH, reflexive_map_cons, Hm.
Qed.

Lemma combine_names_refl (xs : list positive) (m : name_map) :
  reflexive_map m ->
  ∃ m' : name_map, combine_names xs xs m = Some m' ∧ reflexive_map m'.
Proof.
  intros Hm. unfold combine_names. rewrite Nat.eqb_refl.
  eexists. split; [ reflexivity | ].
  induction xs as [ | x xs IH]; simpl; [ exact Hm | ].
  apply reflexive_map_cons, IH.
Qed.

(* ======================================================================== *)
(* The comparison is reflexive                                              *)
(* ======================================================================== *)

Lemma forall2b_refl {A : Type} (f : A -> A -> bool) (l : list A) :
  (∀ a : A, f a a = true) -> forall2b f l l = true.
Proof.
  intros Hf. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hf, IH. reflexivity.
Qed.

Lemma const_eqb_refl (c : const) : const_eqb c c = true.
Proof. unfold const_eqb. destruct (const_eq_dec c c); congruence. Qed.

Lemma simple_eqb_refl (vm : name_map) (s : simple) :
  reflexive_map vm -> simple_eqb vm s s = true.
Proof.
  intros Hvm. destruct s as [x | sym | c]; simpl;
    [ apply Hvm | apply Pos.eqb_refl | apply const_eqb_refl ].
Qed.

Lemma simples_eqb_refl (vm : name_map) (args : list simple) :
  reflexive_map vm -> simples_eqb vm args args = true.
Proof.
  intros Hvm. apply forall2b_refl. intros s. apply simple_eqb_refl, Hvm.
Qed.

Lemma value_slots_eqb_refl (vm : name_map)
    (slots : list (value_slot * simple)) :
  reflexive_map vm -> value_slots_eqb vm slots slots = true.
Proof.
  intros Hvm. apply forall2b_refl. intros slot.
  rewrite Pos.eqb_refl, simple_eqb_refl; [ reflexivity | exact Hvm ].
Qed.

Lemma named_eqb_refl (vm : name_map) (d : named) :
  reflexive_map vm -> named_eqb vm d d = true.
Proof.
  intros Hvm. destruct d as [s | p args | code slots | slot closure]; simpl;
    rewrite ?prim_eqb_refl, ?Pos.eqb_refl, ?simple_eqb_refl,
      ?simples_eqb_refl, ?value_slots_eqb_refl;
    auto.
Qed.

Lemma static_const_eqb_refl (vm : name_map) (const : static_const) :
  reflexive_map vm -> static_const_eqb vm const const = true.
Proof.
  intros Hvm. destruct const as [code slots | tag fields | s | bytes]; simpl;
    rewrite ?Pos.eqb_refl, ?Z.eqb_refl, ?simple_eqb_refl, ?simples_eqb_refl,
      ?value_slots_eqb_refl;
    auto.
  apply forall2b_refl, Z.eqb_refl.
Qed.

Lemma apply_cont_eqb_refl (vm km : name_map) (ac : apply_cont) :
  reflexive_map vm -> reflexive_map km -> apply_cont_eqb vm km ac ac = true.
Proof.
  intros Hvm Hkm. unfold apply_cont_eqb.
  rewrite Hkm, simples_eqb_refl; [ reflexivity | exact Hvm ].
Qed.

Lemma apply_eqb_refl (vm km : name_map) (ap : apply_expr) :
  reflexive_map vm -> reflexive_map km -> apply_eqb vm km ap ap = true.
Proof.
  intros Hvm Hkm. unfold apply_eqb.
  rewrite !Hkm, simple_eqb_refl, simples_eqb_refl by exact Hvm.
  destruct (ap_call_kind ap); simpl; rewrite ?Pos.eqb_refl; reflexivity.
Qed.

Fixpoint expr_eqb_refl (e : expr) :
  ∀ vm km : name_map,
    reflexive_map vm -> reflexive_map km -> expr_eqb vm km e e = true
with handler_eqb_refl (h : continuation_handler) :
  ∀ vm km : name_map,
    reflexive_map vm -> reflexive_map km -> handler_eqb vm km h h = true
with binding_eqb_refl (binding : static_binding) :
  ∀ vm : name_map, reflexive_map vm -> binding_eqb vm binding binding = true
with code_eqb_refl (c : code) : code_eqb c c = true.
Proof.
  - destruct e
      as [ x d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros vm km Hvm Hkm; simpl.
    + rewrite named_eqb_refl by exact Hvm.
      apply expr_eqb_refl; [ apply reflexive_map_cons, Hvm | exact Hkm ].
    + rewrite (expr_eqb_refl body vm km Hvm Hkm), andb_true_r.
      induction bindings as [ | binding bindings IH]; simpl; [ reflexivity | ].
      rewrite (binding_eqb_refl binding vm Hvm), IH. reflexivity.
    + rewrite (handler_eqb_refl h vm km Hvm Hkm).
      apply expr_eqb_refl; [ exact Hvm | apply reflexive_map_cons, Hkm ].
    + destruct (combine_names_refl (map fst handlers) km Hkm)
        as (km' & -> & Hkm').
      rewrite (expr_eqb_refl body vm km' Hvm Hkm'), andb_true_r.
      clear Hkm. induction handlers as [ | [k h] handlers IH]; simpl;
        [ reflexivity | ].
      rewrite (handler_eqb_refl h vm km' Hvm Hkm'), IH. reflexivity.
    + apply apply_eqb_refl; assumption.
    + apply apply_cont_eqb_refl; assumption.
    + rewrite simple_eqb_refl by exact Hvm. apply forall2b_refl. intros arm.
      rewrite Z.eqb_refl, apply_cont_eqb_refl; auto.
    + reflexivity.
  - destruct h as [params handler]. intros vm km Hvm Hkm. simpl.
    destruct (bind_names_refl params vm Hvm) as (vm' & -> & Hvm').
    apply expr_eqb_refl; assumption.
  - destruct binding as [id c | id | sym const]; intros vm Hvm; simpl.
    + rewrite Pos.eqb_refl, (code_eqb_refl c). reflexivity.
    + apply Pos.eqb_refl.
    + rewrite Pos.eqb_refl, static_const_eqb_refl; auto.
  - destruct c as [params my_closure ret exn body]. simpl.
    destruct (bind_names_refl params [(my_closure, my_closure)]
                (reflexive_map_cons _ _ reflexive_map_nil))
      as (vm & -> & Hvm).
    apply expr_eqb_refl; [ exact Hvm | ].
    apply reflexive_map_cons, reflexive_map_cons, reflexive_map_nil.
Qed.

(* ======================================================================== *)
(* Environments that give paired names the same things                      *)
(* ======================================================================== *)

Definition envs_match (vm : name_map) (vars vars' : env) : Prop :=
  ∀ x x' : variable,
    names_match vm x x' = true -> lookup x vars = lookup x' vars'.

Lemma envs_match_same (vars : env) : envs_match [] vars vars.
Proof. intros x x' Hx. apply names_match_nil in Hx. subst x'. reflexivity. Qed.

Lemma envs_match_cons (vm : name_map) (vars vars' : env) (a a' : variable)
    (v : value) :
  envs_match vm vars vars' ->
  envs_match ((a, a') :: vm) ((a, v) :: vars) ((a', v) :: vars').
Proof.
  intros Hmatch x x'. simpl. destruct (Pos.eqb x a).
  - intros ->. reflexivity.
  - destruct (Pos.eqb x' a'); [ discriminate | apply Hmatch ].
Qed.

(* Binding paired parameters: both fail or both succeed, and then the
   environments match under the pairs with those of the parameters. *)
Lemma bind_params_match (params : list variable) :
  ∀ (params' : list variable) (vs : list value) (vm vm' : name_map)
    (vars vars' : env),
    bind_names params params' vm = Some vm' ->
    envs_match vm vars vars' ->
    match bind_params params vs vars, bind_params params' vs vars' with
    | Some bound, Some bound' => envs_match vm' bound bound'
    | None, None => True
    | _, _ => False
    end.
Proof.
  induction params as [ | p params IH];
    intros [ | p' params'] vs vm vm' vars vars'; simpl; try discriminate.
  - intros [= <-] Hmatch. destruct vs; [ exact Hmatch | exact I ].
  - intros Hbind Hmatch. destruct vs as [ | v vs]; [ exact I | ].
    apply (IH params' vs _ _ _ _ Hbind), envs_match_cons, Hmatch.
Qed.

Lemma eval_simple_match (vm : name_map) (vars vars' : env) (s s' : simple) :
  envs_match vm vars vars' ->
  simple_eqb vm s s' = true ->
  eval_simple vars s = eval_simple vars' s'.
Proof.
  intros Hmatch.
  destruct s as [x | sym | c], s' as [x' | sym' | c']; simpl;
    try discriminate.
  - apply Hmatch.
  - intros Heq. apply Pos.eqb_eq in Heq. subst sym'. reflexivity.
  - unfold const_eqb. destruct (const_eq_dec c c'); [ | discriminate ].
    subst c'. reflexivity.
Qed.

Lemma eval_simples_match (vm : name_map) (vars vars' : env)
    (args : list simple) :
  envs_match vm vars vars' ->
  ∀ args' : list simple,
    simples_eqb vm args args' = true ->
    eval_simples vars args = eval_simples vars' args'.
Proof.
  intros Hmatch. unfold simples_eqb.
  induction args as [ | s args IH]; intros [ | s' args']; simpl;
    try discriminate; [ reflexivity | ].
  intros Heq. apply andb_true_iff in Heq as [Hs Hargs].
  rewrite (eval_simple_match vm vars vars' s s' Hmatch Hs), (IH args' Hargs).
  reflexivity.
Qed.

Lemma eval_value_slots_match (vm : name_map) (vars vars' : env)
    (slots : list (value_slot * simple)) :
  envs_match vm vars vars' ->
  ∀ slots' : list (value_slot * simple),
    value_slots_eqb vm slots slots' = true ->
    eval_value_slots vars slots = eval_value_slots vars' slots'.
Proof.
  intros Hmatch. unfold value_slots_eqb.
  induction slots as [ | [slot s] slots IH]; intros [ | [slot' s'] slots'];
    simpl; try discriminate; [ reflexivity | ].
  intros Heq. apply andb_true_iff in Heq as [Hslot Hslots].
  apply andb_true_iff in Hslot as [Hslot Hs].
  apply Pos.eqb_eq in Hslot. subst slot'.
  rewrite (eval_simple_match vm vars vars' s s' Hmatch Hs), (IH slots' Hslots).
  reflexivity.
Qed.

(* ======================================================================== *)
(* Static environments                                                      *)
(* ======================================================================== *)

(* The same statically allocated values and, for each code id, code that
   is the same up to its bound names. *)
Definition statics_match (statics statics' : static_env) : Prop :=
  Forall2
    (fun ic ic' => fst ic = fst ic' ∧ code_eqb (snd ic) (snd ic') = true)
    (static_code statics) (static_code statics')
  ∧ static_values statics = static_values statics'.

Lemma statics_match_same (statics : static_env) :
  statics_match statics statics.
Proof.
  split; [ | reflexivity ].
  induction (static_code statics) as [ | ic code IH];
    [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact IH ].
  split; [ reflexivity | apply code_eqb_refl ].
Qed.

Lemma lookup_code_match (id : code_id) (statics statics' : static_env) :
  statics_match statics statics' ->
  match lookup id (static_code statics), lookup id (static_code statics') with
  | Some c, Some c' => code_eqb c c' = true
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros [Hcode _].
  induction Hcode as [ | [id1 c] [id1' c'] code code' [Hid Hc] _ IH]; simpl;
    [ exact I | ].
  simpl in Hid. subst id1'. destruct (Pos.eqb id id1); [ exact Hc | exact IH ].
Qed.

Lemma closure_of_match (statics statics' : static_env) (v : value) :
  statics_match statics statics' ->
  closure_of statics v = closure_of statics' v.
Proof.
  intros [_ Hvalues]. unfold closure_of. rewrite Hvalues. reflexivity.
Qed.

Lemma eval_named_match (vm : name_map) (vars vars' : env)
    (statics statics' : static_env) (d d' : named) :
  envs_match vm vars vars' ->
  statics_match statics statics' ->
  named_eqb vm d d' = true ->
  eval_named statics vars d = eval_named statics' vars' d'.
Proof.
  intros Hmatch Hstatics.
  destruct d as [s | p args | code slots | slot closure],
    d' as [s' | p' args' | code' slots' | slot' closure'];
    simpl; try discriminate; intros Heq.
  - exact (eval_simple_match vm vars vars' s s' Hmatch Heq).
  - apply andb_true_iff in Heq as [Hp Hargs]. apply prim_eqb_sound in Hp.
    subst p'.
    rewrite (eval_simples_match vm vars vars' args Hmatch args' Hargs).
    reflexivity.
  - apply andb_true_iff in Heq as [Hcode Hslots]. apply Pos.eqb_eq in Hcode.
    subst code'.
    rewrite (eval_value_slots_match vm vars vars' slots Hmatch slots' Hslots).
    reflexivity.
  - apply andb_true_iff in Heq as [Hslot Hclosure].
    apply Pos.eqb_eq in Hslot. subst slot'.
    rewrite (eval_simple_match vm vars vars' closure closure' Hmatch Hclosure).
    destruct (eval_simple vars' closure') as [v | ]; simpl; [ | reflexivity ].
    rewrite (closure_of_match statics statics' v Hstatics). reflexivity.
Qed.

Lemma forall2b_Z_eqb (l l' : list Z) : forall2b Z.eqb l l' = true -> l = l'.
Proof.
  revert l'. induction l as [ | z l IH]; intros [ | z' l']; simpl;
    try discriminate; [ reflexivity | ].
  intros Heq. apply andb_true_iff in Heq as [Hz Hl].
  apply Z.eqb_eq in Hz. rewrite Hz, (IH l' Hl). reflexivity.
Qed.

Lemma eval_static_const_match (vm : name_map) (vars vars' : env)
    (const const' : static_const) :
  envs_match vm vars vars' ->
  static_const_eqb vm const const' = true ->
  eval_static_const vars const = eval_static_const vars' const'.
Proof.
  intros Hmatch.
  destruct const as [code slots | tag fields | s | bytes],
    const' as [code' slots' | tag' fields' | s' | bytes'];
    simpl; try discriminate; intros Heq.
  - apply andb_true_iff in Heq as [Hcode Hslots]. apply Pos.eqb_eq in Hcode.
    subst code'.
    rewrite (eval_value_slots_match vm vars vars' slots Hmatch slots' Hslots).
    reflexivity.
  - apply andb_true_iff in Heq as [Htag Hfields]. apply Z.eqb_eq in Htag.
    subst tag'.
    rewrite (eval_simples_match vm vars vars' fields Hmatch fields' Hfields).
    reflexivity.
  - rewrite (eval_simple_match vm vars vars' s s' Hmatch Heq). reflexivity.
  - rewrite (forall2b_Z_eqb bytes bytes' Heq). reflexivity.
Qed.

(* Matching groups of bindings added to matching static environments:
   both fail, or the results match. *)
Lemma eval_static_bindings_match (vm : name_map) (vars vars' : env)
    (bindings : list static_binding) :
  envs_match vm vars vars' ->
  ∀ (bindings' : list static_binding) (statics statics' : static_env),
    forall2b (binding_eqb vm) bindings bindings' = true ->
    statics_match statics statics' ->
    match
      eval_static_bindings vars bindings statics,
      eval_static_bindings vars' bindings' statics'
    with
    | Some extended, Some extended' => statics_match extended extended'
    | None, None => True
    | _, _ => False
    end.
Proof.
  intros Hmatch.
  induction bindings as [ | binding bindings IH];
    intros [ | binding' bindings'] statics statics'; simpl; try discriminate;
    [ intros _ Hstatics; exact Hstatics | ].
  intros Heq Hstatics. pose proof Hstatics as [Hcode Hvalues].
  apply andb_true_iff in Heq as [Hbinding Hrest].
  destruct binding as [id c | id | sym const],
    binding' as [id' c' | id' | sym' const'];
    simpl in Hbinding; try discriminate.
  - apply andb_true_iff in Hbinding as [Hid Hc]. apply Pos.eqb_eq in Hid.
    subst id'.
    pose proof (lookup_code_match id statics statics' Hstatics) as Hid.
    destruct (lookup id (static_code statics)),
      (lookup id (static_code statics')); try contradiction; [ exact I | ].
    apply (IH bindings' _ _ Hrest). split; [ | exact Hvalues ].
    apply Forall2_cons; [ split; [ reflexivity | exact Hc ] | exact Hcode ].
  - apply (IH bindings' _ _ Hrest). split; assumption.
  - apply andb_true_iff in Hbinding as [Hsym Hconst].
    apply Pos.eqb_eq in Hsym. subst sym'. rewrite <- Hvalues.
    destruct (lookup sym (static_values statics)); [ exact I | ].
    rewrite (eval_static_const_match vm vars vars' const const' Hmatch Hconst).
    destruct (eval_static_const vars' const') as [allocated | ]; simpl;
      [ | exact I ].
    apply (IH bindings' _ _ Hrest). split; [ exact Hcode | ].
    simpl. rewrite Hvalues. reflexivity.
Qed.

(* ======================================================================== *)
(* Continuations                                                            *)
(* ======================================================================== *)

(* The handlers of a recursive group, compared one with one. *)
Definition handlers_eqb (vm km : name_map)
    (handlers handlers' : list (continuation * continuation_handler)) : bool :=
  forall2b (fun '(_, h) '(_, h') => handler_eqb vm km h h') handlers handlers'.

(* What two continuation names that match stand for: the same way out, the
   same continuation, or closures whose handlers are the same up to bound
   names, under the pairs of names of where they were defined, with
   matching environments. *)
#[local] Set Warnings "-register-all".
Inductive cont_matches : cont_value -> cont_value -> Prop :=
  | Same_matches (c : cont_value) : cont_matches c c
  | Closure_matches (vm km km' : name_map) (h h' : continuation_handler)
      (vars vars' : env) (conts conts' : cont_env)
      (recursive recursive' : list (continuation * continuation_handler)) :
    combine_names (map fst recursive) (map fst recursive') km = Some km' ->
    handler_eqb vm km' h h' = true ->
    handlers_eqb vm km' recursive recursive' = true ->
    envs_match vm vars vars' ->
    (∀ k k' : continuation,
      names_match km k k' = true ->
      cont_matches (resolve k conts) (resolve k' conts')) ->
    cont_matches (Closure h vars conts recursive)
      (Closure h' vars' conts' recursive').

Definition conts_match (km : name_map) (conts conts' : cont_env) : Prop :=
  ∀ k k' : continuation,
    names_match km k k' = true ->
    cont_matches (resolve k conts) (resolve k' conts').

Lemma conts_match_same (conts : cont_env) : conts_match [] conts conts.
Proof.
  intros k k' Hk. apply names_match_nil in Hk. subst k'. apply Same_matches.
Qed.

Lemma conts_match_cons (km : name_map) (conts conts' : cont_env)
    (a a' : continuation) (c c' : cont_value) :
  conts_match km conts conts' ->
  cont_matches c c' ->
  conts_match ((a, a') :: km) ((a, c) :: conts) ((a', c') :: conts').
Proof.
  intros Hmatch Hc k k'. unfold resolve. simpl. destruct (Pos.eqb k a).
  - intros ->. exact Hc.
  - destruct (Pos.eqb k' a'); [ discriminate | apply Hmatch ].
Qed.

(* The environments in which the handlers of two matching recursive groups
   run. [all] and [all'] are the whole groups, kept apart from the handlers
   still to be gone through. *)
Lemma rec_conts_match_aux (vm km km' : name_map) (vars vars' : env)
    (conts conts' : cont_env)
    (all all' : list (continuation * continuation_handler)) :
  combine_names (map fst all) (map fst all') km = Some km' ->
  handlers_eqb vm km' all all' = true ->
  envs_match vm vars vars' ->
  conts_match km conts conts' ->
  ∀ handlers handlers' : list (continuation * continuation_handler),
    handlers_eqb vm km' handlers handlers' = true ->
    conts_match (combine (map fst handlers) (map fst handlers') ++ km)
      (map (fun '(k, h) => (k, Closure h vars conts all)) handlers ++ conts)
      (map (fun '(k, h) => (k, Closure h vars' conts' all')) handlers'
       ++ conts').
Proof.
  intros Hnames Hall Hvars Hconts. unfold handlers_eqb.
  induction handlers as [ | [k h] handlers IH];
    intros [ | [k' h'] handlers']; simpl; try discriminate;
    [ intros _; exact Hconts | ].
  intros Heq. apply andb_true_iff in Heq as [Hh Hrest].
  apply conts_match_cons; [ exact (IH handlers' Hrest) | ].
  exact (Closure_matches vm km km' h h' vars vars' conts conts' all all'
    Hnames Hh Hall Hvars Hconts).
Qed.

Lemma rec_conts_match (vm km km' : name_map) (vars vars' : env)
    (conts conts' : cont_env)
    (handlers handlers' : list (continuation * continuation_handler)) :
  combine_names (map fst handlers) (map fst handlers') km = Some km' ->
  handlers_eqb vm km' handlers handlers' = true ->
  envs_match vm vars vars' ->
  conts_match km conts conts' ->
  conts_match km' (rec_closures handlers vars conts ++ conts)
    (rec_closures handlers' vars' conts' ++ conts').
Proof.
  intros Hnames Hhandlers Hvars Hconts.
  pose proof (rec_conts_match_aux vm km km' vars vars' conts conts' handlers
    handlers' Hnames Hhandlers Hvars Hconts handlers handlers' Hhandlers)
    as Hmatch.
  assert (Hkm' :
    km' = combine (map fst handlers) (map fst handlers') ++ km).
  { unfold combine_names in Hnames.
    match type of Hnames with
    | context [if ?same_length then _ else _] => destruct same_length
    end;
      cbv iota in Hnames; [ | discriminate ].
    injection Hnames as Hkm'. symmetry. exact Hkm'. }
  rewrite Hkm'. exact Hmatch.
Qed.

(* ======================================================================== *)
(* States                                                                   *)
(* ======================================================================== *)

Inductive state_matches : state -> state -> Prop :=
  | State_matches (vm km : name_map) (e e' : expr) (vars vars' : env)
      (conts conts' : cont_env) (statics statics' : static_env) :
    expr_eqb vm km e e' = true ->
    envs_match vm vars vars' ->
    conts_match km conts conts' ->
    statics_match statics statics' ->
    state_matches (State e vars conts statics) (State e' vars' conts' statics').

(* A continuation closure matches itself, by the reflexivity of the
   comparison. *)
Lemma closure_matches_itself (h : continuation_handler) (vars : env)
    (conts : cont_env)
    (recursive : list (continuation * continuation_handler)) :
  ∃ km' : name_map,
    combine_names (map fst recursive) (map fst recursive) [] = Some km'
    ∧ handler_eqb [] km' h h = true
    ∧ handlers_eqb [] km' recursive recursive = true.
Proof.
  destruct (combine_names_refl (map fst recursive) [] reflexive_map_nil)
    as (km' & Hnames & Hkm').
  exists km'. split; [ exact Hnames | ].
  split; [ apply handler_eqb_refl; [ apply reflexive_map_nil | exact Hkm' ] | ].
  unfold handlers_eqb. apply forall2b_refl. intros [k h0].
  apply handler_eqb_refl; [ apply reflexive_map_nil | exact Hkm' ].
Qed.

(* Applying matching continuations to the same values, under matching
   static environments. *)
Lemma apply_cont_value_match (c c' : cont_value) (vs : list value)
    (statics statics' : static_env) :
  cont_matches c c' ->
  statics_match statics statics' ->
  result_related state_matches (apply_cont_value c vs statics)
    (apply_cont_value c' vs statics').
Proof.
  intros Hc Hstatics.
  assert (Hclosure :
    ∀ (vm km km' : name_map) (h h' : continuation_handler)
      (vars vars' : env) (conts conts' : cont_env)
      (recursive recursive' : list (continuation * continuation_handler)),
      combine_names (map fst recursive) (map fst recursive') km = Some km' ->
      handler_eqb vm km' h h' = true ->
      handlers_eqb vm km' recursive recursive' = true ->
      envs_match vm vars vars' ->
      conts_match km conts conts' ->
      result_related state_matches
        (apply_cont_value (Closure h vars conts recursive) vs statics)
        (apply_cont_value (Closure h' vars' conts' recursive') vs statics')).
  { intros vm km km' [params handler] [params' handler'] vars vars' conts
      conts' recursive recursive' Hnames Hh Hrec Hvars Hconts.
    simpl in Hh |- *.
    destruct (bind_names params params' vm) as [vm' | ] eqn:Hbind;
      [ | discriminate ].
    pose proof (bind_params_match params params' vs vm vm' vars vars' Hbind
      Hvars) as Hbound.
    destruct (bind_params params vs vars), (bind_params params' vs vars');
      try contradiction; simpl; [ | exact I ].
    apply (State_matches vm' km');
      [ exact Hh | exact Hbound | | exact Hstatics ].
    exact (rec_conts_match vm km km' vars vars' conts conts' recursive
      recursive' Hnames Hrec Hvars Hconts). }
  destruct Hc
    as [[h vars conts recursive | exit]
       | vm km km' h h' vars vars' conts conts' recursive recursive' Hnames
           Hh Hrec Hvars Hconts].
  - destruct (closure_matches_itself h vars conts recursive)
      as (km' & Hnames & Hh & Hrec).
    exact (Hclosure [] [] km' h h vars vars conts conts recursive recursive
      Hnames Hh Hrec (envs_match_same vars) (conts_match_same conts)).
  - simpl. auto.
  - exact (Hclosure vm km km' h h' vars vars' conts conts' recursive
      recursive' Hnames Hh Hrec Hvars Hconts).
Qed.

Lemma call_kind_eqb_eq (kind kind' : call_kind) :
  call_kind_eqb kind kind' = true -> kind = kind'.
Proof.
  destruct kind as [code | ], kind' as [code' | ]; simpl; try discriminate;
    [ | reflexivity ].
  intros Heq. apply Pos.eqb_eq in Heq. subst code'. reflexivity.
Qed.

(* Expressions that are the same up to bound names agree on whether they
   bind something static. *)
Fixpoint expr_eqb_binds_statics (e : expr) :
  ∀ (vm km : name_map) (e' : expr),
    expr_eqb vm km e e' = true -> binds_statics e = binds_statics e'.
Proof.
  destruct e
    as [ x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    intros vm km
      [ x' d' body' | bindings' body' | k' h' body' | handlers' body' | ap'
      | ac' | scrutinee' arms' | ];
    simpl; try discriminate; try reflexivity; intros Heq.
  - apply andb_true_iff in Heq as [_ Hbody].
    exact (expr_eqb_binds_statics body _ _ _ Hbody).
  - apply andb_true_iff in Heq as [Hbindings Hbody].
    rewrite (expr_eqb_binds_statics body _ _ _ Hbody). f_equal.
    clear Hbody. revert bindings' Hbindings.
    induction bindings as [ | binding bindings IH];
      intros [ | binding' bindings']; simpl; try discriminate;
      [ reflexivity | ].
    intros Heq. apply andb_true_iff in Heq as [Hbinding Hrest].
    rewrite (IH _ Hrest). f_equal.
    destruct binding, binding'; simpl in Hbinding; try discriminate;
      reflexivity.
  - apply andb_true_iff in Heq as [Hh Hbody].
    destruct h as [params handler], h' as [params' handler'].
    simpl in Hh |- *.
    destruct (bind_names params params' vm) as [vm' | ]; [ | discriminate ].
    rewrite (expr_eqb_binds_statics handler _ _ _ Hh),
      (expr_eqb_binds_statics body _ _ _ Hbody).
    reflexivity.
  - destruct (combine_names (map fst handlers) (map fst handlers') km)
      as [km' | ]; [ | discriminate ].
    apply andb_true_iff in Heq as [Hhandlers Hbody].
    rewrite (expr_eqb_binds_statics body _ _ _ Hbody). f_equal.
    clear Hbody. revert handlers' Hhandlers.
    induction handlers as [ | [k [params handler]] handlers IH];
      intros [ | [k' [params' handler']] handlers']; simpl;
      try discriminate; [ reflexivity | ].
    intros Heq. apply andb_true_iff in Heq as [Hh Hrest].
    destruct (bind_names params params' vm) as [vm' | ]; [ | discriminate ].
    rewrite (expr_eqb_binds_statics handler _ _ _ Hh), (IH _ Hrest).
    reflexivity.
Qed.

Lemma handlers_eqb_bind_statics (vm km : name_map)
    (handlers : list (continuation * continuation_handler)) :
  ∀ handlers' : list (continuation * continuation_handler),
    forall2b (fun '(_, h) '(_, h') => handler_eqb vm km h h') handlers
      handlers'
    = true ->
    handlers_bind_statics handlers = handlers_bind_statics handlers'.
Proof.
  unfold handlers_bind_statics.
  induction handlers as [ | [k [params handler]] handlers IH];
    intros [ | [k' [params' handler']] handlers']; simpl;
    try discriminate; [ reflexivity | ].
  intros Heq. apply andb_true_iff in Heq as [Hh Hrest].
  destruct (bind_names params params' vm) as [vm' | ]; [ | discriminate ].
  rewrite (expr_eqb_binds_statics handler _ _ _ Hh), (IH _ Hrest).
  reflexivity.
Qed.

(* The same call under matching static environments, returning to matching
   continuations. *)
Lemma call_function_match (callee : value) (kind : call_kind)
    (vs : list value) (return_to return_to' exn_to exn_to' : cont_value)
    (statics statics' : static_env) :
  statics_match statics statics' ->
  cont_matches return_to return_to' ->
  cont_matches exn_to exn_to' ->
  result_related state_matches
    (call_function callee kind vs return_to exn_to statics)
    (call_function callee kind vs return_to' exn_to' statics').
Proof.
  intros Hstatics Hreturn Hexn. unfold call_function.
  rewrite <- (closure_of_match statics statics' callee Hstatics).
  destruct (closure_of statics callee) as [[called slots] | ]; [ | exact I ].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | exact I ].
  pose proof (lookup_code_match called statics statics' Hstatics) as Hc.
  destruct (lookup called (static_code statics))
    as [[params my_closure ret exn body] | ],
    (lookup called (static_code statics'))
    as [[params' my_closure' ret' exn' body'] | ];
    try contradiction; [ | exact I ].
  simpl in Hc |- *.
  destruct (bind_names params params' [(my_closure, my_closure')])
    as [vm | ] eqn:Hbind; [ | discriminate ].
  rewrite <- (expr_eqb_binds_statics body _ _ _ Hc).
  destruct (binds_statics body); [ exact I | ].
  pose proof (bind_params_match params params' vs _ vm
    [(my_closure, callee)] [(my_closure', callee)] Hbind
    (envs_match_cons [] [] [] my_closure my_closure' callee
       (envs_match_same [])))
    as Hbound.
  destruct (bind_params params vs [(my_closure, callee)]),
    (bind_params params' vs [(my_closure', callee)]);
    try contradiction; simpl; [ | exact I ].
  apply (State_matches vm [(ret, ret'); (exn, exn')]);
    [ exact Hc | exact Hbound | | exact Hstatics ].
  apply conts_match_cons; [ | exact Hreturn ].
  apply conts_match_cons; [ apply conts_match_same | exact Hexn ].
Qed.

Lemma find_arm_match (vm km : name_map) (i : Z)
    (arms : list (Z * apply_cont)) :
  ∀ arms' : list (Z * apply_cont),
    forall2b
      (fun arm arm' =>
         Z.eqb (fst arm) (fst arm')
         && apply_cont_eqb vm km (snd arm) (snd arm'))
      arms arms'
    = true ->
    match find_arm i arms, find_arm i arms' with
    | Some ac, Some ac' => apply_cont_eqb vm km ac ac' = true
    | None, None => True
    | _, _ => False
    end.
Proof.
  induction arms as [ | [d ac] arms IH]; intros [ | [d' ac'] arms']; simpl;
    try discriminate; [ intros _; exact I | ].
  intros Heq. apply andb_true_iff in Heq as [Harm Hrest].
  apply andb_true_iff in Harm as [Hd Hac]. apply Z.eqb_eq in Hd. subst d'.
  destruct (Z.eqb i d); [ exact Hac | exact (IH arms' Hrest) ].
Qed.

(* Matching states step alike. *)
Lemma matched_step (s s' : state) :
  state_matches s s' -> result_related state_matches (step s) (step s').
Proof.
  intros [vm km e e' vars vars' conts conts' statics statics' He Hvars
            Hconts Hstatics].
  destruct e
    as [ x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ],
    e'
    as [ x' d' body' | bindings' body' | k' h' body' | handlers' body' | ap'
       | ac' | scrutinee' arms' | ];
    simpl in He; try discriminate; autorewrite with step; simpl.
  - (* Let *)
    apply andb_true_iff in He as [Hd Hbody].
    rewrite (eval_named_match vm vars vars' statics statics' d d' Hvars
      Hstatics Hd).
    destruct (eval_named statics' vars' d') as [v | ]; simpl; [ | exact I ].
    apply (State_matches ((x, x') :: vm) km);
      [ exact Hbody | apply envs_match_cons, Hvars | exact Hconts
      | exact Hstatics ].
  - (* Let_static *)
    apply andb_true_iff in He as [Hbindings Hbody].
    pose proof (eval_static_bindings_match vm vars vars' bindings Hvars
      bindings' statics statics' Hbindings Hstatics) as Hextended.
    destruct (eval_static_bindings vars bindings statics),
      (eval_static_bindings vars' bindings' statics');
      try contradiction; simpl; [ | exact I ].
    apply (State_matches vm km); assumption.
  - (* Let_cont_non_recursive *)
    apply andb_true_iff in He as [Hh Hbody].
    apply (State_matches vm ((k, k') :: km));
      [ exact Hbody | exact Hvars | | exact Hstatics ].
    apply conts_match_cons; [ exact Hconts | ].
    apply (Closure_matches vm km km h h' vars vars' conts conts' [] []);
      [ reflexivity | exact Hh | reflexivity | exact Hvars | exact Hconts ].
  - (* Let_cont_recursive *)
    destruct (combine_names (map fst handlers) (map fst handlers') km)
      as [km' | ] eqn:Hnames; [ | discriminate ].
    apply andb_true_iff in He as [Hhandlers Hbody].
    rewrite <- (handlers_eqb_bind_statics vm km' handlers handlers'
      Hhandlers).
    destruct (handlers_bind_statics handlers); [ exact I | ].
    apply (State_matches vm km');
      [ exact Hbody | exact Hvars | | exact Hstatics ].
    exact (rec_conts_match vm km km' vars vars' conts conts' handlers
      handlers' Hnames Hhandlers Hvars Hconts).
  - (* Apply *)
    unfold apply_eqb in He.
    apply andb_true_iff in He as [He Hexn].
    apply andb_true_iff in He as [He Hreturn].
    apply andb_true_iff in He as [He Hargs].
    apply andb_true_iff in He as [Hcallee Hkind].
    apply call_kind_eqb_eq in Hkind.
    rewrite (eval_simple_match vm vars vars' _ _ Hvars Hcallee),
      (eval_simples_match vm vars vars' _ Hvars _ Hargs), <- Hkind.
    destruct (eval_simple vars' (ap_callee ap')) as [callee | ];
      [ | exact I ].
    destruct (eval_simples vars' (ap_args ap')) as [vs | ]; [ | exact I ].
    apply call_function_match;
      [ exact Hstatics | exact (Hconts _ _ Hreturn) | exact (Hconts _ _ Hexn) ].
  - (* Apply_cont *)
    unfold apply_cont_eqb in He. apply andb_true_iff in He as [Hk Hargs].
    rewrite (eval_simples_match vm vars vars' _ Hvars _ Hargs).
    destruct (eval_simples vars' (ac_args ac')) as [vs | ]; [ | exact I ].
    apply apply_cont_value_match; [ exact (Hconts _ _ Hk) | exact Hstatics ].
  - (* Switch *)
    apply andb_true_iff in He as [Hscrutinee Harms].
    rewrite (eval_simple_match vm vars vars' _ _ Hvars Hscrutinee).
    destruct (eval_simple vars' scrutinee') as [v | ]; [ | exact I ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
    pose proof (find_arm_match vm km i arms arms' Harms) as Harm.
    destruct (find_arm i arms) as [ac | ], (find_arm i arms') as [ac' | ];
      try contradiction; simpl; [ | exact I ].
    apply (State_matches vm km); assumption.
  - (* Invalid *)
    exact I.
Qed.

Theorem expr_eqb_sound : expr_eqb_sound_statement.
Proof.
  intros e e' Heq vars conts statics.
  apply (bisimulation_equivalent state_matches matched_step).
  apply (State_matches [] []);
    [ exact Heq | apply envs_match_same | apply conts_match_same
    | apply statics_match_same ].
Qed.
