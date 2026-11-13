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

(* Proofs of the statements of FlambdaMergeTablesSpec.v. Nothing here
   needs review.

   The refinement of a [Switch] is by the steps of the machine, as in
   FlambdaMergeSwitchesProofs.v: where the [Switch] has a step it goes
   to an arm, which the test has found to be the merged application
   with an element of the table in place of the variable; the merged
   term binds the variable to the value of that element in the steps
   of its [Let]s, the last of which is the load, and then the two
   apply the same continuation to the same values. The load has that
   value because the table is bound to the values of its elements
   ([tables_bound]), which a group of static bindings that has a value
   makes true of its own tables and keeps true of the others
   ([tables_under_statics_bound]). Down a term and in the bodies of
   code, the recursion is that of
   FlambdaUnboxInScopeProofs.rewrite_code_in_scope_refines_aux, with
   the tables for what is known of symbols. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaMapSpec FlambdaValueSpec FlambdaPrimitiveModel FlambdaPrimitiveSpec
  FlambdaPrimitiveProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaWellFormedSpec FlambdaWellFormedProofs FlambdaContextSpec
  FlambdaContextProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaAlphaProofs FlambdaNormaliseSpec FlambdaNormaliseProofs
  FlambdaMergeSwitchesSpec FlambdaMergeSwitchesProofs FlambdaMergeTablesSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The values of the merged arguments                                       *)
(* ======================================================================== *)

(* Under a binding of the variable to the value of an element, an
   argument has the value that it has with the element in place of the
   variable, in any environment that binds the other variables alike. *)
Lemma eval_simple_element_for (v : variable) (element : simple) (w : value)
    (vars vars' : env) (s : simple) :
  eval_simple [] element = Some w ->
  (∀ x : variable, x <> v -> lookup x vars' = lookup x vars) ->
  eval_simple ((v, w) :: vars') s = eval_simple vars (element_for v element s).
Proof.
  intros Helement Hagree. destruct s as [x | sym | c]; simpl; try reflexivity.
  destruct (Pos.eqb_spec x v) as [-> | Hne].
  - destruct element as [y | sym | c]; simpl in Helement |- *;
      [ discriminate | symmetry; exact Helement | symmetry; exact Helement ].
  - simpl. apply Hagree, Hne.
Qed.

Lemma eval_simples_element_for (v : variable) (element : simple) (w : value)
    (vars vars' : env) (args : list simple) :
  eval_simple [] element = Some w ->
  (∀ x : variable, x <> v -> lookup x vars' = lookup x vars) ->
  eval_simples ((v, w) :: vars') args
  = eval_simples vars (map (element_for v element) args).
Proof.
  intros Helement Hagree.
  induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite (eval_simple_element_for v element w vars vars' s Helement Hagree),
    IH.
  reflexivity.
Qed.

(* So the merged application steps as the arm does. *)
Lemma merged_steps_as_loaded_arm (v : variable) (element : simple)
    (w : value) (merged : apply_cont) (vars vars' : env) (conts : cont_env)
    (statics : static_env) (hp : heap) :
  eval_simple [] element = Some w ->
  (∀ x : variable, x <> v -> lookup x vars' = lookup x vars) ->
  step (State (Apply_cont merged) ((v, w) :: vars') conts statics hp)
  = step
      (State
         (Apply_cont
            (Apply_cont_expr (ac_continuation merged)
               (map (element_for v element) (ac_args merged))
               (ac_trap_action merged)))
         vars conts statics hp).
Proof.
  intros Helement Hagree. rewrite !step_apply_cont. simpl.
  rewrite (eval_simples_element_for v element w vars vars' _ Helement Hagree).
  reflexivity.
Qed.

(* The arm that a [Switch] goes to is one that the test has looked at. *)
Lemma arm_is_loaded_found (v : variable) (merged : apply_cont)
    (first offset : Z) (elements : list simple) (immediates : bool)
    (arms : list (Z * apply_cont)) (i : Z) (ac : apply_cont) :
  forallb (arm_is_loaded v merged first offset elements immediates) arms
  = true ->
  find_arm i arms = Some ac ->
  ∃ element : simple,
    table_element first offset elements i = Some element
    ∧ element_taken immediates element = true
    ∧ ac
      = Apply_cont_expr (ac_continuation merged)
          (map (element_for v element) (ac_args merged))
          (ac_trap_action merged).
Proof.
  intros Hall Hfind. apply find_arm_in in Hfind.
  rewrite forallb_forall in Hall. specialize (Hall (i, ac) Hfind).
  unfold arm_is_loaded in Hall. simpl in Hall.
  destruct (table_element first offset elements i) as [element | ];
    [ | discriminate ].
  apply andb_prop in Hall as [Htaken Hsame].
  exists element. split; [ reflexivity | split; [ exact Htaken | ] ].
  destruct (apply_cont_eq_dec ac _) as [Heq | ]; [ exact Heq | discriminate ].
Qed.

(* ======================================================================== *)
(* The steps of the new [Let]s                                              *)
(* ======================================================================== *)

(* The [Let] of the offset, where there is one, binds the variable to
   the index. *)
Lemma bind_table_offset_equivalent (v : variable)
    (first offset i index : Z) (body : expr) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap) :
  lookup v vars = Some (Value_const (Tagged_immediate i)) ->
  table_index first offset i = Some index ->
  ∃ vars' : env,
    lookup v vars' = Some (Value_const (Tagged_immediate index))
    ∧ (∀ x : variable, x <> v -> lookup x vars' = lookup x vars)
    ∧ in_range (int_width Standard_tagged_immediate) index = true
    ∧ equivalent
        (State (bind_table_offset v first offset body) vars conts statics hp)
        (State body vars' conts statics hp).
Proof.
  intros Hv Hindex. unfold table_index in Hindex. cbv zeta in Hindex.
  destruct (in_range (int_width Standard_naked_immediate) i) eqn:Hrange;
    [ | discriminate ].
  unfold bind_table_offset.
  destruct (Z.eqb_spec first 0) as [-> | Hfirst].
  - injection Hindex as <-. exists vars.
    split; [ exact Hv | split; [ reflexivity | split ] ];
      [ exact Hrange | apply equivalent_refl ].
  - destruct (in_range (int_width Standard_tagged_immediate) offset)
      eqn:Hoffset; [ | discriminate ].
    injection Hindex as <-.
    exists
      ((v,
        Value_const
          (Tagged_immediate
             (wrap (int_width Standard_tagged_immediate) (i + offset))))
       :: vars).
    split; [ simpl; rewrite Pos.eqb_refl; reflexivity | split; [ | split ] ].
    + intros x Hne. apply lookup_other_variable, Hne.
    + exact
        (wrap_in_range _ _ (int_width_positive Standard_tagged_immediate)).
    + apply step_equivalent. rewrite step_let.
      cbn [eval_named eval_simples eval_simple]. rewrite Hv.
      cbn [eval_prim eval_binary_primitive int_of_value].
      change (int_width Standard_naked_immediate)
        with (int_width Standard_tagged_immediate) in Hrange.
      rewrite Hrange, Hoffset. reflexivity.
Qed.

(* A value that the load kind takes is of kind [Value]. *)
Lemma array_element_ok_value (kind : array_kind) (w : value) :
  array_element_ok kind w = true -> kind_eqb (kind_of_value w) Value = true.
Proof.
  destruct kind; cbn [array_element_ok]; intros Hok; try exact Hok.
  unfold is_tagged_immediate in Hok.
  destruct w; simpl in Hok |- *; try discriminate; try reflexivity.
  match goal with
  | c : const |- _ =>
    destruct c; simpl in Hok |- *; try discriminate; reflexivity
  end.
Qed.

(* The load of an element of a static array (P1's law, in the form
   that is needed here). *)
Lemma array_load_of_static (statics : static_env) (s : symbol)
    (elements : list value) (kind : array_kind)
    (load_kind : array_load_kind) (mut : mutability) (index v : value)
    (i : Z) :
  lookup s (static_values statics) = Some (Static_immutable_array elements) ->
  int_of_value Standard_tagged_immediate index = Some i ->
  0 <= i < Z.of_nat (length elements) ->
  nth_error elements (Z.to_nat i) = Some v ->
  array_element_ok (array_kind_of_load_kind load_kind) v = true ->
  eval_prim statics (Binary (Array_load kind load_kind mut))
    [Value_symbol s; index]
  = Some v.
Proof.
  intros Hs Hi [Hlow Hhigh] Hnth Hok.
  cbn [eval_prim eval_binary_primitive array_of]. rewrite Hs.
  cbn beta iota. unfold array_loaded, array_index. rewrite Hi.
  cbn beta iota.
  apply Z.leb_le in Hlow. apply Z.ltb_lt in Hhigh. rewrite Hlow, Hhigh.
  cbn [andb]; cbn beta iota. rewrite Hnth. cbn beta iota.
  rewrite Hok. reflexivity.
Qed.

(* The values of the elements of a table, one for one. *)
Lemma eval_simples_nth (elements : list simple) :
  ∀ (vs : list value) (n : nat) (element : simple),
    eval_simples [] elements = Some vs ->
    nth_error elements n = Some element ->
    ∃ w : value, eval_simple [] element = Some w ∧ nth_error vs n = Some w.
Proof.
  induction elements as [ | element0 elements IH];
    intros vs n element Heval Hnth; [ destruct n; discriminate | ].
  simpl in Heval.
  destruct (eval_simple [] element0) as [w0 | ] eqn:Hw0; [ | discriminate ].
  destruct (eval_simples [] elements) as [ws | ] eqn:Hws; [ | discriminate ].
  injection Heval as <-.
  destruct n as [ | n]; simpl in Hnth |- *.
  - injection Hnth as <-. exists w0. split; [ exact Hw0 | reflexivity ].
  - exact (IH ws n element eq_refl Hnth).
Qed.

Lemma eval_simples_length (vars : env) (elements : list simple) :
  ∀ vs : list value,
    eval_simples vars elements = Some vs -> length vs = length elements.
Proof.
  induction elements as [ | element elements IH]; intros vs Heval;
    simpl in Heval.
  - injection Heval as <-. reflexivity.
  - destruct (eval_simple vars element); [ | discriminate ].
    destruct (eval_simples vars elements) as [ws | ]; [ | discriminate ].
    injection Heval as <-. simpl. f_equal. exact (IH ws eq_refl).
Qed.

(* An element that the test has passed is one that the load kind of the
   table takes. *)
Lemma element_taken_ok (elements : list simple) (element : simple)
    (w : value) :
  element ∈ elements ->
  eval_simple [] element = Some w ->
  element_taken (all_immediates elements) element = true ->
  array_element_ok
    (array_kind_of_load_kind (table_load_kind (all_immediates elements))) w
  = true.
Proof.
  intros Hin Hw Htaken.
  destruct (all_immediates elements) eqn:Himmediates;
    cbn [table_load_kind array_kind_of_load_kind].
  - unfold all_immediates in Himmediates.
    rewrite forallb_forall in Himmediates.
    specialize (Himmediates element Hin). rewrite Hw in Himmediates.
    exact Himmediates.
  - unfold element_taken in Htaken. cbn [orb] in Htaken.
    rewrite Hw in Htaken. exact Htaken.
Qed.

(* ======================================================================== *)
(* The refinement of a [Switch]                                             *)
(* ======================================================================== *)

Lemma merge_by_table_refines (v : variable) (merged : apply_cont)
    (first offset : Z) (arms : list (Z * apply_cont)) (s : symbol)
    (elements : list simple) (vs : list value) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap) :
  forallb
    (arm_is_loaded v merged first offset elements (all_immediates elements))
    arms
  = true ->
  eval_simples [] elements = Some vs ->
  lookup s (static_values statics) = Some (Static_immutable_array vs) ->
  refines (State (Switch (Var v) arms) vars conts statics hp)
    (State
       (bind_table_load v s first offset (all_immediates elements)
          (Apply_cont merged))
       vars conts statics hp).
Proof.
  intros Hall Hvs Hs.
  destruct (step_switch_cases (Var v) arms vars conts statics hp)
    as [Hwrong | (w & i & ac & Hv & Hi & Hfind & Hstep)];
    [ apply step_undefined_refines, Hwrong | ].
  apply naked_immediate_of_value_some in Hi. subst w.
  destruct (arm_is_loaded_found _ _ _ _ _ _ _ _ _ Hall Hfind)
    as (element & Helement & Htaken & ->).
  unfold table_element in Helement.
  destruct (table_index first offset i) as [index | ] eqn:Hindex;
    [ | discriminate ].
  cbn beta iota in Helement.
  destruct ((0 <=? index) && (index <? Z.of_nat (length elements)))
    eqn:Hbounds; [ | discriminate ].
  apply andb_prop in Hbounds as [Hlow Hhigh].
  apply Z.leb_le in Hlow. apply Z.ltb_lt in Hhigh.
  destruct (eval_simples_nth elements vs _ element Hvs Helement)
    as (w & Hw & Hnth).
  apply (element_taken_ok elements element w
           (nth_error_In _ _ Helement) Hw) in Htaken.
  assert (Hrange : in_range (int_width Standard_naked_immediate) i = true).
  { unfold table_index in Hindex. cbv zeta in Hindex.
    destruct (in_range (int_width Standard_naked_immediate) i);
      [ reflexivity | discriminate ]. }
  apply equivalent_refines.
  eapply equivalent_trans; [ apply step_equivalent, Hstep | ].
  apply equivalent_sym. unfold bind_table_load.
  eapply equivalent_trans;
    [ apply step_equivalent, (step_bind_tagged v i);
      [ exact Hv | exact Hrange ]
    | ].
  destruct
    (bind_table_offset_equivalent v first offset i index
       (Let v Value
          (Prim
             (Binary
                (Array_load (table_array_kind (all_immediates elements))
                   (table_load_kind (all_immediates elements)) Immutable))
             [Symbol s; Var v])
          (Apply_cont merged))
       ((v, Value_const (Tagged_immediate i)) :: vars) conts statics hp)
    as (vars' & Hv' & Hagree & Hindex_range & Hequiv);
    [ simpl; rewrite Pos.eqb_refl; reflexivity | exact Hindex | ].
  eapply equivalent_trans; [ exact Hequiv | ].
  eapply equivalent_trans.
  - apply step_equivalent. rewrite step_let.
    cbn [eval_named eval_simples eval_simple]. rewrite Hv'.
    cbn beta iota.
    rewrite
      (array_load_of_static statics s vs _ _ Immutable
         (Value_const (Tagged_immediate index)) w index Hs);
      [ rewrite (array_element_ok_value _ w Htaken); reflexivity
      | cbn [int_of_value]; rewrite Hindex_range; reflexivity
      | rewrite (eval_simples_length [] elements vs Hvs); lia
      | exact Hnth | exact Htaken ].
  - apply step_eq_equivalent, merged_steps_as_loaded_arm; [ exact Hw | ].
    intros x Hne. rewrite (Hagree x Hne). apply lookup_other_variable, Hne.
Qed.

Lemma merge_switch_by_table_refines (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) (merged : expr)
    (vars : env) (conts : cont_env) (statics : static_env) (hp : heap) :
  tables_bound tables statics ->
  merge_switch_by_table tables scrutinee arms = Some merged ->
  refines (State (Switch scrutinee arms) vars conts statics hp)
    (State merged vars conts statics hp).
Proof.
  intros Hbound. unfold merge_switch_by_table.
  destruct scrutinee as [v | sym | c]; try discriminate.
  destruct arms as [ | [first ac] [ | arm1 [ | arm2 others]]];
    try discriminate.
  cbv zeta.
  destruct (var_in_simples v _); [ | discriminate ].
  destruct (find _ tables) as [[s elements] | ] eqn:Hfind; [ | discriminate ].
  intros [= <-].
  apply find_some in Hfind as [Hin Hhas].
  unfold table_has_arms in Hhas. apply andb_prop in Hhas as [_ Hall].
  cbv zeta in Hall. cbn [snd] in Hall.
  destruct (Hbound s elements Hin) as (vs & Hvs & Hs).
  exact (merge_by_table_refines v _ first _ _ s elements vs vars conts
    statics hp Hall Hvs Hs).
Qed.

(* With no table in scope no table has the arms. *)
Lemma merge_switch_by_table_nil (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  merge_switch_by_table [] scrutinee arms = None.
Proof.
  unfold merge_switch_by_table.
  destruct scrutinee as [v | sym | c]; try reflexivity.
  destruct arms as [ | [first ac] [ | arm1 [ | arm2 others]]];
    try reflexivity.
  cbv zeta. destruct (var_in_simples v _); reflexivity.
Qed.

(* The test for no table at all changes nothing of the answer. *)
Lemma merge_switch_with_tables_unfold (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) :
  merge_switch_with_tables tables scrutinee arms
  = match merge_switch_by_table tables scrutinee arms with
    | Some merged =>
      match merge_switch scrutinee arms with
      | Switch _ _ => merged
      | Let _ _ _ _ | Let_static _ _ | Let_cont_non_recursive _ _ _
      | Let_cont_recursive _ _ | Apply _ | Apply_cont _ | Invalid =>
        Switch scrutinee arms
      end
    | None => Switch scrutinee arms
    end.
Proof.
  unfold merge_switch_with_tables.
  destruct tables as [ | table tables]; [ | reflexivity ].
  rewrite merge_switch_by_table_nil. reflexivity.
Qed.

Lemma merge_switch_with_tables_refines (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) (vars : env)
    (conts : cont_env) (statics : static_env) (hp : heap) :
  tables_bound tables statics ->
  refines (State (Switch scrutinee arms) vars conts statics hp)
    (State (merge_switch_with_tables tables scrutinee arms) vars conts
       statics hp).
Proof.
  intros Hbound. rewrite merge_switch_with_tables_unfold.
  destruct (merge_switch_by_table tables scrutinee arms) as [merged | ]
    eqn:Hmerged; [ | apply refines_refl ].
  destruct (merge_switch scrutinee arms); try apply refines_refl.
  exact (merge_switch_by_table_refines tables scrutinee arms merged vars conts
    statics hp Hbound Hmerged).
Qed.

(* ======================================================================== *)
(* The tables are bound                                                     *)
(* ======================================================================== *)

Lemma no_tables_bound (statics : static_env) : tables_bound [] statics.
Proof. intros s elements []. Qed.

Lemma tables_bound_extend (tables : known_tables)
    (statics statics' : static_env) :
  tables_bound tables statics ->
  statics_extend statics statics' ->
  tables_bound tables statics'.
Proof.
  intros Hbound [_ Hvalues] s elements Hin.
  destruct (Hbound s elements Hin) as (vs & Hvs & Hs).
  exists vs. split; [ exact Hvs | exact (Hvalues _ _ Hs) ].
Qed.

(* Elements with no variable have their values under any variables. *)
Lemma eval_closed_elements (vars : env) (elements : list simple) :
  forallb element_closed elements = true ->
  eval_simples vars elements = eval_simples [] elements.
Proof.
  induction elements as [ | element elements IH]; simpl; [ reflexivity | ].
  intros Hclosed. apply andb_prop in Hclosed as [Helement Hclosed].
  rewrite (IH Hclosed).
  destruct element as [x | sym | c]; try reflexivity. discriminate Helement.
Qed.

(* A group of static bindings that has a value binds its tables. *)
Lemma group_tables_bound (vars : env) (bindings : list static_binding) :
  ∀ (statics extended : static_env) (s : symbol) (elements : list simple),
    eval_static_bindings vars bindings statics = Some extended ->
    (s, elements) ∈ flat_map table_of_binding bindings ->
    ∃ vs : list value,
      eval_simples [] elements = Some vs
      ∧ lookup s (static_values extended) = Some (Static_immutable_array vs).
Proof.
  induction bindings as [ | binding bindings IH];
    intros statics extended s elements Heval Hin; [ destruct Hin | ].
  cbn [flat_map] in Hin. apply in_app_or in Hin.
  destruct binding as [id c | id | s0 const];
    cbn [eval_static_bindings] in Heval.
  - destruct (lookup id (static_code statics)); [ discriminate | ].
    destruct Hin as [[] | Hin]. exact (IH _ _ s elements Heval Hin).
  - destruct Hin as [[] | Hin]. exact (IH _ _ s elements Heval Hin).
  - destruct (lookup s0 (static_values statics)); [ discriminate | ].
    destruct (eval_static_const vars const) as [allocated | ] eqn:Hconst;
      [ | discriminate ].
    cbn beta iota in Heval.
    destruct Hin as [Hin | Hin]; [ | exact (IH _ _ s elements Heval Hin) ].
    destruct const as [ | | | | | elements0]; try destruct Hin.
    cbn [table_of_binding] in Hin.
    destruct (forallb element_closed elements0) eqn:Hclosed;
      [ | destruct Hin ].
    destruct Hin as [[= <- <-] | []].
    cbn [eval_static_const] in Hconst.
    rewrite (eval_closed_elements vars elements0 Hclosed) in Hconst.
    destruct (eval_simples [] elements0) as [vs | ]; [ | discriminate ].
    injection Hconst as <-.
    exists vs. split; [ reflexivity | ].
    destruct (eval_static_bindings_extend vars bindings _ extended Heval)
      as [_ Hvalues].
    apply Hvalues. simpl. rewrite Pos.eqb_refl. reflexivity.
Qed.

Lemma tables_under_statics_bound (tables : known_tables)
    (bindings : list static_binding) (vars : env)
    (statics extended : static_env) :
  tables_bound tables statics ->
  eval_static_bindings vars bindings statics = Some extended ->
  tables_bound (tables_under_statics tables bindings) extended.
Proof.
  intros Hbound Heval s elements Hin.
  unfold tables_under_statics in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - exact (group_tables_bound vars bindings statics extended s elements Heval
      Hin).
  - exact (tables_bound_extend tables statics extended Hbound
      (eval_static_bindings_extend vars bindings statics extended Heval)
      s elements Hin).
Qed.

(* ======================================================================== *)
(* Down a term                                                              *)
(* ======================================================================== *)

(* The rewrite leaves what binds something static as it is. *)
Lemma merge_switch_by_table_binds_statics (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) (merged : expr) :
  merge_switch_by_table tables scrutinee arms = Some merged ->
  binds_statics merged = false.
Proof.
  unfold merge_switch_by_table.
  destruct scrutinee as [v | sym | c]; try discriminate.
  destruct arms as [ | [first ac] [ | arm1 [ | arm2 others]]];
    try discriminate.
  cbv zeta.
  destruct (var_in_simples v _); [ | discriminate ].
  destruct (find _ tables) as [[s elements] | ]; [ | discriminate ].
  intros [= <-].
  unfold bind_table_load, bind_tagged, bind_table_offset.
  destruct (first =? 0); reflexivity.
Qed.

Lemma merge_switch_with_tables_binds_statics (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) :
  binds_statics (merge_switch_with_tables tables scrutinee arms) = false.
Proof.
  rewrite merge_switch_with_tables_unfold.
  destruct (merge_switch_by_table tables scrutinee arms) as [merged | ]
    eqn:Hmerged; [ | reflexivity ].
  destruct (merge_switch scrutinee arms); try reflexivity.
  exact (merge_switch_by_table_binds_statics tables scrutinee arms merged
    Hmerged).
Qed.

Fixpoint merge_tables_knowing_binds_statics (e : expr) :
  ∀ tables : known_tables,
    binds_statics (merge_tables_knowing tables e) = binds_statics e.
Proof.
  destruct e
    as [ x kind d body | bindings body | k h body | handlers body
       | ap | ac | scrutinee arms | ];
    intros tables;
    cbn [merge_tables_knowing merge_tables_in_handler binds_statics];
    try reflexivity.
  - apply merge_tables_knowing_binds_statics.
  - rewrite merge_tables_knowing_binds_statics. reflexivity.
  - destruct h as [params metadata handler].
    cbn [merge_tables_in_handler handler_binds_statics].
    rewrite !merge_tables_knowing_binds_statics. reflexivity.
  - rewrite merge_tables_knowing_binds_statics. f_equal.
    induction handlers as [ | [k [params metadata handler]] handlers IH];
      simpl; [ reflexivity | ].
    rewrite merge_tables_knowing_binds_statics, IH. reflexivity.
  - apply merge_switch_with_tables_binds_statics.
Qed.

Lemma merge_tables_knowing_handlers_bind_statics (tables : known_tables)
    (handlers : list (continuation * continuation_handler)) :
  handlers_bind_statics
    (map (fun '(k, h) => (k, merge_tables_in_handler tables h)) handlers)
  = handlers_bind_statics handlers.
Proof.
  unfold handlers_bind_statics.
  induction handlers as [ | [k [params metadata handler]] handlers IH]; simpl;
    [ reflexivity | ].
  rewrite merge_tables_knowing_binds_statics, IH. reflexivity.
Qed.

Fixpoint merge_tables_knowing_refines_aux (e : expr) :
  ∀ (tables : known_tables) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap),
    tables_bound tables statics ->
    refines (State e vars conts statics hp)
      (State (merge_tables_knowing tables e) vars conts statics hp).
Proof.
  destruct e
    as [ x kind d body | bindings body | k h body | handlers body
       | ap | ac | scrutinee arms | ];
    intros tables vars conts statics hp Hbound;
    cbn [merge_tables_knowing]; try apply refines_refl.
  - apply let_refines_step; [ reflexivity | intros v _ _ ].
    apply merge_tables_knowing_refines_aux, Hbound.
  - apply let_static_refines_step.
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hbindings; [ | exact I ].
    apply merge_tables_knowing_refines_aux.
    exact (tables_under_statics_bound tables bindings vars statics extended
      Hbound Hbindings).
  - destruct h as [params metadata handler].
    cbn [merge_tables_in_handler].
    apply (refines_trans _
      (State
         (Let_cont_non_recursive k
            (Handler params metadata (merge_tables_knowing tables handler))
            body)
         vars conts statics hp)).
    + apply (let_cont_handler_refines_where (tables_bound tables)
        (tables_bound_extend tables)); [ exact Hbound | ].
      intros vs handler_vars conts' statics' hp' Hbound' _ _.
      apply merge_tables_knowing_refines_aux, Hbound'.
    + apply let_cont_non_recursive_refines_step,
        merge_tables_knowing_refines_aux, Hbound.
  - apply (refines_trans _
      (State
         (Let_cont_recursive
            (map (fun '(k, h) => (k, merge_tables_in_handler tables h))
               handlers)
            body)
         vars conts statics hp)).
    + assert (Hhandlers :
        handlers_refine (tables_bound tables) vars handlers
          (map (fun '(k, h) => (k, merge_tables_in_handler tables h))
             handlers)).
      { induction handlers
          as [ | [k [params metadata handler]] handlers IH];
          simpl.
        - split; apply Forall2_nil.
        - destruct IH as [Hforwards Hbackwards].
          split; (apply Forall2_cons; [ | assumption ]);
            (split; [ reflexivity | ]); apply Handler_related;
            intros vs handler_vars conts' statics' hp' Hbound' _ _;
            apply merge_tables_knowing_refines_aux, Hbound'. }
      destruct Hhandlers as [Hforwards Hbackwards].
      apply (let_cont_recursive_handlers_refine_where
        (tables_bound tables) (tables_bound_extend tables));
        try assumption.
      symmetry. apply merge_tables_knowing_handlers_bind_statics.
    + apply let_cont_recursive_refines_step; [ reflexivity | intros _ ].
      apply merge_tables_knowing_refines_aux, Hbound.
  - apply merge_switch_with_tables_refines, Hbound.
Qed.

Theorem merge_tables_knowing_refines : merge_tables_knowing_refines_statement.
Proof.
  intros tables e vars conts statics hp Hbound.
  apply merge_tables_knowing_refines_aux, Hbound.
Qed.

(* ======================================================================== *)
(* In the bodies of code                                                    *)
(* ======================================================================== *)

(* The tables of a group are those of the group with its code
   rewritten. *)
Lemma tables_under_rewritten_code (g : expr -> expr) (tables : known_tables)
    (bindings : list static_binding) :
  tables_under_statics tables (map (rewrite_code_in_binding g) bindings)
  = tables_under_statics tables bindings.
Proof.
  unfold tables_under_statics. f_equal.
  induction bindings as [ | binding bindings IH]; [ reflexivity | ].
  cbn [map flat_map]. rewrite IH.
  destruct binding
    as [id [params my_closure ret exn metadata body] | id | s const];
    reflexivity.
Qed.

(* The code of a group refines its counterparts where the tables are
   bound. *)
Lemma merged_bindings_refine (tables : known_tables)
    (bindings : list static_binding) :
  bindings_refine (tables_bound tables) bindings
    (map (rewrite_code_in_binding (merge_tables_knowing tables)) bindings).
Proof.
  induction bindings
    as [ | [id [params my_closure ret exn metadata code_body] | id
           | sym const]
           bindings [Hforwards Hbackwards]];
    simpl.
  - split; apply Forall2_nil.
  - unfold rewrite_code_body.
    destruct (Bool.eqb (binds_statics code_body)
                (binds_statics (merge_tables_knowing tables code_body)))
      eqn:Hbinds;
      [ apply eqb_prop in Hbinds | ];
      split; (apply Forall2_cons; [ | assumption ]);
      try apply Binding_same;
      apply Binding_code, Codes_related;
      first
        [ exact Hbinds | exact (eq_sym Hbinds)
        | intros vars conts statics Hbound;
          apply merge_tables_knowing_refines_aux; assumption ].
  - split; (apply Forall2_cons; [ apply Binding_same | assumption ]).
  - split; (apply Forall2_cons; [ apply Binding_same | assumption ]).
Qed.

Fixpoint merge_tables_in_code_binds_statics (e : expr) :
  ∀ tables : known_tables,
    binds_statics (merge_tables_in_code tables e) = binds_statics e.
Proof.
  destruct e
    as [ x kind d body | bindings body | k h body | handlers body
       | ap | ac | scrutinee arms | ];
    intros tables;
    cbn [merge_tables_in_code merge_tables_in_code_in_handler binds_statics];
    cbv zeta; try reflexivity.
  - apply merge_tables_in_code_binds_statics.
  - rewrite merge_tables_in_code_binds_statics. f_equal.
    generalize
      (merge_tables_knowing (tables_under_statics tables bindings)).
    intros g.
    induction bindings
      as [ | [id [params my_closure ret exn metadata code_body] | id
             | sym const]
             bindings IH];
      simpl; congruence.
  - destruct h as [params metadata handler].
    cbn [merge_tables_in_code_in_handler handler_binds_statics].
    rewrite !merge_tables_in_code_binds_statics. reflexivity.
  - rewrite merge_tables_in_code_binds_statics. f_equal.
    induction handlers as [ | [k [params metadata handler]] handlers IH];
      simpl; [ reflexivity | ].
    rewrite merge_tables_in_code_binds_statics, IH. reflexivity.
Qed.

Lemma merge_tables_in_code_handlers_bind_statics (tables : known_tables)
    (handlers : list (continuation * continuation_handler)) :
  handlers_bind_statics
    (map (fun '(k, h) => (k, merge_tables_in_code_in_handler tables h))
       handlers)
  = handlers_bind_statics handlers.
Proof.
  unfold handlers_bind_statics.
  induction handlers as [ | [k [params metadata handler]] handlers IH]; simpl;
    [ reflexivity | ].
  rewrite merge_tables_in_code_binds_statics, IH. reflexivity.
Qed.

(* Down the term, with the static environment binding the tables: at
   once in a body, and from then on in a handler and in code. *)
Fixpoint merge_tables_in_code_refines_aux (e : expr) :
  ∀ (tables : known_tables) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap),
    tables_bound tables statics ->
    refines (State e vars conts statics hp)
      (State (merge_tables_in_code tables e) vars conts statics hp).
Proof.
  destruct e
    as [ x kind d body | bindings body | k h body | handlers body
       | ap | ac | scrutinee arms | ];
    intros tables vars conts statics hp Hbound;
    cbn [merge_tables_in_code]; cbv zeta; try apply refines_refl.
  - apply let_refines_step; [ reflexivity | intros v _ _ ].
    apply merge_tables_in_code_refines_aux, Hbound.
  - (* the code of the group is rewritten with the tables of the group
       in scope: the body under the one static environment refines it
       under the other; then down the body *)
    set (tables' := tables_under_statics tables bindings).
    destruct (merged_bindings_refine tables' bindings)
      as [Hforwards Hbackwards].
    apply (fun H =>
      eval_static_bindings_related _ vars _ _ H statics statics
        (statics_related_refl _ statics)) in Hforwards, Hbackwards.
    apply let_static_refines_step.
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hbindings,
      (eval_static_bindings vars
         (map (rewrite_code_in_binding (merge_tables_knowing tables'))
            bindings)
         statics)
      as [extended' | ] eqn:Hbindings';
      try contradiction; [ | exact I ].
    assert (Hbound' : tables_bound tables' extended).
    { exact (tables_under_statics_bound tables bindings vars statics extended
        Hbound Hbindings). }
    assert (Hbound'' : tables_bound tables' extended').
    { unfold tables' at 1.
      rewrite <-
        (tables_under_rewritten_code (merge_tables_knowing tables') tables
           bindings).
      exact (tables_under_statics_bound tables _ vars statics extended'
        Hbound Hbindings'). }
    apply (refines_trans _ (State body vars conts extended' hp)).
    + apply (related_states_refines (tables_bound tables')
        (tables_bound_extend tables'));
        [ exact Hbound' | exact Hbound'' | apply cont_env_related_refl
        | apply cont_env_related_refl | exact Hforwards | exact Hbackwards ].
    + apply merge_tables_in_code_refines_aux, Hbound''.
  - destruct h as [params metadata handler].
    cbn [merge_tables_in_code_in_handler].
    apply (refines_trans _
      (State
         (Let_cont_non_recursive k
            (Handler params metadata (merge_tables_in_code tables handler))
            body)
         vars conts statics hp)).
    + apply (let_cont_handler_refines_where (tables_bound tables)
        (tables_bound_extend tables)); [ exact Hbound | ].
      intros vs handler_vars conts' statics' hp' Hbound' _ _.
      apply merge_tables_in_code_refines_aux, Hbound'.
    + apply let_cont_non_recursive_refines_step,
        merge_tables_in_code_refines_aux, Hbound.
  - apply (refines_trans _
      (State
         (Let_cont_recursive
            (map
               (fun '(k, h) =>
                  (k, merge_tables_in_code_in_handler tables h))
               handlers)
            body)
         vars conts statics hp)).
    + assert (Hhandlers :
        handlers_refine (tables_bound tables) vars handlers
          (map
             (fun '(k, h) => (k, merge_tables_in_code_in_handler tables h))
             handlers)).
      { induction handlers
          as [ | [k [params metadata handler]] handlers IH];
          simpl.
        - split; apply Forall2_nil.
        - destruct IH as [Hforwards Hbackwards].
          split; (apply Forall2_cons; [ | assumption ]);
            (split; [ reflexivity | ]); apply Handler_related;
            intros vs handler_vars conts' statics' hp' Hbound' _ _;
            apply merge_tables_in_code_refines_aux, Hbound'. }
      destruct Hhandlers as [Hforwards Hbackwards].
      apply (let_cont_recursive_handlers_refine_where
        (tables_bound tables) (tables_bound_extend tables));
        try assumption.
      symmetry. apply merge_tables_in_code_handlers_bind_statics.
    + apply let_cont_recursive_refines_step; [ reflexivity | intros _ ].
      apply merge_tables_in_code_refines_aux, Hbound.
Qed.

Theorem merge_tables_in_code_refines : merge_tables_in_code_refines_statement.
Proof.
  intros tables e vars conts statics hp Hbound.
  apply merge_tables_in_code_refines_aux, Hbound.
Qed.

Theorem merge_tables_refines : merge_tables_refines_statement.
Proof.
  intros e vars conts statics hp. unfold merge_tables.
  eapply refines_trans.
  - apply merge_tables_knowing_refines_aux, no_tables_bound.
  - apply merge_tables_in_code_refines_aux, no_tables_bound.
Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

(* The elements of the tables in scope have no variable. *)
Definition tables_closed (tables : known_tables) : Prop :=
  ∀ (s : symbol) (elements : list simple),
    (s, elements) ∈ tables -> forallb element_closed elements = true.

Lemma element_closed_renamed (r : renaming) (s : simple) :
  element_closed (rename_simple r s) = element_closed s.
Proof. destruct s; reflexivity. Qed.

Lemma closed_element_renamed (r : renaming) (s : simple) :
  element_closed s = true -> rename_simple r s = s.
Proof. destruct s; [ discriminate | reflexivity | reflexivity ]. Qed.

Lemma closed_elements_renamed (r : renaming) (elements : list simple) :
  forallb element_closed elements = true ->
  map (rename_simple r) elements = elements.
Proof.
  induction elements as [ | element elements IH]; simpl; [ reflexivity | ].
  intros Hclosed. apply andb_prop in Hclosed as [Helement Hclosed].
  rewrite (closed_element_renamed r element Helement), (IH Hclosed).
  reflexivity.
Qed.

Lemma table_of_binding_renamed (r : renaming) (binding : static_binding) :
  table_of_binding (rename_static_binding r binding)
  = table_of_binding binding.
Proof.
  destruct binding as [id c | id | s const]; try reflexivity.
  destruct const as [ | | | | | elements]; try reflexivity.
  cbn [rename_static_binding rename_static_const table_of_binding].
  rewrite (forallb_under_map _ _ element_closed)
    by apply element_closed_renamed.
  destruct (forallb element_closed elements) eqn:Hclosed; [ | reflexivity ].
  rewrite (closed_elements_renamed r elements Hclosed). reflexivity.
Qed.

Lemma tables_under_statics_renamed (r : renaming) (tables : known_tables)
    (bindings : list static_binding) :
  tables_under_statics tables (map (rename_static_binding r) bindings)
  = tables_under_statics tables bindings.
Proof.
  unfold tables_under_statics. f_equal.
  induction bindings as [ | binding bindings IH]; [ reflexivity | ].
  cbn [map flat_map]. rewrite table_of_binding_renamed, IH. reflexivity.
Qed.

Lemma no_tables_closed : tables_closed [].
Proof. intros s elements []. Qed.

Lemma tables_under_statics_closed (tables : known_tables)
    (bindings : list static_binding) :
  tables_closed tables ->
  tables_closed (tables_under_statics tables bindings).
Proof.
  intros Hclosed s elements Hin. unfold tables_under_statics in Hin.
  apply in_app_or in Hin as [Hin | Hin]; [ | exact (Hclosed s elements Hin) ].
  apply in_flat_map in Hin as (binding & _ & Hin).
  destruct binding as [id c | id | s0 const]; try destruct Hin.
  destruct const as [ | | | | | elements0]; try destruct Hin.
  cbn [table_of_binding] in Hin.
  destruct (forallb element_closed elements0) eqn:Hclosed0;
    [ | destruct Hin ].
  destruct Hin as [[= <- <-] | []]. exact Hclosed0.
Qed.

Lemma element_for_renamed (r : renaming) (v : variable) (element : simple)
    (s : simple) :
  element_closed element = true ->
  element_for (rename_variable r v) element (rename_simple r s)
  = rename_simple r (element_for v element s).
Proof.
  intros Hclosed. destruct s as [x | sym | c]; simpl; try reflexivity.
  rewrite rename_variable_eqb.
  destruct (Pos.eqb x v); [ | reflexivity ].
  symmetry. exact (closed_element_renamed r element Hclosed).
Qed.

Lemma elements_for_renamed (r : renaming) (v : variable) (element : simple)
    (args : list simple) :
  element_closed element = true ->
  map (element_for (rename_variable r v) element)
    (map (rename_simple r) args)
  = map (rename_simple r) (map (element_for v element) args).
Proof.
  intros Hclosed. rewrite !map_map. apply map_ext. intros s.
  apply element_for_renamed, Hclosed.
Qed.

Lemma table_element_closed (first offset : Z) (elements : list simple)
    (i : Z) (element : simple) :
  forallb element_closed elements = true ->
  table_element first offset elements i = Some element ->
  element_closed element = true.
Proof.
  intros Hclosed Helement. unfold table_element in Helement.
  destruct (table_index first offset i) as [index | ]; [ | discriminate ].
  cbn beta iota in Helement.
  destruct (_ && _); [ | discriminate ].
  apply nth_error_In in Helement.
  rewrite forallb_forall in Hclosed. exact (Hclosed element Helement).
Qed.

Lemma arm_is_loaded_renamed (r : renaming) (v : variable)
    (merged : apply_cont) (first offset : Z) (elements : list simple)
    (immediates : bool) (arm : Z * apply_cont) :
  forallb element_closed elements = true ->
  arm_is_loaded (rename_variable r v) (rename_apply_cont r merged) first
    offset elements immediates (fst arm, rename_apply_cont r (snd arm))
  = arm_is_loaded v merged first offset elements immediates arm.
Proof.
  intros Hclosed. unfold arm_is_loaded. cbn [fst snd].
  destruct (table_element first offset elements (fst arm)) as [element | ]
    eqn:Helement; [ | reflexivity ].
  f_equal.
  set (target :=
    Apply_cont_expr (ac_continuation merged)
      (map (element_for v element) (ac_args merged))
      (ac_trap_action merged)).
  replace
    (Apply_cont_expr (ac_continuation (rename_apply_cont r merged))
       (map (element_for (rename_variable r v) element)
          (ac_args (rename_apply_cont r merged)))
       (ac_trap_action (rename_apply_cont r merged)))
    with (rename_apply_cont r target).
  - destruct (apply_cont_eq_dec (snd arm) target) as [-> | Hne],
      (apply_cont_eq_dec (rename_apply_cont r _) (rename_apply_cont r _))
        as [Heq | Hne'];
      try reflexivity; [ contradiction | ].
    elim Hne. exact (renamed_apply_cont_same r _ _ Heq).
  - unfold target, rename_apply_cont. cbn [ac_continuation ac_args
      ac_trap_action].
    rewrite elements_for_renamed; [ reflexivity | ].
    exact (table_element_closed first offset elements _ element Hclosed
      Helement).
Qed.

Lemma table_has_arms_renamed (r : renaming) (v : variable)
    (merged : apply_cont) (first offset : Z) (arms : list (Z * apply_cont))
    (table : symbol * list simple) :
  forallb element_closed (snd table) = true ->
  table_has_arms (rename_variable r v) (rename_apply_cont r merged) first
    offset (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
    table
  = table_has_arms v merged first offset arms table.
Proof.
  intros Hclosed. unfold table_has_arms. rewrite length_map. f_equal.
  cbv zeta. apply forallb_under_map. intros arm.
  apply arm_is_loaded_renamed, Hclosed.
Qed.

Lemma merged_across_renamed (r : renaming) (v : variable)
    (arms : list (Z * apply_cont)) :
  ∀ args : list simple,
    merged_across (rename_variable r v) (map (rename_simple r) args)
      (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
    = map (rename_simple r) (merged_across v args arms).
Proof.
  induction arms as [ | arm arms IH]; intros args; [ reflexivity | ].
  cbn [map merged_across snd].
  change (ac_args (rename_apply_cont r (snd arm)))
    with (map (rename_simple r) (ac_args (snd arm))).
  rewrite merged_arguments_renamed. apply IH.
Qed.

Lemma find_same_among {A : Type} (f g : A -> bool) (l : list A) :
  (∀ a : A, a ∈ l -> f a = g a) -> find f l = find g l.
Proof.
  induction l as [ | a l IH]; intros Hsame; [ reflexivity | ].
  cbn [find]. rewrite (Hsame a (or_introl eq_refl)).
  destruct (g a); [ reflexivity | ].
  apply IH. intros a' Hin. apply Hsame. right. exact Hin.
Qed.

Lemma bind_table_load_renamed (r : renaming) (v : variable) (s : symbol)
    (first offset : Z) (immediates : bool) (body : expr) :
  bind_table_load (rename_variable r v) s first offset immediates
    (rename_expr r body)
  = rename_expr r (bind_table_load v s first offset immediates body).
Proof.
  unfold bind_table_load, bind_tagged, bind_table_offset.
  destruct (first =? 0); reflexivity.
Qed.

Lemma merge_switch_by_table_renamed (r : renaming) (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) :
  tables_closed tables ->
  merge_switch_by_table tables (rename_simple r scrutinee)
    (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  = option_map (rename_expr r) (merge_switch_by_table tables scrutinee arms).
Proof.
  intros Hclosed.
  destruct scrutinee as [v | sym | c]; try reflexivity.
  destruct arms as [ | [first ac] [ | arm1 [ | arm2 others]]];
    try reflexivity.
  unfold merge_switch_by_table. cbn [map fst snd rename_simple]. cbv zeta.
  set (merged :=
    Apply_cont_expr (ac_continuation ac)
      (merged_across v (ac_args ac) (arm1 :: arm2 :: others)) None).
  replace
    (Apply_cont_expr (ac_continuation (rename_apply_cont r ac))
       (merged_across (rename_variable r v)
          (ac_args (rename_apply_cont r ac))
          ((fst arm1, rename_apply_cont r (snd arm1))
           :: (fst arm2, rename_apply_cont r (snd arm2))
           :: map (fun arm => (fst arm, rename_apply_cont r (snd arm)))
                others))
       None)
    with (rename_apply_cont r merged)
    by (unfold merged, rename_apply_cont;
        cbn [ac_continuation ac_args ac_trap_action option_map];
        rewrite <- (merged_across_renamed r v (arm1 :: arm2 :: others));
        reflexivity).
  change (ac_args (rename_apply_cont r merged))
    with (map (rename_simple r) (ac_args merged)).
  rewrite var_in_simples_renamed.
  destruct (var_in_simples v (ac_args merged)); [ | reflexivity ].
  change
    ((first, rename_apply_cont r ac)
     :: (fst arm1, rename_apply_cont r (snd arm1))
     :: (fst arm2, rename_apply_cont r (snd arm2))
     :: map (fun arm => (fst arm, rename_apply_cont r (snd arm))) others)
    with
      (map (fun arm => (fst arm, rename_apply_cont r (snd arm)))
         ((first, ac) :: arm1 :: arm2 :: others)).
  rewrite
    (find_same_among _
       (table_has_arms v merged first (table_offset first)
          ((first, ac) :: arm1 :: arm2 :: others))
       tables).
  - destruct (find _ tables) as [[s elements] | ]; [ | reflexivity ].
    cbn [option_map]. f_equal.
    exact (bind_table_load_renamed r v s first _ _ (Apply_cont merged)).
  - intros [s elements] Hin. apply table_has_arms_renamed.
    exact (Hclosed s elements Hin).
Qed.

Lemma merge_switch_with_tables_renamed (r : renaming) (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) :
  tables_closed tables ->
  merge_switch_with_tables tables (rename_simple r scrutinee)
    (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  = rename_expr r (merge_switch_with_tables tables scrutinee arms).
Proof.
  intros Hclosed. rewrite !merge_switch_with_tables_unfold.
  rewrite merge_switch_equivariant,
    (merge_switch_by_table_renamed r tables scrutinee arms Hclosed).
  destruct (merge_switch_by_table tables scrutinee arms); [ | reflexivity ].
  cbn [option_map].
  destruct (merge_switch scrutinee arms); reflexivity.
Qed.

Fixpoint merge_tables_knowing_equivariant (r : renaming) (e : expr) :
  ∀ tables : known_tables,
    tables_closed tables ->
    merge_tables_knowing tables (rename_expr r e)
    = rename_expr r (merge_tables_knowing tables e)
with merge_tables_in_handler_equivariant (r : renaming)
    (h : continuation_handler) :
  ∀ tables : known_tables,
    tables_closed tables ->
    merge_tables_in_handler tables (rename_handler r h)
    = rename_handler r (merge_tables_in_handler tables h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros tables Hclosed; cbn [rename_expr merge_tables_knowing];
      try reflexivity.
    + rewrite (merge_tables_knowing_equivariant r body tables Hclosed).
      reflexivity.
    + rewrite tables_under_statics_renamed,
        (merge_tables_knowing_equivariant r body _
           (tables_under_statics_closed tables bindings Hclosed)).
      reflexivity.
    + rewrite (merge_tables_in_handler_equivariant r h tables Hclosed),
        (merge_tables_knowing_equivariant r body tables Hclosed).
      reflexivity.
    + rewrite (merge_tables_knowing_equivariant r body tables Hclosed).
      f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (merge_tables_in_handler_equivariant r h tables Hclosed), IH.
      reflexivity.
    + apply merge_switch_with_tables_renamed, Hclosed.
  - destruct h as [params metadata handler]. intros tables Hclosed.
    cbn [rename_handler merge_tables_in_handler].
    rewrite (merge_tables_knowing_equivariant r handler tables Hclosed).
    reflexivity.
Qed.

Lemma merged_body_renamed (tables : known_tables) (r : renaming)
    (body : expr) :
  tables_closed tables ->
  rewrite_code_body (merge_tables_knowing tables) (rename_expr r body)
  = rename_expr r (rewrite_code_body (merge_tables_knowing tables) body).
Proof.
  intros Hclosed. unfold rewrite_code_body.
  rewrite (merge_tables_knowing_equivariant r body tables Hclosed),
    !rename_binds_statics.
  destruct (Bool.eqb (binds_statics body)
              (binds_statics (merge_tables_knowing tables body)));
    reflexivity.
Qed.

Lemma merged_binding_renamed (tables : known_tables) (r : renaming)
    (binding : static_binding) :
  tables_closed tables ->
  rewrite_code_in_binding (merge_tables_knowing tables)
    (rename_static_binding r binding)
  = rename_static_binding r
      (rewrite_code_in_binding (merge_tables_knowing tables) binding).
Proof.
  intros Hclosed.
  destruct binding
    as [id [params my_closure ret exn metadata body] | id | sym const];
    try reflexivity.
  cbn [rename_static_binding rename_code rewrite_code_in_binding].
  rewrite (merged_body_renamed tables _ _ Hclosed). reflexivity.
Qed.

Fixpoint merge_tables_in_code_equivariant (r : renaming) (e : expr) :
  ∀ tables : known_tables,
    tables_closed tables ->
    merge_tables_in_code tables (rename_expr r e)
    = rename_expr r (merge_tables_in_code tables e)
with merge_tables_in_code_in_handler_equivariant (r : renaming)
    (h : continuation_handler) :
  ∀ tables : known_tables,
    tables_closed tables ->
    merge_tables_in_code_in_handler tables (rename_handler r h)
    = rename_handler r (merge_tables_in_code_in_handler tables h).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros tables Hclosed; cbn [rename_expr merge_tables_in_code];
      cbv zeta; try reflexivity.
    + rewrite (merge_tables_in_code_equivariant r body tables Hclosed).
      reflexivity.
    + rewrite tables_under_statics_renamed,
        (merge_tables_in_code_equivariant r body _
           (tables_under_statics_closed tables bindings Hclosed)),
        !map_map.
      f_equal. apply map_ext. intros binding.
      apply merged_binding_renamed, tables_under_statics_closed, Hclosed.
    + rewrite
        (merge_tables_in_code_in_handler_equivariant r h tables Hclosed),
        (merge_tables_in_code_equivariant r body tables Hclosed).
      reflexivity.
    + rewrite (merge_tables_in_code_equivariant r body tables Hclosed).
      f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite
        (merge_tables_in_code_in_handler_equivariant r h tables Hclosed), IH.
      reflexivity.
  - destruct h as [params metadata handler]. intros tables Hclosed.
    cbn [rename_handler merge_tables_in_code_in_handler].
    rewrite (merge_tables_in_code_equivariant r handler tables Hclosed).
    reflexivity.
Qed.

Theorem merge_tables_equivariant : merge_tables_equivariant_statement.
Proof.
  intros r e. unfold merge_tables.
  rewrite (merge_tables_knowing_equivariant r e [] no_tables_closed).
  exact (merge_tables_in_code_equivariant r _ [] no_tables_closed).
Qed.

(* ======================================================================== *)
(* A term with no table                                                     *)
(* ======================================================================== *)

Lemma no_tables_under_statics (bindings : list static_binding) :
  forallb binding_binds_no_table bindings = true ->
  tables_under_statics [] bindings = [].
Proof.
  unfold tables_under_statics. rewrite app_nil_r.
  induction bindings as [ | binding bindings IH]; [ reflexivity | ].
  cbn [forallb flat_map]. intros Hnone.
  apply andb_prop in Hnone as [Hbinding Hnone]. rewrite (IH Hnone).
  destruct binding as [id c | id | s const]; try reflexivity.
  destruct const; try reflexivity. discriminate Hbinding.
Qed.

Fixpoint merge_tables_knowing_without_tables (e : expr) :
  binds_no_table e = true -> merge_tables_knowing [] e = e
with merge_tables_in_handler_without_tables (h : continuation_handler) :
  handler_binds_no_table h = true -> merge_tables_in_handler [] h = h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [binds_no_table merge_tables_knowing]; intros Hnone;
      try reflexivity.
    + rewrite (merge_tables_knowing_without_tables body Hnone). reflexivity.
    + apply andb_prop in Hnone as [Hbindings Hbody].
      rewrite (no_tables_under_statics bindings Hbindings),
        (merge_tables_knowing_without_tables body Hbody).
      reflexivity.
    + apply andb_prop in Hnone as [Hhandler Hbody].
      rewrite (merge_tables_in_handler_without_tables h Hhandler),
        (merge_tables_knowing_without_tables body Hbody).
      reflexivity.
    + apply andb_prop in Hnone as [Hhandlers Hbody].
      rewrite (merge_tables_knowing_without_tables body Hbody). f_equal.
      induction handlers as [ | [k h] handlers IH]; [ reflexivity | ].
      cbn [forallb map] in Hhandlers |- *.
      apply andb_prop in Hhandlers as [Hhandler Hhandlers].
      rewrite (merge_tables_in_handler_without_tables h Hhandler),
        (IH Hhandlers).
      reflexivity.
  - destruct h as [params metadata handler].
    cbn [handler_binds_no_table merge_tables_in_handler]. intros Hnone.
    rewrite (merge_tables_knowing_without_tables handler Hnone). reflexivity.
Qed.

Lemma merged_binding_without_tables (binding : static_binding) :
  binding_binds_no_table binding = true ->
  rewrite_code_in_binding (merge_tables_knowing []) binding = binding.
Proof.
  destruct binding
    as [id [params my_closure ret exn metadata body] | id | s const];
    try reflexivity.
  cbn [binding_binds_no_table code_binds_no_table rewrite_code_in_binding].
  intros Hnone. unfold rewrite_code_body.
  rewrite (merge_tables_knowing_without_tables body Hnone).
  destruct (Bool.eqb _ _); reflexivity.
Qed.

Fixpoint merge_tables_in_code_without_tables (e : expr) :
  binds_no_table e = true -> merge_tables_in_code [] e = e
with merge_tables_in_code_in_handler_without_tables
    (h : continuation_handler) :
  handler_binds_no_table h = true ->
  merge_tables_in_code_in_handler [] h = h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [binds_no_table merge_tables_in_code]; cbv zeta; intros Hnone;
      try reflexivity.
    + rewrite (merge_tables_in_code_without_tables body Hnone). reflexivity.
    + apply andb_prop in Hnone as [Hbindings Hbody].
      rewrite (no_tables_under_statics bindings Hbindings),
        (merge_tables_in_code_without_tables body Hbody).
      f_equal.
      induction bindings as [ | binding bindings IH]; [ reflexivity | ].
      cbn [forallb map] in Hbindings |- *.
      apply andb_prop in Hbindings as [Hbinding Hbindings].
      rewrite (merged_binding_without_tables binding Hbinding),
        (IH Hbindings).
      reflexivity.
    + apply andb_prop in Hnone as [Hhandler Hbody].
      rewrite (merge_tables_in_code_in_handler_without_tables h Hhandler),
        (merge_tables_in_code_without_tables body Hbody).
      reflexivity.
    + apply andb_prop in Hnone as [Hhandlers Hbody].
      rewrite (merge_tables_in_code_without_tables body Hbody). f_equal.
      induction handlers as [ | [k h] handlers IH]; [ reflexivity | ].
      cbn [forallb map] in Hhandlers |- *.
      apply andb_prop in Hhandlers as [Hhandler Hhandlers].
      rewrite (merge_tables_in_code_in_handler_without_tables h Hhandler),
        (IH Hhandlers).
      reflexivity.
  - destruct h as [params metadata handler].
    cbn [handler_binds_no_table merge_tables_in_code_in_handler].
    intros Hnone.
    rewrite (merge_tables_in_code_without_tables handler Hnone). reflexivity.
Qed.

Theorem merge_tables_without_tables : merge_tables_without_tables_statement.
Proof.
  intros e Hnone. unfold merge_tables.
  rewrite (merge_tables_knowing_without_tables e Hnone).
  exact (merge_tables_in_code_without_tables e Hnone).
Qed.

(* ======================================================================== *)
(* Two terms                                                                *)
(* ======================================================================== *)

Theorem merge_tables_example : merge_tables_example_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem merge_tables_equal_elements_example :
  merge_tables_equal_elements_example_statement.
Proof. vm_compute. reflexivity. Qed.
