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


(* Proofs of the statements of FlambdaJoinSpec.v. *)

From Stdlib Require Import ZArith List Bool PeanoNat Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec FlambdaMapProofs
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesProofs
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaJoinEnv FlambdaJoinTypes
  FlambdaJoinSpec.
Import ListNotations.
Import FlambdaJoinSpec.Interim.

(* ======================================================================== *)
(* Small facts                                                              *)
(* ======================================================================== *)

(* A variable that may occur in terms is known. *)
Lemma in_scope_in_terms_knows (tenv : Typing_env.t) (x : variable) :
  in_scope_in_terms tenv x -> knows tenv x.
Proof.
  unfold in_scope_in_terms, knows, Typing_env.mem.
  destruct
    (Keyed.lookup name_eqb (Name_var x) (Typing_env.names_to_types tenv))
    as [[ty binding_time_and_mode] | ]; [ reflexivity | discriminate ].
Qed.

(* The environment that knows nothing is satisfied strictly by every
   valuation. *)
Lemma create_satisfied_strictly (statics : static_env) (valuation : env) :
  typing_env_satisfied_strictly statics valuation Typing_env.create.
Proof.
  split; [ reflexivity | ]. split.
  - intros n ty binding_time_and_mode v Hlookup. discriminate.
  - apply empty_respected.
Qed.

(* The one use of a list of one. *)
Lemma use_at_singleton {A : Type} (source : Typing_env.t) (scope : Scope.t)
    (id : A) (tenv use : Typing_env.t) (index : Index.t) :
  use_at {| source := source; cut_after := scope; uses := [(id, tenv)] |}
    index use ->
  use = tenv.
Proof.
  intros [id' Hnth]. cbn in Hnth. destruct index as [ | index]; cbn in Hnth.
  - injection Hnth as _ <-. reflexivity.
  - destruct index; discriminate.
Qed.

(* ======================================================================== *)
(* The contract is neither empty nor met by everything                      *)
(* ======================================================================== *)

Theorem join_to_source_sound : join_to_source_sound_statement.
Proof.
  intros typing_env_well_formed A avoid inputs target analysis
    [[Hsource _] _] Hrefine Hjoin.
  injection Hjoin as <- <-.
  split; [ exact Hsource | ]. split; [ | split; [ | split ] ].
  - split; [ | repeat split ].
    intros n ty binding_time_and_mode Hlookup. exists ty. exact Hlookup.
  - intros x Hknown Hnot_known. contradiction.
  - split; [ | split ].
    + intros index id Hlookup. discriminate.
    + intros x simples kind index simple Hlookup. discriminate.
    + intros x simples kind index simple Hlookup. discriminate.
  - intros index use Huse statics valuation Hsatisfied.
    destruct (Hrefine index use Huse statics valuation Hsatisfied)
      as [valuation0 [Hsource0 Hagrees]].
    exists valuation0. split; [ exact Hsource0 | ].
    split; [ exact Hagrees | ].
    split; intros x simples kind simple Hlookup; discriminate.
Qed.

Theorem join_to_bottom_unsound : join_to_bottom_unsound_statement.
Proof.
  intros Hsound.
  pose (inputs :=
    {| source := Typing_env.create;
       cut_after := Typing_env.current_scope Typing_env.create;
       uses := [(tt, Typing_env.create)] |}).
  assert (Hwell_formed : join_inputs_well_formed (fun _ => True) [] inputs).
  { split; [ split; [ exact I | intros; exact I ] | ].
    split; [ | split ].
    - intros index use Huse _.
      apply use_at_singleton in Huse. subst use.
      exists Typing_env_level.empty. reflexivity.
    - intros index use s Huse Hdefined.
      apply use_at_singleton in Huse. subst use. exact Hdefined.
    - split.
      + intros x Hknown. discriminate.
      + intros index use x Huse Hknown.
        apply use_at_singleton in Huse. subst use. discriminate. }
  assert (Hrefine : uses_refine_source inputs).
  { intros index use Huse statics valuation Hsatisfied.
    apply use_at_singleton in Huse. subst use.
    exists valuation. split; [ exact Hsatisfied | ].
    intros x _. reflexivity. }
  destruct (Hsound [] inputs _ _ Hwell_formed Hrefine eq_refl)
    as [_ [_ [_ [_ Hadmits]]]].
  assert (Huse : use_at inputs 0 Typing_env.create).
  { exists tt. reflexivity. }
  destruct
    (Hadmits 0 Typing_env.create Huse (Static_env [] []) []
       (create_satisfied_strictly _ _))
    as [valuation' [[Hnot_bottom _] _]].
  discriminate.
Qed.

(* ======================================================================== *)
(* In the machine                                                           *)
(* ======================================================================== *)

Theorem join_admits_use_in_machine : join_admits_use_in_machine_statement.
Proof.
  intros use target definitions definitions_at_normal_mode index statics vars
    Hadmits Hscope [valuation [Hsatisfied [Hterms Hbound]]].
  destruct (Hadmits statics valuation Hsatisfied)
    as [valuation' [Htarget [Hagrees [_ Hdefinitions]]]].
  exists valuation'. split; [ exact Htarget | ].
  split; [ | split ].
  - intros x Hx. rewrite (Hagrees x).
    + apply Hterms. apply Hscope. exact Hx.
    + apply in_scope_in_terms_knows. apply Hscope. exact Hx.
  - intros x Hx. apply Hbound. apply Hscope. exact Hx.
  - intros x simples kind simple Hlookup Hfind Hnormal.
    rewrite (Hdefinitions x simples kind simple Hlookup Hfind).
    destruct simple as [y | s | c]; cbn in *; [ | reflexivity | reflexivity ].
    apply Hterms. exact Hnormal.
Qed.

Theorem join_admits_use_env_satisfies
  : join_admits_use_env_satisfies_statement.
Proof.
  intros use target definitions definitions_at_normal_mode index statics vars
    Hadmits Hscope Hsatisfies.
  destruct
    (join_admits_use_in_machine use target definitions
       definitions_at_normal_mode index statics vars Hadmits Hscope
       Hsatisfies)
    as [valuation' [Htarget [Hterms [Hbound _]]]].
  exists valuation'. split; [ exact Htarget | ]. split; assumption.
Qed.

(* Whether a variable may occur in terms depends on its binding time and
   name mode and on the first binding time in scope. *)
Lemma in_scope_in_terms_kept (source target : Typing_env.t) (x : variable) :
  join_keeps_source source target ->
  knows source x ->
  in_scope_in_terms target x ->
  in_scope_in_terms source x.
Proof.
  intros [Hnames [_ [_ [_ Hmin]]]].
  unfold knows, in_scope_in_terms, Typing_env.mem.
  destruct
    (Keyed.lookup name_eqb (Name_var x) (Typing_env.names_to_types source))
    as [[ty binding_time_and_mode] | ] eqn:Hsource; [ | discriminate ].
  destruct (Hnames _ _ _ Hsource) as [ty' Htarget].
  rewrite Htarget, Hmin. intros _ Hscope. exact Hscope.
Qed.

Theorem join_guarantees_in_machine : join_guarantees_in_machine_statement.
Proof.
  intros typing_env_well_formed A avoid inputs target analysis index use
    statics vars [_ [Hkeeps [Hintroduces [_ Hadmits]]]] Hterms Huse
    Hsatisfies.
  apply
    (join_admits_use_env_satisfies use target
       (Analysis.definitions_in_joined_envs analysis)
       (Analysis.canonical_definitions_at_normal_mode analysis) index
       statics vars (Hadmits index use Huse)); [ | exact Hsatisfies ].
  intros x Hscope. apply (Hterms index use x Huse).
  destruct (Typing_env.mem None (source inputs) (Name_var x)) eqn:Hknown.
  - exact (in_scope_in_terms_kept _ _ x Hkeeps Hknown Hscope).
  - destruct (Hintroduces x (in_scope_in_terms_knows _ _ Hscope))
      as [Hnot_in_scope _].
    + unfold knows. rewrite Hknown. discriminate.
    + contradiction.
Qed.

Theorem known_value_at_use : known_value_at_use_statement.
Proof.
  intros definitions index valuation valuation' x simples kind simple c
    Hdefinitions Hlookup Hfind Hvalue.
  rewrite (Hdefinitions x simples kind simple Hlookup Hfind).
  destruct simple as [y | s | c']; cbn in Hvalue; try discriminate.
  injection Hvalue as <-. reflexivity.
Qed.

(* ======================================================================== *)
(* The n-way join of closures entries                                       *)
(* ======================================================================== *)

(* The instance is that of the examples of the meaning of types: the
   type that a projection of a value slot gives a closure, joined with
   one that names a code other than the closure's. *)
Theorem n_way_join_closures_entry_not_upper_bound
  : n_way_join_closures_entry_not_upper_bound_statement.
Proof.
  exists Examples.statics, Examples.vars, (Value_symbol Examples.a_closure),
    unnamed_function_slot,
    (Row_like_index
       (Row_like_index_domain.At_least
          (Set_of_closures_contents [] [Examples.a_value_slot]))
       tt),
    [], [(Examples.a_value_slot, unknown Value)], [],
    [(unnamed_function_slot,
      Or_unknown.Known (Function_type Examples.other_code))].
  split.
  - exact Examples.nway_join_input_has.
  - exact Examples.nway_join_has_not.
Qed.

(* What a join of function types that answers a code says of each of
   the function types joined. *)
Lemma known_function_types_in
    (func_types : list (Index.t * Or_unknown.t function_type))
    (known : list function_type) (index : Index.t)
    (func_type : Or_unknown.t function_type) :
  known_function_types func_types = Some known ->
  In (index, func_type) func_types ->
  ∃ func_type' : function_type,
    func_type = Or_unknown.Known func_type' ∧ In func_type' known.
Proof.
  revert known. induction func_types as [ | [index' func_type'] func_types IH];
    intros known Hknown Hin; [ destruct Hin | ].
  cbn in Hknown. destruct func_type' as [func_type' | ]; [ | discriminate ].
  destruct (known_function_types func_types) as [known' | ];
    [ | discriminate ].
  injection Hknown as <-. destruct Hin as [Heq | Hin].
  - injection Heq as _ <-. exists func_type'. split; [ reflexivity | ].
    left. reflexivity.
  - destruct (IH known' eq_refl Hin) as [func_type'' [Heq Hin']].
    exists func_type''. split; [ exact Heq | ]. right. exact Hin'.
Qed.

Lemma n_way_join_function_type_known
    (func_types : list (Index.t * Or_unknown.t function_type))
    (joined : function_type) (index : Index.t)
    (func_type : Or_unknown.t function_type) :
  n_way_join_function_type func_types = Or_unknown.Known joined ->
  In (index, func_type) func_types ->
  ∃ func_type' : function_type,
    func_type = Or_unknown.Known func_type'
    ∧ function_type_code_id func_type' = function_type_code_id joined.
Proof.
  unfold n_way_join_function_type. intros Hjoined Hin.
  destruct (known_function_types func_types) as [known | ] eqn:Hknown;
    [ | discriminate ].
  destruct known as [ | first known]; [ discriminate | ].
  destruct
    (forallb
       (fun func_type' =>
          Pos.eqb (function_type_code_id first)
            (function_type_code_id func_type'))
       known) eqn:Hall; [ | discriminate ].
  injection Hjoined as <-.
  destruct (known_function_types_in _ _ _ _ Hknown Hin)
    as [func_type' [Heq [Hfirst | Hrest]]].
  - exists func_type'. split; [ exact Heq | ]. subst func_type'. reflexivity.
  - exists func_type'. split; [ exact Heq | ].
    rewrite forallb_forall in Hall. specialize (Hall func_type' Hrest).
    apply Pos.eqb_eq in Hall. symmetry. exact Hall.
Qed.

(* One step of the gathering proposed. *)
Definition gather_step_proposed
    (function_types : finite_map (list (Index.t * Or_unknown.t function_type)))
    (entry : Index.t * finite_map (Or_unknown.t function_type))
    : finite_map (list (Index.t * Or_unknown.t function_type)) :=
  merge
    (fun vals_opt val2_opt =>
       match vals_opt, val2_opt with
       | None, _ | _, None => None
       | Some vals, Some val2 => Some ((fst entry, val2) :: vals)
       end)
    function_types (snd entry).

Lemma lookup_gather_step_proposed
    (function_types : finite_map (list (Index.t * Or_unknown.t function_type)))
    (entry : Index.t * finite_map (Or_unknown.t function_type))
    (g : function_slot)
    (contributors : list (Index.t * Or_unknown.t function_type)) :
  lookup g (gather_step_proposed function_types entry) = Some contributors ->
  ∃ (vals : list (Index.t * Or_unknown.t function_type))
    (val2 : Or_unknown.t function_type),
    lookup g function_types = Some vals
    ∧ lookup g (snd entry) = Some val2
    ∧ contributors = (fst entry, val2) :: vals.
Proof.
  unfold gather_step_proposed. rewrite lookup_merge; [ | reflexivity ].
  destruct (lookup g function_types) as [vals | ]; [ | discriminate ].
  destruct (lookup g (snd entry)) as [val2 | ]; [ | discriminate ].
  intros Heq. injection Heq as <-. exists vals, val2. repeat split.
Qed.

(* What is gathered for a slot holds a function type of every entry gone
   through, and what was gathered before. *)
Lemma lookup_fold_gather_proposed
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    (function_types : finite_map (list (Index.t * Or_unknown.t function_type)))
    (g : function_slot)
    (contributors : list (Index.t * Or_unknown.t function_type)) :
  lookup g (List.fold_left gather_step_proposed entries function_types)
  = Some contributors ->
  (∃ vals : list (Index.t * Or_unknown.t function_type),
     lookup g function_types = Some vals
     ∧ ∀ contributor, In contributor vals -> In contributor contributors)
  ∧ ∀ (index : Index.t)
      (function_types' : finite_map (Or_unknown.t function_type)),
      In (index, function_types') entries ->
      ∃ func_type : Or_unknown.t function_type,
        lookup g function_types' = Some func_type
        ∧ In (index, func_type) contributors.
Proof.
  revert function_types.
  induction entries as [ | entry entries IH]; intros function_types Hlookup.
  - split; [ | intros index function_types' [] ].
    exists contributors. split; [ exact Hlookup | ]. intros; assumption.
  - cbn in Hlookup.
    destruct (IH _ Hlookup) as [[vals1 [Hstep Hincluded]] Hentries].
    destruct (lookup_gather_step_proposed _ _ _ _ Hstep)
      as [vals [val2 [Hvals [Hval2 Heq]]]].
    subst vals1. split.
    + exists vals. split; [ exact Hvals | ].
      intros contributor Hin. apply Hincluded. right. exact Hin.
    + intros index function_types' [Heq | Hin].
      * subst entry. exists val2. split; [ exact Hval2 | ].
        apply Hincluded. left. reflexivity.
      * exact (Hentries index function_types' Hin).
Qed.

Lemma lookup_gather_function_types_proposed
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    (g : function_slot)
    (contributors : list (Index.t * Or_unknown.t function_type))
    (index : Index.t)
    (function_types : finite_map (Or_unknown.t function_type)) :
  lookup g (gather_function_types_proposed entries) = Some contributors ->
  In (index, function_types) entries ->
  ∃ func_type : Or_unknown.t function_type,
    lookup g function_types = Some func_type
    ∧ In (index, func_type) contributors.
Proof.
  destruct entries as [ | [id1 function_types1] entries];
    intros Hlookup Hin; [ destruct Hin | ].
  cbn in Hlookup.
  change
    (lookup g
       (List.fold_left gather_step_proposed entries
          (map_values (fun func_type => [(id1, func_type)]) function_types1))
     = Some contributors) in Hlookup.
  destruct (lookup_fold_gather_proposed _ _ _ _ Hlookup)
    as [[vals [Hvals Hincluded]] Hentries].
  destruct Hin as [Heq | Hin]; [ | exact (Hentries _ _ Hin) ].
  injection Heq as <- <-.
  rewrite lookup_map_values in Hvals.
  destruct (lookup g function_types1) as [func_type | ]; [ | discriminate ].
  injection Hvals as <-. exists func_type. split; [ reflexivity | ].
  apply Hincluded. left. reflexivity.
Qed.

Theorem n_way_join_function_types_proposed_sound
  : n_way_join_function_types_proposed_sound_statement.
Proof.
  intros statics vars v slot functions value_slots entries index
    function_types closure_types value_slot_types Hin.
  rewrite !closures_entry_lookup_iff.
  intros [Hfunctions Hrest]. split; [ | exact Hrest ].
  intros g joined code Hlookup Hcode.
  unfold n_way_join_function_types_proposed in Hlookup.
  rewrite lookup_map_values in Hlookup.
  destruct (lookup g (gather_function_types_proposed entries))
    as [contributors | ] eqn:Hgathered; [ | discriminate ].
  injection Hlookup as Hjoined.
  destruct
    (lookup_gather_function_types_proposed _ _ _ _ _ Hgathered Hin)
    as [func_type [Hfunc_type Hcontributor]].
  destruct (n_way_join_function_type_known _ _ _ _ Hjoined Hcontributor)
    as [func_type' [Heq Hsame_code]].
  subst func_type. rewrite <- Hsame_code.
  exact (Hfunctions g func_type' code Hfunc_type Hcode).
Qed.
