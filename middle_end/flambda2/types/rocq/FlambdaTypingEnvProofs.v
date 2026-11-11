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


(* Proofs of the statements of FlambdaTypingEnvSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec
  FlambdaEnvAliasesProofs FlambdaTypingEnv FlambdaTypingEnvSpec.
Import ListNotations.

(* ======================================================================== *)
(* Kinds                                                                    *)
(* ======================================================================== *)

Lemma naked_number_kind_eqb_eq (k k' : naked_number_kind) :
  naked_number_kind_eqb k k' = true <-> k = k'.
Proof.
  split; [ | intros <-; destruct k; reflexivity ].
  destruct k, k'; simpl; try discriminate; reflexivity.
Qed.

Lemma kind_eqb_eq (k k' : flambda_kind) : kind_eqb k k' = true <-> k = k'.
Proof.
  split.
  - destruct k as [ | n | | ], k' as [ | n' | | ]; simpl; try discriminate;
      try reflexivity.
    intros H. apply naked_number_kind_eqb_eq in H. congruence.
  - intros <-. destruct k as [ | n | | ]; simpl; try reflexivity.
    apply naked_number_kind_eqb_eq. reflexivity.
Qed.

Theorem kind_eqb_decides_equality : kind_eqb_decides_equality_statement.
Proof. intros k k'. apply kind_eqb_eq. Qed.

Lemma kind_bottom (k : flambda_kind) : kind (bottom k) = k.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma kind_unknown (k : flambda_kind) : kind (unknown k) = k.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma kind_alias_type_of (k : flambda_kind) (s : simple) :
  kind (alias_type_of k s) = k.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

(* The type that the compiler gives a constant is of its kind. *)
Lemma kind_type_for_const (c : const) : kind (type_for_const c) = kind_of_const c.
Proof.
  symmetry.
  exact (type_satisfied_kind empty_static_env [] (Value_const c)
           (type_for_const c) (type_for_const_satisfied empty_static_env [] c)).
Qed.

(* ======================================================================== *)
(* Poison                                                                   *)
(* ======================================================================== *)

Theorem satisfied_unless_poison_kind : satisfied_unless_poison_kind_statement.
Proof.
  intros statics valuation v ty [-> | Hty]; [ reflexivity | ].
  exact (type_satisfied_kind statics valuation v ty Hty).
Qed.

Theorem satisfied_unless_poison_not_poison
    : satisfied_unless_poison_not_poison_statement.
Proof.
  intros statics valuation v ty [-> | Hty] Hnot_poison; [ | exact Hty ].
  exfalso. exact (Hnot_poison (kind ty) eq_refl).
Qed.

(* A value that has a type is what is asked of the value of a name of
   that type. *)
Lemma type_satisfied_unless_poison (statics : static_env) (valuation : env)
    (v : value) (ty : flambda_type) :
  type_satisfied statics valuation v ty ->
  satisfied_unless_poison statics valuation v ty.
Proof. intros Hty. right. exact Hty. Qed.

(* ======================================================================== *)
(* Reading the lookup functions back                                        *)
(* ======================================================================== *)

(* What [find_with_binding_time_and_mode'] answers, in an environment
   that is not bottom: the entry of the name, or the type of a symbol
   that is defined and has none. *)
Lemma find_with_binding_time_and_mode'_cases (tenv : Typing_env.t) (n : name)
    (kind : option flambda_kind) (ty : flambda_type)
    (binding_time_and_mode : Binding_time.With_name_mode.t) :
  Typing_env.is_bottom tenv = false ->
  Typing_env.find_with_binding_time_and_mode' tenv n kind
  = Some (ty, binding_time_and_mode) ->
  Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
  = Some (ty, binding_time_and_mode)
  ∨ ((∃ s : symbol, n = Name_symbol s)
     ∧ (ty, binding_time_and_mode) = Typing_env.initial_symbol_type).
Proof.
  intros Hbottom. unfold Typing_env.find_with_binding_time_and_mode'.
  rewrite Hbottom.
  destruct (Keyed.lookup name_eqb n (Typing_env.names_to_types tenv))
    as [[ty' binding_time_and_mode'] | ] eqn:Hlookup.
  - destruct (Typing_env.check_optional_kind_matches ty' kind);
      [ | discriminate ].
    intros [= <- <-]. left. reflexivity.
  - destruct n as [x | s]; [ discriminate | ].
    destruct (among s (Typing_env.defined_symbols tenv)
              && Typing_env.check_optional_kind_matches
                   (fst Typing_env.initial_symbol_type) kind);
      [ | discriminate ].
    intros [= <- <-]. right. split; [ exists s; reflexivity | reflexivity ].
Qed.

(* A valuation that satisfies an environment gives the name its type,
   whichever of the two it is. *)
Lemma find_with_binding_time_and_mode'_satisfied (statics : static_env)
    (valuation : env) (tenv : Typing_env.t) (n : name)
    (kind : option flambda_kind) (ty : flambda_type)
    (binding_time_and_mode : Binding_time.With_name_mode.t) :
  typing_env_satisfied statics valuation tenv ->
  Typing_env.find_with_binding_time_and_mode' tenv n kind
  = Some (ty, binding_time_and_mode) ->
  ∃ v : value,
    value_of_name valuation n = Some v
    ∧ satisfied_unless_poison statics valuation v ty.
Proof.
  intros [Hbottom [Htypes _]] Hfind.
  apply find_with_binding_time_and_mode'_cases in Hfind; [ | exact Hbottom ].
  destruct Hfind as [Hlookup | [[s ->] [= -> ->]]].
  - exact (Htypes n ty binding_time_and_mode Hlookup).
  - exists (Value_symbol s). split; [ reflexivity | ].
    apply type_satisfied_unless_poison, any_non_null_value_satisfied.
    split; [ reflexivity | discriminate ].
Qed.

Lemma find_with_binding_time_and_mode_satisfied (statics : static_env)
    (valuation : env) (tenv : Typing_env.t) (n : name)
    (kind : option flambda_kind) (ty : flambda_type)
    (binding_time_and_mode : Binding_time.With_name_mode.t) :
  typing_env_satisfied statics valuation tenv ->
  Typing_env.find_with_binding_time_and_mode tenv n kind
  = Some (ty, binding_time_and_mode) ->
  ∃ v : value,
    value_of_name valuation n = Some v
    ∧ satisfied_unless_poison statics valuation v ty.
Proof.
  intros Hsatisfied. unfold Typing_env.find_with_binding_time_and_mode.
  destruct (Typing_env.find_with_binding_time_and_mode' tenv n kind)
    as [[ty' binding_time_and_mode'] | ] eqn:Hfind; [ | discriminate ].
  intros [= <- _].
  exact (find_with_binding_time_and_mode'_satisfied statics valuation tenv n
           kind ty' binding_time_and_mode' Hsatisfied Hfind).
Qed.

(* [mem] with the normal name mode, of a variable: its entry has the
   normal name mode in scope. *)
Lemma in_scope_in_terms_lookup (tenv : Typing_env.t) (x : variable) :
  in_scope_in_terms tenv x
  <-> ∃ (ty : flambda_type)
        (binding_time_and_mode : Binding_time.With_name_mode.t),
        Keyed.lookup name_eqb (Name_var x) (Typing_env.names_to_types tenv)
        = Some (ty, binding_time_and_mode)
        ∧ Binding_time.With_name_mode.scoped_name_mode binding_time_and_mode
            (Typing_env.min_binding_time tenv)
          = Name_mode.Normal.
Proof.
  unfold in_scope_in_terms, Typing_env.mem.
  destruct (Keyed.lookup name_eqb (Name_var x) (Typing_env.names_to_types tenv))
    as [[ty binding_time_and_mode] | ].
  - split.
    + intros Hmode. exists ty, binding_time_and_mode.
      split; [ reflexivity | ].
      destruct (Binding_time.With_name_mode.scoped_name_mode
                  binding_time_and_mode (Typing_env.min_binding_time tenv));
        [ reflexivity | discriminate | discriminate ].
    + intros [ty' [binding_time_and_mode' [[= <- <-] ->]]]. reflexivity.
  - split; [ discriminate | ].
    intros [ty [binding_time_and_mode [Hlookup _]]]. discriminate.
Qed.

(* ======================================================================== *)
(* What every environment satisfies, and what none does                     *)
(* ======================================================================== *)

(* What [Aliases.get_canonical_element_exn] answers for the normal name
   mode, if it is a variable: the element asked about, or a variable in
   scope with the normal name mode. *)
Lemma get_canonical_element_exn_normal {A : Type}
    (resolver : name -> Binding_time.With_name_mode.t)
    (map : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (a : Aliases.t) (element : simple) (elt_name_mode : Name_mode.t)
    (min_binding_time : Binding_time.t) (y : variable) :
  Aliases.get_canonical_element_exn resolver map a element elt_name_mode
    Name_mode.Normal min_binding_time
  = Some (Var y) ->
  element = Var y
  ∨ ∃ (data : A) (binding_time_and_mode : Binding_time.With_name_mode.t),
      Keyed.lookup name_eqb (Name_var y) map
      = Some (data, binding_time_and_mode)
      ∧ Binding_time.With_name_mode.scoped_name_mode binding_time_and_mode
          min_binding_time
        = Name_mode.Normal.
Proof.
  intros Hanswer. apply canonical_at_mode_name_mode in Hanswer.
  destruct Hanswer as [[-> _] | [c [Hcompare Hc]]];
    [ left; reflexivity | right ].
  unfold Aliases.compute_name_mode, Aliases.binding_time_and_name_mode in *.
  destruct (Keyed.lookup name_eqb (Name_var y) map)
    as [[data binding_time_and_mode] | ].
  - exists data, binding_time_and_mode. split; [ reflexivity | ].
    destruct (Binding_time.With_name_mode.scoped_name_mode
                binding_time_and_mode min_binding_time);
      [ reflexivity | | ]; simpl in Hcompare; injection Hcompare as <-; lia.
  - exfalso. revert Hcompare.
    unfold Binding_time.With_name_mode.scoped_name_mode. simpl.
    destruct (min_binding_time <=? Binding_time.imported_variables)%Z;
      simpl; intros [= <-]; lia.
Qed.

Theorem create_satisfied : create_satisfied_statement.
Proof.
  intros statics vars. exists vars. split; [ | intros x _; reflexivity ].
  split; [ reflexivity | ]. split.
  - intros n ty binding_time_and_mode Hlookup. discriminate.
  - apply empty_respected.
Qed.

Theorem bottom_not_satisfied : bottom_not_satisfied_statement.
Proof.
  intros tenv statics vars Hbottom [valuation [[Hnot_bottom _] _]].
  congruence.
Qed.

Theorem make_bottom_not_satisfied : make_bottom_not_satisfied_statement.
Proof.
  intros tenv statics vars. apply bottom_not_satisfied. reflexivity.
Qed.

Theorem typing_env_satisfied_env_satisfies
    : typing_env_satisfied_env_satisfies_statement.
Proof.
  intros tenv statics vars Hsatisfied. exists vars.
  split; [ exact Hsatisfied | intros x _; reflexivity ].
Qed.

Theorem env_satisfies_coincide : env_satisfies_coincide_statement.
Proof.
  intros tenv statics vars vars' Hcoincide [valuation [Hsatisfied Hagrees]].
  exists valuation. split; [ exact Hsatisfied | ].
  intros x Hscope. rewrite (Hagrees x Hscope). exact (Hcoincide x Hscope).
Qed.

(* ======================================================================== *)
(* Looking a name up                                                        *)
(* ======================================================================== *)

Theorem find_satisfied : find_satisfied_statement.
Proof.
  intros statics valuation tenv n kind ty Hsatisfied.
  unfold Typing_env.find.
  destruct (Typing_env.find_with_binding_time_and_mode' tenv n kind)
    as [[ty' binding_time_and_mode] | ] eqn:Hfind; [ | discriminate ].
  intros [= <-].
  exact (find_with_binding_time_and_mode'_satisfied statics valuation tenv n
           kind ty' binding_time_and_mode Hsatisfied Hfind).
Qed.

Theorem find_kind : find_kind_statement.
Proof.
  intros tenv n k ty. unfold Typing_env.find,
    Typing_env.find_with_binding_time_and_mode'.
  destruct (Keyed.lookup name_eqb n (Typing_env.names_to_types tenv))
    as [[ty' binding_time_and_mode] | ].
  - simpl. destruct (kind_eqb k (kind ty')) eqn:Hkind; [ | discriminate ].
    apply kind_eqb_eq in Hkind.
    destruct (Typing_env.is_bottom tenv); intros [= <-].
    + rewrite kind_bottom. symmetry. exact Hkind.
    + symmetry. exact Hkind.
  - destruct n as [x | s]; [ discriminate | ].
    destruct (among s (Typing_env.defined_symbols tenv)); [ | discriminate ].
    simpl. destruct (kind_eqb k Value) eqn:Hkind; [ | discriminate ].
    apply kind_eqb_eq in Hkind. intros [= <-]. symmetry. exact Hkind.
Qed.

Theorem mem_find : mem_find_statement.
Proof.
  intros tenv min_name_mode n. unfold Typing_env.mem, Typing_env.find,
    Typing_env.find_with_binding_time_and_mode'.
  destruct n as [x | s].
  - destruct (Keyed.lookup name_eqb (Name_var x)
                (Typing_env.names_to_types tenv))
      as [[ty binding_time_and_mode] | ]; [ | discriminate ].
    intros _. simpl. destruct (Typing_env.is_bottom tenv); eexists; reflexivity.
  - intros Hdefined.
    destruct (Keyed.lookup name_eqb (Name_symbol s)
                (Typing_env.names_to_types tenv))
      as [[ty binding_time_and_mode] | ].
    + simpl. destruct (Typing_env.is_bottom tenv); eexists; reflexivity.
    + rewrite Hdefined. simpl. eexists. reflexivity.
Qed.

(* A valuation that agrees with the machine gives a variable in scope
   the value that the machine has. *)
Lemma agrees_value_of_name (tenv : Typing_env.t) (valuation vars : env)
    (x : variable) :
  agrees_in_terms tenv valuation vars ->
  in_scope_in_terms tenv x ->
  value_of_name valuation (Name_var x) = lookup x vars.
Proof. intros Hagrees Hscope. exact (Hagrees x Hscope). Qed.

(* A type whose variables are in scope means the same under a valuation
   and under the variables of the machine that it agrees with. *)
Lemma type_satisfied_agrees (tenv : Typing_env.t) (statics : static_env)
    (valuation vars : env) (v : value) (ty : flambda_type) :
  agrees_in_terms tenv valuation vars ->
  (∀ y : variable, y ∈ free_variables ty -> in_scope_in_terms tenv y) ->
  type_satisfied statics valuation v ty ->
  type_satisfied statics vars v ty.
Proof.
  intros Hagrees Hfree.
  apply (proj1 (type_satisfied_coincide statics valuation vars v ty
                  (fun y Hy => Hagrees y (Hfree y Hy)))).
Qed.

Theorem in_scope_in_terms_bound : in_scope_in_terms_bound_statement.
Proof.
  intros tenv statics vars x ty [valuation [Hsatisfied Hagrees]] Hscope Hfind.
  destruct (find_satisfied statics valuation tenv (Name_var x) None ty
              Hsatisfied Hfind) as [v [Hvalue Hty]].
  exists v. split.
  - rewrite <- (agrees_value_of_name tenv valuation vars x Hagrees Hscope).
    exact Hvalue.
  - exact (satisfied_unless_poison_kind statics valuation v ty Hty).
Qed.

Theorem find_variable_in_terms : find_variable_in_terms_statement.
Proof.
  intros tenv statics vars x kind ty [valuation [Hsatisfied Hagrees]] Hscope
    Hfind Hfree.
  destruct (find_satisfied statics valuation tenv (Name_var x) kind ty
              Hsatisfied Hfind) as [v [Hvalue Hty]].
  exists v. split.
  - rewrite <- (agrees_value_of_name tenv valuation vars x Hagrees Hscope).
    exact Hvalue.
  - destruct Hty as [-> | Hty]; [ left; reflexivity | right ].
    exact (type_satisfied_agrees tenv statics valuation vars v ty Hagrees
             Hfree Hty).
Qed.

Theorem find_symbol_in_terms : find_symbol_in_terms_statement.
Proof.
  intros tenv statics vars s kind ty [valuation [Hsatisfied Hagrees]] Hfind
    Hfree.
  destruct (find_satisfied statics valuation tenv (Name_symbol s) kind ty
              Hsatisfied Hfind) as [v [[= <-] [Hpoison | Hty]]];
    [ discriminate | ].
  exact (type_satisfied_agrees tenv statics valuation vars (Value_symbol s)
           ty Hagrees Hfree Hty).
Qed.

(* ======================================================================== *)
(* Canonical elements                                                       *)
(* ======================================================================== *)

Theorem canonical_ignoring_name_mode_satisfied
    : canonical_ignoring_name_mode_satisfied_statement.
Proof.
  intros statics valuation tenv s [_ [_ Hrespected]].
  destruct s as [x | s | c]; [ | | reflexivity ].
  - exact (respected_canonical (Typing_env.aliases tenv) valuation
             (Name_var x) Hrespected).
  - exact (respected_canonical (Typing_env.aliases tenv) valuation
             (Name_symbol s) Hrespected).
Qed.

Theorem get_canonical_simple_satisfied
    : get_canonical_simple_satisfied_statement.
Proof.
  intros statics valuation tenv min_name_mode name_mode_of_existing_simple s
    canonical [_ [_ Hrespected]].
  unfold Typing_env.get_canonical_simple_exn.
  destruct (match name_mode_of_existing_simple with
            | Some name_mode => Some name_mode
            | None =>
              option_map Binding_time.With_name_mode.name_mode
                (Typing_env.binding_time_and_mode_of_simple tenv s)
            end) as [name_mode_simple | ]; [ | discriminate ].
  intros [= Hcanonical].
  exact (respected_canonical_at_mode _ _ _ _ valuation _ _ _ _ _ Hrespected
           Hcanonical).
Qed.

Theorem get_alias_then_canonical_simple_satisfied
    : get_alias_then_canonical_simple_satisfied_statement.
Proof.
  intros statics valuation tenv min_name_mode name_mode_of_existing_simple typ
    canonical v Hsatisfied.
  unfold Typing_env.get_alias_then_canonical_simple_exn.
  destruct (get_alias_opt typ) as [s | ] eqn:Halias; [ | discriminate ].
  intros Hcanonical Hty.
  rewrite (get_canonical_simple_satisfied statics valuation tenv min_name_mode
             name_mode_of_existing_simple s canonical Hsatisfied Hcanonical).
  apply (get_alias_satisfied statics valuation v typ s Halias) in Hty.
  exact (proj1 Hty).
Qed.

Theorem type_simple_in_term_satisfied
    : type_simple_in_term_satisfied_statement.
Proof.
  intros statics valuation tenv min_name_mode s canonical ty Hsatisfied.
  unfold Typing_env.type_simple_in_term_exn.
  (* The [Simple] has a value, of the type that the environment finds. *)
  assert (Hfound :
    ∀ (ty' : flambda_type)
      (binding_time_and_mode : Binding_time.With_name_mode.t),
      match s with
      | Const const =>
        Some (type_for_const const, Binding_time.With_name_mode.consts)
      | Var x =>
        Typing_env.find_with_binding_time_and_mode tenv (Name_var x) None
      | Symbol sym =>
        Typing_env.find_with_binding_time_and_mode tenv (Name_symbol sym) None
      end = Some (ty', binding_time_and_mode) ->
      ∃ v : value,
        eval_simple valuation s = Some v
        ∧ kind_of_value v = FlambdaTypeGrammar.kind ty').
  { intros ty' binding_time_and_mode. destruct s as [x | sym | c].
    - intros Hfind.
      destruct (find_with_binding_time_and_mode_satisfied statics valuation
                  tenv (Name_var x) None ty' binding_time_and_mode Hsatisfied
                  Hfind) as [v [Hvalue Hty]].
      exists v. split; [ exact Hvalue | ].
      exact (satisfied_unless_poison_kind statics valuation v ty' Hty).
    - intros Hfind.
      destruct (find_with_binding_time_and_mode_satisfied statics valuation
                  tenv (Name_symbol sym) None ty' binding_time_and_mode
                  Hsatisfied Hfind) as [v [Hvalue Hty]].
      exists v. split; [ exact Hvalue | ].
      exact (satisfied_unless_poison_kind statics valuation v ty' Hty).
    - intros [= <- _]. exists (Value_const c).
      split; [ reflexivity | ]. rewrite kind_type_for_const. reflexivity. }
  destruct (match s with
            | Const const =>
              Some (type_for_const const, Binding_time.With_name_mode.consts)
            | Var x =>
              Typing_env.find_with_binding_time_and_mode tenv (Name_var x) None
            | Symbol sym =>
              Typing_env.find_with_binding_time_and_mode tenv
                (Name_symbol sym) None
            end) as [[ty' binding_time_and_mode] | ]; [ | discriminate ].
  destruct (Hfound ty' binding_time_and_mode eq_refl) as [v [Hvalue Hkind]].
  destruct (Aliases.get_canonical_element_exn _ _ _ _ _ _ _) as [alias | ]
    eqn:Hcanonical; [ | discriminate ].
  intros [= <- <-].
  destruct Hsatisfied as [_ [_ Hrespected]].
  assert (Halias : eval_simple valuation alias = eval_simple valuation s)
    by exact (respected_canonical_at_mode _ _ _ _ valuation _ _ _ _ _
                Hrespected Hcanonical).
  split; [ exact Halias | ].
  exists v. split; [ exact Hvalue | ].
  apply alias_satisfied. split; [ congruence | exact Hkind ].
Qed.

Theorem type_simple_in_term_canonical
    : type_simple_in_term_canonical_statement.
Proof.
  intros tenv statics vars s canonical ty [valuation [Hsatisfied Hagrees]]
    Hmem Hcanonical.
  (* The [Simple] and its canonical element have, in the machine, the
     values that the valuation gives them. *)
  assert (Hs : eval_simple vars s = eval_simple valuation s).
  { destruct s as [x | sym | c]; [ | reflexivity | reflexivity ].
    symmetry. exact (Hagrees x Hmem). }
  assert (Hc : eval_simple vars canonical = eval_simple valuation canonical).
  { destruct canonical as [y | sym | c]; [ | reflexivity | reflexivity ].
    revert Hcanonical. unfold Typing_env.type_simple_in_term_exn.
    destruct (match s with
              | Const const =>
                Some (type_for_const const, Binding_time.With_name_mode.consts)
              | Var x =>
                Typing_env.find_with_binding_time_and_mode tenv (Name_var x)
                  None
              | Symbol sym =>
                Typing_env.find_with_binding_time_and_mode tenv
                  (Name_symbol sym) None
              end) as [[ty' binding_time_and_mode] | ]; [ | discriminate ].
    destruct (Aliases.get_canonical_element_exn _ _ _ _ _ _ _) as [alias | ]
      eqn:Halias; [ | discriminate ].
    intros [= _ ->].
    apply get_canonical_element_exn_normal in Halias.
    destruct Halias as [-> | [data [binding_time_and_mode' [Hlookup Hmode]]]].
    - exact Hs.
    - symmetry. apply Hagrees. apply in_scope_in_terms_lookup.
      exists data, binding_time_and_mode'. split; assumption. }
  rewrite Hs, Hc.
  exact (proj1 (type_simple_in_term_satisfied statics valuation tenv
                  (Some Name_mode.normal) s canonical ty Hsatisfied
                  Hcanonical)).
Qed.
