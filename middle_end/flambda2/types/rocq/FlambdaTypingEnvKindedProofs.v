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


(* Proofs of the statements of FlambdaTypingEnvKindedSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaPrimitiveProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesProofs
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvProofs
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs
  FlambdaTypingEnvOperationsSpec FlambdaTypingEnvOperationsProofs
  FlambdaTypingEnvKindedSpec.
Import ListNotations.

(* ======================================================================== *)
(* The kind of a [Simple]                                                   *)
(* ======================================================================== *)

(* [simple_of_kind] of a name, as one proposition. *)
Lemma simple_of_kind_of_name (tenv : Typing_env.t) (n : name)
    (kind : flambda_kind) :
  simple_of_kind tenv (simple_of_name n) kind
  <-> ∃ ty : flambda_type, Typing_env.find tenv n (Some kind) = Some ty.
Proof. destruct n; reflexivity. Qed.

Theorem simple_of_kind_name : simple_of_kind_name_statement.
Proof.
  intros tenv n kind. rewrite simple_of_kind_of_name.
  unfold Typing_env.find, Typing_env.find_with_binding_time_and_mode',
    Typing_env.mem.
  destruct (Keyed.lookup name_eqb n (Typing_env.names_to_types tenv))
    as [[ty' btm] | ] eqn:Hlookup.
  - cbn [Typing_env.check_optional_kind_matches].
    destruct (kind_eqb kind (FlambdaTypeGrammar.kind ty')) eqn:Hkind.
    + apply kind_eqb_eq in Hkind. split.
      * intros _. left. exists ty', btm.
        split; [ reflexivity | symmetry; exact Hkind ].
      * intros _. destruct (Typing_env.is_bottom tenv); eexists; reflexivity.
    + split.
      * intros [ty Hfind]. discriminate.
      * intros [[ty [btm' [[= <- <-] Hk]]] | [Hnone _]]; [ | discriminate ].
        subst kind. rewrite (proj2 (kind_eqb_eq _ _) eq_refl) in Hkind.
        discriminate.
  - destruct n as [x | s].
    + split; [ intros [ty Hfind]; discriminate | ].
      intros [[ty [btm [Hsome _]]] | [_ [Hmem _]]]; discriminate.
    + cbn [Typing_env.check_optional_kind_matches
           Typing_env.initial_symbol_type fst].
      destruct (among s (Typing_env.defined_symbols tenv)).
      * change (FlambdaTypeGrammar.kind any_non_null_value) with Value.
        destruct (kind_eqb kind Value) eqn:Hkind.
        -- apply kind_eqb_eq in Hkind. split.
           ++ intros _. right. split; [ reflexivity | ].
              split; [ reflexivity | exact Hkind ].
           ++ intros _. eexists. reflexivity.
        -- split; [ intros [ty Hfind]; discriminate | ].
           intros [[ty [btm [Hsome _]]] | [_ [_ Hk]]]; [ discriminate | ].
           subst kind. discriminate.
      * split; [ intros [ty Hfind]; discriminate | ].
        intros [[ty [btm [Hsome _]]] | [_ [Hmem _]]]; discriminate.
Qed.

(* The same, in a form that [rewrite] takes. *)
Lemma simple_of_kind_name_iff (tenv : Typing_env.t) (n : name)
    (kind : flambda_kind) :
  simple_of_kind tenv (simple_of_name n) kind
  <-> (∃ (ty : flambda_type)
         (binding_time_and_mode : Binding_time.With_name_mode.t),
         Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
         = Some (ty, binding_time_and_mode)
         ∧ FlambdaTypeGrammar.kind ty = kind)
      ∨ (Keyed.lookup name_eqb n (Typing_env.names_to_types tenv) = None
         ∧ Typing_env.mem None tenv n = true
         ∧ kind = Value).
Proof. exact (simple_of_kind_name tenv n kind). Qed.

Theorem simple_of_kind_unique : simple_of_kind_unique_statement.
Proof.
  intros tenv s kind kind'.
  destruct s as [x | sym | c].
  - change (Var x) with (simple_of_name (Name_var x)).
    rewrite !simple_of_kind_name_iff.
    intros [[ty [btm [Hlookup <-]]] | [Hnone [_ ->]]]
      [[ty' [btm' [Hlookup' <-]]] | [Hnone' [_ ->]]];
      try congruence.
  - change (Symbol sym) with (simple_of_name (Name_symbol sym)).
    rewrite !simple_of_kind_name_iff.
    intros [[ty [btm [Hlookup <-]]] | [Hnone [_ ->]]]
      [[ty' [btm' [Hlookup' <-]]] | [Hnone' [_ ->]]];
      try congruence.
  - simpl. congruence.
Qed.

(* [simple_of_kind] reads the types of the names and the symbols that
   are defined, and nothing else. *)
Lemma simple_of_kind_same (tenv tenv' : Typing_env.t) (s : simple)
    (kind : flambda_kind) :
  Typing_env.names_to_types tenv' = Typing_env.names_to_types tenv ->
  Typing_env.defined_symbols tenv' = Typing_env.defined_symbols tenv ->
  (simple_of_kind tenv' s kind <-> simple_of_kind tenv s kind).
Proof.
  intros Htypes Hsymbols.
  destruct s as [x | sym | c]; [ | | reflexivity ].
  - change (Var x) with (simple_of_name (Name_var x)).
    rewrite !simple_of_kind_name_iff, !mem_var_is_bound, Htypes.
    reflexivity.
  - change (Symbol sym) with (simple_of_name (Name_symbol sym)).
    rewrite !simple_of_kind_name_iff, Htypes.
    change (Typing_env.mem None tenv' (Name_symbol sym))
      with (among sym (Typing_env.defined_symbols tenv')).
    rewrite Hsymbols. reflexivity.
Qed.

(* ======================================================================== *)
(* What the functions do to the kind of a [Simple]                          *)
(* ======================================================================== *)

Theorem make_bottom_simple_of_kind : make_bottom_simple_of_kind_statement.
Proof. intros tenv s kind. apply simple_of_kind_same; reflexivity. Qed.

Theorem increment_scope_simple_of_kind
    : increment_scope_simple_of_kind_statement.
Proof. intros tenv s kind. apply simple_of_kind_same; reflexivity. Qed.

Theorem closure_env_simple_of_kind : closure_env_simple_of_kind_statement.
Proof. intros tenv s kind. apply simple_of_kind_same; reflexivity. Qed.

Theorem add_symbol_definition_simple_of_kind
    : add_symbol_definition_simple_of_kind_statement.
Proof.
  intros tenv sym s kind.
  destruct s as [x | sym' | c].
  - change (Var x) with (simple_of_name (Name_var x)).
    rewrite !simple_of_kind_name_iff. cbn [simple_of_name].
    change (Typing_env.names_to_types
              (Typing_env.add_symbol_definition tenv sym))
      with (Typing_env.names_to_types tenv).
    split; [ intros H; left; exact H | ].
    intros [H | [Heq _]]; [ exact H | discriminate ].
  - change (Symbol sym') with (simple_of_name (Name_symbol sym')).
    rewrite !simple_of_kind_name_iff. cbn [simple_of_name].
    change (Typing_env.names_to_types
              (Typing_env.add_symbol_definition tenv sym))
      with (Typing_env.names_to_types tenv).
    change (Typing_env.mem None (Typing_env.add_symbol_definition tenv sym)
              (Name_symbol sym'))
      with (among sym' (sym :: Typing_env.defined_symbols tenv)).
    change (Typing_env.mem None tenv (Name_symbol sym'))
      with (among sym' (Typing_env.defined_symbols tenv)).
    rewrite among_cons. split.
    + intros [Hentry | [Hnone [Hmem ->]]];
        [ left; left; exact Hentry | ].
      apply orb_true_iff in Hmem. destruct Hmem as [Heq | Hmem].
      * apply Pos.eqb_eq in Heq. subst sym'. right.
        split; [ reflexivity | ]. split; [ reflexivity | exact Hnone ].
      * left. right. split; [ exact Hnone | ].
        split; [ exact Hmem | reflexivity ].
    + intros [[Hentry | [Hnone [Hmem ->]]] | [[= ->] [-> Hnone]]].
      * left. exact Hentry.
      * right. split; [ exact Hnone | ]. split; [ | reflexivity ].
        rewrite Hmem. apply orb_true_r.
      * right. split; [ exact Hnone | ]. split; [ | reflexivity ].
        rewrite Pos.eqb_refl. reflexivity.
  - simpl. split; [ intros H; left; exact H | ].
    intros [H | [Heq _]]; [ exact H | discriminate ].
Qed.

Theorem add_variable_definition_simple_of_kind
    : add_variable_definition_simple_of_kind_statement.
Proof.
  intros tenv var kind_of_var name_mode s kind.
  destruct s as [x | sym | c].
  - change (Var x) with (simple_of_name (Name_var x)).
    rewrite !simple_of_kind_name_iff, add_variable_definition_lookup.
    cbn [simple_of_name].
    destruct (keyed_eqb_spec name_eqb name_eqb_eq (Name_var x) (Name_var var))
      as [Heq | Hne].
    + injection Heq as ->. split.
      * intros [[ty [btm [[= <- <-] Hkind]]] | [Hnone _]]; [ | discriminate ].
        left. split; [ reflexivity | ].
        rewrite kind_unknown in Hkind. symmetry. exact Hkind.
      * intros [[_ ->] | [Hne _]]; [ | contradiction ].
        left. eexists. eexists. split; [ reflexivity | apply kind_unknown ].
    + assert (Hmem :
        Typing_env.mem None
          (Typing_env.add_variable_definition tenv var kind_of_var name_mode)
          (Name_var x)
        = Typing_env.mem None tenv (Name_var x)).
      { apply mem_add_variable_definition. congruence. }
      rewrite Hmem. split.
      * intros H. right. split; [ congruence | exact H ].
      * intros [[Heq _] | [_ H]]; [ congruence | exact H ].
  - change (Symbol sym) with (simple_of_name (Name_symbol sym)).
    rewrite !simple_of_kind_name_iff, add_variable_definition_lookup.
    cbn [simple_of_name].
    destruct (keyed_eqb_spec name_eqb name_eqb_eq (Name_symbol sym)
                (Name_var var)) as [Heq | _]; [ discriminate | ].
    change (Typing_env.mem None
              (Typing_env.add_variable_definition tenv var kind_of_var
                 name_mode) (Name_symbol sym))
      with (Typing_env.mem None tenv (Name_symbol sym)).
    split.
    + intros H. right. split; [ discriminate | exact H ].
    + intros [[Heq _] | [_ H]]; [ discriminate | exact H ].
  - simpl. split.
    + intros H. right. split; [ discriminate | exact H ].
    + intros [[Heq _] | [_ H]]; [ discriminate | exact H ].
Qed.

Theorem replace_equation_simple_of_kind
    : replace_equation_simple_of_kind_statement.
Proof.
  intros tenv n ty s kind Hkind.
  apply simple_of_kind_name_iff in Hkind.
  assert (Hsymbols :
    ∀ sym : symbol,
      Typing_env.mem None (Typing_env.replace_equation tenv n ty)
        (Name_symbol sym)
      = Typing_env.mem None tenv (Name_symbol sym)) by reflexivity.
  (* The same for a name. *)
  assert (Hname :
    ∀ m : name,
      simple_of_kind (Typing_env.replace_equation tenv n ty)
        (simple_of_name m) kind
      <-> simple_of_kind tenv (simple_of_name m) kind).
  { intros m. rewrite !simple_of_kind_name_iff.
    destruct (keyed_eqb_spec name_eqb name_eqb_eq m n) as [-> | Hne].
    - rewrite (replace_equation_lookup tenv n ty).
      destruct Hkind
        as [[ty0 [btm0 [Hlookup Hkind0]]] | [Hnone [Hmem Hvalue]]].
      + rewrite Hlookup. destruct n as [x | sym]; simpl.
        * split.
          -- intros [[ty1 [btm1 [[= <- <-] Hk]]] | [Hnone _]];
               [ | discriminate ].
             left. exists ty0, btm0. split; [ reflexivity | congruence ].
          -- intros [[ty1 [btm1 [[= <- <-] Hk]]] | [Hnone _]];
               [ | discriminate ].
             left. eexists. eexists. split; [ reflexivity | congruence ].
        * split.
          -- intros [[ty1 [btm1 [[= <- <-] Hk]]] | [Hnone _]];
               [ | discriminate ].
             left. exists ty0, btm0. split; [ reflexivity | congruence ].
          -- intros [[ty1 [btm1 [[= <- <-] Hk]]] | [Hnone _]];
               [ | discriminate ].
             left. eexists. eexists. split; [ reflexivity | congruence ].
      + destruct n as [x | sym].
        * exfalso. rewrite mem_var_is_bound in Hmem.
          unfold Keyed.is_bound in Hmem. rewrite Hnone in Hmem.
          discriminate.
        * rewrite Hnone. simpl. split.
          -- intros [[ty1 [btm1 [[= <- <-] Hk]]] | [Hnone' _]];
               [ | discriminate ].
             right. split; [ reflexivity | ].
             split; [ exact Hmem | congruence ].
          -- intros [[ty1 [btm1 [Hsome _]]] | [_ [_ ->]]];
               [ discriminate | ].
             left. eexists. eexists. split; [ reflexivity | exact Hvalue ].
    - rewrite (replace_equation_lookup_other tenv n m ty Hne).
      destruct m as [y | sym]; [ | rewrite Hsymbols; reflexivity ].
      rewrite !mem_var_is_bound. unfold Keyed.is_bound.
      rewrite (replace_equation_lookup_other tenv n (Name_var y) ty Hne).
      reflexivity. }
  destruct s as [x | sym | c]; [ | | reflexivity ].
  - exact (Hname (Name_var x)).
  - exact (Hname (Name_symbol sym)).
Qed.

Theorem add_alias_simple_of_kind : add_alias_simple_of_kind_statement.
Proof.
  intros tenv c1 c2 result s kind Hadd.
  destruct (add_alias_frame tenv c1 c2 result Hadd)
    as [_ [Hsymbols [_ [_ [Htypes _]]]]].
  apply simple_of_kind_same; assumption.
Qed.

(* ======================================================================== *)
(* The functions keep the kinds of what is known to be equal                *)
(* ======================================================================== *)

(* Two different simples that are known to be equal: the aliases speak
   of each that is a name. *)
Lemma aliased_mentioned (t : Aliases.t) (e e' : simple) (n : name) :
  aliased t e e' ->
  e <> e' ->
  e = simple_of_name n ->
  aliases_mention t n.
Proof.
  unfold aliased. intros Haliased Hne ->.
  destruct (canonical_cases t (simple_of_name n))
    as [[_ Hself] | [n0 [c [Heq [Hdemoted _]]]]].
  - destruct (canonical_cases t e')
      as [[_ Hself'] | [n' [c' [-> [Hdemoted' [_ Hcanonical']]]]]].
    + congruence.
    + right. left. exists n'. rewrite Hself, Hcanonical' in Haliased.
      rewrite Haliased. exact Hdemoted'.
  - apply simple_of_name_inj in Heq. subst n0. left. exists c.
    exact Hdemoted.
Qed.

(* Environments with the same aliases in which the simples have the
   same kinds. *)
Lemma aliases_kinded_same (tenv tenv' : Typing_env.t) :
  Typing_env.aliases tenv' = Typing_env.aliases tenv ->
  (∀ (s : simple) (kind : flambda_kind),
    simple_of_kind tenv' s kind -> simple_of_kind tenv s kind) ->
  aliases_kinded tenv ->
  aliases_kinded tenv'.
Proof.
  intros Haliases Hkinds Hkinded e e' kind kind' Haliased He He'.
  rewrite Haliases in Haliased.
  exact (Hkinded e e' kind kind' Haliased (Hkinds e kind He)
           (Hkinds e' kind' He')).
Qed.

Theorem create_aliases_kinded : create_aliases_kinded_statement.
Proof.
  intros e e' kind kind' Haliased He He'.
  assert (Heq : e = e').
  { unfold aliased in Haliased.
    destruct (canonical_cases (Typing_env.aliases Typing_env.create) e)
      as [[_ Hself] | [n [c [_ [Hdemoted _]]]]]; [ | discriminate Hdemoted ].
    destruct (canonical_cases (Typing_env.aliases Typing_env.create) e')
      as [[_ Hself'] | [n [c [_ [Hdemoted _]]]]]; [ | discriminate Hdemoted ].
    congruence. }
  subst e'. exact (simple_of_kind_unique _ e kind kind' He He').
Qed.

Theorem make_bottom_aliases_kinded : make_bottom_aliases_kinded_statement.
Proof.
  intros tenv. apply aliases_kinded_same; [ reflexivity | ].
  intros s kind. apply make_bottom_simple_of_kind.
Qed.

Theorem increment_scope_aliases_kinded
    : increment_scope_aliases_kinded_statement.
Proof.
  intros tenv. apply aliases_kinded_same; [ reflexivity | ].
  intros s kind. apply increment_scope_simple_of_kind.
Qed.

Theorem closure_env_aliases_kinded : closure_env_aliases_kinded_statement.
Proof.
  intros tenv. apply aliases_kinded_same; [ reflexivity | ].
  intros s kind. apply closure_env_simple_of_kind.
Qed.

Theorem add_symbol_definition_aliases_kinded
    : add_symbol_definition_aliases_kinded_statement.
Proof.
  intros tenv sym Hwf Hkinded e e' kind kind' Haliased He He'.
  change (Typing_env.aliases (Typing_env.add_symbol_definition tenv sym))
    with (Typing_env.aliases tenv) in Haliased.
  destruct (simple_equal e e') eqn:Hequal.
  { apply simple_equal_decides_equality in Hequal. subst e'.
    exact (simple_of_kind_unique _ e kind kind' He He'). }
  assert (Hne : e <> e').
  { intros Heq. apply simple_equal_decides_equality in Heq. congruence. }
  (* A simple that is known to be equal to another was of its kind. *)
  assert (Hold :
    ∀ (a b : simple) (k : flambda_kind),
      aliased (Typing_env.aliases tenv) a b ->
      a <> b ->
      simple_of_kind (Typing_env.add_symbol_definition tenv sym) a k ->
      simple_of_kind tenv a k).
  { intros a b k Hab Hab_ne Ha.
    apply add_symbol_definition_simple_of_kind in Ha.
    destruct Ha as [Ha | [-> [-> Hnone]]]; [ exact Ha | ].
    pose proof (aliased_mentioned _ _ _ (Name_symbol sym) Hab Hab_ne eq_refl)
      as Hmention.
    pose proof (well_formed_mentioned_known tenv _ Hwf Hmention) as Hbound.
    apply (simple_of_kind_name_iff tenv (Name_symbol sym) Value). right.
    split; [ exact Hnone | ]. split; [ exact Hbound | reflexivity ]. }
  apply (Hkinded e e' kind kind' Haliased).
  - exact (Hold e e' kind Haliased Hne He).
  - apply (Hold e' e kind'); [ | congruence | exact He' ].
    unfold aliased in *. congruence.
Qed.

Theorem add_variable_definition_aliases_kinded
    : add_variable_definition_aliases_kinded_statement.
Proof.
  intros tenv var kind_of_var name_mode Hwf Hfresh Hkinded e e' kind kind'
    Haliased He He'.
  change (Typing_env.aliases
            (Typing_env.add_variable_definition tenv var kind_of_var
               name_mode))
    with (Typing_env.aliases tenv) in Haliased.
  destruct (simple_equal e e') eqn:Hequal.
  { apply simple_equal_decides_equality in Hequal. subst e'.
    exact (simple_of_kind_unique _ e kind kind' He He'). }
  assert (Hne : e <> e').
  { intros Heq. apply simple_equal_decides_equality in Heq. congruence. }
  assert (Hold :
    ∀ (a b : simple) (k : flambda_kind),
      aliased (Typing_env.aliases tenv) a b ->
      a <> b ->
      simple_of_kind
        (Typing_env.add_variable_definition tenv var kind_of_var name_mode) a
        k ->
      simple_of_kind tenv a k).
  { intros a b k Hab Hab_ne Ha.
    apply add_variable_definition_simple_of_kind in Ha.
    destruct Ha as [[-> _] | [_ Ha]]; [ exfalso | exact Ha ].
    pose proof (aliased_mentioned _ _ _ (Name_var var) Hab Hab_ne eq_refl)
      as Hmention.
    pose proof (well_formed_mentioned_known tenv _ Hwf Hmention) as Hbound.
    congruence. }
  apply (Hkinded e e' kind kind' Haliased).
  - exact (Hold e e' kind Haliased Hne He).
  - apply (Hold e' e kind'); [ | congruence | exact He' ].
    unfold aliased in *. congruence.
Qed.

Theorem replace_equation_aliases_kinded
    : replace_equation_aliases_kinded_statement.
Proof.
  intros tenv n ty Hkind.
  apply aliases_kinded_same; [ apply replace_equation_aliases | ].
  intros s kind.
  apply (replace_equation_simple_of_kind tenv n ty s kind Hkind).
Qed.

Theorem add_alias_aliases_kinded : add_alias_aliases_kinded_statement.
Proof.
  intros tenv c1 c2 result kind Hconsistent Hc1 Hc2 Hkind1 Hkind2 Hadd
    Hkinded e e' k k' Haliased He He'.
  apply (add_alias_simple_of_kind tenv c1 c2 result e k Hadd) in He.
  apply (add_alias_simple_of_kind tenv c1 c2 result e' k' Hadd) in He'.
  destruct (add_alias_frame tenv c1 c2 result Hadd)
    as [[added [Hadded [Haliases _]]] _].
  rewrite Haliases in Haliased.
  apply (add_aliased _ _ _ _ c1 c2 added e e' Hconsistent Hc1 Hc2 Hadded)
    in Haliased.
  destruct Haliased as [Hold | [[H1 H2] | [H2 H1]]].
  - exact (Hkinded e e' k k' Hold He He').
  - rewrite (Hkinded e c1 k kind H1 He Hkind1).
    exact (eq_sym (Hkinded e' c2 k' kind H2 He' Hkind2)).
  - rewrite (Hkinded e c2 k kind H2 He Hkind2).
    exact (eq_sym (Hkinded e' c1 k' kind H1 He' Hkind1)).
Qed.

(* ======================================================================== *)
(* Constants                                                                *)
(* ======================================================================== *)

Theorem aliases_kinded_constants_of_kind
    : aliases_kinded_constants_of_kind_statement.
Proof.
  intros tenv Hconsistent Hkinded s kind c Hs.
  unfold Typing_env.get_canonical_simple_exn.
  destruct (option_map Binding_time.With_name_mode.name_mode
              (Typing_env.binding_time_and_mode_of_simple tenv s))
    as [name_mode_simple | ]; [ | discriminate ].
  intros [= Hcanonical].
  pose proof (canonical_at_mode_aliased _ _ _ _ _ _ _ _ _ Hconsistent
                Hcanonical) as Haliased.
  exact (Hkinded (Const c) s _ kind Haliased eq_refl Hs).
Qed.
