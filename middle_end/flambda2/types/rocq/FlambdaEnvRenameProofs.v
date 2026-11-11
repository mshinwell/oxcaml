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


(* Proofs of the statements of FlambdaEnvRenameSpec.v. Nothing here needs
   review.

   The laws of the action are had part by part: a map whose keys and
   values are renamed has each law when the renaming of its keys and
   that of its values have it. The parts are the action on types
   (FlambdaTypeRenameProofs.v) and the action on the aliases
   (FlambdaEnvAliasesRenamingProofs.v). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaMapProofs FlambdaSemanticsSpec FlambdaNominalSpec
  FlambdaNominalProofs FlambdaAlphaSpec FlambdaAlphaProofs
  FlambdaNameAbstractionSpec FlambdaNameAbstractionProofs
  FlambdaNominalInstancesSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaEnvAliasesRenamingSpec
  FlambdaEnvAliasesRenamingProofs FlambdaTypingEnv FlambdaTypeRenameSpec
  FlambdaTypeRenameProofs FlambdaTypeNominalSpec FlambdaTypeNominalProofs
  FlambdaEnvRenameSpec.
Import ListNotations.
Import Nominal.

(* ======================================================================== *)
(* Maps whose keys and values are renamed                                   *)
(* ======================================================================== *)

Lemma map_bindings_same {K A : Type} (f : K -> K) (g : A -> A)
    (bindings : Keyed.finite_map K A) :
  (∀ (k : K) (a : A), (k, a) ∈ bindings -> f k = k ∧ g a = a) ->
  Keyed.map_bindings f g bindings = bindings.
Proof.
  intros Hsame. unfold Keyed.map_bindings.
  induction bindings as [ | [k a] bindings IH]; simpl; [ reflexivity | ].
  destruct (Hsame k a (or_introl eq_refl)) as [-> ->]. rewrite IH;
    [ reflexivity | ].
  intros k' a' Hin. apply Hsame. right. exact Hin.
Qed.

Lemma map_bindings_alike {K K' A B : Type} (f f' : K -> K') (g g' : A -> B)
    (bindings : Keyed.finite_map K A) :
  (∀ (k : K) (a : A), (k, a) ∈ bindings -> f k = f' k ∧ g a = g' a) ->
  Keyed.map_bindings f g bindings = Keyed.map_bindings f' g' bindings.
Proof.
  intros Halike. unfold Keyed.map_bindings. apply map_ext_in.
  intros [k a] Hin. simpl. destruct (Halike k a Hin) as [-> ->].
  reflexivity.
Qed.

Lemma map_bindings_twice {K K' K'' A B C : Type} (f : K' -> K'')
    (f' : K -> K') (g : B -> C) (g' : A -> B)
    (bindings : Keyed.finite_map K A) :
  Keyed.map_bindings f g (Keyed.map_bindings f' g' bindings)
  = Keyed.map_bindings (fun k => f (f' k)) (fun a => g (g' a)) bindings.
Proof. unfold Keyed.map_bindings. rewrite map_map. reflexivity. Qed.

Lemma in_flat_map_of {A B : Type} (f : A -> list B) (l : list A) (a : A)
    (b : B) :
  a ∈ l -> b ∈ f a -> b ∈ flat_map f l.
Proof. intros Ha Hb. apply in_flat_map. exists a. split; assumption. Qed.

Lemma flat_map_mapped {A B C D : Type} (h : A -> B) (f : A -> list C)
    (f' : B -> list D) (g : C -> D) (l : list A) :
  (∀ a : A, f' (h a) = map g (f a)) ->
  flat_map f' (map h l) = map g (flat_map f l).
Proof.
  intros Hf. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hf, IH, map_app. reflexivity.
Qed.

(* ======================================================================== *)
(* The parts: names, and what the environment knows of a name               *)
(* ======================================================================== *)

Lemma rename_variable_identity (x : variable) :
  rename_variable identity_renaming x = x.
Proof. reflexivity. Qed.

Lemma rename_name_same (n : name) : rename_name identity_renaming n = n.
Proof. destruct n; reflexivity. Qed.

Lemma rename_name_twice (second first : renaming) (n : name) :
  rename_name (compose_renaming second first) n
  = rename_name second (rename_name first n).
Proof.
  destruct n; simpl; [ rewrite rename_variable_compose | ]; reflexivity.
Qed.

Lemma rename_name_alike (r r' : renaming) (n : name) :
  (∀ x : variable,
    x ∈ free_variables_of_name n ->
    rename_variable r x = rename_variable r' x) ->
  rename_name r n = rename_name r' n.
Proof.
  destruct n as [x | s]; simpl; intros Halike; [ | reflexivity ].
  rewrite (Halike x (or_introl eq_refl)). reflexivity.
Qed.

Lemma rename_binding_same
    (binding : flambda_type * Binding_time.With_name_mode.t) :
  rename_binding identity_renaming binding = binding.
Proof.
  destruct binding as [ty binding_time]. unfold rename_binding. simpl.
  rewrite (proj1 rename_type_identity). reflexivity.
Qed.

Lemma rename_binding_twice (second first : renaming)
    (binding : flambda_type * Binding_time.With_name_mode.t) :
  rename_binding (compose_renaming second first) binding
  = rename_binding second (rename_binding first binding).
Proof.
  unfold rename_binding. simpl. rewrite (proj1 rename_type_compose).
  reflexivity.
Qed.

Lemma rename_binding_alike (r r' : renaming)
    (binding : flambda_type * Binding_time.With_name_mode.t) :
  (∀ x : variable,
    x ∈ free_variables (fst binding) ->
    rename_variable r x = rename_variable r' x) ->
  rename_binding r binding = rename_binding r' binding.
Proof.
  intros Halike. unfold rename_binding.
  rewrite (proj1 rename_type_extensional r r' (fst binding) Halike).
  reflexivity.
Qed.

(* A map from names whose values are renamed by [g], whose free variables
   are [fv]: the laws, from those of [g]. *)
Section Named_bindings.

Context {B : Type} (g : renaming -> B -> B) (fv : B -> list variable).

Hypothesis g_same : ∀ b : B, g identity_renaming b = b.
Hypothesis g_twice :
  ∀ (second first : renaming) (b : B),
    g (compose_renaming second first) b = g second (g first b).
Hypothesis g_alike :
  ∀ (r r' : renaming) (b : B),
    (∀ x : variable, x ∈ fv b -> rename_variable r x = rename_variable r' x)
    ->
    g r b = g r' b.
Hypothesis g_free :
  ∀ (r : renaming) (b : B), fv (g r b) = map (rename_variable r) (fv b).

Definition bindings_free_variables (bindings : Keyed.finite_map name B)
    : list variable :=
  flat_map
    (fun binding => free_variables_of_name (fst binding) ++ fv (snd binding))
    bindings.

Lemma named_bindings_same (bindings : Keyed.finite_map name B) :
  Keyed.map_bindings (rename_name identity_renaming) (g identity_renaming)
    bindings
  = bindings.
Proof.
  apply map_bindings_same. intros n b _. split;
    [ apply rename_name_same | apply g_same ].
Qed.

Lemma named_bindings_twice (second first : renaming)
    (bindings : Keyed.finite_map name B) :
  Keyed.map_bindings (rename_name (compose_renaming second first))
    (g (compose_renaming second first)) bindings
  = Keyed.map_bindings (rename_name second) (g second)
      (Keyed.map_bindings (rename_name first) (g first) bindings).
Proof.
  rewrite map_bindings_twice. apply map_bindings_alike. intros n b _.
  split; [ apply rename_name_twice | apply g_twice ].
Qed.

Lemma named_bindings_alike (r r' : renaming)
    (bindings : Keyed.finite_map name B) :
  (∀ x : variable,
    x ∈ bindings_free_variables bindings ->
    rename_variable r x = rename_variable r' x) ->
  Keyed.map_bindings (rename_name r) (g r) bindings
  = Keyed.map_bindings (rename_name r') (g r') bindings.
Proof.
  intros Halike. apply map_bindings_alike. intros n b Hin.
  split; [ apply rename_name_alike | apply g_alike ]; intros x Hx;
    apply Halike;
    apply (in_flat_map_of _ bindings (n, b) x Hin), in_or_app;
    [ left | right ]; exact Hx.
Qed.

Lemma named_bindings_free (r : renaming)
    (bindings : Keyed.finite_map name B) :
  bindings_free_variables (Keyed.map_bindings (rename_name r) (g r) bindings)
  = map (rename_variable r) (bindings_free_variables bindings).
Proof.
  unfold bindings_free_variables, Keyed.map_bindings.
  apply flat_map_mapped. intros [n b]. simpl.
  rewrite FlambdaTypeRenameProofs.free_variables_of_name_renamed, g_free,
    map_app.
  reflexivity.
Qed.

End Named_bindings.

(* ======================================================================== *)
(* The aliases: two renamings that agree on the free variables              *)
(* ======================================================================== *)

Lemma rename_aliases_inverse_r (r : renaming) (t : Aliases.t) :
  rename_aliases r (rename_aliases (inverse_renaming r) t) = t.
Proof.
  rewrite <- rename_aliases_compose.
  rewrite (rename_aliases_extensional _ identity_renaming);
    [ apply rename_aliases_identity | ].
  intros x. rewrite rename_variable_compose. apply rename_variable_inverse_r.
Qed.

Lemma rename_aliases_alike (r r' : renaming) (t : Aliases.t) :
  (∀ x : variable,
    x ∈ aliases_free_variables t ->
    rename_variable r x = rename_variable r' x) ->
  rename_aliases r t = rename_aliases r' t.
Proof.
  intros Halike.
  assert (Hfixed :
    rename_aliases (compose_renaming (inverse_renaming r) r') t = t).
  { apply rename_aliases_fixes. intros x Hx.
    rewrite rename_variable_compose, <- (Halike x (proj1 (among_In _ _) Hx)).
    apply rename_variable_inverse_l. }
  rewrite rename_aliases_compose in Hfixed.
  rewrite <- Hfixed at 1. apply rename_aliases_inverse_r.
Qed.

(* ======================================================================== *)
(* Levels                                                                   *)
(* ======================================================================== *)

Lemma level_eq (defined_vars defined_vars' : finite_map flambda_kind)
    (binding_times binding_times'
      : Keyed.finite_map Binding_time.t (list variable))
    (equations equations' : Keyed.finite_map name flambda_type) :
  defined_vars = defined_vars' -> binding_times = binding_times' ->
  equations = equations' ->
  Typing_env_level.create defined_vars binding_times equations
  = Typing_env_level.create defined_vars' binding_times' equations'.
Proof. intros -> -> ->. reflexivity. Qed.

Theorem rename_level_identity : rename_level_identity_statement.
Proof.
  intros [defined_vars binding_times equations]. unfold rename_level. simpl.
  apply level_eq.
  - apply map_bindings_same. intros x kind _. split; reflexivity.
  - unfold Keyed.map_values.
    induction binding_times as [ | [binding_time vars] binding_times IH];
      simpl; [ reflexivity | ].
    rewrite map_id, IH. reflexivity.
  - apply (named_bindings_same rename_type). exact (proj1 rename_type_identity).
Qed.

Theorem rename_level_compose : rename_level_compose_statement.
Proof.
  intros second first [defined_vars binding_times equations].
  unfold rename_level. simpl. apply level_eq.
  - unfold Keyed.map_keys. rewrite map_bindings_twice.
    apply map_bindings_alike. intros x kind _. split; [ | reflexivity ].
    apply rename_variable_compose.
  - unfold Keyed.map_values. rewrite map_map. apply map_ext.
    intros [binding_time vars]. simpl. rewrite map_map. f_equal.
    apply map_ext. intros x. apply rename_variable_compose.
  - apply (named_bindings_twice rename_type).
    exact (proj1 rename_type_compose).
Qed.

Theorem rename_level_extensional : rename_level_extensional_statement.
Proof.
  intros r r' [defined_vars binding_times equations] Halike.
  unfold level_free_variables in Halike. simpl in Halike.
  unfold rename_level. simpl. apply level_eq.
  - apply map_bindings_alike. intros x kind Hin. split; [ | reflexivity ].
    apply Halike, in_or_app. left. exact (in_map fst _ _ Hin).
  - unfold Keyed.map_values. apply map_ext_in.
    intros [binding_time vars] Hin. simpl. f_equal. apply map_ext_in.
    intros x Hx. apply Halike, in_or_app. right. apply in_or_app. left.
    exact (in_flat_map_of snd _ _ x Hin Hx).
  - apply (named_bindings_alike rename_type free_variables).
    + exact (proj1 rename_type_extensional).
    + intros x Hx. apply Halike, in_or_app. right. apply in_or_app. right.
      exact Hx.
Qed.

Theorem rename_level_fixes : rename_level_fixes_statement.
Proof.
  intros r level Hfixes.
  rewrite (rename_level_extensional r identity_renaming level);
    [ apply rename_level_identity | ].
  exact Hfixes.
Qed.

Theorem rename_level_inverse : rename_level_inverse_statement.
Proof.
  intros r level. rewrite <- rename_level_compose.
  apply rename_level_fixes. intros x _.
  rewrite rename_variable_compose. apply rename_variable_inverse_l.
Qed.

Theorem free_variables_rename_level : free_variables_rename_level_statement.
Proof.
  intros r [defined_vars binding_times equations].
  unfold level_free_variables, rename_level. simpl. rewrite !map_app.
  apply f_equal2; [ | apply f_equal2 ].
  - unfold Keyed.map_keys, Keyed.map_bindings. rewrite !map_map. reflexivity.
  - unfold Keyed.map_values. apply flat_map_mapped. intros [bt vars].
    reflexivity.
  - apply (named_bindings_free rename_type free_variables).
    exact (proj1 free_variables_rename_type).
Qed.

(* ======================================================================== *)
(* What the environment knows of its names                                  *)
(* ======================================================================== *)

Lemma cached_level_eq
    (names_to_types names_to_types'
      : Keyed.finite_map name (flambda_type * Binding_time.With_name_mode.t))
    (aliases aliases' : Aliases.t) :
  names_to_types = names_to_types' -> aliases = aliases' ->
  {| Cached_level.names_to_types := names_to_types;
     Cached_level.aliases := aliases |}
  = {| Cached_level.names_to_types := names_to_types';
       Cached_level.aliases := aliases' |}.
Proof. intros -> ->. reflexivity. Qed.

Lemma rename_cached_level_same (cached : Cached_level.t) :
  rename_cached_level identity_renaming cached = cached.
Proof.
  destruct cached as [names_to_types aliases]. unfold rename_cached_level.
  simpl. apply cached_level_eq.
  - apply (named_bindings_same rename_binding). exact rename_binding_same.
  - apply rename_aliases_identity.
Qed.

Lemma rename_cached_level_twice (second first : renaming)
    (cached : Cached_level.t) :
  rename_cached_level (compose_renaming second first) cached
  = rename_cached_level second (rename_cached_level first cached).
Proof.
  destruct cached as [names_to_types aliases]. unfold rename_cached_level.
  simpl. apply cached_level_eq.
  - apply (named_bindings_twice rename_binding). exact rename_binding_twice.
  - apply rename_aliases_compose.
Qed.

Lemma rename_cached_level_alike (r r' : renaming) (cached : Cached_level.t) :
  (∀ x : variable,
    x ∈ cached_level_free_variables cached ->
    rename_variable r x = rename_variable r' x) ->
  rename_cached_level r cached = rename_cached_level r' cached.
Proof.
  destruct cached as [names_to_types aliases].
  unfold cached_level_free_variables, rename_cached_level. simpl.
  intros Halike. apply cached_level_eq.
  - apply (named_bindings_alike rename_binding
             (fun binding => free_variables (fst binding))).
    + exact rename_binding_alike.
    + intros x Hx. apply Halike, in_or_app. left. exact Hx.
  - apply rename_aliases_alike. intros x Hx. apply Halike, in_or_app.
    right. exact Hx.
Qed.

Lemma cached_level_free_variables_renamed (r : renaming)
    (cached : Cached_level.t) :
  cached_level_free_variables (rename_cached_level r cached)
  = map (rename_variable r) (cached_level_free_variables cached).
Proof.
  destruct cached as [names_to_types aliases].
  unfold cached_level_free_variables, rename_cached_level. simpl.
  rewrite map_app, rename_free_variables. f_equal.
  apply (named_bindings_free rename_binding
           (fun binding => free_variables (fst binding))).
  intros r' binding. exact (proj1 free_variables_rename_type r' (fst binding)).
Qed.

(* ======================================================================== *)
(* Environments                                                             *)
(* ======================================================================== *)

Lemma typing_env_eq (tenv : Typing_env.t)
    (prev_levels : list Typing_env.One_level.t)
    (current_level : Typing_env.One_level.t)
    (just_after_level : Cached_level.t) :
  prev_levels = Typing_env.prev_levels tenv ->
  current_level = Typing_env.current_level tenv ->
  just_after_level = Typing_env.just_after_level tenv ->
  {| Typing_env.defined_symbols := Typing_env.defined_symbols tenv;
     Typing_env.prev_levels := prev_levels;
     Typing_env.current_level := current_level;
     Typing_env.just_after_level := just_after_level;
     Typing_env.next_binding_time := Typing_env.next_binding_time tenv;
     Typing_env.min_binding_time := Typing_env.min_binding_time tenv;
     Typing_env.is_bottom := Typing_env.is_bottom tenv |}
  = tenv.
Proof. intros -> -> ->. destruct tenv. reflexivity. Qed.

Lemma rename_one_level_same (one_level : Typing_env.One_level.t) :
  rename_one_level identity_renaming one_level = one_level.
Proof.
  destruct one_level as [scope level]. unfold rename_one_level. simpl.
  rewrite rename_level_identity. reflexivity.
Qed.

Lemma rename_one_level_twice (second first : renaming)
    (one_level : Typing_env.One_level.t) :
  rename_one_level (compose_renaming second first) one_level
  = rename_one_level second (rename_one_level first one_level).
Proof.
  unfold rename_one_level. simpl. rewrite rename_level_compose. reflexivity.
Qed.

Lemma rename_one_level_alike (r r' : renaming)
    (one_level : Typing_env.One_level.t) :
  (∀ x : variable,
    x ∈ level_free_variables (Typing_env.One_level.level one_level) ->
    rename_variable r x = rename_variable r' x) ->
  rename_one_level r one_level = rename_one_level r' one_level.
Proof.
  intros Halike. unfold rename_one_level.
  rewrite (rename_level_extensional r r' _ Halike). reflexivity.
Qed.

Theorem rename_typing_env_identity : rename_typing_env_identity_statement.
Proof.
  intros tenv. unfold rename_typing_env. apply typing_env_eq.
  - rewrite (map_ext _ (fun one_level => one_level) rename_one_level_same).
    apply map_id.
  - apply rename_one_level_same.
  - apply rename_cached_level_same.
Qed.

Theorem rename_typing_env_compose : rename_typing_env_compose_statement.
Proof.
  intros second first tenv. unfold rename_typing_env. simpl.
  rewrite map_map, rename_one_level_twice, rename_cached_level_twice.
  rewrite (map_ext _ _ (rename_one_level_twice second first)). reflexivity.
Qed.

Theorem rename_typing_env_extensional :
  rename_typing_env_extensional_statement.
Proof.
  intros r r' tenv Halike. unfold typing_env_free_variables in Halike.
  unfold rename_typing_env.
  rewrite (rename_one_level_alike r r' (Typing_env.current_level tenv)),
    (rename_cached_level_alike r r' (Typing_env.just_after_level tenv)).
  - f_equal. apply map_ext_in. intros one_level Hin.
    apply rename_one_level_alike. intros x Hx. apply Halike, in_or_app.
    left.
    exact
      (in_flat_map_of
         (fun one_level =>
            level_free_variables (Typing_env.One_level.level one_level))
         _ one_level x Hin Hx).
  - intros x Hx. apply Halike, in_or_app. right. apply in_or_app. right.
    exact Hx.
  - intros x Hx. apply Halike, in_or_app. right. apply in_or_app. left.
    exact Hx.
Qed.

Theorem rename_typing_env_fixes : rename_typing_env_fixes_statement.
Proof.
  intros r tenv Hfixes.
  rewrite (rename_typing_env_extensional r identity_renaming tenv);
    [ apply rename_typing_env_identity | ].
  exact Hfixes.
Qed.

Theorem rename_typing_env_inverse : rename_typing_env_inverse_statement.
Proof.
  intros r tenv. rewrite <- rename_typing_env_compose.
  apply rename_typing_env_fixes. intros x _.
  rewrite rename_variable_compose. apply rename_variable_inverse_l.
Qed.

Theorem free_variables_rename_typing_env :
  free_variables_rename_typing_env_statement.
Proof.
  intros r tenv. unfold typing_env_free_variables, rename_typing_env. simpl.
  rewrite !map_app, free_variables_rename_level,
    cached_level_free_variables_renamed.
  f_equal. apply flat_map_mapped. intros one_level. simpl.
  apply free_variables_rename_level.
Qed.

(* ======================================================================== *)
(* The two instances                                                        *)
(* ======================================================================== *)

Theorem level_names_nominal : level_names_nominal_statement.
Proof.
  constructor; simpl.
  - reflexivity.
  - intros t t' Hsame. symmetry. exact Hsame.
  - intros t t' t'' -> ->. reflexivity.
  - exact rename_level_identity.
  - intros second first level.
    exact
      (rename_level_compose (variables_renaming second)
         (variables_renaming first) level).
  - intros p p' level Hsame. apply rename_level_extensional.
    intros x _. exact (Hsame x).
  - intros p t t' ->. reflexivity.
  - intros p level name. rewrite free_variables_rename_level.
    apply among_renamed_variables.
  - intros t t' -> name. reflexivity.
  - intros p level Hfixes. apply rename_level_fixes.
    intros x Hin. exact (fixes_in p _ x Hfixes Hin).
Qed.

Theorem typing_env_names_nominal : typing_env_names_nominal_statement.
Proof.
  constructor; simpl.
  - reflexivity.
  - intros t t' Hsame. symmetry. exact Hsame.
  - intros t t' t'' -> ->. reflexivity.
  - exact rename_typing_env_identity.
  - intros second first tenv.
    exact
      (rename_typing_env_compose (variables_renaming second)
         (variables_renaming first) tenv).
  - intros p p' tenv Hsame. apply rename_typing_env_extensional.
    intros x _. exact (Hsame x).
  - intros p t t' ->. reflexivity.
  - intros p tenv name. rewrite free_variables_rename_typing_env.
    apply among_renamed_variables.
  - intros t t' -> name. reflexivity.
  - intros p tenv Hfixes. apply rename_typing_env_fixes.
    intros x Hin. exact (fixes_in p _ x Hfixes Hin).
Qed.

(* ======================================================================== *)
(* Lookups and domains of renamed maps                                      *)
(* ======================================================================== *)

(* The lemmas of FlambdaEnvAliasesRenamingProofs.v on maps whose keys
   are renamed, for the two sorts of keys here: names and variables. *)
Lemma lookup_named_renamed {B C : Type} (r : renaming) (g : B -> C)
    (n : name) (bindings : Keyed.finite_map name B) :
  Keyed.lookup name_eqb (rename_name r n)
    (Keyed.map_bindings (rename_name r) g bindings)
  = option_map g (Keyed.lookup name_eqb n bindings).
Proof.
  exact (lookup_renamed name_eqb (rename_name r) (name_eqb_renamed r) g n
           bindings).
Qed.

Lemma domain_named_renamed {B C : Type} (r : renaming) (g : B -> C)
    (bindings : Keyed.finite_map name B) :
  Keyed.domain name_eqb (Keyed.map_bindings (rename_name r) g bindings)
  = map (rename_name r) (Keyed.domain name_eqb bindings).
Proof.
  exact (domain_renamed name_eqb (rename_name r) (name_eqb_renamed r) g
           bindings).
Qed.

Lemma unbind_named_renamed {B C : Type} (r : renaming) (g : B -> C)
    (n : name) (bindings : Keyed.finite_map name B) :
  Keyed.unbind name_eqb (rename_name r n)
    (Keyed.map_bindings (rename_name r) g bindings)
  = Keyed.map_bindings (rename_name r) g (Keyed.unbind name_eqb n bindings).
Proof.
  exact (unbind_renamed name_eqb (rename_name r) (name_eqb_renamed r) g n
           bindings).
Qed.

Lemma compact_named_renamed {B C : Type} (r : renaming) (g : B -> C)
    (bindings : Keyed.finite_map name B) :
  Keyed.compact name_eqb (Keyed.map_bindings (rename_name r) g bindings)
  = Keyed.map_bindings (rename_name r) g (Keyed.compact name_eqb bindings).
Proof.
  unfold Keyed.compact. rewrite domain_named_renamed.
  apply (tabulate_renamed (rename_name r) g). intros n.
  apply lookup_named_renamed.
Qed.

Lemma lookup_variable_renamed {B C : Type} (r : renaming) (g : B -> C)
    (x : variable) (bindings : finite_map B) :
  lookup (rename_variable r x)
    (Keyed.map_bindings (rename_variable r) g bindings)
  = option_map g (lookup x bindings).
Proof.
  exact (lookup_renamed Pos.eqb (rename_variable r) (rename_variable_eqb r) g
           x bindings).
Qed.

Lemma domain_variable_renamed {B C : Type} (r : renaming) (g : B -> C)
    (bindings : finite_map B) :
  domain (Keyed.map_bindings (rename_variable r) g bindings)
  = map (rename_variable r) (domain bindings).
Proof.
  exact (domain_renamed Pos.eqb (rename_variable r) (rename_variable_eqb r) g
           bindings).
Qed.

Lemma dedup_variables_renamed (r : renaming) (vars : list variable) :
  dedup (map (rename_variable r) vars) = map (rename_variable r) (dedup vars).
Proof.
  exact (dedup_renamed Pos.eqb (rename_variable r) (rename_variable_eqb r)
           vars).
Qed.

Lemma inter_variables_renamed (r : renaming) (vars vars' : list variable) :
  inter (map (rename_variable r) vars) (map (rename_variable r) vars')
  = map (rename_variable r) (inter vars vars').
Proof.
  unfold inter. apply filter_renamed. intros x.
  exact
    (FlambdaEnvAliasesRenamingProofs.among_keys_renamed Pos.eqb
       (rename_variable r) (rename_variable_eqb r) x vars').
Qed.

Lemma domain_map_values_keyed {K A B : Type} (eqb : K -> K -> bool)
    (f : A -> B) (bindings : Keyed.finite_map K A) :
  Keyed.domain eqb (Keyed.map_values f bindings) = Keyed.domain eqb bindings.
Proof.
  unfold Keyed.domain, Keyed.map_values. rewrite map_map. reflexivity.
Qed.

Lemma flat_map_each_mapped {A C D : Type} (f : A -> list C)
    (f' : A -> list D) (g : C -> D) (l : list A) :
  (∀ a : A, f' a = map g (f a)) -> flat_map f' l = map g (flat_map f l).
Proof.
  intros Hf. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hf, IH, map_app. reflexivity.
Qed.

Lemma some_if_mapped {A B : Type} (c : bool) (g : A -> B) (a : A) (b : B) :
  g a = b ->
  (if c then Some b else None) = option_map g (if c then Some a else None).
Proof. intros <-. destruct c; reflexivity. Qed.

(* The variables that a level has at a binding time, if it has some. *)
Lemma consed_to_found {A B : Type} (f : A -> B) (a : A)
    (found : option (list A)) :
  match option_map (map f) found with
  | Some prev => f a :: prev
  | None => [f a]
  end
  = map f match found with
          | Some prev => a :: prev
          | None => [a]
          end.
Proof. destruct found; reflexivity. Qed.

Lemma dedup_of_found (r : renaming) (found : option (list variable)) :
  match option_map (map (rename_variable r)) found with
  | Some vars => dedup vars
  | None => []
  end
  = map (rename_variable r) match found with
                            | Some vars => dedup vars
                            | None => []
                            end.
Proof.
  destruct found as [vars | ]; simpl; [ | reflexivity ].
  apply dedup_variables_renamed.
Qed.

(* ======================================================================== *)
(* The functions of a level                                                 *)
(* ======================================================================== *)

Theorem level_empty_equivariant : level_empty_equivariant_statement.
Proof. intros r. reflexivity. Qed.

Theorem level_defined_variables_equivariant :
  level_defined_variables_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations].
  exact (domain_variable_renamed r (fun kind => kind) defined_vars).
Qed.

Theorem level_defined_names_equivariant :
  level_defined_names_equivariant_statement.
Proof.
  intros r level. unfold Typing_env_level.defined_names.
  rewrite level_defined_variables_equivariant, !map_map. reflexivity.
Qed.

Theorem level_find_kind_equivariant : level_find_kind_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations] var.
  unfold Typing_env_level.find_kind, rename_level. simpl.
  unfold Keyed.map_keys.
  rewrite (lookup_variable_renamed r (fun kind => kind) var defined_vars).
  destruct (lookup var defined_vars); reflexivity.
Qed.

Theorem level_variable_is_defined_equivariant :
  level_variable_is_defined_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations] var.
  unfold Typing_env_level.variable_is_defined, rename_level, is_bound. simpl.
  unfold Keyed.map_keys.
  rewrite (lookup_variable_renamed r (fun kind => kind) var defined_vars).
  destruct (lookup var defined_vars); reflexivity.
Qed.

Theorem level_is_empty_equivariant : level_is_empty_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations].
  unfold Typing_env_level.is_empty, rename_level. simpl.
  unfold Keyed.map_keys, Keyed.map_bindings, Keyed.map_values.
  rewrite !is_empty_map. reflexivity.
Qed.

Theorem level_add_definition_equivariant :
  level_add_definition_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations] var kind binding_time.
  unfold Typing_env_level.add_definition, rename_level. simpl.
  rewrite keyed_lookup_map_values.
  apply level_eq; [ reflexivity | | reflexivity ].
  apply f_equal2; [ | reflexivity ]. apply f_equal.
  apply (consed_to_found (rename_variable r)).
Qed.

Theorem level_add_or_replace_equation_equivariant :
  level_add_or_replace_equation_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations] n ty.
  unfold Typing_env_level.add_or_replace_equation, rename_level. simpl.
  rewrite is_obviously_unknown_renamed.
  destruct (is_obviously_unknown ty); [ | reflexivity ].
  apply level_eq; try reflexivity. apply unbind_named_renamed.
Qed.

Theorem level_concat_equivariant : level_concat_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations]
    [defined_vars' binding_times' equations'].
  unfold Typing_env_level.concat, rename_level. simpl.
  unfold Keyed.map_keys.
  rewrite !domain_variable_renamed, inter_variables_renamed, is_empty_map,
    !domain_map_values_keyed.
  apply (some_if_mapped _ (rename_level r)). unfold rename_level. simpl.
  unfold Keyed.map_keys, Keyed.map_bindings, Keyed.map_values.
  rewrite !map_app. reflexivity.
Qed.

Theorem level_as_extension_equivariant :
  level_as_extension_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations].
  unfold Typing_env_level.as_extension_without_bindings, rename_level. simpl.
  f_equal. exact (compact_named_renamed r (rename_type r) equations).
Qed.

Theorem level_variables_in_order_equivariant :
  level_variables_in_order_equivariant_statement.
Proof.
  intros r [defined_vars binding_times equations].
  unfold Typing_env_level.variables_in_order, rename_level. simpl.
  rewrite domain_map_values_keyed. apply flat_map_each_mapped.
  intros binding_time. rewrite keyed_lookup_map_values.
  apply (dedup_of_found r).
Qed.

Theorem level_fold_on_defined_vars_equivariant :
  level_fold_on_defined_vars_equivariant_statement.
Proof.
  intros A r rename_acc f f' level init Hf.
  unfold Typing_env_level.fold_on_defined_vars.
  rewrite level_variables_in_order_equivariant.
  change (Some (rename_acc init)) with (option_map rename_acc (Some init)).
  generalize (Some init) as acc.
  induction (Typing_env_level.variables_in_order level) as [ | var vars IH];
    intros acc; simpl; [ reflexivity | ].
  rewrite <- IH. f_equal. destruct acc as [acc | ]; simpl; [ | reflexivity ].
  rewrite level_find_kind_equivariant.
  destruct (Typing_env_level.find_kind level var) as [kind | ]; simpl;
    [ | reflexivity ].
  rewrite Hf. reflexivity.
Qed.

(* ======================================================================== *)
(* What the environment knows of its names                                  *)
(* ======================================================================== *)

Theorem cached_level_empty_equivariant :
  cached_level_empty_equivariant_statement.
Proof. intros r. reflexivity. Qed.

Theorem cached_level_add_or_replace_binding_equivariant :
  cached_level_add_or_replace_binding_equivariant_statement.
Proof. intros r cached n ty binding_time name_mode. reflexivity. Qed.

Theorem cached_level_replace_variable_binding_equivariant :
  cached_level_replace_variable_binding_equivariant_statement.
Proof.
  intros r [names_to_types aliases] var ty.
  unfold Cached_level.replace_variable_binding, rename_cached_level. simpl.
  change (Name_var (rename_variable r var))
    with (rename_name r (Name_var var)).
  rewrite lookup_named_renamed.
  destruct (Keyed.lookup name_eqb (Name_var var) names_to_types)
    as [[ty' binding_time] | ];
    reflexivity.
Qed.

Theorem cached_level_with_aliases_equivariant :
  cached_level_with_aliases_equivariant_statement.
Proof. intros r cached aliases. reflexivity. Qed.

(* ======================================================================== *)
(* The aliases read the environment for binding times only                  *)
(* ======================================================================== *)

(* The functions of the aliases take a resolver and the map from names
   to types with binding times, of which they read the binding times.
   Two resolvers that answer alike and two maps that give each name the
   same binding time and name mode are the same to them. *)
Lemma fold_left_alike {A B : Type} (f f' : A -> B -> A) (l : list B)
    (init : A) :
  (∀ (a : A) (b : B), f a b = f' a b) ->
  List.fold_left f l init = List.fold_left f' l init.
Proof.
  intros Hf. revert init.
  induction l as [ | b l IH]; intros init; simpl; [ reflexivity | ].
  rewrite Hf. apply IH.
Qed.

Lemma find_earliest_candidates_alike
    (t : Aliases.Aliases_of_canonical_element.t)
    (filter_by_scope filter_by_scope' : Name_mode.t -> list name -> list name)
    (min_name_mode : Name_mode.t) :
  (∀ (name_mode : Name_mode.t) (names : list name),
    filter_by_scope name_mode names = filter_by_scope' name_mode names) ->
  Aliases.Aliases_of_canonical_element.find_earliest_candidates t
    filter_by_scope min_name_mode
  = Aliases.Aliases_of_canonical_element.find_earliest_candidates t
      filter_by_scope' min_name_mode.
Proof.
  intros Hfilter.
  unfold Aliases.Aliases_of_canonical_element.find_earliest_candidates.
  apply fold_left_alike. intros res_opt order. rewrite Hfilter. reflexivity.
Qed.

Section Binding_times_alike.

Context {A B : Type}
  (resolver resolver' : name -> Binding_time.With_name_mode.t)
  (times : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
  (times' : Keyed.finite_map name (B * Binding_time.With_name_mode.t)).

Hypothesis resolvers_alike : ∀ n : name, resolver n = resolver' n.

Hypothesis times_alike :
  ∀ n : name,
    option_map snd (Keyed.lookup name_eqb n times)
    = option_map snd (Keyed.lookup name_eqb n times').

Lemma binding_time_and_name_mode_alike (elt : simple) :
  Aliases.binding_time_and_name_mode times elt
  = Aliases.binding_time_and_name_mode times' elt.
Proof.
  destruct elt as [x | sym | c]; simpl; try reflexivity.
  pose proof (times_alike (Name_var x)) as Hx.
  destruct (Keyed.lookup name_eqb (Name_var x) times) as [[a bt] | ],
    (Keyed.lookup name_eqb (Name_var x) times') as [[b bt'] | ];
    simpl in Hx; try discriminate; [ | reflexivity ].
  injection Hx as ->. reflexivity.
Qed.

Lemma name_defined_earlier_alike (alias than : name) :
  Aliases.name_defined_earlier resolver times alias than
  = Aliases.name_defined_earlier resolver' times' alias than.
Proof.
  unfold Aliases.name_defined_earlier.
  pose proof (times_alike alias) as Halias.
  pose proof (times_alike than) as Hthan.
  rewrite !resolvers_alike.
  destruct (Keyed.lookup name_eqb alias times) as [[a bt] | ],
    (Keyed.lookup name_eqb alias times') as [[b bt'] | ];
    simpl in Halias; try discriminate;
    destruct (Keyed.lookup name_eqb than times) as [[a2 bt2] | ],
      (Keyed.lookup name_eqb than times') as [[b2 bt2'] | ];
    simpl in Hthan; try discriminate;
    repeat
      match goal with
      | H : Some _ = Some _ |- _ => injection H as ->
      end;
    reflexivity.
Qed.

Lemma defined_earlier_alike (alias than : simple) :
  Aliases.defined_earlier resolver times alias than
  = Aliases.defined_earlier resolver' times' alias than.
Proof.
  unfold Aliases.defined_earlier.
  destruct (name_of_simple than); [ | reflexivity ].
  destruct (name_of_simple alias); [ | reflexivity ].
  apply name_defined_earlier_alike.
Qed.

Lemma compute_name_mode_unscoped_alike (elt : simple) :
  Aliases.compute_name_mode_unscoped times elt
  = Aliases.compute_name_mode_unscoped times' elt.
Proof.
  unfold Aliases.compute_name_mode_unscoped.
  rewrite binding_time_and_name_mode_alike. reflexivity.
Qed.

Lemma compute_name_mode_alike (elt : simple)
    (min_binding_time : Binding_time.t) :
  Aliases.compute_name_mode times elt min_binding_time
  = Aliases.compute_name_mode times' elt min_binding_time.
Proof.
  unfold Aliases.compute_name_mode.
  rewrite binding_time_and_name_mode_alike. reflexivity.
Qed.

Lemma add_alias_between_canonical_elements_alike (t : Aliases.t)
    (canonical_element to_be_demoted : simple) :
  Aliases.add_alias_between_canonical_elements times t canonical_element
    to_be_demoted
  = Aliases.add_alias_between_canonical_elements times' t canonical_element
      to_be_demoted.
Proof.
  unfold Aliases.add_alias_between_canonical_elements.
  rewrite compute_name_mode_unscoped_alike. reflexivity.
Qed.

Lemma add_alike (t : Aliases.t)
    (canonical_element1 canonical_element2 : simple) :
  Aliases.add resolver times t canonical_element1 canonical_element2
  = Aliases.add resolver' times' t canonical_element1 canonical_element2.
Proof.
  unfold Aliases.add, Aliases.add0, Aliases.add_alias,
    Aliases.choose_canonical_element_to_be_demoted.
  rewrite defined_earlier_alike.
  destruct
    (Aliases.defined_earlier resolver' times' canonical_element1
       canonical_element2);
    rewrite add_alias_between_canonical_elements_alike; reflexivity.
Qed.

Lemma find_earliest_alias_alike (t : Aliases.t) (canonical_element : simple)
    (min_binding_time : Binding_time.t) (min_name_mode : Name_mode.t) :
  Aliases.find_earliest_alias resolver times t canonical_element
    min_binding_time min_name_mode
  = Aliases.find_earliest_alias resolver' times' t canonical_element
      min_binding_time min_name_mode.
Proof.
  unfold Aliases.find_earliest_alias.
  rewrite
    (find_earliest_candidates_alike _ _
       (fun name_mode names =>
          if Name_mode.equal name_mode Name_mode.in_types
          then names
          else
            filter
              (fun name =>
                 Name_mode.equal name_mode
                   (Aliases.compute_name_mode times' (simple_of_name name)
                      min_binding_time))
              names)).
  - destruct
      (Aliases.Aliases_of_canonical_element.find_earliest_candidates _ _ _)
      as [[ | first rest] | ];
      try reflexivity.
    do 2 f_equal. apply fold_left_alike. intros min_elt elt.
    rewrite name_defined_earlier_alike. reflexivity.
  - intros name_mode names.
    destruct (Name_mode.equal name_mode Name_mode.in_types);
      [ reflexivity | ].
    apply filter_ext. intros name. rewrite compute_name_mode_alike.
    reflexivity.
Qed.

Lemma get_canonical_element_exn_alike (t : Aliases.t) (element : simple)
    (elt_name_mode min_name_mode : Name_mode.t)
    (min_binding_time : Binding_time.t) :
  Aliases.get_canonical_element_exn resolver times t element elt_name_mode
    min_name_mode min_binding_time
  = Aliases.get_canonical_element_exn resolver' times' t element
      elt_name_mode min_name_mode min_binding_time.
Proof.
  unfold Aliases.get_canonical_element_exn.
  destruct (Aliases.canonical t element) as [ | canonical_element];
    cbv beta iota zeta;
    rewrite ?compute_name_mode_alike, ?find_earliest_alias_alike;
    reflexivity.
Qed.

End Binding_times_alike.

(* ======================================================================== *)
(* What an environment is asked                                             *)
(* ======================================================================== *)

Ltac open_binding :=
  cbn [option_map fst snd]; unfold rename_binding; cbn [fst snd].

Lemma names_to_types_renamed (r : renaming) (tenv : Typing_env.t) :
  Typing_env.names_to_types (rename_typing_env r tenv)
  = Keyed.map_bindings (rename_name r) (rename_binding r)
      (Typing_env.names_to_types tenv).
Proof. reflexivity. Qed.

Theorem create_equivariant : create_equivariant_statement.
Proof. intros r. reflexivity. Qed.

Theorem aliases_equivariant : aliases_equivariant_statement.
Proof. intros r tenv. reflexivity. Qed.

Theorem names_to_types_equivariant : names_to_types_equivariant_statement.
Proof. exact names_to_types_renamed. Qed.

Theorem current_scope_equivariant : current_scope_equivariant_statement.
Proof. intros r tenv. reflexivity. Qed.

Theorem name_domain_equivariant : name_domain_equivariant_statement.
Proof.
  intros r tenv. unfold Typing_env.name_domain.
  rewrite names_to_types_renamed, domain_named_renamed, map_app, map_map.
  reflexivity.
Qed.

Lemma check_optional_kind_matches_renamed (r : renaming) (ty : flambda_type)
    (kind : option flambda_kind) :
  Typing_env.check_optional_kind_matches (rename_type r ty) kind
  = Typing_env.check_optional_kind_matches ty kind.
Proof.
  destruct kind as [kind | ]; simpl; [ | reflexivity ].
  rewrite kind_rename_type. reflexivity.
Qed.

Theorem find_unscoped_equivariant : find_unscoped_equivariant_statement.
Proof.
  intros r tenv n kind. unfold Typing_env.find_with_binding_time_and_mode'.
  rewrite names_to_types_renamed, lookup_named_renamed.
  destruct (Keyed.lookup name_eqb n (Typing_env.names_to_types tenv))
    as [[ty binding_time] | ];
    open_binding.
  - rewrite check_optional_kind_matches_renamed.
    destruct (Typing_env.check_optional_kind_matches ty kind);
      [ | reflexivity ].
    change (Typing_env.is_bottom (rename_typing_env r tenv))
      with (Typing_env.is_bottom tenv).
    destruct (Typing_env.is_bottom tenv); open_binding;
      rewrite ?kind_rename_type, ?rename_type_bottom; reflexivity.
  - destruct n as [x | sym]; [ reflexivity | ].
    cbn [rename_name].
    change (Typing_env.defined_symbols (rename_typing_env r tenv))
      with (Typing_env.defined_symbols tenv).
    destruct
      (among sym (Typing_env.defined_symbols tenv)
       && Typing_env.check_optional_kind_matches
            (fst Typing_env.initial_symbol_type) kind);
      reflexivity.
Qed.

Theorem find_equivariant : find_equivariant_statement.
Proof.
  intros r tenv n kind. unfold Typing_env.find.
  rewrite find_unscoped_equivariant.
  destruct (Typing_env.find_with_binding_time_and_mode' tenv n kind)
    as [[ty binding_time] | ];
    reflexivity.
Qed.

Theorem find_with_binding_time_and_mode_equivariant :
  find_with_binding_time_and_mode_equivariant_statement.
Proof.
  intros r tenv n kind. unfold Typing_env.find_with_binding_time_and_mode.
  rewrite find_unscoped_equivariant.
  destruct (Typing_env.find_with_binding_time_and_mode' tenv n kind)
    as [[ty binding_time] | ];
    reflexivity.
Qed.

Theorem binding_time_and_mode_equivariant :
  binding_time_and_mode_equivariant_statement.
Proof.
  intros r tenv [x | sym]; [ | reflexivity ].
  pose proof
    (find_with_binding_time_and_mode_equivariant r tenv (Name_var x) None)
    as Hfind.
  unfold Typing_env.binding_time_and_mode. cbn [rename_name] in *.
  rewrite Hfind.
  destruct (Typing_env.find_with_binding_time_and_mode tenv (Name_var x) None)
    as [[ty binding_time] | ];
    reflexivity.
Qed.

Theorem binding_time_and_mode_of_simple_equivariant :
  binding_time_and_mode_of_simple_equivariant_statement.
Proof.
  intros r tenv [x | sym | c]; [ | reflexivity | reflexivity ].
  exact (binding_time_and_mode_equivariant r tenv (Name_var x)).
Qed.

Theorem binding_time_resolver_equivariant :
  binding_time_resolver_equivariant_statement.
Proof.
  intros r tenv n. unfold Typing_env.binding_time_resolver.
  rewrite names_to_types_renamed, lookup_named_renamed.
  destruct (Keyed.lookup name_eqb n (Typing_env.names_to_types tenv))
    as [[ty binding_time] | ];
    [ reflexivity | destruct n; reflexivity ].
Qed.

Theorem mem_equivariant : mem_equivariant_statement.
Proof.
  intros r min_name_mode tenv [x | sym]; [ | reflexivity ].
  unfold Typing_env.mem.
  rewrite names_to_types_renamed, lookup_named_renamed.
  destruct
    (Keyed.lookup name_eqb (Name_var x) (Typing_env.names_to_types tenv))
    as [[ty binding_time] | ];
    reflexivity.
Qed.

Theorem mem_simple_equivariant : mem_simple_equivariant_statement.
Proof.
  intros r min_name_mode tenv [x | sym | c]; [ | reflexivity | reflexivity ].
  exact (mem_equivariant r min_name_mode tenv (Name_var x)).
Qed.

Theorem alias_is_bound_strictly_earlier_equivariant :
  alias_is_bound_strictly_earlier_equivariant_statement.
Proof.
  intros r tenv bound_name alias.
  unfold Typing_env.alias_is_bound_strictly_earlier.
  rewrite binding_time_and_mode_equivariant,
    binding_time_and_mode_of_simple_equivariant.
  reflexivity.
Qed.

(* What the functions of the aliases take of the renamed environment is
   what the renaming of FlambdaEnvAliasesRenamingSpec.v makes of what
   they take of the environment, as far as they read it. *)
Lemma resolver_of_renamed (r : renaming) (tenv : Typing_env.t) (n : name) :
  Typing_env.binding_time_resolver (rename_typing_env r tenv) n
  = rename_resolver r (Typing_env.binding_time_resolver tenv) n.
Proof.
  unfold rename_resolver.
  rewrite <- (FlambdaTypeRenameProofs.rename_name_inverse_r r n) at 1.
  apply binding_time_resolver_equivariant.
Qed.

Lemma times_of_renamed (r : renaming) (tenv : Typing_env.t) (n : name) :
  option_map snd
    (Keyed.lookup name_eqb n
       (Typing_env.names_to_types (rename_typing_env r tenv)))
  = option_map snd
      (Keyed.lookup name_eqb n
         (rename_binding_times r (Typing_env.names_to_types tenv))).
Proof.
  rewrite names_to_types_renamed.
  unfold rename_binding_times, Keyed.map_bindings.
  induction (Typing_env.names_to_types tenv) as [ | [n' [ty bt]] bindings IH];
    simpl; [ reflexivity | ].
  destruct n' as [x | sym]; simpl;
    match goal with
    | |- context [name_eqb n ?n'] => destruct (name_eqb n n')
    end;
    first [ reflexivity | exact IH ].
Qed.

Lemma canonical_element_of_renamed (r : renaming) (tenv : Typing_env.t)
    (simple : simple) (elt_name_mode min_name_mode : Name_mode.t) :
  Aliases.get_canonical_element_exn
    (Typing_env.binding_time_resolver (rename_typing_env r tenv))
    (Typing_env.names_to_types (rename_typing_env r tenv))
    (Typing_env.aliases (rename_typing_env r tenv)) (rename_simple r simple)
    elt_name_mode min_name_mode
    (Typing_env.min_binding_time (rename_typing_env r tenv))
  = option_map (rename_simple r)
      (Aliases.get_canonical_element_exn
         (Typing_env.binding_time_resolver tenv)
         (Typing_env.names_to_types tenv) (Typing_env.aliases tenv) simple
         elt_name_mode min_name_mode (Typing_env.min_binding_time tenv)).
Proof.
  rewrite
    (get_canonical_element_exn_alike _
       (rename_resolver r (Typing_env.binding_time_resolver tenv)) _
       (rename_binding_times r (Typing_env.names_to_types tenv))
       (resolver_of_renamed r tenv) (times_of_renamed r tenv)).
  exact
    (rename_canonical_at_mode flambda_type r
       (Typing_env.binding_time_resolver tenv)
       (Typing_env.names_to_types tenv) (Typing_env.aliases tenv) simple
       elt_name_mode min_name_mode (Typing_env.min_binding_time tenv)).
Qed.

Theorem get_canonical_ignoring_name_mode_equivariant :
  get_canonical_ignoring_name_mode_equivariant_statement.
Proof.
  intros r tenv [x | sym | c]; [ | | reflexivity ].
  - exact (rename_canonical r (Typing_env.aliases tenv) (Name_var x)).
  - exact (rename_canonical r (Typing_env.aliases tenv) (Name_symbol sym)).
Qed.

Theorem get_canonical_simple_exn_equivariant :
  get_canonical_simple_exn_equivariant_statement.
Proof.
  intros r tenv min_name_mode name_mode_of_existing_simple simple.
  unfold Typing_env.get_canonical_simple_exn.
  rewrite binding_time_and_mode_of_simple_equivariant.
  destruct
    match name_mode_of_existing_simple with
    | Some name_mode => Some name_mode
    | None =>
      option_map Binding_time.With_name_mode.name_mode
        (Typing_env.binding_time_and_mode_of_simple tenv simple)
    end
    as [name_mode_simple | ];
    [ | reflexivity ].
  cbv beta iota. rewrite canonical_element_of_renamed. reflexivity.
Qed.

Theorem get_alias_then_canonical_simple_exn_equivariant :
  get_alias_then_canonical_simple_exn_equivariant_statement.
Proof.
  intros r tenv min_name_mode name_mode_of_existing_simple typ.
  unfold Typing_env.get_alias_then_canonical_simple_exn.
  rewrite get_alias_opt_renamed.
  destruct (get_alias_opt typ) as [simple | ]; [ | reflexivity ].
  apply get_canonical_simple_exn_equivariant.
Qed.

(* The type that a [Simple] has in a term, before its canonical element
   is asked for. *)
Lemma typed_simple_renamed (r : renaming) (tenv : Typing_env.t)
    (simple : simple) :
  match rename_simple r simple with
  | Const const =>
    Some (type_for_const const, Binding_time.With_name_mode.consts)
  | Var x =>
    Typing_env.find_with_binding_time_and_mode (rename_typing_env r tenv)
      (Name_var x) None
  | Symbol s =>
    Typing_env.find_with_binding_time_and_mode (rename_typing_env r tenv)
      (Name_symbol s) None
  end
  = option_map (rename_binding r)
      match simple with
      | Const const =>
        Some (type_for_const const, Binding_time.With_name_mode.consts)
      | Var x =>
        Typing_env.find_with_binding_time_and_mode tenv (Name_var x) None
      | Symbol s =>
        Typing_env.find_with_binding_time_and_mode tenv (Name_symbol s) None
      end.
Proof.
  destruct simple as [x | sym | c]; cbn [rename_simple].
  - exact
      (find_with_binding_time_and_mode_equivariant r tenv (Name_var x) None).
  - exact
      (find_with_binding_time_and_mode_equivariant r tenv (Name_symbol sym)
         None).
  - open_binding.
    rewrite rename_type_type_for_const. reflexivity.
Qed.

Theorem type_simple_in_term_exn_equivariant :
  type_simple_in_term_exn_equivariant_statement.
Proof.
  intros r tenv min_name_mode simple.
  unfold Typing_env.type_simple_in_term_exn.
  rewrite typed_simple_renamed.
  destruct
    match simple with
    | Const const =>
      Some (type_for_const const, Binding_time.With_name_mode.consts)
    | Var x =>
      Typing_env.find_with_binding_time_and_mode tenv (Name_var x) None
    | Symbol s =>
      Typing_env.find_with_binding_time_and_mode tenv (Name_symbol s) None
    end
    as [[ty binding_time] | ];
    [ | reflexivity ].
  cbv beta iota; open_binding.
  rewrite canonical_element_of_renamed, kind_rename_type.
  destruct
    (Aliases.get_canonical_element_exn _ _ _ simple _ _ _)
    as [alias | ];
    cbn [option_map fst snd]; [ | reflexivity ].
  rewrite rename_type_alias_type_of. reflexivity.
Qed.
