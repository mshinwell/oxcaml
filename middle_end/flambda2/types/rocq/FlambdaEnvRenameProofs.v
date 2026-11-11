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
