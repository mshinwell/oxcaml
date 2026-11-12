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


(* Proofs of the statements of FlambdaEnvRenameJoinSpec.v, and the
   functions of the join of environments on renamed arguments. Nothing
   here needs review.

   After the statements: for each function of FlambdaJoinEnv.v, in the
   order of that file, a lemma named after the function says that on
   renamed arguments it gives the renamed answer. A function that is
   given a function (the source of new names, the parameters, the
   function that imports a variable) is given, on the renamed side,
   one that is related to it. *)

From Stdlib Require Import ZArith List Bool PeanoNat.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaNominalSpec FlambdaNominalProofs FlambdaAlphaSpec
  FlambdaAlphaProofs FlambdaNameAbstractionSpec FlambdaNameAbstractionProofs.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeRenameSpec FlambdaTypeRenameProofs FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesRenamingSpec
  FlambdaEnvAliasesRenamingProofs FlambdaTypingEnv FlambdaEnvRenameSpec
  FlambdaEnvRenameProofs FlambdaExpandHead FlambdaJoinEnv FlambdaJoinEnvSpec
  FlambdaJoinMeet FlambdaEnvRenameJoinSpec.
Import ListNotations.

(* ======================================================================== *)
(* Lists and maps                                                           *)
(* ======================================================================== *)

Lemma map_rename_variable_inverse_l (r : renaming) (names : list variable) :
  map (rename_variable (inverse_renaming r)) (map (rename_variable r) names)
  = names.
Proof.
  rewrite map_map. rewrite <- (map_id names) at 2. apply map_ext.
  intros x. apply rename_variable_inverse_l.
Qed.

Lemma map_rename_variable_inverse_r (r : renaming) (names : list variable) :
  map (rename_variable r) (map (rename_variable (inverse_renaming r)) names)
  = names.
Proof.
  rewrite map_map. rewrite <- (map_id names) at 2. apply map_ext.
  intros x. apply rename_variable_inverse_r.
Qed.

(* A map whose keys are kept and whose bindings are renamed: the laws
   of a map whose keys are renamed, at the renaming of keys that moves
   none. *)
Section Kept_keys.

Context {K : Type} (eqb : K -> K -> bool).

Lemma is_bound_map_values {B C : Type} (g : B -> C) (k : K)
    (bindings : Keyed.finite_map K B) :
  Keyed.is_bound eqb k (Keyed.map_values g bindings)
  = Keyed.is_bound eqb k bindings.
Proof.
  exact (is_bound_renamed eqb (fun k => k) (fun _ _ => eq_refl) g k bindings).
Qed.

Lemma domain_map_values {B C : Type} (g : B -> C)
    (bindings : Keyed.finite_map K B) :
  Keyed.domain eqb (Keyed.map_values g bindings) = Keyed.domain eqb bindings.
Proof.
  etransitivity;
    [ exact (domain_renamed eqb (fun k => k) (fun _ _ => eq_refl) g bindings)
    | apply map_id ].
Qed.

Lemma compact_map_values {B C : Type} (g : B -> C)
    (bindings : Keyed.finite_map K B) :
  Keyed.compact eqb (Keyed.map_values g bindings)
  = Keyed.map_values g (Keyed.compact eqb bindings).
Proof.
  exact
    (compact_keys_renamed eqb (fun k => k) (fun _ _ => eq_refl) g bindings).
Qed.

End Kept_keys.

(* [for_all_bindings_b] of a map whose keys are renamed. *)
Section Renamed_keys.

Context {K : Type} (eqb : K -> K -> bool) (f : K -> K).
Hypothesis eqb_renamed : ∀ k k' : K, eqb (f k) (f k') = eqb k k'.

Lemma for_all_bindings_b_renamed {B C : Type} (g : B -> C)
    (p : K -> B -> bool) (p' : K -> C -> bool)
    (bindings : Keyed.finite_map K B) :
  (∀ (k : K) (b : B), p' (f k) (g b) = p k b) ->
  Keyed.for_all_bindings_b eqb p' (Keyed.map_bindings f g bindings)
  = Keyed.for_all_bindings_b eqb p bindings.
Proof.
  intros Hp. unfold Keyed.for_all_bindings_b, Keyed.map_bindings.
  change (@nil K) with (map f (@nil K)) at 1.
  generalize (@nil K) as seen.
  induction bindings as [ | [k b] bindings IH]; intros seen;
    cbn [map fst snd]; [ reflexivity | ].
  rewrite (among_keys_renamed eqb f eqb_renamed), Hp.
  change (f k :: map f seen) with (map f (k :: seen)). rewrite IH.
  reflexivity.
Qed.

End Renamed_keys.

Lemma for_all_bindings_b_map_values {K B C : Type} (eqb : K -> K -> bool)
    (g : B -> C) (p : K -> B -> bool) (p' : K -> C -> bool)
    (bindings : Keyed.finite_map K B) :
  (∀ (k : K) (b : B), p' k (g b) = p k b) ->
  Keyed.for_all_bindings_b eqb p' (Keyed.map_values g bindings)
  = Keyed.for_all_bindings_b eqb p bindings.
Proof.
  intros Hp.
  exact
    (for_all_bindings_b_renamed eqb (fun k => k) (fun _ _ => eq_refl) g p p'
       bindings Hp).
Qed.

(* ======================================================================== *)
(* The source of new names                                                  *)
(* ======================================================================== *)

Theorem no_source_commutes : no_source_commutes_statement.
Proof.
  intros fresh Hrelated.
  specialize
    (Hrelated (Renaming [(fresh [], Pos.succ (fresh []))] []) []).
  cbn [map] in Hrelated.
  unfold rename_variable in Hrelated.
  cbn [variable_permutation permute] in Hrelated. unfold swap in Hrelated.
  rewrite Pos.eqb_refl in Hrelated.
  exact (Pos.succ_discr (fresh []) Hrelated).
Qed.

Theorem rename_fresh_related : rename_fresh_related_statement.
Proof.
  intros r fresh names. unfold rename_fresh.
  rewrite map_rename_variable_inverse_l. reflexivity.
Qed.

Theorem fresh_related_unique : fresh_related_unique_statement.
Proof.
  intros r fresh fresh' Hrelated names. unfold rename_fresh.
  rewrite <- Hrelated, map_rename_variable_inverse_r. reflexivity.
Qed.

Theorem fresh_related_avoids : fresh_related_avoids_statement.
Proof.
  intros r fresh fresh' Hrelated Havoids names Hin.
  rewrite (fresh_related_unique r fresh fresh' Hrelated) in Hin.
  unfold rename_fresh in Hin.
  apply (Havoids (map (rename_variable (inverse_renaming r)) names)).
  apply in_map_iff.
  exists
    (rename_variable r
       (fresh (map (rename_variable (inverse_renaming r)) names))).
  split; [ apply rename_variable_inverse_l | exact Hin ].
Qed.

(* ======================================================================== *)
(* The parameters of the join                                               *)
(* ======================================================================== *)

Theorem join_parameters_related : join_parameters_related_statement.
Proof.
  intros r join_depth. unfold parameters_related.
  cbn [with_fresh join_parameters Join_env.fresh Join_env.type_eqb
       Join_env.env_extension_eqb Join_env.expand_const Join_env.join_depth].
  split; [ apply rename_fresh_related | ].
  split; [ exact (proj1 type_eqb_rename r) | ].
  split; [ exact (proj2 type_eqb_rename r) | ].
  split; [ | reflexivity ].
  intros c. destruct c; try reflexivity.
  match goal with
  | kind : flambda_kind |- _ =>
    destruct kind as [ | k | | ]; try reflexivity; destruct k; reflexivity
  end.
Qed.

Theorem parameters_related_avoids : parameters_related_avoids_statement.
Proof.
  intros r p p' Hrelated Havoids.
  exact
    (fresh_related_avoids r (Join_env.fresh p) (Join_env.fresh p')
       (proj1 Hrelated) Havoids).
Qed.

(* ======================================================================== *)
(* Indices and vectors                                                      *)
(* ======================================================================== *)

(* An index of a joined environment is not a name. A map keyed by
   indices is renamed by what it binds them to. *)

Lemma number_renamed {A B : Type} (g : A -> B) (xs : list A) :
  Index.number (map g xs) = Keyed.map_values g (Index.number xs).
Proof.
  unfold Index.number, Keyed.map_values. rewrite length_map.
  generalize (seq 0 (length xs)) as indices.
  induction xs as [ | x xs IH]; intros [ | index indices];
    cbn [combine map fst snd]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma insert_renamed {A B : Type} (g : A -> B) (binding : Index.t * A)
    (sorted : list (Index.t * A)) :
  Index.insert (fst binding, g (snd binding)) (Keyed.map_values g sorted)
  = Keyed.map_values g (Index.insert binding sorted).
Proof.
  unfold Keyed.map_values.
  induction sorted as [ | binding' sorted IH];
    cbn [Index.insert map fst snd]; [ reflexivity | ].
  destruct (Nat.leb (fst binding) (fst binding')); cbn [map fst snd];
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma bindings_renamed {A B : Type} (g : A -> B)
    (map : Keyed.finite_map Index.t A) :
  Index.bindings (Keyed.map_values g map)
  = Keyed.map_values g (Index.bindings map).
Proof.
  unfold Index.bindings. rewrite compact_map_values.
  induction (Keyed.compact Index.equal map) as [ | binding bindings IH];
    [ reflexivity | ].
  cbn [List.fold_right]. rewrite <- insert_renamed, <- IH. reflexivity.
Qed.

Lemma choose_renamed {A B : Type} (g : A -> B)
    (map : Keyed.finite_map Index.t A) :
  Index.choose (Keyed.map_values g map)
  = option_map (fun binding => (fst binding, g (snd binding)))
      (Index.choose map).
Proof.
  unfold Index.choose. rewrite bindings_renamed.
  destruct (Index.bindings map); reflexivity.
Qed.

Lemma simples_find_renamed (r : renaming) (index : Index.t)
    (simples : Simples_in_joined_envs.t) :
  Simples_in_joined_envs.find index (rename_simples_in_joined_envs r simples)
  = option_map (rename_simple r) (Simples_in_joined_envs.find index simples).
Proof. apply keyed_lookup_map_values. Qed.

Lemma simples_equal_renamed (r : renaming)
    (simples simples' : Simples_in_joined_envs.t) :
  Simples_in_joined_envs.equal (rename_simples_in_joined_envs r simples)
    (rename_simples_in_joined_envs r simples')
  = Simples_in_joined_envs.equal simples simples'.
Proof.
  unfold Simples_in_joined_envs.equal, rename_simples_in_joined_envs.
  f_equal.
  - apply for_all_bindings_b_map_values. intros index simple.
    change (Keyed.map_values (rename_simple r) simples')
      with (rename_simples_in_joined_envs r simples').
    rewrite simples_find_renamed.
    destruct (Simples_in_joined_envs.find index simples') as [simple' | ];
      cbn [option_map]; [ apply simple_equal_renamed | reflexivity ].
  - apply for_all_bindings_b_map_values. intros index simple.
    apply is_bound_map_values.
Qed.

(* ======================================================================== *)
(* The source environment                                                   *)
(* ======================================================================== *)

Lemma exists_in_source_env_renamed (r : renaming) (source_env : Source_env.t)
    (var : variable) :
  Source_env.exists_in_source_env (rename_typing_env r source_env)
    (rename_variable r var)
  = Source_env.exists_in_source_env source_env var.
Proof. exact (mem_equivariant r None source_env (Name_var var)). Qed.

Lemma exists_at_name_mode_renamed (r : renaming) (min_name_mode : Name_mode.t)
    (source_env : Source_env.t) (var : variable) :
  Source_env.exists_at_name_mode min_name_mode (rename_typing_env r source_env)
    (rename_variable r var)
  = Source_env.exists_at_name_mode min_name_mode source_env var.
Proof.
  exact (mem_equivariant r (Some min_name_mode) source_env (Name_var var)).
Qed.

Lemma latest_bound_renamed (r : renaming) (source_env : Source_env.t)
    (var var0 : variable) :
  Source_env.latest_bound (rename_typing_env r source_env)
    (rename_variable r var) (rename_variable r var0)
  = option_map (rename_variable r)
      (Source_env.latest_bound source_env var var0).
Proof.
  unfold Source_env.latest_bound. rewrite rename_variable_eqb.
  destruct (Pos.eqb var var0); [ reflexivity | ].
  change (Name_var (rename_variable r var))
    with (rename_name r (Name_var var)).
  change (Name_var (rename_variable r var0))
    with (rename_name r (Name_var var0)).
  rewrite !binding_time_and_mode_equivariant.
  destruct (Typing_env.binding_time_and_mode source_env (Name_var var))
    as [time | ];
    [ | reflexivity ].
  destruct (Typing_env.binding_time_and_mode source_env (Name_var var0))
    as [time0 | ];
    [ | reflexivity ].
  cbv zeta.
  destruct
    (Binding_time.strictly_earlier
       (Binding_time.With_name_mode.binding_time time)
       (Binding_time.With_name_mode.binding_time time0));
    [ reflexivity | ].
  destruct
    (Binding_time.strictly_earlier
       (Binding_time.With_name_mode.binding_time time0)
       (Binding_time.With_name_mode.binding_time time));
    reflexivity.
Qed.

Lemma source_var_of_renamed (r : renaming) (source_env : Source_env.t)
    (simple : simple) :
  Source_env.source_var_of (rename_typing_env r source_env)
    (rename_simple r simple)
  = option_map (rename_variable r)
      (Source_env.source_var_of source_env simple).
Proof.
  destruct simple as [var | sym | c];
    cbn [Source_env.source_var_of rename_simple]; try reflexivity.
  rewrite exists_in_source_env_renamed.
  destruct (Source_env.exists_in_source_env source_env var); reflexivity.
Qed.

Lemma candidate_step_renamed (r : renaming) (source_env : Source_env.t)
    (possible : Source_env.candidate) (canonical : simple) :
  Source_env.candidate_step (rename_typing_env r source_env)
    (rename_candidate r possible) (rename_simple r canonical)
  = option_map (rename_candidate r)
      (Source_env.candidate_step source_env possible canonical).
Proof.
  unfold Source_env.candidate_step. cbv zeta.
  destruct possible as [ | | shared_simple | var];
    cbn [rename_candidate]; rewrite ?source_var_of_renamed.
  - reflexivity.
  - destruct (Source_env.source_var_of source_env canonical); reflexivity.
  - rewrite simple_equal_renamed.
    destruct (simple_equal canonical shared_simple); [ reflexivity | ].
    destruct (Source_env.source_var_of source_env shared_simple) as [var | ];
      cbn [option_map].
    + destruct (Source_env.source_var_of source_env canonical) as [var0 | ];
        cbn [option_map]; [ | reflexivity ].
      rewrite latest_bound_renamed.
      destruct (Source_env.latest_bound source_env var var0); reflexivity.
    + destruct (Source_env.source_var_of source_env canonical); reflexivity.
  - destruct (Source_env.source_var_of source_env canonical) as [var0 | ];
      cbn [option_map]; [ | reflexivity ].
    rewrite latest_bound_renamed.
    destruct (Source_env.latest_bound source_env var var0); reflexivity.
Qed.

Lemma candidate_canonical_in_source_env_renamed (r : renaming)
    (source_env : Source_env.t) (canonicals : Simples_in_joined_envs.t) :
  Source_env.candidate_canonical_in_source_env (rename_typing_env r source_env)
    (rename_simples_in_joined_envs r canonicals)
  = option_map (rename_candidate r)
      (Source_env.candidate_canonical_in_source_env source_env canonicals).
Proof.
  unfold Source_env.candidate_canonical_in_source_env,
    rename_simples_in_joined_envs.
  rewrite compact_map_values.
  change (Some Source_env.No_simples_in_joined_envs)
    with (option_map (rename_candidate r)
            (Some Source_env.No_simples_in_joined_envs))
    at 1.
  apply
    (fold_left_renamed (option_map (rename_candidate r))
       (fun binding : Index.t * simple =>
          (fst binding, rename_simple r (snd binding)))).
  intros [possible | ] binding; cbn [option_map fst snd]; [ | reflexivity ].
  apply candidate_step_renamed.
Qed.

(* ======================================================================== *)
(* The names of the target environment                                      *)
(* ======================================================================== *)

Lemma is_bound_rename_keys {A : Type} (r : renaming) (var : variable)
    (bindings : finite_map A) :
  is_bound (rename_variable r var) (rename_keys r bindings)
  = is_bound var bindings.
Proof.
  exact
    (is_bound_renamed Pos.eqb (rename_variable r) (rename_variable_eqb r)
       (fun a => a) var bindings).
Qed.

Lemma from_source_env_renamed (r : renaming) (names_to_avoid : list variable)
    (source_env : Source_env.t) :
  Bindings_in_target_env.from_source_env
    (map (rename_variable r) names_to_avoid) (rename_typing_env r source_env)
  = rename_bindings_in_target_env r
      (Bindings_in_target_env.from_source_env names_to_avoid source_env).
Proof. reflexivity. Qed.

Lemma exists_in_target_env_renamed (r : renaming)
    (bindings : Bindings_in_target_env.t) (var : variable) :
  Bindings_in_target_env.exists_in_target_env
    (rename_bindings_in_target_env r bindings) (rename_variable r var)
  = Bindings_in_target_env.exists_in_target_env bindings var.
Proof.
  unfold Bindings_in_target_env.exists_in_target_env.
  cbn [rename_bindings_in_target_env Bindings_in_target_env.source_env
       Bindings_in_target_env.existential_variables
       Bindings_in_target_env.imported_variables].
  rewrite exists_in_source_env_renamed, !is_bound_rename_keys. reflexivity.
Qed.

Lemma has_existential_for_these_simples_renamed (r : renaming)
    (bindings : Bindings_in_target_env.t)
    (simples : Simples_in_joined_envs.t) :
  Bindings_in_target_env.has_existential_for_these_simples
    (rename_bindings_in_target_env r bindings)
    (rename_simples_in_joined_envs r simples)
  = option_map (rename_variable r)
      (Bindings_in_target_env.has_existential_for_these_simples bindings
         simples).
Proof.
  exact
    (lookup_renamed Simples_in_joined_envs.equal
       (rename_simples_in_joined_envs r) (simples_equal_renamed r)
       (rename_variable r) simples
       (Bindings_in_target_env.existential_for_these_simples_map bindings)).
Qed.

Theorem existential_for_these_simples_renamed :
  existential_for_these_simples_renamed_statement.
Proof.
  intros r fresh fresh' bindings simples kind Hrelated.
  unfold Bindings_in_target_env.existential_for_these_simples.
  rewrite has_existential_for_these_simples_renamed.
  destruct
    (Bindings_in_target_env.has_existential_for_these_simples bindings
       simples)
    as [existing | ];
    cbn [option_map fst snd]; [ reflexivity | ].
  cbv zeta.
  change
    (Bindings_in_target_env.names_to_avoid
       (rename_bindings_in_target_env r bindings))
    with (map (rename_variable r)
            (Bindings_in_target_env.names_to_avoid bindings)).
  rewrite Hrelated. reflexivity.
Qed.

Lemma import_from_all_envs_renamed (r : renaming)
    (bindings : Bindings_in_target_env.t) (imported_var : variable)
    (kind : flambda_kind) :
  Bindings_in_target_env.import_from_all_envs
    (rename_bindings_in_target_env r bindings)
    (rename_variable r imported_var) kind
  = rename_bindings_in_target_env r
      (Bindings_in_target_env.import_from_all_envs bindings imported_var kind).
Proof.
  unfold Bindings_in_target_env.import_from_all_envs.
  change
    (Bindings_in_target_env.imported_variables
       (rename_bindings_in_target_env r bindings))
    with (rename_keys r (Bindings_in_target_env.imported_variables bindings)).
  rewrite is_bound_rename_keys.
  destruct
    (is_bound imported_var
       (Bindings_in_target_env.imported_variables bindings));
    reflexivity.
Qed.

Lemma compact_rename_keys {A : Type} (r : renaming) (bindings : finite_map A) :
  compact (rename_keys r bindings) = rename_keys r (compact bindings).
Proof.
  exact
    (compact_keys_renamed Pos.eqb (rename_variable r) (rename_variable_eqb r)
       (fun a => a) bindings).
Qed.

Lemma imported_variables_in_order_renamed (r : renaming)
    (bindings : Bindings_in_target_env.t) :
  Bindings_in_target_env.imported_variables_in_order
    (rename_bindings_in_target_env r bindings)
  = rename_keys r
      (Bindings_in_target_env.imported_variables_in_order bindings).
Proof.
  unfold Bindings_in_target_env.imported_variables_in_order.
  change
    (Bindings_in_target_env.imported_variables
       (rename_bindings_in_target_env r bindings))
    with (rename_keys r (Bindings_in_target_env.imported_variables bindings)).
  rewrite compact_rename_keys. unfold rename_keys, Keyed.map_bindings.
  symmetry. apply map_rev.
Qed.

Lemma existential_variables_in_order_renamed (r : renaming)
    (bindings : Bindings_in_target_env.t) :
  Bindings_in_target_env.existential_variables_in_order
    (rename_bindings_in_target_env r bindings)
  = rename_keys r
      (Bindings_in_target_env.existential_variables_in_order bindings).
Proof.
  unfold Bindings_in_target_env.existential_variables_in_order.
  change
    (Bindings_in_target_env.existential_variables
       (rename_bindings_in_target_env r bindings))
    with (rename_keys r
            (Bindings_in_target_env.existential_variables bindings)).
  rewrite compact_rename_keys. unfold rename_keys, Keyed.map_bindings.
  symmetry. apply map_rev.
Qed.

(* ======================================================================== *)
(* The joined environments                                                  *)
(* ======================================================================== *)

Lemma get_nth_joined_env_renamed (r : renaming) (envs : Joined_envs.t)
    (index : Index.t) :
  Joined_envs.get_nth_joined_env (rename_joined_envs r envs) index
  = option_map (rename_typing_env r)
      (Joined_envs.get_nth_joined_env envs index).
Proof.
  unfold Joined_envs.get_nth_joined_env, rename_joined_envs.
  rewrite keyed_lookup_map_values.
  destruct (Keyed.lookup Index.equal index envs) as [[tenv equations] | ];
    reflexivity.
Qed.

Lemma joined_envs_keys_renamed (r : renaming) (envs : Joined_envs.t) :
  Joined_envs.keys (rename_joined_envs r envs) = Joined_envs.keys envs.
Proof. apply domain_map_values. Qed.

Lemma exists_in_all_joined_envs_renamed {A B : Type} (r : renaming)
    (g : A -> B) (envs : Joined_envs.t) (map : Keyed.finite_map Index.t A) :
  Joined_envs.exists_in_all_joined_envs (rename_joined_envs r envs)
    (Keyed.map_values g map)
  = Joined_envs.exists_in_all_joined_envs envs map.
Proof.
  unfold Joined_envs.exists_in_all_joined_envs.
  rewrite joined_envs_keys_renamed.
  induction (Joined_envs.keys envs) as [ | index keys IH]; cbn [forallb];
    [ reflexivity | rewrite is_bound_map_values, IH; reflexivity ].
Qed.

Lemma equal_in_bindings_renamed (r : renaming) (envs : Joined_envs.t)
    (simple : simple) (bindings : list (Index.t * FlambdaModel.simple)) :
  Joined_envs.equal_in_bindings (rename_joined_envs r envs)
    (rename_simple r simple) (Keyed.map_values (rename_simple r) bindings)
  = Joined_envs.equal_in_bindings envs simple bindings.
Proof.
  induction bindings as [ | [index canonical] bindings IH];
    cbn [Joined_envs.equal_in_bindings Keyed.map_values map fst snd];
    [ reflexivity | ].
  rewrite simple_equal_renamed.
  destruct (simple_equal canonical simple); [ exact IH | ].
  rewrite get_nth_joined_env_renamed.
  destruct (Joined_envs.get_nth_joined_env envs index) as [env | ];
    cbn [option_map]; [ | reflexivity ].
  rewrite get_canonical_ignoring_name_mode_equivariant, simple_equal_renamed.
  destruct
    (simple_equal canonical
       (Typing_env.get_canonical_simple_ignoring_name_mode env simple));
    [ exact IH | reflexivity ].
Qed.

Lemma equal_in_all_joined_envs_renamed (r : renaming) (envs : Joined_envs.t)
    (simple : simple) (simples : Simples_in_joined_envs.t) :
  Joined_envs.equal_in_all_joined_envs (rename_joined_envs r envs)
    (rename_simple r simple) (rename_simples_in_joined_envs r simples)
  = Joined_envs.equal_in_all_joined_envs envs simple simples.
Proof.
  unfold Joined_envs.equal_in_all_joined_envs, rename_simples_in_joined_envs.
  rewrite compact_map_values. apply equal_in_bindings_renamed.
Qed.

Lemma canonicals_of_alias_types_renamed (r : renaming) (envs : Joined_envs.t)
    (types : list (Index.t * flambda_type)) :
  Joined_envs.canonicals_of_alias_types (rename_joined_envs r envs)
    (Keyed.map_values (rename_type r) types)
  = option_map (option_map (rename_simples_in_joined_envs r))
      (Joined_envs.canonicals_of_alias_types envs types).
Proof.
  induction types as [ | [index ty] types IH];
    cbn [Joined_envs.canonicals_of_alias_types Keyed.map_values map fst snd];
    [ reflexivity | ].
  rewrite get_nth_joined_env_renamed.
  destruct (Joined_envs.get_nth_joined_env envs index) as [env | ];
    cbn [option_map]; [ | reflexivity ].
  change (map (fun binding => (fst binding, rename_type r (snd binding))) types)
    with (Keyed.map_values (rename_type r) types).
  rewrite IH.
  destruct (Joined_envs.canonicals_of_alias_types envs types)
    as [canonicals | ];
    cbn [option_map]; [ | reflexivity ].
  rewrite (proj2 (rename_type_alias r)).
  destruct (get_alias_opt ty) as [alias | ], canonicals as [canonicals | ];
    cbn [option_map]; try reflexivity.
  rewrite get_canonical_ignoring_name_mode_equivariant. reflexivity.
Qed.

Lemma get_alias_then_canonical_simple_ignoring_name_mode_exn_renamed
    (r : renaming) (envs : Joined_envs.t)
    (types : Keyed.finite_map Index.t flambda_type) :
  Joined_envs.get_alias_then_canonical_simple_ignoring_name_mode_exn
    (rename_joined_envs r envs) (Keyed.map_values (rename_type r) types)
  = option_map (option_map (rename_simples_in_joined_envs r))
      (Joined_envs.get_alias_then_canonical_simple_ignoring_name_mode_exn
         envs types).
Proof.
  unfold Joined_envs.get_alias_then_canonical_simple_ignoring_name_mode_exn.
  rewrite compact_map_values. apply canonicals_of_alias_types_renamed.
Qed.

(* The type of a constant is given by a function: on the renamed side
   it is to give the renamed type. *)
Lemma types_of_simples_renamed (r : renaming)
    (expand_const expand_const' : const -> flambda_type)
    (envs : Joined_envs.t) (kind : flambda_kind)
    (simples : list (Index.t * simple)) :
  (∀ c : const, expand_const' c = rename_type r (expand_const c)) ->
  Joined_envs.types_of_simples expand_const' (rename_joined_envs r envs) kind
    (Keyed.map_values (rename_simple r) simples)
  = option_map (Keyed.map_values (rename_type r))
      (Joined_envs.types_of_simples expand_const envs kind simples).
Proof.
  intros Hconst.
  induction simples as [ | [index simple] simples IH];
    cbn [Joined_envs.types_of_simples Keyed.map_values map fst snd];
    [ reflexivity | ].
  change
    (map (fun binding => (fst binding, rename_simple r (snd binding))) simples)
    with (Keyed.map_values (rename_simple r) simples).
  rewrite IH.
  destruct simple as [var | sym | c]; cbn [rename_simple].
  - rewrite get_nth_joined_env_renamed.
    destruct (Joined_envs.get_nth_joined_env envs index) as [env | ];
      cbn [option_map]; [ | reflexivity ].
    change (Name_var (rename_variable r var))
      with (rename_name r (Name_var var)).
    rewrite find_equivariant.
    destruct (Typing_env.find env (Name_var var) (Some kind)) as [ty | ];
      cbn [option_map]; [ | reflexivity ].
    destruct (Joined_envs.types_of_simples expand_const envs kind simples);
      reflexivity.
  - rewrite get_nth_joined_env_renamed.
    destruct (Joined_envs.get_nth_joined_env envs index) as [env | ];
      cbn [option_map]; [ | reflexivity ].
    change (Name_symbol sym) with (rename_name r (Name_symbol sym)) at 1.
    rewrite find_equivariant.
    destruct (Typing_env.find env (Name_symbol sym) (Some kind)) as [ty | ];
      cbn [option_map]; [ | reflexivity ].
    destruct (Joined_envs.types_of_simples expand_const envs kind simples);
      reflexivity.
  - rewrite Hconst.
    destruct (Joined_envs.types_of_simples expand_const envs kind simples);
      reflexivity.
Qed.

Lemma find_simples_in_joined_envs_renamed (r : renaming)
    (expand_const expand_const' : const -> flambda_type)
    (envs : Joined_envs.t) (simples : Simples_in_joined_envs.t)
    (kind : flambda_kind) :
  (∀ c : const, expand_const' c = rename_type r (expand_const c)) ->
  Joined_envs.find_simples_in_joined_envs expand_const'
    (rename_joined_envs r envs) (rename_simples_in_joined_envs r simples) kind
  = option_map (Keyed.map_values (rename_type r))
      (Joined_envs.find_simples_in_joined_envs expand_const envs simples
         kind).
Proof.
  intros Hconst.
  unfold Joined_envs.find_simples_in_joined_envs,
    rename_simples_in_joined_envs.
  rewrite compact_map_values. apply types_of_simples_renamed, Hconst.
Qed.

(* A joined environment with the equations of its level, renamed. *)
Local Abbreviation rename_joined r :=
  (fun joined : Typing_env.t * Keyed.finite_map name flambda_type =>
     (rename_typing_env r (fst joined),
      Keyed.map_bindings (rename_name r) (rename_type r) (snd joined))).

Lemma types_of_imported_var_renamed (r : renaming)
    (envs :
       list (Index.t * (Typing_env.t * Keyed.finite_map name flambda_type)))
    (var : variable) (kind : flambda_kind) :
  Joined_envs.types_of_imported_var
    (Keyed.map_values (rename_joined r) envs) (rename_variable r var) kind
  = option_map (Keyed.map_values (rename_type r))
      (Joined_envs.types_of_imported_var envs var kind).
Proof.
  induction envs as [ | [index [env equations]] envs IH];
    cbn [Joined_envs.types_of_imported_var Keyed.map_values map fst snd];
    [ reflexivity | ].
  change
    (map
       (fun binding
            : Index.t
              * (Typing_env.t * Keyed.finite_map name flambda_type) =>
          (fst binding,
           (rename_typing_env r (fst (snd binding)),
            Keyed.map_bindings (rename_name r) (rename_type r)
              (snd (snd binding)))))
       envs)
    with (Keyed.map_values (rename_joined r) envs).
  rewrite IH.
  destruct (Joined_envs.types_of_imported_var envs var kind) as [types | ];
    cbn [option_map]; [ | reflexivity ].
  change (Name_var (rename_variable r var))
    with (rename_name r (Name_var var)).
  rewrite mem_equivariant.
  destruct (Typing_env.mem None env (Name_var var)); [ | reflexivity ].
  rewrite find_equivariant.
  destruct (Typing_env.find env (Name_var var) (Some kind)); reflexivity.
Qed.

Lemma find_imported_var_renamed (r : renaming) (envs : Joined_envs.t)
    (var : variable) (kind : flambda_kind) :
  Joined_envs.find_imported_var (rename_joined_envs r envs)
    (rename_variable r var) kind
  = option_map (Keyed.map_values (rename_type r))
      (Joined_envs.find_imported_var envs var kind).
Proof.
  unfold Joined_envs.find_imported_var, rename_joined_envs.
  rewrite compact_map_values. apply types_of_imported_var_renamed.
Qed.

Lemma kind_of_var_in_renamed (r : renaming)
    (envs :
       list (Index.t * (Typing_env.t * Keyed.finite_map name flambda_type)))
    (var : variable) :
  Joined_envs.kind_of_var_in (Keyed.map_values (rename_joined r) envs)
    (rename_variable r var)
  = Joined_envs.kind_of_var_in envs var.
Proof.
  induction envs as [ | [index [env equations]] envs IH];
    cbn [Joined_envs.kind_of_var_in Keyed.map_values map fst snd];
    [ reflexivity | ].
  change
    (map
       (fun binding
            : Index.t
              * (Typing_env.t * Keyed.finite_map name flambda_type) =>
          (fst binding,
           (rename_typing_env r (fst (snd binding)),
            Keyed.map_bindings (rename_name r) (rename_type r)
              (snd (snd binding)))))
       envs)
    with (Keyed.map_values (rename_joined r) envs).
  rewrite IH.
  change (Name_var (rename_variable r var))
    with (rename_name r (Name_var var)).
  rewrite find_equivariant, mem_equivariant.
  destruct (Typing_env.find env (Name_var var) None) as [ty | ];
    cbn [option_map]; [ | reflexivity ].
  rewrite kind_rename_type. reflexivity.
Qed.

Lemma kind_of_imported_var_renamed (r : renaming) (envs : Joined_envs.t)
    (var : variable) :
  Joined_envs.kind_of_imported_var (rename_joined_envs r envs)
    (rename_variable r var)
  = Joined_envs.kind_of_imported_var envs var.
Proof.
  unfold Joined_envs.kind_of_imported_var, rename_joined_envs.
  rewrite compact_map_values. apply kind_of_var_in_renamed.
Qed.

Lemma get_canonical_simples_ignoring_name_mode_renamed (r : renaming)
    (envs : Joined_envs.t) (simples : list (Index.t * simple)) :
  Joined_envs.get_canonical_simples_ignoring_name_mode
    (rename_joined_envs r envs) (Keyed.map_values (rename_simple r) simples)
  = option_map (rename_simples_in_joined_envs r)
      (Joined_envs.get_canonical_simples_ignoring_name_mode envs simples).
Proof.
  unfold Joined_envs.get_canonical_simples_ignoring_name_mode.
  match goal with
  | |- List.fold_left _ _ ?init = _ =>
    change init with (option_map (rename_simples_in_joined_envs r) init)
      at 1
  end.
  apply
    (fold_left_renamed (option_map (rename_simples_in_joined_envs r))
       (fun binding : Index.t * simple =>
          (fst binding, rename_simple r (snd binding)))).
  intros [acc | ] [index simple]; cbn [option_map fst snd];
    [ | reflexivity ].
  rewrite get_nth_joined_env_renamed.
  destruct (Joined_envs.get_nth_joined_env envs index) as [env | ];
    cbn [option_map]; [ | reflexivity ].
  rewrite get_canonical_ignoring_name_mode_equivariant. reflexivity.
Qed.

(* ======================================================================== *)
(* Maps keyed by variables                                                  *)
(* ======================================================================== *)

Lemma lookup_renamed_keys {A B : Type} (r : renaming) (g : A -> B)
    (var : variable) (bindings : finite_map A) :
  lookup (rename_variable r var)
    (Keyed.map_bindings (rename_variable r) g bindings)
  = option_map g (lookup var bindings).
Proof.
  exact
    (lookup_renamed Pos.eqb (rename_variable r) (rename_variable_eqb r) g var
       bindings).
Qed.

Lemma is_bound_renamed_keys {A B : Type} (r : renaming) (g : A -> B)
    (var : variable) (bindings : finite_map A) :
  is_bound (rename_variable r var)
    (Keyed.map_bindings (rename_variable r) g bindings)
  = is_bound var bindings.
Proof.
  exact
    (is_bound_renamed Pos.eqb (rename_variable r) (rename_variable_eqb r) g
       var bindings).
Qed.

Lemma among_renamed_variables (r : renaming) (var : variable)
    (names : list variable) :
  among (rename_variable r var) (map (rename_variable r) names)
  = among var names.
Proof.
  exact
    (among_keys_renamed Pos.eqb (rename_variable r) (rename_variable_eqb r)
       var names).
Qed.

Lemma filter_bindings_renamed_keys {A B : Type} (r : renaming) (g : A -> B)
    (keep : variable -> A -> bool) (keep' : variable -> B -> bool)
    (bindings : finite_map A) :
  (∀ (var : variable) (a : A), keep' (rename_variable r var) (g a) = keep var a)
  ->
  filter_bindings keep' (Keyed.map_bindings (rename_variable r) g bindings)
  = Keyed.map_bindings (rename_variable r) g (filter_bindings keep bindings).
Proof.
  exact
    (filter_bindings_renamed Pos.eqb (rename_variable r)
       (rename_variable_eqb r) g keep keep' bindings).
Qed.

(* ======================================================================== *)
(* The aliases of the variables made                                        *)
(* ======================================================================== *)

Lemma aliases_of_existential_var_renamed (r : renaming)
    (aliases : Aliases_of_existentials.t) (var : variable) :
  Aliases_of_existentials.aliases_of_existential_var
    (rename_aliases_of_existentials r aliases) (rename_variable r var)
  = map (rename_variable r)
      (Aliases_of_existentials.aliases_of_existential_var aliases var).
Proof.
  unfold Aliases_of_existentials.aliases_of_existential_var,
    rename_aliases_of_existentials.
  rewrite lookup_renamed_keys.
  destruct (lookup var aliases); reflexivity.
Qed.

Lemma aliases_add_renamed (r : renaming) (aliases : Aliases_of_existentials.t)
    (demoted_var existential_var : variable) :
  Aliases_of_existentials.add (rename_aliases_of_existentials r aliases)
    (rename_variable r demoted_var) (rename_variable r existential_var)
  = rename_aliases_of_existentials r
      (Aliases_of_existentials.add aliases demoted_var existential_var).
Proof.
  unfold Aliases_of_existentials.add. cbv zeta.
  rewrite aliases_of_existential_var_renamed, among_renamed_variables.
  destruct
    (among demoted_var
       (Aliases_of_existentials.aliases_of_existential_var aliases
          existential_var));
    reflexivity.
Qed.

(* ======================================================================== *)
(* The state of a join                                                      *)
(* ======================================================================== *)

Lemma join_env_create_renamed (r : renaming) (joined_envs : Joined_envs.t)
    (bindings : Bindings_in_target_env.t) :
  Join_env.create (rename_joined_envs r joined_envs)
    (rename_bindings_in_target_env r bindings)
  = rename_join_env r (Join_env.create joined_envs bindings).
Proof. reflexivity. Qed.

Lemma join_env_source_env_renamed (r : renaming) (env : Join_env.t) :
  Join_env.source_env (rename_join_env r env)
  = rename_typing_env r (Join_env.source_env env).
Proof. reflexivity. Qed.

Lemma new_definitions_of_existentials_renamed (r : renaming)
    (env since : Join_env.t) :
  Join_env.new_definitions_of_existentials (rename_join_env r env)
    (rename_join_env r since)
  = Keyed.map_bindings (rename_variable r)
      (fun definition : Simples_in_joined_envs.t * flambda_kind =>
         (rename_simples_in_joined_envs r (fst definition), snd definition))
      (Join_env.new_definitions_of_existentials env since).
Proof.
  unfold Join_env.new_definitions_of_existentials.
  cbn [rename_join_env Join_env.definitions_of_existentials].
  apply filter_bindings_renamed_keys. intros var definition.
  rewrite is_bound_renamed_keys. reflexivity.
Qed.

Lemma new_equations_in_joined_envs_renamed (r : renaming)
    (env since : Join_env.t) :
  Join_env.new_equations_in_joined_envs (rename_join_env r env)
    (rename_join_env r since)
  = Keyed.map_bindings (rename_variable r) (Keyed.map_values (rename_type r))
      (Join_env.new_equations_in_joined_envs env since).
Proof.
  unfold Join_env.new_equations_in_joined_envs.
  cbn [rename_join_env Join_env.types_in_joined_envs].
  apply filter_bindings_renamed_keys. intros var types.
  rewrite is_bound_renamed_keys. reflexivity.
Qed.

Lemma with_bindings_renamed (r : renaming) (env : Join_env.t)
    (bindings : Bindings_in_target_env.t) :
  Join_env.with_bindings (rename_join_env r env)
    (rename_bindings_in_target_env r bindings)
  = rename_join_env r (Join_env.with_bindings env bindings).
Proof. reflexivity. Qed.

Theorem existential_for_these_canonicals_renamed :
  existential_for_these_canonicals_renamed_statement.
Proof.
  intros r p p' env canonicals kind Hrelated.
  unfold Join_env.existential_for_these_canonicals.
  change (Join_env.bindings (rename_join_env r env))
    with (rename_bindings_in_target_env r (Join_env.bindings env)).
  rewrite
    (existential_for_these_simples_renamed r (Join_env.fresh p)
       (Join_env.fresh p') (Join_env.bindings env) canonicals kind
       (proj1 Hrelated)).
  destruct
    (Bindings_in_target_env.existential_for_these_simples (Join_env.fresh p)
       (Join_env.bindings env) canonicals kind)
    as [existential_var bindings].
  cbn [fst snd rename_join_env Join_env.definitions_of_existentials].
  rewrite is_bound_renamed_keys.
  destruct
    (is_bound existential_var (Join_env.definitions_of_existentials env));
    reflexivity.
Qed.

Lemma add_alias_of_existential_renamed (r : renaming)
    (p p' : Join_env.parameters) (env : Join_env.t) (kind : flambda_kind)
    (var : variable) (canonicals : Simples_in_joined_envs.t) :
  parameters_related r p p' ->
  Join_env.add_alias_of_existential p' (rename_join_env r env) kind
    (rename_variable r var) (rename_simples_in_joined_envs r canonicals)
  = rename_join_env r
      (Join_env.add_alias_of_existential p env kind var canonicals).
Proof.
  intros Hrelated. unfold Join_env.add_alias_of_existential.
  rewrite
    (existential_for_these_canonicals_renamed r p p' env canonicals kind
       Hrelated).
  destruct (Join_env.existential_for_these_canonicals p env canonicals kind)
    as [existential_var env'].
  cbn [fst snd]. unfold rename_join_env at 2.
  cbn [rename_join_env Join_env.joined_envs Join_env.types_in_target_env
       Join_env.types_in_joined_envs Join_env.aliases_of_existentials
       Join_env.imported_vars Join_env.definitions_of_existentials
       Join_env.bindings].
  rewrite aliases_add_renamed. reflexivity.
Qed.

Lemma add_equation_in_target_env_renamed (r : renaming) (env : Join_env.t)
    (var : variable) (ty : flambda_type) :
  Join_env.add_equation_in_target_env (rename_join_env r env)
    (rename_variable r var) (rename_type r ty)
  = option_map (rename_join_env r)
      (Join_env.add_equation_in_target_env env var ty).
Proof.
  unfold Join_env.add_equation_in_target_env.
  cbn [rename_join_env Join_env.types_in_target_env].
  rewrite is_bound_renamed_keys.
  destruct (is_bound var (Join_env.types_in_target_env env)); reflexivity.
Qed.

Lemma add_equations_in_joined_envs_renamed (r : renaming) (env : Join_env.t)
    (var : variable) (types : Keyed.finite_map Index.t flambda_type) :
  Join_env.add_equations_in_joined_envs (rename_join_env r env)
    (rename_variable r var) (Keyed.map_values (rename_type r) types)
  = rename_join_env r (Join_env.add_equations_in_joined_envs env var types).
Proof. reflexivity. Qed.

(* What stands in the target for a vector of canonical [Simple]s,
   renamed. *)
Definition rename_canonical_in_target_env (r : renaming)
    (canonical : Join_env.canonical_in_target_env)
    : Join_env.canonical_in_target_env :=
  match canonical with
  | Join_env.Canonical_in_source_env simple =>
    Join_env.Canonical_in_source_env (rename_simple r simple)
  | Join_env.Import_from_all_joined_envs var =>
    Join_env.Import_from_all_joined_envs (rename_variable r var)
  | Join_env.Existential_for_these_canonicals canonicals =>
    Join_env.Existential_for_these_canonicals
      (rename_simples_in_joined_envs r canonicals)
  end.

Lemma n_way_join_canonical_simples_renamed (r : renaming) (env : Join_env.t)
    (canonicals : Simples_in_joined_envs.t) :
  Join_env.n_way_join_canonical_simples (rename_join_env r env)
    (rename_simples_in_joined_envs r canonicals)
  = option_map (rename_canonical_in_target_env r)
      (Join_env.n_way_join_canonical_simples env canonicals).
Proof.
  unfold Join_env.n_way_join_canonical_simples.
  rewrite join_env_source_env_renamed,
    candidate_canonical_in_source_env_renamed.
  destruct
    (Source_env.candidate_canonical_in_source_env (Join_env.source_env env)
       canonicals)
    as [[ | | simple | var] | ];
    cbn [option_map rename_candidate]; try reflexivity.
  - destruct simple as [var | sym | c]; cbn [rename_simple];
      try reflexivity.
    rewrite exists_in_source_env_renamed.
    destruct (Source_env.exists_in_source_env (Join_env.source_env env) var);
      reflexivity.
  - change (Var (rename_variable r var)) with (rename_simple r (Var var)).
    change (Join_env.joined_envs (rename_join_env r env))
      with (rename_joined_envs r (Join_env.joined_envs env)).
    rewrite equal_in_all_joined_envs_renamed.
    destruct
      (Joined_envs.equal_in_all_joined_envs (Join_env.joined_envs env)
         (Var var) canonicals)
      as [[ | ] | ];
      reflexivity.
Qed.

(* ======================================================================== *)
(* Importing a variable                                                     *)
(* ======================================================================== *)

(* The functions that import a variable are one recursion; each takes
   the function that imports a variable. Two such functions are
   related by a renaming: on the renamed state and the renamed
   variable, the second answers the renamed state of the first. *)
Definition import_var_related (r : renaming)
    (import_var import_var' : Join_env.t -> variable -> option Join_env.t)
    : Prop :=
  ∀ (env : Join_env.t) (var : variable),
    import_var' (rename_join_env r env) (rename_variable r var)
    = option_map (rename_join_env r) (import_var env var).

Lemma import_type_transitive_with_renamed (r : renaming)
    (import_var import_var' : Join_env.t -> variable -> option Join_env.t)
    (env : Join_env.t) (ty : flambda_type) :
  import_var_related r import_var import_var' ->
  Join_env.import_type_transitive_with import_var' (rename_join_env r env)
    (rename_type r ty)
  = option_map (rename_join_env r)
      (Join_env.import_type_transitive_with import_var env ty).
Proof.
  intros Himport. unfold Join_env.import_type_transitive_with.
  rewrite (proj1 free_variables_rename_type).
  change (Some (rename_join_env r env))
    with (option_map (rename_join_env r) (Some env)).
  apply (fold_left_renamed (option_map (rename_join_env r))
           (rename_variable r)).
  intros [env' | ] var; cbn [option_map]; [ apply Himport | reflexivity ].
Qed.

Lemma add_equals_in_joined_envs_with_renamed (r : renaming)
    (p p' : Join_env.parameters)
    (import_var import_var' : Join_env.t -> variable -> option Join_env.t)
    (env : Join_env.t) (kind : flambda_kind) (var : variable)
    (simples : Simples_in_joined_envs.t) :
  parameters_related r p p' ->
  import_var_related r import_var import_var' ->
  Join_env.add_equals_in_joined_envs_with p' import_var'
    (rename_join_env r env) kind (rename_variable r var)
    (rename_simples_in_joined_envs r simples)
  = option_map (rename_join_env r)
      (Join_env.add_equals_in_joined_envs_with p import_var env kind var
         simples).
Proof.
  intros Hp Himport. unfold Join_env.add_equals_in_joined_envs_with.
  rewrite n_way_join_canonical_simples_renamed.
  destruct (Join_env.n_way_join_canonical_simples env simples)
    as [[canonical | imported | canonicals] | ];
    cbn [option_map rename_canonical_in_target_env]; [ | | | reflexivity ].
  - rewrite <- (proj1 (rename_type_alias r)).
    apply add_equation_in_target_env_renamed.
  - rewrite Himport.
    destruct (import_var env imported) as [env' | ]; cbn [option_map];
      [ | reflexivity ].
    change (Var (rename_variable r imported))
      with (rename_simple r (Var imported)).
    rewrite <- (proj1 (rename_type_alias r)).
    apply add_equation_in_target_env_renamed.
  - f_equal. apply add_alias_of_existential_renamed, Hp.
Qed.

Lemma import_or_delay_n_way_join_of_concrete_type_with_renamed (r : renaming)
    (p p' : Join_env.parameters)
    (import_var import_var' : Join_env.t -> variable -> option Join_env.t)
    (env : Join_env.t) (var : variable)
    (types : Keyed.finite_map Index.t flambda_type) :
  parameters_related r p p' ->
  import_var_related r import_var import_var' ->
  Join_env.import_or_delay_n_way_join_of_concrete_type_with p' import_var'
    (rename_join_env r env) (rename_variable r var)
    (Keyed.map_values (rename_type r) types)
  = option_map (rename_join_env r)
      (Join_env.import_or_delay_n_way_join_of_concrete_type_with p import_var
         env var types).
Proof.
  intros Hp Himport.
  unfold Join_env.import_or_delay_n_way_join_of_concrete_type_with.
  rewrite choose_renamed.
  destruct (Index.choose types) as [[index any_ty] | ];
    cbn [option_map fst snd]; [ | reflexivity ].
  rewrite compact_map_values.
  assert (Hall :
    forallb
      (fun binding : Index.t * flambda_type =>
         Index.equal (fst binding) index
         || Join_env.type_eqb p' (rename_type r any_ty) (snd binding))
      (Keyed.map_values (rename_type r) (Keyed.compact Index.equal types))
    = forallb
        (fun binding : Index.t * flambda_type =>
           Index.equal (fst binding) index
           || Join_env.type_eqb p any_ty (snd binding))
        (Keyed.compact Index.equal types)).
  { unfold Keyed.map_values. apply forallb_renamed. intros [index' ty].
    cbn [fst snd]. rewrite (proj1 (proj2 Hp)). reflexivity. }
  rewrite Hall.
  destruct
    (forallb
       (fun binding : Index.t * flambda_type =>
          Index.equal (fst binding) index
          || Join_env.type_eqb p any_ty (snd binding))
       (Keyed.compact Index.equal types));
    [ | reflexivity ].
  rewrite add_equation_in_target_env_renamed.
  destruct (Join_env.add_equation_in_target_env env var any_ty)
    as [env' | ];
    cbn [option_map]; [ | reflexivity ].
  apply import_type_transitive_with_renamed, Himport.
Qed.

Lemma import_or_delay_n_way_join_type_with_renamed (r : renaming)
    (p p' : Join_env.parameters)
    (import_var import_var' : Join_env.t -> variable -> option Join_env.t)
    (env : Join_env.t) (var : variable)
    (types : Keyed.finite_map Index.t flambda_type) :
  parameters_related r p p' ->
  import_var_related r import_var import_var' ->
  Join_env.import_or_delay_n_way_join_type_with p' import_var'
    (rename_join_env r env) (rename_variable r var)
    (Keyed.map_values (rename_type r) types)
  = option_map (rename_join_env r)
      (Join_env.import_or_delay_n_way_join_type_with p import_var env var
         types).
Proof.
  intros Hp Himport. unfold Join_env.import_or_delay_n_way_join_type_with.
  rewrite choose_renamed.
  destruct (Index.choose types) as [[index any_ty] | ];
    cbn [option_map fst snd]; [ | reflexivity ].
  change (Join_env.joined_envs (rename_join_env r env))
    with (rename_joined_envs r (Join_env.joined_envs env)).
  rewrite get_alias_then_canonical_simple_ignoring_name_mode_exn_renamed.
  destruct
    (Joined_envs.get_alias_then_canonical_simple_ignoring_name_mode_exn
       (Join_env.joined_envs env) types)
    as [[canonical_simples | ] | ];
    cbn [option_map]; [ | | reflexivity ].
  - rewrite kind_rename_type.
    apply add_equals_in_joined_envs_with_renamed; assumption.
  - apply import_or_delay_n_way_join_of_concrete_type_with_renamed;
      assumption.
Qed.

(* ======================================================================== *)
(* The choices that the join is handed                                      *)
(* ======================================================================== *)

Lemma stands_for_renamed (r : renaming) (env : Join_env.t) (index : Index.t)
    (var : variable) :
  Join_env.stands_for (rename_join_env r env) index (rename_variable r var)
  = option_map (rename_simple r) (Join_env.stands_for env index var).
Proof.
  unfold Join_env.stands_for.
  cbn [rename_join_env Join_env.definitions_of_existentials].
  rewrite lookup_renamed_keys.
  destruct (lookup var (Join_env.definitions_of_existentials env))
    as [[simples kind] | ];
    cbn [option_map fst snd]; [ apply simples_find_renamed | reflexivity ].
Qed.

Lemma has_alias_in_terms_renamed (r : renaming) (tenv : Typing_env.t)
    (simple : simple) :
  Join_env.has_alias_in_terms (rename_typing_env r tenv)
    (rename_simple r simple)
  = Join_env.has_alias_in_terms tenv simple.
Proof.
  unfold Join_env.has_alias_in_terms.
  rewrite get_canonical_simple_exn_equivariant.
  destruct
    (Typing_env.get_canonical_simple_exn tenv (Some Name_mode.normal) None
       simple)
    as [[canonical | ] | ];
    cbn [option_map]; try reflexivity.
  apply mem_simple_equivariant.
Qed.

Lemma in_terms_in_all_joined_envs_renamed (r : renaming) (env : Join_env.t)
    (var : variable) :
  Join_env.in_terms_in_all_joined_envs (rename_join_env r env)
    (rename_variable r var)
  = Join_env.in_terms_in_all_joined_envs env var.
Proof.
  unfold Join_env.in_terms_in_all_joined_envs.
  change (Join_env.joined_envs (rename_join_env r env))
    with (rename_joined_envs r (Join_env.joined_envs env)).
  rewrite joined_envs_keys_renamed.
  induction (Joined_envs.keys (Join_env.joined_envs env))
    as [ | index keys IH];
    cbn [forallb]; [ reflexivity | ].
  rewrite IH, get_nth_joined_env_renamed, stands_for_renamed.
  destruct
    (Joined_envs.get_nth_joined_env (Join_env.joined_envs env) index)
    as [tenv | ],
    (Join_env.stands_for env index var) as [simple | ];
    cbn [option_map]; try reflexivity.
  rewrite has_alias_in_terms_renamed. reflexivity.
Qed.

Theorem compiler_choices_related : compiler_choices_related_statement.
Proof.
  intros r env var types.
  cbn [Join_env.compiler_choices Join_env.recover_relations_on].
  exact
    (exists_in_all_joined_envs_renamed r (rename_type r)
       (Join_env.joined_envs env) types).
Qed.

Theorem repaired_choices_related : repaired_choices_related_statement.
Proof.
  intros r env var types.
  cbn [Join_env.repaired_choices Join_env.recover_relations_on].
  rewrite in_terms_in_all_joined_envs_renamed.
  f_equal.
  exact
    (exists_in_all_joined_envs_renamed r (rename_type r)
       (Join_env.joined_envs env) types).
Qed.
