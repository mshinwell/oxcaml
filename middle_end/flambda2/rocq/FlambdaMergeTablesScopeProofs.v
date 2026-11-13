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

(* Proof of the statement of FlambdaMergeTablesScopeSpec.v. Nothing
   here needs review. It follows the proof for the merging of the arms
   of a [Switch] in FlambdaKeepsScopeProofs.v, whose lemmas about the
   [Let]s that bind the variable of the scrutinee again it uses. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaPrimitiveModel FlambdaBindersSpec FlambdaNormaliseSpec
  FlambdaMergeSwitchesSpec FlambdaValidatorEquivarianceSpec
  FlambdaScopedProofs FlambdaKeepsScopeProofs FlambdaMergeTablesSpec
  FlambdaMergeTablesScopeSpec.
Import ListNotations.

(* The [Let]s bind the variable of the scrutinee again, and read it and
   the symbol of the table. *)
Lemma bind_table_load_binds_again (v : variable) (s : symbol)
    (first offset : Z) (immediates : bool) :
  binds_again v (bind_table_load v s first offset immediates).
Proof.
  assert (Hoffset : binds_again v (bind_table_offset v first offset)).
  { intros body. unfold bind_table_offset.
    destruct (first =? 0)%Z; [ exact (binds_again_nothing v body) | ].
    split; [ reflexivity | split; [ | reflexivity ] ].
    scope. simpl.
    intros x [<- | Hx]; [ left; reflexivity | right ].
    apply in_without in Hx. apply Hx. }
  assert
    (Hload :
      binds_again v
        (fun body =>
           Let v Value
             (Prim
                (Binary
                   (Array_load (table_array_kind immediates)
                      (table_load_kind immediates) Immutable))
                [Symbol s; Var v])
             body)).
  { intros body. split; [ reflexivity | split; [ | reflexivity ] ].
    scope. simpl.
    intros x [<- | Hx]; [ left; reflexivity | right ].
    apply in_without in Hx. apply Hx. }
  exact
    (binds_again_twice v _ _ (bind_tagged_binds_again v)
       (binds_again_twice v _ _ Hoffset Hload)).
Qed.

(* The merged arguments are among those of the first arm and the
   variable of the scrutinee. *)
Lemma merged_across_free (v : variable) (arms : list (Z * apply_cont)) :
  ∀ args : list simple,
    incl (free_variables_of_simples (merged_across v args arms))
      (v :: free_variables_of_simples args).
Proof.
  induction arms as [ | arm arms IH]; intros args; cbn [merged_across].
  - apply incl_tl, incl_refl.
  - intros x Hx. apply IH in Hx.
    destruct Hx as [<- | Hx]; [ left; reflexivity | ].
    exact (merged_arguments_free v args _ x Hx).
Qed.

Lemma merge_switch_by_table_scoped (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) (merged : expr) :
  merge_switch_by_table tables scrutinee arms = Some merged ->
  scoped (Switch scrutinee arms) merged.
Proof.
  unfold merge_switch_by_table.
  destruct scrutinee as [v | sym | c]; try discriminate.
  destruct arms as [ | [first ac] [ | arm1 [ | arm2 others]]];
    try discriminate.
  cbv zeta.
  destruct (var_in_simples v _); [ | discriminate ].
  destruct (find _ tables) as [[s elements] | ]; [ | discriminate ].
  intros [= <-] _.
  change
    (merged_across v
       (merged_arguments v
          (merged_arguments v (ac_args ac) (ac_args (snd arm1)))
          (ac_args (snd arm2)))
       others)
    with (merged_across v (ac_args ac) (arm1 :: arm2 :: others)).
  destruct
    (bind_table_load_binds_again v s first (table_offset first)
       (all_immediates elements)
       (Apply_cont
          (Apply_cont_expr (ac_continuation ac)
             (merged_across v (ac_args ac) (arm1 :: arm2 :: others)) None)))
    as (Hclosed & Hv & Hk).
  rewrite Hclosed, Hk. split; [ reflexivity | split ].
  - assert
      (Hswitch :
        ∀ y : variable,
          y = v ∨ In y (free_variables_of_simples (ac_args ac)) ->
          In y
            (free_variables_of_expr
               (Switch (Var v) ((first, ac) :: arm1 :: arm2 :: others)))).
    { intros y [-> | Hy]; scope; simpl;
        [ left; reflexivity | right; apply in_or_app; left; exact Hy ]. }
    intros x Hx. apply Hswitch. apply Hv in Hx.
    destruct Hx as [<- | Hx]; [ left; reflexivity | ].
    scope_in Hx. apply merged_across_free in Hx.
    destruct Hx as [<- | Hx]; [ left; reflexivity | right; exact Hx ].
  - scope. simpl. intros k [<- | []]. left. reflexivity.
Qed.

Lemma merge_switch_with_tables_scoped (tables : known_tables)
    (scrutinee : simple) (arms : list (Z * apply_cont)) :
  scoped (Switch scrutinee arms)
    (merge_switch_with_tables tables scrutinee arms).
Proof.
  unfold merge_switch_with_tables.
  destruct tables as [ | table tables]; [ apply scoped_refl | ].
  destruct (merge_switch_by_table (table :: tables) scrutinee arms)
    as [merged | ] eqn:Hmerged; [ | apply scoped_refl ].
  destruct (merge_switch scrutinee arms); try apply scoped_refl.
  exact
    (merge_switch_by_table_scoped (table :: tables) scrutinee arms merged
       Hmerged).
Qed.

Fixpoint merge_tables_knowing_scoped (e : expr) :
  ∀ tables : known_tables, scoped e (merge_tables_knowing tables e)
with merge_tables_in_handler_scoped (h : continuation_handler) :
  ∀ tables : known_tables,
    scoped_handler h (merge_tables_in_handler tables h).
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros tables; cbn [merge_tables_knowing merge_tables_in_handler].
    + apply scoped_let;
        [ apply incl_refl | apply merge_tables_knowing_scoped ].
    + apply scoped_let_static;
        [ apply scoped_bindings_refl | apply merge_tables_knowing_scoped ].
    + apply scoped_let_cont;
        [ apply merge_tables_in_handler_scoped
        | apply merge_tables_knowing_scoped ].
    + apply scoped_let_cont_recursive;
        [ | | apply merge_tables_knowing_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply merge_tables_in_handler_scoped | exact IH ].
    + apply scoped_refl.
    + apply scoped_refl.
    + apply merge_switch_with_tables_scoped.
    + apply scoped_refl.
  - destruct h as [params metadata handler]. intros tables.
    cbn [merge_tables_knowing merge_tables_in_handler].
    apply scoped_handler_intro, merge_tables_knowing_scoped.
Qed.

(* In the bodies of code it is a rewrite taken there. *)
Fixpoint merge_tables_in_code_scoped (e : expr) :
  ∀ tables : known_tables, scoped e (merge_tables_in_code tables e)
with merge_tables_in_code_in_handler_scoped (h : continuation_handler) :
  ∀ tables : known_tables,
    scoped_handler h (merge_tables_in_code_in_handler tables h).
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros tables;
      cbn [merge_tables_in_code merge_tables_in_code_in_handler];
      cbv zeta.
    + apply scoped_let;
        [ apply incl_refl | apply merge_tables_in_code_scoped ].
    + apply scoped_let_static;
        [ apply rewrite_code_in_bindings_scoped, keeps_scope_intro;
          intros code_body; apply merge_tables_knowing_scoped
        | apply merge_tables_in_code_scoped ].
    + apply scoped_let_cont;
        [ apply merge_tables_in_code_in_handler_scoped
        | apply merge_tables_in_code_scoped ].
    + apply scoped_let_cont_recursive;
        [ | | apply merge_tables_in_code_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply merge_tables_in_code_in_handler_scoped | exact IH ].
    + apply scoped_refl.
    + apply scoped_refl.
    + apply scoped_refl.
    + apply scoped_refl.
  - destruct h as [params metadata handler]. intros tables.
    cbn [merge_tables_in_code merge_tables_in_code_in_handler].
    apply scoped_handler_intro, merge_tables_in_code_scoped.
Qed.

Lemma merge_tables_scoped (e : expr) : scoped e (merge_tables e).
Proof.
  unfold merge_tables.
  eapply scoped_trans;
    [ apply merge_tables_knowing_scoped | apply merge_tables_in_code_scoped ].
Qed.

Theorem merge_tables_keeps_scope : merge_tables_keeps_scope_statement.
Proof. apply keeps_scope_intro, merge_tables_scoped. Qed.
