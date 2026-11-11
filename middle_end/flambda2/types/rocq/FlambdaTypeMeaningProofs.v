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


(* Proofs of the statements of FlambdaTypeMeaningSpec.v, and examples: for
   each constructor of the grammar, a value that has a type built with it
   and a value that has not. Nothing here needs review. *)

From Stdlib Require Import ZArith List Bool Lia Setoid.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaWellFormedSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec.
Import ListNotations.

(* ======================================================================== *)
(* What the meaning reads of a value                                        *)
(* ======================================================================== *)

Theorem observations_disjoint : observations_disjoint_statement.
Proof.
  intros statics v. unfold block_of, boxed_number_of, string_of.
  destruct v as [c | code slots | s]; simpl;
    [ repeat split; congruence | repeat split; congruence | ].
  destruct (lookup s (static_values statics)) as [[ | | [] | ] | ];
    repeat split; congruence.
Qed.

Lemma block_of_kind (statics : static_env) (v : value) (tag : Z)
    (fields : list value) :
  block_of statics v = Some (tag, fields) -> kind_of_value v = Value.
Proof. destruct v; [ discriminate | discriminate | reflexivity ]. Qed.

Lemma boxed_number_of_kind (statics : static_env) (v : value) (c : const) :
  boxed_number_of statics v = Some c -> kind_of_value v = Value.
Proof. destruct v; [ discriminate | discriminate | reflexivity ]. Qed.

Lemma string_of_kind (statics : static_env) (v : value) (bytes : list Z) :
  string_of statics v = Some bytes -> kind_of_value v = Value.
Proof. destruct v; [ discriminate | discriminate | reflexivity ]. Qed.

Lemma closure_of_kind (statics : static_env) (v : value)
    (closure : code_id * list (value_slot * value)) :
  closure_of statics v = Some closure -> kind_of_value v = Value.
Proof. destruct v; [ discriminate | reflexivity | reflexivity ]. Qed.

Lemma closure_in_set_kind (statics : static_env) (v : value)
    (closure :
      function_slot * list (function_slot * code_id)
      * list (value_slot * value)) :
  closure_in_set statics v = Some closure -> kind_of_value v = Value.
Proof.
  unfold closure_in_set.
  destruct (closure_of statics v) as [[code slots] | ] eqn:Hclosure;
    [ | discriminate ].
  intros _. exact (closure_of_kind _ _ _ Hclosure).
Qed.

(* ======================================================================== *)
(* Going through lists and maps                                             *)
(* ======================================================================== *)

Lemma every_iff {A : Type} (P : A -> Prop) (l : list A) :
  every P l <-> (∀ a : A, a ∈ l -> P a).
Proof.
  induction l as [ | a l IH]; simpl.
  - split; [ intros _ a [] | auto ].
  - rewrite IH. split.
    + intros [Ha Hl] a' [<- | Hin]; [ exact Ha | exact (Hl a' Hin) ].
    + intros Hall. split; [ apply Hall; left; reflexivity | ].
      intros a' Hin. apply Hall. right. exact Hin.
Qed.

Lemma for_all_bindings_iff {A : Type} (P : positive -> A -> Prop)
    (m : finite_map A) :
  for_all_bindings P m
  <-> (∀ (name : positive) (a : A), lookup name m = Some a -> P name a).
Proof.
  unfold for_all_bindings. rewrite every_iff. split.
  - intros Hall name a Hlookup.
    exact (Hall (name, a) (lookup_in _ _ _ Hlookup) Hlookup).
  - intros Hall [name a] _ Hlookup. exact (Hall name a Hlookup).
Qed.

Lemma at_binding_iff {A : Type} (P : A -> Prop) (name : positive)
    (m : finite_map A) :
  at_binding P name m <-> (∀ a : A, lookup name m = Some a -> P a).
Proof.
  unfold at_binding. rewrite every_iff. split.
  - intros Hall a Hlookup.
    exact (Hall (name, a) (lookup_in _ _ _ Hlookup) Hlookup).
  - intros Hall [name' a] _ Hlookup. exact (Hall a Hlookup).
Qed.

Lemma find_tag_in {A : Type} (tag : Z) (a : A) (cases : list (Z * A)) :
  find_tag tag cases = Some a -> (tag, a) ∈ cases.
Proof.
  induction cases as [ | [tag' a'] cases IH]; simpl; [ discriminate | ].
  destruct (Z.eqb_spec tag tag') as [-> | _].
  - intros [= ->]. left. reflexivity.
  - intros Hfind. right. exact (IH Hfind).
Qed.

Lemma at_tag_iff {A : Type} (P : A -> Prop) (tag : Z) (cases : list (Z * A)) :
  at_tag P tag cases <-> (∀ a : A, find_tag tag cases = Some a -> P a).
Proof.
  unfold at_tag. rewrite every_iff. split.
  - intros Hall a Hfind.
    exact (Hall (tag, a) (find_tag_in _ _ _ Hfind) Hfind).
  - intros Hall [tag' a] _ Hfind. exact (Hall a Hfind).
Qed.

Lemma for_all_names_iff {A : Type} (P : name -> A -> Prop)
    (m : finite_name_map A) :
  for_all_names P m
  <-> (∀ (n : name) (a : A), lookup_name n m = Some a -> P n a).
Proof.
  unfold for_all_names. rewrite !for_all_bindings_iff. split.
  - intros [Hvars Hsymbols] [x | s] a Hlookup;
      [ exact (Hvars x a Hlookup) | exact (Hsymbols s a Hlookup) ].
  - intros Hall. split.
    + intros x a Hlookup. exact (Hall (Name_var x) a Hlookup).
    + intros s a Hlookup. exact (Hall (Name_symbol s) a Hlookup).
Qed.

Theorem every_in : every_in_statement.
Proof. exact @every_iff. Qed.

Theorem for_all_bindings_lookup : for_all_bindings_lookup_statement.
Proof. exact @for_all_bindings_iff. Qed.

Theorem at_binding_lookup : at_binding_lookup_statement.
Proof. exact @at_binding_iff. Qed.

Theorem at_tag_find : at_tag_find_statement.
Proof. exact @at_tag_iff. Qed.

Theorem for_all_names_lookup : for_all_names_lookup_statement.
Proof. exact @for_all_names_iff. Qed.

(* ======================================================================== *)
(* One equation for each constructor                                        *)
(* ======================================================================== *)

(* What [type_satisfied] and the functions defined with it come to on each
   constructor. They hold by definition; they are stated so that a proof
   can rewrite with them and never unfold the definition, whose functions
   are defined together and print badly when unfolded. The hint database
   [type_satisfied] has them all. The equations for the row-like
   structures, the entries of closures and the environment extensions are
   further down, by [lookup]: [row_like_for_blocks_find_iff],
   [row_like_for_closures_lookup_iff], [closures_entry_lookup_iff] and
   [env_extension_lookup_iff]. *)

Lemma type_satisfied_value (statics : static_env) (vars : env) (v : value)
    (ty : type_descr head_of_kind_value) :
  type_satisfied statics vars v (Type_value ty)
  = descr_satisfied vars Value (head_of_kind_value_satisfied statics vars v)
      v ty.
Proof. reflexivity. Qed.

Lemma type_satisfied_naked_immediate (statics : static_env) (vars : env)
    (v : value) (ty : type_descr head_of_kind_naked_immediate) :
  type_satisfied statics vars v (Type_naked_immediate ty)
  = descr_satisfied vars (Naked_number Kind_naked_immediate)
      (head_of_kind_naked_immediate_satisfied statics vars v) v ty.
Proof. reflexivity. Qed.

Lemma type_satisfied_naked_number (statics : static_env) (vars : env)
    (v : value) (k : naked_number_kind) (ty : type_descr (list Z)) :
  type_satisfied statics vars v (Type_naked_number k ty)
  = descr_satisfied vars (Naked_number k) (naked_numbers_satisfied k v) v ty.
Proof. reflexivity. Qed.

Lemma type_satisfied_rec_info (statics : static_env) (vars : env) (v : value)
    (ty : type_descr unit) :
  type_satisfied statics vars v (Type_rec_info ty)
  = descr_satisfied vars Rec_info (fun _ => kind_of_value v = Rec_info) v ty.
Proof. reflexivity. Qed.

Lemma type_satisfied_region (statics : static_env) (vars : env) (v : value)
    (ty : type_descr unit) :
  type_satisfied statics vars v (Type_region ty)
  = descr_satisfied vars Region (fun _ => kind_of_value v = Region) v ty.
Proof. reflexivity. Qed.

Lemma head_of_kind_value_satisfied_eq (statics : static_env) (vars : env)
    (v : value) (non_null : or_unknown_or_bottom head_of_kind_value_non_null)
    (is_null : is_null) :
  head_of_kind_value_satisfied statics vars v
    (Head_of_kind_value non_null is_null)
  = ((v = Value_const Null
      ∧ match is_null with
        | Not_null => False
        | Maybe_null is_null => variable_is vars is_null 1
        end)
     ∨ (v <> Value_const Null
        ∧ match non_null with
          | Unknown => kind_of_value v = Value
          | Bottom => False
          | Ok head =>
            head_of_kind_value_non_null_satisfied statics vars v head
          end
        ∧ match is_null with
          | Not_null => True
          | Maybe_null is_null => variable_is vars is_null 0
          end)).
Proof. reflexivity. Qed.

Lemma variant_satisfied (statics : static_env) (vars : env) (v : value)
    (is_int : option variable) (immediates : Or_unknown.t flambda_type)
    (get_tag : option variable) (blocks : Or_unknown.t row_like_for_blocks)
    (extensions : variant_extensions) (is_unique : bool) :
  head_of_kind_value_non_null_satisfied statics vars v
    (Variant is_int immediates get_tag blocks extensions is_unique)
  = ((∃ i : Z,
       v = Value_const (Tagged_immediate i)
       ∧ variable_is vars is_int 1
       ∧ match immediates with
         | Or_unknown.Unknown => True
         | Or_unknown.Known ty =>
           type_satisfied statics vars (Value_const (Naked_immediate i)) ty
         end
       ∧ match extensions with
         | No_extensions => True
         | Ext when_immediate _ =>
           env_extension_satisfied statics vars when_immediate
         end)
     ∨ (∃ (tag : Z) (fields : list value),
         block_of statics v = Some (tag, fields)
         ∧ variable_is vars is_int 0
         ∧ variable_is vars get_tag tag
         ∧ match blocks with
           | Or_unknown.Unknown => True
           | Or_unknown.Known blocks =>
             row_like_for_blocks_satisfied statics vars tag fields blocks
           end
         ∧ match extensions with
           | No_extensions => True
           | Ext _ when_block =>
             env_extension_satisfied statics vars when_block
           end)).
Proof. reflexivity. Qed.

Lemma mutable_block_head_satisfied (statics : static_env) (vars : env)
    (v : value) (alloc_mode : Alloc_mode.t) :
  head_of_kind_value_non_null_satisfied statics vars v
    (Mutable_block alloc_mode)
  = False.
Proof. reflexivity. Qed.

Lemma boxed_number_satisfied (statics : static_env) (vars : env) (v : value)
    (k : naked_number_kind) (contents : flambda_type)
    (alloc_mode : Alloc_mode.t) :
  head_of_kind_value_non_null_satisfied statics vars v
    (Boxed_number k contents alloc_mode)
  = (∃ c : const,
      boxed_number_of statics v = Some c
      ∧ kind_of_const c = Naked_number k
      ∧ type_satisfied statics vars (Value_const c) contents).
Proof. reflexivity. Qed.

Lemma closures_satisfied (statics : static_env) (vars : env) (v : value)
    (by_function_slot : row_like_for_closures) (alloc_mode : Alloc_mode.t) :
  head_of_kind_value_non_null_satisfied statics vars v
    (Closures by_function_slot alloc_mode)
  = (∃ (slot : function_slot) (functions : list (function_slot * code_id))
       (value_slots : list (value_slot * value)),
      closure_in_set statics v = Some (slot, functions, value_slots)
      ∧ row_like_for_closures_satisfied statics vars v slot functions
          value_slots by_function_slot).
Proof. reflexivity. Qed.

Lemma string_satisfied (statics : static_env) (vars : env) (v : value)
    (strs : list (list Z)) :
  head_of_kind_value_non_null_satisfied statics vars v (String strs)
  = (∃ bytes : list Z, string_of statics v = Some bytes ∧ bytes ∈ strs).
Proof. reflexivity. Qed.

Create Rewrite HintDb type_satisfied.
#[global] Hint Rewrite type_satisfied_value type_satisfied_naked_immediate
  type_satisfied_naked_number type_satisfied_rec_info type_satisfied_region
  head_of_kind_value_satisfied_eq variant_satisfied
  mutable_block_head_satisfied boxed_number_satisfied closures_satisfied
  string_satisfied : type_satisfied.

(* ======================================================================== *)
(* What every kind has: unknown, bottom, aliases                            *)
(* ======================================================================== *)

Theorem unknown_satisfied : unknown_satisfied_statement.
Proof. intros statics vars v k. destruct k as [ | [] | | ]; reflexivity. Qed.

Theorem bottom_satisfied : bottom_satisfied_statement.
Proof.
  intros statics vars v k. destruct k as [ | [] | | ]; intros [].
Qed.

Theorem alias_satisfied : alias_satisfied_statement.
Proof. intros statics vars v k s. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma get_alias_descr {head : Type} (vars : env) (k : flambda_kind)
    (head_satisfied : head -> Prop) (v : value) (ty : type_descr head)
    (s : simple) :
  match ty with
  | Ok (Equals s) => Some s
  | Unknown | Bottom | Ok (No_alias _) => None
  end = Some s ->
  (descr_satisfied vars k head_satisfied v ty
   <-> eval_simple vars s = Some v ∧ kind_of_value v = k).
Proof.
  destruct ty as [ | [h | s'] | ]; try discriminate.
  intros [= ->]. reflexivity.
Qed.

Theorem get_alias_satisfied : get_alias_satisfied_statement.
Proof.
  intros statics vars v t s. destruct t; simpl; apply get_alias_descr.
Qed.

Theorem this_const_satisfied : this_const_satisfied_statement.
Proof.
  intros statics vars v c. unfold this_const.
  rewrite (alias_satisfied statics vars v).
  simpl. split.
  - intros [[= <-] _]. reflexivity.
  - intros ->. split; reflexivity.
Qed.

(* ======================================================================== *)
(* Null, immediates and blocks                                              *)
(* ======================================================================== *)

Theorem null_satisfied : null_satisfied_statement.
Proof.
  intros statics vars v. simpl. split.
  - intros [[Hnull _] | [_ [[] _]]]. exact Hnull.
  - intros ->. left. split; [ reflexivity | exact I ].
Qed.

Theorem any_non_null_value_satisfied : any_non_null_value_satisfied_statement.
Proof.
  intros statics vars v. simpl. split.
  - intros [[_ []] | [Hnot_null [Hkind _]]]. split; assumption.
  - intros [Hkind Hnot_null]. right. repeat split; assumption.
Qed.

Theorem type_for_const_satisfied : type_for_const_satisfied_statement.
Proof.
  intros statics vars c.
  destruct c; try (apply this_const_satisfied; reflexivity).
  - apply null_satisfied. reflexivity.
  - apply unknown_satisfied. reflexivity.
Qed.

(* A non-null head alone: the value is not [Null] for free, as no head
   admits [Null]. *)
Lemma head_non_null_kind (statics : static_env) (vars : env) (v : value)
    (head : head_of_kind_value_non_null) :
  head_of_kind_value_non_null_satisfied statics vars v head ->
  kind_of_value v = Value ∧ v <> Value_const Null.
Proof.
  destruct head as [is_int immediates get_tag blocks extensions is_unique
                   | alloc_mode | k contents alloc_mode
                   | by_function_slot alloc_mode | strs]; simpl.
  - intros [[i [-> _]] | [tag [fields [Hblock _]]]];
      [ split; [ reflexivity | discriminate ] | ].
    split; [ exact (block_of_kind _ _ _ _ Hblock) | ].
    intros ->. discriminate.
  - intros [].
  - intros [c [Hboxed _]].
    split; [ exact (boxed_number_of_kind _ _ _ Hboxed) | ].
    intros ->. discriminate.
  - intros [slot [functions [value_slots [Hclosure _]]]].
    split; [ exact (closure_in_set_kind _ _ _ Hclosure) | ].
    intros ->. discriminate.
  - intros [bytes [Hstring _]].
    split; [ exact (string_of_kind _ _ _ Hstring) | ].
    intros ->. discriminate.
Qed.

Lemma non_null_value_satisfied (statics : static_env) (vars : env) (v : value)
    (head : head_of_kind_value_non_null) :
  type_satisfied statics vars v (non_null_value head)
  <-> head_of_kind_value_non_null_satisfied statics vars v head.
Proof.
  simpl. split.
  - intros [[_ []] | [_ [Hhead _]]]. exact Hhead.
  - intros Hhead. right.
    split; [ exact (proj2 (head_non_null_kind _ _ _ _ Hhead)) | ].
    split; [ exact Hhead | exact I ].
Qed.

Theorem type_satisfied_kind : type_satisfied_kind_statement.
Proof.
  intros statics vars v t.
  assert (Hdescr :
    ∀ (head : Type) (k : flambda_kind) (head_satisfied : head -> Prop)
      (ty : type_descr head),
      (∀ h : head, head_satisfied h -> kind_of_value v = k) ->
      descr_satisfied vars k head_satisfied v ty -> kind_of_value v = k).
  { intros head k head_satisfied [ | [h | s] | ] Hhead; simpl;
      [ auto | apply Hhead | intros [_ Hkind]; exact Hkind | intros [] ]. }
  destruct t as [ty | ty | k ty | ty | ty]; simpl; apply Hdescr.
  - intros [non_null is_null]. simpl.
    intros [[-> _] | [_ [Hnon_null _]]]; [ reflexivity | ].
    destruct non_null as [ | head | ];
      [ exact Hnon_null | | destruct Hnon_null ].
    exact (proj1 (head_non_null_kind _ _ _ _ Hnon_null)).
  - intros head [i [-> _]]. reflexivity.
  - intros numbers [c [n [-> [Hkind _]]]]. exact Hkind.
  - auto.
  - auto.
Qed.

Theorem create_variant_satisfied : create_variant_satisfied_statement.
Proof.
  intros statics vars v is_unique immediates blocks extensions.
  unfold create_variant. rewrite non_null_value_satisfied. simpl.
  split.
  - intros [[i [Hv [_ Himmediate]]] | [tag [fields [Hblock [_ [_ Hblock']]]]]].
    + left. exists i. split; assumption.
    + right. exists tag, fields. split; assumption.
  - intros [[i [Hv Himmediate]] | [tag [fields [Hblock Hblock']]]].
    + left. exists i. repeat split; tauto.
    + right. exists tag, fields. repeat split; tauto.
Qed.

Lemma row_like_for_blocks_bottom_satisfied (statics : static_env) (vars : env)
    (tag : Z) (fields : list value) :
  ~ row_like_for_blocks_satisfied statics vars tag fields
      row_like_for_blocks_bottom.
Proof. simpl. intros [_ Hother]. exact (Hother eq_refl). Qed.

Theorem any_tagged_immediate_satisfied
  : any_tagged_immediate_satisfied_statement.
Proof.
  intros statics vars v. unfold any_tagged_immediate.
  rewrite (create_variant_satisfied statics vars v). split.
  - intros [[i [Hv _]] | [tag [fields [_ [Hblocks _]]]]].
    + exists i. exact Hv.
    + destruct (row_like_for_blocks_bottom_satisfied _ _ _ _ Hblocks).
  - intros [i Hv]. left. exists i. repeat split. exact Hv.
Qed.

Theorem tag_immediate_satisfied : tag_immediate_satisfied_statement.
Proof.
  intros statics vars v t. unfold tag_immediate.
  rewrite (create_variant_satisfied statics vars v). split.
  - intros [[i [Hv [Ht _]]] | [tag [fields [_ [Hblocks _]]]]].
    + exists i. split; assumption.
    + destruct (row_like_for_blocks_bottom_satisfied _ _ _ _ Hblocks).
  - intros [i [Hv Ht]]. left. exists i. repeat split; assumption.
Qed.

Theorem any_block_satisfied : any_block_satisfied_statement.
Proof.
  intros statics vars v. unfold any_block.
  rewrite (create_variant_satisfied statics vars v). split.
  - intros [[i [_ [Hbottom _]]] | [tag [fields [Hblock _]]]].
    + destruct (bottom_satisfied _ _ _ _ Hbottom).
    + exists tag, fields. exact Hblock.
  - intros [tag [fields Hblock]]. right. exists tag, fields.
    repeat split. exact Hblock.
Qed.

Theorem mutable_block_satisfied : mutable_block_satisfied_statement.
Proof.
  intros statics vars v alloc_mode. unfold mutable_block.
  rewrite non_null_value_satisfied. simpl. auto.
Qed.

(* ======================================================================== *)
(* Numbers                                                                  *)
(* ======================================================================== *)

Theorem these_naked_immediates_satisfied
  : these_naked_immediates_satisfied_statement.
Proof.
  intros statics vars v imms.
  assert (Hhead :
    type_satisfied statics vars v
      (Type_naked_immediate
         (Ok
            (No_alias
               (Head_of_kind_naked_immediate (Or_unknown.Known imms) []))))
    <-> ∃ i : Z, v = Value_const (Naked_immediate i) ∧ i ∈ imms).
  { simpl. unfold head_of_kind_naked_immediate_satisfied. simpl. split.
    - intros [i [Hv [Hin _]]]. exists i. split; assumption.
    - intros [i [Hv Hin]]. exists i. repeat split; [ assumption .. | ].
      intros relation n []. }
  destruct imms as [ | i [ | i' imms]]; [ | | exact Hhead ].
  - split; [ intros Hbottom | intros [i [_ []]] ].
    destruct (bottom_satisfied _ _ _ _ Hbottom).
  - unfold these_naked_immediates, this_naked_immediate.
    rewrite (this_const_satisfied statics vars v). split.
    + intros ->. exists i. split; [ reflexivity | left; reflexivity ].
    + intros [i' [-> [<- | []]]]. reflexivity.
Qed.

Theorem type_naked_number_satisfied : type_naked_number_satisfied_statement.
Proof. intros statics vars v k numbers. reflexivity. Qed.

(* The type of the result of a relation on the value of a name, where the
   numbers known include every result the relation can have. *)
Lemma relation_type_satisfied (statics : static_env) (vars : env) (v : value)
    (relation : Relation.t) (scrutinee : name)
    (numbers : Or_unknown.t (list Z)) :
  (∀ (w : value) (i : Z),
    relation_holds statics relation w i ->
    match numbers with
    | Or_unknown.Unknown => True
    | Or_unknown.Known numbers => i ∈ numbers
    end) ->
  type_satisfied statics vars v
    (Type_naked_immediate
       (Ok
          (No_alias
             (Head_of_kind_naked_immediate numbers [(relation, scrutinee)]))))
  <-> ∃ (i : Z) (w : value),
        v = Value_const (Naked_immediate i)
        ∧ value_of_name vars scrutinee = Some w
        ∧ relation_holds statics relation w i.
Proof.
  intros Hnumbers. simpl. unfold head_of_kind_naked_immediate_satisfied.
  simpl. split.
  - intros [i [Hv [_ Hrelations]]].
    destruct (Hrelations relation scrutinee (or_introl eq_refl))
      as [w [Hw Hholds]].
    exists i, w. repeat split; assumption.
  - intros [i [w [Hv [Hw Hholds]]]]. exists i.
    split; [ exact Hv | ]. split; [ exact (Hnumbers w i Hholds) | ].
    intros relation' n [[= <- <-] | []]. exists w. split; assumption.
Qed.

Theorem is_int_for_scrutinee_satisfied
  : is_int_for_scrutinee_satisfied_statement.
Proof.
  intros statics vars v scrutinee. apply relation_type_satisfied.
  intros w i [[_ ->] | [_ ->]]; simpl; auto.
Qed.

Theorem get_tag_for_block_satisfied : get_tag_for_block_satisfied_statement.
Proof.
  intros statics vars v block. apply relation_type_satisfied.
  intros w i _. exact I.
Qed.

Theorem is_null_for_scrutinee_satisfied
  : is_null_for_scrutinee_satisfied_statement.
Proof.
  intros statics vars v scrutinee. apply relation_type_satisfied.
  intros w i [[_ ->] | [_ ->]]; simpl; auto.
Qed.

Theorem these_tagged_immediates_satisfied
  : these_tagged_immediates_satisfied_statement.
Proof.
  intros statics vars v imms.
  destruct imms as [ | i [ | i' imms]].
  - split; [ intros Hbottom | intros [i [_ []]] ].
    destruct (bottom_satisfied _ _ _ _ Hbottom).
  - unfold these_tagged_immediates, this_tagged_immediate.
    rewrite (this_const_satisfied statics vars v). split.
    + intros ->. exists i. split; [ reflexivity | left; reflexivity ].
    + intros [i' [-> [<- | []]]]. reflexivity.
  - unfold these_tagged_immediates.
    rewrite (tag_immediate_satisfied statics vars v). split.
    + intros [n [Hv Hn]]. exists n. split; [ exact Hv | ].
      apply (these_naked_immediates_satisfied statics vars) in Hn
        as [n' [[= <-] Hin]].
      exact Hin.
    + intros [n [Hv Hin]]. exists n. split; [ exact Hv | ].
      apply (these_naked_immediates_satisfied statics vars). exists n.
      split; [ reflexivity | exact Hin ].
Qed.

(* ======================================================================== *)
(* Blocks                                                                   *)
(* ======================================================================== *)

Lemma fields_satisfied_nth_iff (P : value -> flambda_type -> Prop)
    (tys : list flambda_type) (fields : list value) :
  fields_satisfied P tys fields
  <-> (∀ (i : nat) (ty : flambda_type) (field : value),
        nth_error tys i = Some ty ->
        nth_error fields i = Some field ->
        P field ty).
Proof.
  revert fields. induction tys as [ | ty tys IH]; intros fields.
  - simpl. split; [ | auto ]. intros _ [ | i] ty field; discriminate.
  - destruct fields as [ | field fields]; simpl.
    + split; [ | auto ]. intros _ [ | i] ty' field; discriminate.
    + rewrite IH. split.
      * intros [Hfield Hfields] [ | i] ty' field'; simpl.
        -- intros [= <-] [= <-]. exact Hfield.
        -- apply Hfields.
      * intros Hall. split; [ exact (Hall 0 ty field eq_refl eq_refl) | ].
        intros i ty' field'. exact (Hall (S i) ty' field').
Qed.

Theorem fields_satisfied_nth : fields_satisfied_nth_statement.
Proof. exact fields_satisfied_nth_iff. Qed.

(* With as many fields as types, position by position is [Forall2]. *)
Lemma fields_satisfied_Forall2 (P : value -> flambda_type -> Prop)
    (tys : list flambda_type) (fields : list value) :
  length fields = length tys ->
  (fields_satisfied P tys fields <-> Forall2 P fields tys).
Proof.
  revert fields. induction tys as [ | ty tys IH]; intros [ | field fields];
    simpl; try discriminate.
  - intros _. split; [ constructor | auto ].
  - intros [= Hlength]. rewrite (IH fields Hlength). split.
    + intros [Hfield Hfields]. constructor; assumption.
    + intros Hall. inversion Hall; subst. split; assumption.
Qed.

(* The case of a tag, or failing one something else. *)
Lemma at_tag_or_else {A : Type} (P : A -> Prop) (Q : Prop) (tag : Z)
    (cases : list (Z * A)) :
  at_tag P tag cases ∧ (find_tag tag cases = None -> Q)
  <-> match find_tag tag cases with
      | Some a => P a
      | None => Q
      end.
Proof.
  rewrite at_tag_iff. destruct (find_tag tag cases) as [a | ]; split.
  - intros [Hcase _]. exact (Hcase a eq_refl).
  - intros Hcase. split; [ | discriminate ]. intros a' [= <-]. exact Hcase.
  - intros [_ Hother]. exact (Hother eq_refl).
  - intros Hother. split; [ discriminate | ]. intros _. exact Hother.
Qed.

Lemma row_like_for_blocks_find_iff (statics : static_env) (vars : env)
    (tag : Z) (fields : list value)
    (known_tags : list (Z * Or_unknown.t row_like_block_case))
    (other_tags : Or_bottom.t row_like_block_case)
    (alloc_mode : Alloc_mode.t) :
  row_like_for_blocks_satisfied statics vars tag fields
    (Row_like_for_blocks known_tags other_tags alloc_mode)
  <-> match find_tag tag known_tags with
      | Some (Or_unknown.Known case) =>
        row_like_block_case_satisfied statics vars tag fields case
      | Some Or_unknown.Unknown => True
      | None =>
        match other_tags with
        | Or_bottom.Ok case =>
          row_like_block_case_satisfied statics vars tag fields case
        | Or_bottom.Bottom => False
        end
      end.
Proof.
  simpl. rewrite at_tag_or_else. unfold row_like_block_case in *.
  destruct (find_tag tag known_tags) as [[case | ] | ];
    [ reflexivity | reflexivity | destruct other_tags; reflexivity ].
Qed.

Theorem row_like_for_blocks_find : row_like_for_blocks_find_statement.
Proof. exact row_like_for_blocks_find_iff. Qed.

Theorem immutable_block_satisfied : immutable_block_satisfied_statement.
Proof.
  intros statics vars v is_unique tag shape alloc_mode field_tys.
  unfold immutable_block.
  rewrite (create_variant_satisfied statics vars v).
  unfold row_like_for_blocks_create_exactly.
  split.
  - intros [[i [_ [Hbottom _]]] | [tag' [fields [Hblock [Hblocks _]]]]];
      [ destruct (bottom_satisfied _ _ _ _ Hbottom) | ].
    rewrite row_like_for_blocks_find_iff in Hblocks. simpl in Hblocks.
    destruct (Z.eqb_spec tag' tag) as [-> | _]; [ | destruct Hblocks ].
    destruct Hblocks as [[Hlength Hshape] [Hfields _]]. simpl in *.
    exists fields. split; [ exact Hblock | ]. split; [ exact Hshape | ].
    apply fields_satisfied_Forall2; assumption.
  - intros [fields [Hblock [Hshape Hfields]]]. right. exists tag, fields.
    split; [ exact Hblock | ]. split; [ | exact I ].
    rewrite row_like_for_blocks_find_iff. simpl. rewrite Z.eqb_refl.
    assert (Hlength : length fields = length field_tys)
      by exact (Forall2_length Hfields).
    split; [ split; [ exact Hlength | exact Hshape ] | ].
    split; [ apply fields_satisfied_Forall2; assumption | ].
    simpl. split; exact I.
Qed.

(* ======================================================================== *)
(* Boxed numbers, strings and closures                                      *)
(* ======================================================================== *)

Theorem box_number_satisfied : box_number_satisfied_statement.
Proof.
  intros statics vars v k contents alloc_mode. unfold box_number.
  rewrite non_null_value_satisfied. reflexivity.
Qed.

Theorem this_immutable_string_satisfied
  : this_immutable_string_satisfied_statement.
Proof.
  intros statics vars v bytes. unfold this_immutable_string.
  rewrite non_null_value_satisfied. simpl. split.
  - intros [bytes' [Hstring [<- | []]]]. exact Hstring.
  - intros Hstring. exists bytes. split; [ exact Hstring | ].
    left. reflexivity.
Qed.

Lemma row_like_for_closures_lookup_iff (statics : static_env) (vars : env)
    (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (known_closures : finite_map row_like_closures_case) :
  row_like_for_closures_satisfied statics vars v slot functions value_slots
    (Row_like_for_closures known_closures)
  <-> ∃ case : row_like_closures_case,
        lookup slot known_closures = Some case
        ∧ row_like_closures_case_satisfied statics vars v slot functions
            value_slots case.
Proof.
  simpl. rewrite at_binding_iff, is_bound_lookup. split.
  - intros [[case Hlookup] Hcase]. exists case.
    split; [ exact Hlookup | exact (Hcase case Hlookup) ].
  - intros [case [Hlookup Hcase]]. split; [ exists case; exact Hlookup | ].
    intros case' Hlookup'. rewrite Hlookup in Hlookup'.
    injection Hlookup' as <-. exact Hcase.
Qed.

Theorem row_like_for_closures_lookup
  : row_like_for_closures_lookup_statement.
Proof. exact row_like_for_closures_lookup_iff. Qed.

Lemma closures_entry_lookup_iff (statics : static_env) (vars : env)
    (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (function_types : finite_map (Or_unknown.t function_type))
    (closure_types value_slot_types : finite_map flambda_type) :
  closures_entry_satisfied statics vars v slot functions value_slots
    (Closures_entry function_types closure_types value_slot_types)
  <-> (∀ (g : function_slot) (function_type : function_type),
        lookup g function_types = Some (Or_unknown.Known function_type) ->
        lookup g functions = Some (function_type_code_id function_type))
      ∧ (∀ (g : function_slot) (ty : flambda_type) (closure : value),
          lookup g closure_types = Some ty ->
          project_function_slot statics slot g v = Some closure ->
          type_satisfied statics vars closure ty)
      ∧ (∀ (w : value_slot) (ty : flambda_type) (contents : value),
          lookup w value_slot_types = Some ty ->
          lookup w value_slots = Some contents ->
          type_satisfied statics vars contents ty).
Proof.
  simpl. rewrite !for_all_bindings_iff.
  split; intros [Hfunctions [Hclosures Hslots]];
    (split; [ exact Hfunctions | split; eauto ]).
Qed.

Theorem closures_entry_lookup : closures_entry_lookup_statement.
Proof. exact closures_entry_lookup_iff. Qed.

Lemma env_extension_lookup_iff (statics : static_env) (vars : env)
    (equations : finite_name_map flambda_type) :
  env_extension_satisfied statics vars (Env_extension equations)
  <-> (∀ (n : name) (ty : flambda_type),
        lookup_name n equations = Some ty ->
        ∃ v : value,
          value_of_name vars n = Some v ∧ type_satisfied statics vars v ty).
Proof. simpl. rewrite for_all_names_iff. reflexivity. Qed.

Theorem env_extension_lookup : env_extension_lookup_statement.
Proof. exact env_extension_lookup_iff. Qed.

Lemma empty_env_extension_satisfied (statics : static_env) (vars : env) :
  env_extension_satisfied statics vars empty_env_extension.
Proof.
  apply env_extension_lookup_iff. intros [x | s] ty; discriminate.
Qed.

Theorem exactly_this_closure_satisfied
  : exactly_this_closure_satisfied_statement.
Proof.
  intros statics vars v slot function_types closure_types value_slot_types
    alloc_mode.
  unfold exactly_this_closure, create_closures.
  rewrite non_null_value_satisfied, closures_satisfied. split.
  - intros [slot' [functions [value_slots [Hclosure Hrow]]]].
    rewrite row_like_for_closures_lookup_iff in Hrow.
    destruct Hrow as [case [Hlookup Hcase]]. simpl in Hlookup.
    destruct (Pos.eqb_spec slot' slot) as [-> | _]; [ | discriminate ].
    injection Hlookup as <-.
    destruct Hcase as [[Hfunctions Hslots] [Hentry _]].
    exists functions, value_slots.
    split; [ exact Hclosure | ]. split; [ exact Hfunctions | ].
    split; [ exact Hslots | exact Hentry ].
  - intros [functions [value_slots [Hclosure [Hfunctions [Hslots Hentry]]]]].
    exists slot, functions, value_slots. split; [ exact Hclosure | ].
    rewrite row_like_for_closures_lookup_iff. eexists. split.
    + simpl. rewrite Pos.eqb_refl. reflexivity.
    + split; [ split; assumption | ].
      split; [ exact Hentry | apply empty_env_extension_satisfied ].
Qed.

(* ======================================================================== *)
(* Examples                                                                 *)
(* ======================================================================== *)

(* For each constructor of the grammar, a value that has a type built
   with it and a value that has not, under a static environment with a
   block, a boxed float, a string and a closure, and an environment with
   three variables. No statement about types holds for want of values. *)

Module Examples.

Local Open Scope Z_scope.

Definition a_block : symbol := 1%positive.
Definition a_boxed_float : symbol := 2%positive.
Definition a_string : symbol := 3%positive.
Definition a_closure : symbol := 4%positive.
Definition unbound : symbol := 5%positive.
Definition some_code : code_id := 1%positive.
Definition other_code : code_id := 2%positive.
Definition a_value_slot : value_slot := 1%positive.

(* A block of tag 0 with two fields, a boxed float, a string of two
   bytes, and a closure with one value slot. *)
Definition statics : static_env :=
  Static_env []
    [(a_block,
      Static_block 0
        [Value_const (Tagged_immediate 7); Value_symbol a_boxed_float]);
     (a_boxed_float, Static_boxed_number (Value_const (Naked_float 42)));
     (a_string, Static_string [104; 105]);
     (a_closure,
      Static_closure some_code
        [(a_value_slot, Value_const (Tagged_immediate 3))])].

Definition x : variable := 1%positive.
Definition zero : variable := 2%positive.
Definition one : variable := 3%positive.

Definition vars : env :=
  [(x, Value_const (Tagged_immediate 5));
   (zero, Value_const (Naked_immediate 0));
   (one, Value_const (Naked_immediate 1))].

Definition has (v : value) (t : flambda_type) : Prop :=
  type_satisfied statics vars v t.

Definition tagged (i : Z) : value := Value_const (Tagged_immediate i).
Definition naked (i : Z) : value := Value_const (Naked_immediate i).

(* What is to be proved is decided by computing: [yes] proves that a
   value has a type and [no] that it has not. *)
Ltac yes :=
  compute;
  repeat
    first
      [ exact I | reflexivity
      | match goal with
        | H : False |- _ => destruct H
        | H : _ ∨ _ |- _ => destruct H
        | H : ?a = ?a |- _ => clear H
        | H : _ = _ |- _ => discriminate H
        | H : (_, _) = (_, _) |- _ => injection H as <- <-
        | H : Some _ = Some _ |- _ => injection H as <-
        | H : (if ?b then _ else _) = Some _ |- _ => destruct b
        end
      | discriminate | progress compute in * | intro | split | eexists
      | left; solve [ yes ] | right; solve [ yes ] ].

Ltac no :=
  compute; intros Hsatisfied;
  repeat
    match goal with
    | H : _ ∧ _ |- _ => destruct H
    | H : ∃ _, _ |- _ => destruct H
    | H : _ ∨ _ |- _ => destruct H
    | H : False |- _ => destruct H
    | H : True |- _ => clear H
    | H : _ = _ |- _ => discriminate H
    | H : Some _ = Some _ |- _ => injection H as H; subst
    | H : Value_const _ = Value_const _ |- _ => injection H as H; subst
    | H : ?a = ?a -> _ |- _ => specialize (H eq_refl)
    | H : ?a <> ?a |- _ => destruct (H eq_refl)
    | H : ∀ r n, (?r0, ?n0) = (r, n) ∨ _ -> _ |- _ =>
      specialize (H r0 n0 (or_introl eq_refl))
    | H : ∀ c, Some ?v = Some c -> _ |- _ => specialize (H v eq_refl)
    | H : ∀ (g : positive) (function_type : function_type), _ |- _ =>
      specialize (H 1%positive _ eq_refl)
    | _ => progress compute in *
    end;
  try congruence; try lia.

(* [Unknown]. *)
Example unknown_has : has (tagged 1) (unknown Value).
Proof. yes. Qed.

Example unknown_has_not : ~ has (naked 1) (unknown Value).
Proof. no. Qed.

(* [Equals]. *)
Example alias_has : has (tagged 5) (alias_type_of Value (Var x)).
Proof. yes. Qed.

Example alias_has_not : ~ has (tagged 6) (alias_type_of Value (Var x)).
Proof. no. Qed.

Example alias_of_symbol_has
  : has (Value_symbol a_block) (alias_type_of Value (Symbol a_block)).
Proof. yes. Qed.

Example alias_of_symbol_has_not
  : ~ has (Value_symbol a_string) (alias_type_of Value (Symbol a_block)).
Proof. no. Qed.

(* [Type_naked_immediate]: numbers, and relations. *)
Example naked_immediates_has : has (naked 2) (these_naked_immediates [1; 2]).
Proof. yes. Qed.

Example naked_immediates_has_not
  : ~ has (naked 3) (these_naked_immediates [1; 2]).
Proof. no. Qed.

Example is_int_has : has (naked 1) (is_int_for_scrutinee (Name_var x)).
Proof. yes. Qed.

Example is_int_has_not : ~ has (naked 0) (is_int_for_scrutinee (Name_var x)).
Proof. no. Qed.

Example is_int_of_block_has
  : has (naked 0) (is_int_for_scrutinee (Name_symbol a_block)).
Proof. yes. Qed.

Example get_tag_has
  : has (naked 0) (get_tag_for_block (Name_symbol a_block)).
Proof. yes. Qed.

Example get_tag_has_not
  : ~ has (naked 1) (get_tag_for_block (Name_symbol a_block)).
Proof. no. Qed.

Example is_null_has
  : has (naked 0) (is_null_for_scrutinee (Name_symbol a_closure)).
Proof. yes. Qed.

Example is_null_has_not
  : ~ has (naked 1) (is_null_for_scrutinee (Name_symbol a_closure)).
Proof. no. Qed.

(* [Type_naked_number]. *)
Example naked_floats_has
  : has (Value_const (Naked_float 42))
      (Type_naked_number Kind_naked_float (Ok (No_alias [42; 43]))).
Proof. yes. Qed.

Example naked_floats_has_not
  : ~ has (Value_const (Naked_int32 42))
        (Type_naked_number Kind_naked_float (Ok (No_alias [42; 43]))).
Proof. no. Qed.

(* [Type_region] and [Type_rec_info]: the machine has no value of these
   kinds but [Poison]. *)
Example region_has
  : has (Value_const (Poison Region)) (Type_region (Ok (No_alias tt))).
Proof. yes. Qed.

Example region_has_not : ~ has (tagged 0) (Type_region (Ok (No_alias tt))).
Proof. no. Qed.

Example rec_info_has
  : has (Value_const (Poison Rec_info)) (Type_rec_info (Ok (No_alias tt))).
Proof. yes. Qed.

Example rec_info_has_not
  : ~ has (tagged 0) (Type_rec_info (Ok (No_alias tt))).
Proof. no. Qed.

(* [Head_of_kind_value]: null or not. *)
Example null_has : has (Value_const Null) null.
Proof. yes. Qed.

Example null_has_not : ~ has (tagged 0) null.
Proof. no. Qed.

Example non_null_has : has (Value_symbol unbound) any_non_null_value.
Proof. yes. Qed.

Example non_null_has_not : ~ has (Value_const Null) any_non_null_value.
Proof. no. Qed.

(* With a variable for [Is_null]: [one] holds 1 and [zero] holds 0. *)
Definition maybe_null (is_null : variable) : flambda_type :=
  Type_value
    (Ok (No_alias (Head_of_kind_value Unknown (Maybe_null (Some is_null))))).

Example is_null_variable_has : has (Value_const Null) (maybe_null one).
Proof. yes. Qed.

Example is_null_variable_has_not : ~ has (Value_const Null) (maybe_null zero).
Proof. no. Qed.

Example is_not_null_variable_has : has (tagged 0) (maybe_null zero).
Proof. yes. Qed.

Example is_not_null_variable_has_not : ~ has (tagged 0) (maybe_null one).
Proof. no. Qed.

(* [Variant]: immediates. *)
Example tagged_immediates_has
  : has (tagged 1) (these_tagged_immediates [0; 1; 2]).
Proof. yes. Qed.

Example tagged_immediates_has_not
  : ~ has (tagged 5) (these_tagged_immediates [0; 1; 2]).
Proof. no. Qed.

Example any_tagged_immediate_has_not
  : ~ has (Value_symbol a_block) any_tagged_immediate.
Proof. no. Qed.

(* [Variant]: blocks, of a known tag and size. *)
Example block_has
  : has (Value_symbol a_block)
      (immutable_block false 0 (Scannable Value_only) Alloc_mode.Heap
         [this_tagged_immediate 7; unknown Value]).
Proof. yes. Qed.

Example block_field_has_not
  : ~ has (Value_symbol a_block)
        (immutable_block false 0 (Scannable Value_only) Alloc_mode.Heap
           [this_tagged_immediate 8; unknown Value]).
Proof. no. Qed.

Example block_size_has_not
  : ~ has (Value_symbol a_block)
        (immutable_block false 0 (Scannable Value_only) Alloc_mode.Heap
           [this_tagged_immediate 7]).
Proof. no. Qed.

Example block_tag_has_not
  : ~ has (Value_symbol a_block)
        (immutable_block false 1 (Scannable Value_only) Alloc_mode.Heap
           [this_tagged_immediate 7; unknown Value]).
Proof. no. Qed.

Example block_shape_has_not
  : ~ has (Value_symbol a_block)
        (immutable_block false 0 Float_record Alloc_mode.Heap
           [this_tagged_immediate 7; unknown Value]).
Proof. no. Qed.

Example any_block_has : has (Value_symbol a_block) any_block.
Proof. yes. Qed.

Example any_block_has_not : ~ has (Value_symbol a_closure) any_block.
Proof. no. Qed.

(* Blocks of any tag with at least so many fields: [other_tags]. *)
Definition block_of_size_at_least (size : nat) : flambda_type :=
  create_variant false
    (Or_unknown.Known (bottom (Naked_number Kind_naked_immediate)))
    (Or_unknown.Known
       (row_like_for_blocks_create_at_least_unknown_tag size
          (Scannable Value_only) [this_tagged_immediate 7]
          Alloc_mode.Heap))
    No_extensions.

Example other_tags_has : has (Value_symbol a_block) (block_of_size_at_least 1).
Proof. yes. Qed.

Example other_tags_has_not
  : ~ has (Value_symbol a_block) (block_of_size_at_least 3).
Proof. no. Qed.

(* Blocks of a tag of which nothing more is known. *)
Definition block_of_tag (tag : Z) : flambda_type :=
  create_variant false
    (Or_unknown.Known (bottom (Naked_number Kind_naked_immediate)))
    (Or_unknown.Known
       (Row_like_for_blocks [(tag, Or_unknown.Unknown)] Or_bottom.Bottom
          Alloc_mode.Heap))
    No_extensions.

Example unknown_case_has : has (Value_symbol a_block) (block_of_tag 0).
Proof. yes. Qed.

Example unknown_case_has_not : ~ has (Value_symbol a_block) (block_of_tag 1).
Proof. no. Qed.

(* With variables for [Is_int] and [Get_tag], and with extensions: a
   block has the type only if the variables hold 0 and its tag, and if
   the equation that holds of blocks is true. *)
Definition scrutinee (is_int get_tag : variable) (x_is : Z) : flambda_type :=
  non_null_value
    (Variant (Some is_int) Or_unknown.Unknown (Some get_tag)
       Or_unknown.Unknown
       (Ext (Env_extension (Finite_name_map [(x, bottom Value)] []))
          (Env_extension
             (Finite_name_map [(x, this_tagged_immediate x_is)] [])))
       false).

Example variant_variables_has
  : has (Value_symbol a_block) (scrutinee zero zero 5).
Proof. yes. Qed.

Example variant_is_int_has_not
  : ~ has (Value_symbol a_block) (scrutinee one zero 5).
Proof. no. Qed.

Example variant_get_tag_has_not
  : ~ has (Value_symbol a_block) (scrutinee zero one 5).
Proof. no. Qed.

Example variant_extension_has_not
  : ~ has (Value_symbol a_block) (scrutinee zero zero 6).
Proof. no. Qed.

Example variant_when_immediate_has_not
  : ~ has (tagged 0) (scrutinee one zero 5).
Proof. no. Qed.

(* [Boxed_number]. *)
Example boxed_float_has
  : has (Value_symbol a_boxed_float)
      (box_number Kind_naked_float
         (Type_naked_number Kind_naked_float (Ok (No_alias [42])))
         Alloc_mode.Heap).
Proof. yes. Qed.

Example boxed_float_contents_has_not
  : ~ has (Value_symbol a_boxed_float)
        (box_number Kind_naked_float
           (Type_naked_number Kind_naked_float (Ok (No_alias [43])))
           Alloc_mode.Heap).
Proof. no. Qed.

Example boxed_float_kind_has_not
  : ~ has (Value_symbol a_boxed_float)
        (box_number Kind_naked_int32 (unknown (Naked_number Kind_naked_int32))
           Alloc_mode.Heap).
Proof. no. Qed.

Example boxed_float_block_has_not
  : ~ has (Value_symbol a_block)
        (box_number Kind_naked_float (unknown (Naked_number Kind_naked_float))
           Alloc_mode.Heap).
Proof. no. Qed.

(* [String]. *)
Example string_has
  : has (Value_symbol a_string) (this_immutable_string [104; 105]).
Proof. yes. Qed.

Example string_has_not
  : ~ has (Value_symbol a_string) (this_immutable_string [104]).
Proof. no. Qed.

(* [Closures]: the closure of the code [code] whose value slot holds a
   value of the type given. *)
Definition closure_type (code : code_id) (slot_type : flambda_type)
    : flambda_type :=
  exactly_this_closure unnamed_function_slot
    [(unnamed_function_slot, Or_unknown.Known (Function_type code))] []
    [(a_value_slot, slot_type)] Alloc_mode.Heap.

Example closure_has
  : has (Value_symbol a_closure)
      (closure_type some_code (this_tagged_immediate 3)).
Proof. yes. Qed.

Example closure_made_by_let_has
  : has (Value_closure some_code [(a_value_slot, tagged 3)])
      (closure_type some_code (this_tagged_immediate 3)).
Proof. yes. Qed.

Example closure_code_has_not
  : ~ has (Value_symbol a_closure)
        (closure_type other_code (this_tagged_immediate 3)).
Proof. no. Qed.

Example closure_value_slot_has_not
  : ~ has (Value_symbol a_closure)
        (closure_type some_code (this_tagged_immediate 4)).
Proof. no. Qed.

Example closure_block_has_not
  : ~ has (Value_symbol a_block)
        (closure_type some_code (this_tagged_immediate 3)).
Proof. no. Qed.

(* [Mutable_block]: no value has it ([mutable_block_satisfied]), the
   machine having none. *)

End Examples.

(* ======================================================================== *)
(* Proving with the meaning of types                                        *)
(* ======================================================================== *)

(* [simpl] and [cbn] leave [type_satisfied] and the functions defined with
   it alone from here on: rewrite with the equations above
   ([autorewrite with type_satisfied]) and with the statements. Unfolding
   still works where it is asked for, as the examples do with [compute]. *)
#[global] Arguments type_satisfied : simpl never.
#[global] Arguments head_of_kind_value_satisfied : simpl never.
#[global] Arguments head_of_kind_value_non_null_satisfied : simpl never.
#[global] Arguments row_like_for_blocks_satisfied : simpl never.
#[global] Arguments row_like_for_closures_satisfied : simpl never.
#[global] Arguments closures_entry_satisfied : simpl never.
#[global] Arguments env_extension_satisfied : simpl never.

(* ======================================================================== *)
(* When the static environment grows                                        *)
(* ======================================================================== *)

Section Statics_extend.

Variables statics statics' : static_env.
Hypothesis Hextend : statics_extend statics statics'.

Lemma block_of_extend (v : value) (block : Z * list value) :
  block_of statics v = Some block -> block_of statics' v = Some block.
Proof.
  destruct v as [c | code slots | s]; simpl; try discriminate.
  destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hlookup;
    [ | discriminate ].
  rewrite (proj2 Hextend s allocated Hlookup). auto.
Qed.

Lemma boxed_number_of_extend (v : value) (c : const) :
  boxed_number_of statics v = Some c -> boxed_number_of statics' v = Some c.
Proof.
  destruct v as [c' | code slots | s]; simpl; try discriminate.
  destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hlookup;
    [ | discriminate ].
  rewrite (proj2 Hextend s allocated Hlookup). auto.
Qed.

Lemma string_of_extend (v : value) (bytes : list Z) :
  string_of statics v = Some bytes -> string_of statics' v = Some bytes.
Proof.
  destruct v as [c | code slots | s]; simpl; try discriminate.
  destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hlookup;
    [ | discriminate ].
  rewrite (proj2 Hextend s allocated Hlookup). auto.
Qed.

Lemma closure_of_extend (v : value)
    (closure : code_id * list (value_slot * value)) :
  closure_of statics v = Some closure -> closure_of statics' v = Some closure.
Proof.
  destruct v as [c | code slots | s]; simpl; try discriminate; [ auto | ].
  destruct (lookup s (static_values statics)) as [allocated | ] eqn:Hlookup;
    [ | discriminate ].
  rewrite (proj2 Hextend s allocated Hlookup). auto.
Qed.

Lemma closure_in_set_extend (v : value)
    (closure :
      function_slot * list (function_slot * code_id)
      * list (value_slot * value)) :
  closure_in_set statics v = Some closure ->
  closure_in_set statics' v = Some closure.
Proof.
  unfold closure_in_set.
  destruct (closure_of statics v) as [[code slots] | ] eqn:Hclosure;
    [ | discriminate ].
  rewrite (closure_of_extend _ _ Hclosure). auto.
Qed.

(* The closures of the set of a closure are the same ones. *)
Lemma project_function_slot_extend (v : value)
    (closure :
      function_slot * list (function_slot * code_id)
      * list (value_slot * value))
    (move_from move_to : function_slot) :
  closure_in_set statics v = Some closure ->
  project_function_slot statics' move_from move_to v
  = project_function_slot statics move_from move_to v.
Proof.
  unfold closure_in_set, project_function_slot.
  destruct (closure_of statics v) as [[code slots] | ] eqn:Hclosure;
    [ | discriminate ].
  rewrite (closure_of_extend _ _ Hclosure). reflexivity.
Qed.

Lemma some_not_none {A : Type} (o : option A) :
  o <> None <-> ∃ a : A, o = Some a.
Proof.
  destruct o as [a | ]; split; [ eauto | discriminate | congruence | ].
  intros [a [=]].
Qed.

Lemma allocated_extend (v : value) :
  allocated statics v -> allocated statics' v.
Proof.
  unfold allocated. rewrite !some_not_none.
  intros [[b Hb] | [[c Hc] | [[n Hn] | [bytes Hs]]]].
  - left. exists b. exact (block_of_extend _ _ Hb).
  - right. left. exists c. exact (closure_of_extend _ _ Hc).
  - right. right. left. exists n. exact (boxed_number_of_extend _ _ Hn).
  - right. right. right. exists bytes. exact (string_of_extend _ _ Hs).
Qed.

Lemma relation_holds_extend (relation : Relation.t) (v : value) (n : Z) :
  relation_holds statics relation v n -> relation_holds statics' relation v n.
Proof.
  destruct relation; simpl.
  - intros [Hnull | [[Himmediate | Hallocated] Hn]]; [ left; exact Hnull | | ].
    + right. split; [ left; exact Himmediate | exact Hn ].
    + right. split; [ | exact Hn ]. right.
      exact (allocated_extend _ Hallocated).
  - intros [Himmediate | [[tag [fields Hblock]] Hn]];
      [ left; exact Himmediate | ].
    right. split; [ | exact Hn ]. exists tag, fields.
    exact (block_of_extend _ _ Hblock).
  - intros [fields Hblock]. exists fields. exact (block_of_extend _ _ Hblock).
Qed.

(* What holds of the fields under one meaning of types holds under
   another that is implied by it for the types of the fields. *)
Lemma fields_satisfied_impl (P Q : value -> flambda_type -> Prop)
    (tys : list flambda_type) (fields : list value) :
  (∀ ty : flambda_type, ty ∈ tys -> ∀ v : value, P v ty -> Q v ty) ->
  fields_satisfied P tys fields -> fields_satisfied Q tys fields.
Proof.
  revert fields. induction tys as [ | ty tys IH]; intros fields Himpl.
  - auto.
  - destruct fields as [ | field fields]; simpl; [ auto | ].
    intros [Hfield Hfields]. split.
    + exact (Himpl ty (or_introl eq_refl) field Hfield).
    + apply IH; [ | exact Hfields ].
      intros ty' Hin. exact (Himpl ty' (or_intror Hin)).
Qed.

Lemma type_satisfied_statics_extend_all (vars : env) :
  (∀ (t : flambda_type) (v : value),
    type_satisfied statics vars v t -> type_satisfied statics' vars v t)
  ∧ (∀ (head : head_of_kind_value) (v : value),
      head_of_kind_value_satisfied statics vars v head ->
      head_of_kind_value_satisfied statics' vars v head)
  ∧ (∀ (head : head_of_kind_value_non_null) (v : value),
      head_of_kind_value_non_null_satisfied statics vars v head ->
      head_of_kind_value_non_null_satisfied statics' vars v head)
  ∧ (∀ (blocks : row_like_for_blocks) (tag : Z) (fields : list value),
      row_like_for_blocks_satisfied statics vars tag fields blocks ->
      row_like_for_blocks_satisfied statics' vars tag fields blocks)
  ∧ (∀ (closures : row_like_for_closures) (v : value) (slot : function_slot)
       (functions : list (function_slot * code_id))
       (value_slots : list (value_slot * value)),
      closure_in_set statics v = Some (slot, functions, value_slots) ->
      row_like_for_closures_satisfied statics vars v slot functions
        value_slots closures ->
      row_like_for_closures_satisfied statics' vars v slot functions
        value_slots closures)
  ∧ (∀ (entry : closures_entry) (v : value) (slot : function_slot)
       (functions : list (function_slot * code_id))
       (value_slots : list (value_slot * value)),
      closure_in_set statics v = Some (slot, functions, value_slots) ->
      closures_entry_satisfied statics vars v slot functions value_slots
        entry ->
      closures_entry_satisfied statics' vars v slot functions value_slots
        entry)
  ∧ (∀ extension : env_extension,
      env_extension_satisfied statics vars extension ->
      env_extension_satisfied statics' vars extension).
Proof.
  apply types_induction.
  - (* Type_value *)
    intros [ | [head | s] | ] Hhead v; autorewrite with type_satisfied;
      simpl; auto.
  - (* Type_naked_immediate *)
    intros [ | [head | s] | ] v; autorewrite with type_satisfied; simpl; auto.
    intros [i [Hv [Hnumbers Hrelations]]]. exists i.
    split; [ exact Hv | ]. split; [ exact Hnumbers | ].
    intros relation n Hin. destruct (Hrelations relation n Hin) as [w [Hw H]].
    exists w. split; [ exact Hw | exact (relation_holds_extend _ _ _ H) ].
  - intros k ty v. autorewrite with type_satisfied. auto.
  - intros ty v. autorewrite with type_satisfied. auto.
  - intros ty v. autorewrite with type_satisfied. auto.
  - (* Head_of_kind_value *)
    intros non_null is_null Hnon_null v. autorewrite with type_satisfied.
    intros [Hnull | [Hnot_null [Hhead His_null]]]; [ left; exact Hnull | ].
    right. split; [ exact Hnot_null | ]. split; [ | exact His_null ].
    destruct non_null as [ | head | ]; auto.
  - (* Variant *)
    intros is_int immediates get_tag blocks extensions is_unique Himmediates
      Hblocks Hextensions v.
    autorewrite with type_satisfied.
    intros [[i [Hv [His_int [Himmediate Hextension]]]]
           | [tag [fields [Hblock [His_int [Hget_tag [Hrow Hextension]]]]]]].
    + left. exists i. split; [ exact Hv | ]. split; [ exact His_int | ].
      split.
      * destruct immediates as [ty | ]; auto.
      * destruct extensions as [ | when_immediate when_block]; [ exact I | ].
        exact (proj1 Hextensions Hextension).
    + right. exists tag, fields.
      split; [ exact (block_of_extend _ _ Hblock) | ].
      split; [ exact His_int | ]. split; [ exact Hget_tag | ]. split.
      * destruct blocks as [blocks | ]; auto.
      * destruct extensions as [ | when_immediate when_block]; [ exact I | ].
        exact (proj2 Hextensions Hextension).
  - (* Mutable_block *)
    intros alloc_mode v. autorewrite with type_satisfied. auto.
  - (* Boxed_number *)
    intros k contents alloc_mode Hcontents v. autorewrite with type_satisfied.
    intros [c [Hboxed [Hkind Hc]]]. exists c.
    split; [ exact (boxed_number_of_extend _ _ Hboxed) | ]. auto.
  - (* Closures *)
    intros by_function_slot alloc_mode Hclosures v.
    autorewrite with type_satisfied.
    intros [slot [functions [value_slots [Hclosure Hrow]]]].
    exists slot, functions, value_slots.
    split; [ exact (closure_in_set_extend _ _ Hclosure) | ].
    exact (Hclosures v slot functions value_slots Hclosure Hrow).
  - (* String *)
    intros strs v. autorewrite with type_satisfied.
    intros [bytes [Hstring Hin]]. exists bytes.
    split; [ exact (string_of_extend _ _ Hstring) | exact Hin ].
  - (* Row_like_for_blocks *)
    intros known_tags other_tags alloc_mode Hknown Hother tag fields.
    rewrite !row_like_for_blocks_find_iff.
    assert (Hcase :
      ∀ case : row_like_block_case,
        P_block_case
          (fun t =>
             ∀ v : value,
               type_satisfied statics vars v t ->
               type_satisfied statics' vars v t)
          (fun extension =>
             env_extension_satisfied statics vars extension ->
             env_extension_satisfied statics' vars extension)
          case ->
        row_like_block_case_satisfied statics vars tag fields case ->
        row_like_block_case_satisfied statics' vars tag fields case).
    { intros case [Htypes Hextension] [Hindex [Hfields Hext]].
      split; [ exact Hindex | ]. split; [ | exact (Hextension Hext) ].
      exact (fields_satisfied_impl _ _ _ _ Htypes Hfields). }
    destruct (find_tag tag known_tags) as [[case | ] | ] eqn:Hfind.
    + apply Hcase. exact (Hknown tag case (find_tag_in _ _ _ Hfind)).
    + auto.
    + destruct other_tags as [case | ]; [ exact (Hcase case Hother) | auto ].
  - (* Row_like_for_closures *)
    intros known_closures Hknown v slot functions value_slots Hclosure.
    rewrite !row_like_for_closures_lookup_iff.
    intros [case [Hlookup [Hindex [Hentry Hextension]]]]. exists case.
    split; [ exact Hlookup | ].
    destruct (Hknown slot case (lookup_in _ _ _ Hlookup))
      as [IHentry IHextension].
    split; [ exact Hindex | ]. split; [ | exact (IHextension Hextension) ].
    exact (IHentry v slot functions value_slots Hclosure Hentry).
  - (* Closures_entry *)
    intros function_types closure_types value_slot_types Hclosures Hslots v
      slot functions value_slots Hclosure.
    rewrite !closures_entry_lookup_iff.
    intros [Hfunctions [Hclosure_types Hvalue_slots]].
    split; [ exact Hfunctions | ]. split.
    + intros g ty closure Hlookup Hproject.
      rewrite (project_function_slot_extend _ _ _ _ Hclosure) in Hproject.
      apply (Hclosures g ty (lookup_in _ _ _ Hlookup)).
      exact (Hclosure_types g ty closure Hlookup Hproject).
    + intros w ty contents Hlookup Hcontents.
      apply (Hslots w ty (lookup_in _ _ _ Hlookup)).
      exact (Hvalue_slots w ty contents Hlookup Hcontents).
  - (* Env_extension *)
    intros equations Hvariables Hsymbols.
    rewrite !env_extension_lookup_iff.
    intros Hequations n ty Hlookup.
    destruct (Hequations n ty Hlookup) as [v [Hv Hty]]. exists v.
    split; [ exact Hv | ].
    destruct n as [x | s]; simpl in Hlookup.
    + exact (Hvariables x ty (lookup_in _ _ _ Hlookup) v Hty).
    + exact (Hsymbols s ty (lookup_in _ _ _ Hlookup) v Hty).
Qed.

End Statics_extend.

Theorem type_satisfied_statics_extend
  : type_satisfied_statics_extend_statement.
Proof.
  intros statics statics' vars v t Hextend.
  exact (proj1 (type_satisfied_statics_extend_all _ _ Hextend vars) t v).
Qed.

Theorem env_extension_satisfied_statics_extend
  : env_extension_satisfied_statics_extend_statement.
Proof.
  intros statics statics' vars extension Hextend.
  destruct (type_satisfied_statics_extend_all _ _ Hextend vars)
    as [_ [_ [_ [_ [_ [_ Hextension]]]]]].
  exact (Hextension extension).
Qed.

(* ======================================================================== *)
(* The variables that the meaning of a type depends on                      *)
(* ======================================================================== *)

(* Two environments give the same values to some variables. *)
Definition agree (vars vars' : env) (xs : list variable) : Prop :=
  ∀ x : variable, x ∈ xs -> lookup x vars = lookup x vars'.

Lemma agree_app (vars vars' : env) (xs ys : list variable) :
  agree vars vars' (xs ++ ys) <-> agree vars vars' xs ∧ agree vars vars' ys.
Proof.
  unfold agree. split.
  - intros Hagree. split; intros x Hin; apply Hagree, in_or_app; auto.
  - intros [Hxs Hys] x Hin. apply in_app_or in Hin as [Hin | Hin]; auto.
Qed.

Lemma agree_flat_map {A : Type} (vars vars' : env) (f : A -> list variable)
    (l : list A) (a : A) :
  agree vars vars' (flat_map f l) -> a ∈ l -> agree vars vars' (f a).
Proof.
  intros Hagree Hin x Hx. apply Hagree, in_flat_map. exists a. auto.
Qed.

Lemma agree_eval_simple (vars vars' : env) (s : simple) :
  agree vars vars' (free_variables_of_simple s) ->
  eval_simple vars s = eval_simple vars' s.
Proof.
  destruct s as [x | sym | c]; simpl; [ | reflexivity | reflexivity ].
  intros Hagree. apply Hagree. left. reflexivity.
Qed.

Lemma agree_variable_is (vars vars' : env) (x : option variable) (n : Z) :
  agree vars vars' (free_variables_of_option x) ->
  variable_is vars x n -> variable_is vars' x n.
Proof.
  destruct x as [x | ]; simpl; [ | auto ].
  intros Hagree. rewrite (Hagree x (or_introl eq_refl)). auto.
Qed.

Lemma agree_descr {head : Type} (vars vars' : env) (k : flambda_kind)
    (free_variables_of_head : head -> list variable)
    (head_satisfied head_satisfied' : head -> Prop) (v : value)
    (ty : type_descr head) :
  agree vars vars' (free_variables_of_descr free_variables_of_head ty) ->
  (∀ h : head,
    ty = Ok (No_alias h) -> head_satisfied h -> head_satisfied' h) ->
  descr_satisfied vars k head_satisfied v ty ->
  descr_satisfied vars' k head_satisfied' v ty.
Proof.
  destruct ty as [ | [h | s] | ]; simpl; [ auto | | | auto ].
  - intros _ Hhead. exact (Hhead h eq_refl).
  - intros Hagree _. rewrite (agree_eval_simple _ _ _ Hagree). auto.
Qed.

Lemma type_satisfied_agree_all (statics : static_env) :
  (∀ (t : flambda_type) (vars vars' : env) (v : value),
    agree vars vars' (free_variables t) ->
    type_satisfied statics vars v t -> type_satisfied statics vars' v t)
  ∧ (∀ (head : head_of_kind_value) (vars vars' : env) (v : value),
      agree vars vars' (free_variables_of_head_of_kind_value head) ->
      head_of_kind_value_satisfied statics vars v head ->
      head_of_kind_value_satisfied statics vars' v head)
  ∧ (∀ (head : head_of_kind_value_non_null) (vars vars' : env) (v : value),
      agree vars vars' (free_variables_of_head_of_kind_value_non_null head) ->
      head_of_kind_value_non_null_satisfied statics vars v head ->
      head_of_kind_value_non_null_satisfied statics vars' v head)
  ∧ (∀ (blocks : row_like_for_blocks) (vars vars' : env) (tag : Z)
       (fields : list value),
      agree vars vars' (free_variables_of_row_like_for_blocks blocks) ->
      row_like_for_blocks_satisfied statics vars tag fields blocks ->
      row_like_for_blocks_satisfied statics vars' tag fields blocks)
  ∧ (∀ (closures : row_like_for_closures) (vars vars' : env) (v : value)
       (slot : function_slot) (functions : list (function_slot * code_id))
       (value_slots : list (value_slot * value)),
      agree vars vars' (free_variables_of_row_like_for_closures closures) ->
      row_like_for_closures_satisfied statics vars v slot functions
        value_slots closures ->
      row_like_for_closures_satisfied statics vars' v slot functions
        value_slots closures)
  ∧ (∀ (entry : closures_entry) (vars vars' : env) (v : value)
       (slot : function_slot) (functions : list (function_slot * code_id))
       (value_slots : list (value_slot * value)),
      agree vars vars' (free_variables_of_closures_entry entry) ->
      closures_entry_satisfied statics vars v slot functions value_slots
        entry ->
      closures_entry_satisfied statics vars' v slot functions value_slots
        entry)
  ∧ (∀ (extension : env_extension) (vars vars' : env),
      agree vars vars' (free_variables_of_env_extension extension) ->
      env_extension_satisfied statics vars extension ->
      env_extension_satisfied statics vars' extension).
Proof.
  apply types_induction.
  - (* Type_value *)
    intros ty Hhead vars vars' v Hagree. autorewrite with type_satisfied.
    apply (agree_descr _ _ _ _ _ _ _ _ Hagree).
    intros h ->. exact (Hhead vars vars' v Hagree).
  - (* Type_naked_immediate *)
    intros ty vars vars' v Hagree. autorewrite with type_satisfied.
    apply (agree_descr _ _ _ _ _ _ _ _ Hagree).
    intros head ->. simpl in Hagree.
    intros [i [Hv [Hnumbers Hrelations]]]. exists i.
    split; [ exact Hv | ]. split; [ exact Hnumbers | ].
    intros relation n Hin. destruct (Hrelations relation n Hin) as [w [Hw H]].
    exists w. split; [ | exact H ]. unfold value_of_name in *.
    rewrite <- Hw. symmetry. apply agree_eval_simple.
    exact (agree_flat_map _ _ _ _ (relation, n) Hagree Hin).
  - intros k ty vars vars' v Hagree. autorewrite with type_satisfied.
    apply (agree_descr _ _ _ _ _ _ _ _ Hagree). auto.
  - intros ty vars vars' v Hagree. autorewrite with type_satisfied.
    apply (agree_descr _ _ _ _ _ _ _ _ Hagree). auto.
  - intros ty vars vars' v Hagree. autorewrite with type_satisfied.
    apply (agree_descr _ _ _ _ _ _ _ _ Hagree). auto.
  - (* Head_of_kind_value *)
    intros non_null is_null Hnon_null vars vars' v Hagree.
    simpl in Hagree. apply agree_app in Hagree as [Hagree_head Hagree_null].
    autorewrite with type_satisfied.
    intros [[Hnull His_null] | [Hnot_null [Hhead His_null]]].
    + left. split; [ exact Hnull | ].
      destruct is_null as [ | is_null]; [ exact His_null | ].
      exact (agree_variable_is _ _ _ _ Hagree_null His_null).
    + right. split; [ exact Hnot_null | ]. split.
      * destruct non_null as [ | head | ]; auto.
        exact (Hnon_null vars vars' v Hagree_head Hhead).
      * destruct is_null as [ | is_null]; [ exact His_null | ].
        exact (agree_variable_is _ _ _ _ Hagree_null His_null).
  - (* Variant *)
    intros is_int immediates get_tag blocks extensions is_unique Himmediates
      Hblocks Hextensions vars vars' v Hagree.
    simpl in Hagree.
    apply agree_app in Hagree as [Hagree_is_int Hagree].
    apply agree_app in Hagree as [Hagree_immediates Hagree].
    apply agree_app in Hagree as [Hagree_get_tag Hagree].
    apply agree_app in Hagree as [Hagree_blocks Hagree_extensions].
    autorewrite with type_satisfied.
    intros [[i [Hv [His_int [Himmediate Hextension]]]]
           | [tag [fields [Hblock [His_int [Hget_tag [Hrow Hextension]]]]]]].
    + left. exists i. split; [ exact Hv | ].
      split; [ exact (agree_variable_is _ _ _ _ Hagree_is_int His_int) | ].
      split.
      * destruct immediates as [ty | ]; [ | exact I ].
        exact (Himmediates vars vars' _ Hagree_immediates Himmediate).
      * destruct extensions as [ | when_immediate when_block]; [ exact I | ].
        apply agree_app in Hagree_extensions as [Hagree_immediate _].
        exact (proj1 Hextensions vars vars' Hagree_immediate Hextension).
    + right. exists tag, fields. split; [ exact Hblock | ].
      split; [ exact (agree_variable_is _ _ _ _ Hagree_is_int His_int) | ].
      split; [ exact (agree_variable_is _ _ _ _ Hagree_get_tag Hget_tag) | ].
      split.
      * destruct blocks as [blocks | ]; [ | exact I ].
        exact (Hblocks vars vars' tag fields Hagree_blocks Hrow).
      * destruct extensions as [ | when_immediate when_block]; [ exact I | ].
        apply agree_app in Hagree_extensions as [_ Hagree_block].
        exact (proj2 Hextensions vars vars' Hagree_block Hextension).
  - (* Mutable_block *)
    intros alloc_mode vars vars' v _. autorewrite with type_satisfied. auto.
  - (* Boxed_number *)
    intros k contents alloc_mode Hcontents vars vars' v Hagree.
    autorewrite with type_satisfied.
    intros [c [Hboxed [Hkind Hc]]]. exists c.
    split; [ exact Hboxed | ]. split; [ exact Hkind | ].
    exact (Hcontents vars vars' _ Hagree Hc).
  - (* Closures *)
    intros by_function_slot alloc_mode Hclosures vars vars' v Hagree.
    autorewrite with type_satisfied.
    intros [slot [functions [value_slots [Hclosure Hrow]]]].
    exists slot, functions, value_slots. split; [ exact Hclosure | ].
    exact (Hclosures vars vars' v slot functions value_slots Hagree Hrow).
  - (* String *)
    intros strs vars vars' v _. autorewrite with type_satisfied. auto.
  - (* Row_like_for_blocks *)
    intros known_tags other_tags alloc_mode Hknown Hother vars vars' tag
      fields Hagree.
    simpl in Hagree. apply agree_app in Hagree as [Hagree_known Hagree_other].
    rewrite !row_like_for_blocks_find_iff.
    assert (Hcase :
      ∀ case : row_like_block_case,
        P_block_case
          (fun t =>
             ∀ (vars vars' : env) (v : value),
               agree vars vars' (free_variables t) ->
               type_satisfied statics vars v t ->
               type_satisfied statics vars' v t)
          (fun extension =>
             ∀ vars vars' : env,
               agree vars vars' (free_variables_of_env_extension extension) ->
               env_extension_satisfied statics vars extension ->
               env_extension_satisfied statics vars' extension)
          case ->
        agree vars vars'
          (free_variables_of_block_case free_variables
             free_variables_of_env_extension case) ->
        row_like_block_case_satisfied statics vars tag fields case ->
        row_like_block_case_satisfied statics vars' tag fields case).
    { intros case [Htypes Hextension] Hagree [Hindex [Hfields Hext]].
      apply agree_app in Hagree as [Hagree_fields Hagree_extension].
      split; [ exact Hindex | ].
      split; [ | exact (Hextension vars vars' Hagree_extension Hext) ].
      apply (fields_satisfied_impl _ _ _ _) with (2 := Hfields).
      intros ty Hin v.
      exact (Htypes ty Hin vars vars' v
               (agree_flat_map _ _ _ _ ty Hagree_fields Hin)). }
    destruct (find_tag tag known_tags) as [[case | ] | ] eqn:Hfind.
    + apply find_tag_in in Hfind. apply (Hcase case (Hknown tag case Hfind)).
      exact (agree_flat_map _ _ _ _ _ Hagree_known Hfind).
    + auto.
    + destruct other_tags as [case | ]; [ | auto ].
      exact (Hcase case Hother Hagree_other).
  - (* Row_like_for_closures *)
    intros known_closures Hknown vars vars' v slot functions value_slots
      Hagree.
    rewrite !row_like_for_closures_lookup_iff.
    intros [case [Hlookup [Hindex [Hentry Hextension]]]]. exists case.
    split; [ exact Hlookup | ]. apply lookup_in in Hlookup.
    destruct (Hknown slot case Hlookup) as [IHentry IHextension].
    simpl in Hagree.
    apply (agree_flat_map _ _ _ _ _ Hagree) in Hlookup. simpl in Hlookup.
    apply agree_app in Hlookup as [Hagree_entry Hagree_extension].
    split; [ exact Hindex | ].
    split; [ | exact (IHextension vars vars' Hagree_extension Hextension) ].
    exact (IHentry vars vars' v slot functions value_slots Hagree_entry
             Hentry).
  - (* Closures_entry *)
    intros function_types closure_types value_slot_types Hclosures Hslots
      vars vars' v slot functions value_slots Hagree.
    simpl in Hagree.
    apply agree_app in Hagree as [Hagree_closures Hagree_slots].
    rewrite !closures_entry_lookup_iff.
    intros [Hfunctions [Hclosure_types Hvalue_slots]].
    split; [ exact Hfunctions | ]. split.
    + intros g ty closure Hlookup Hproject.
      pose proof (lookup_in _ _ _ Hlookup) as Hin.
      apply (Hclosures g ty Hin vars vars').
      * exact (agree_flat_map _ _ _ _ _ Hagree_closures Hin).
      * exact (Hclosure_types g ty closure Hlookup Hproject).
    + intros w ty contents Hlookup Hcontents.
      pose proof (lookup_in _ _ _ Hlookup) as Hin.
      apply (Hslots w ty Hin vars vars').
      * exact (agree_flat_map _ _ _ _ _ Hagree_slots Hin).
      * exact (Hvalue_slots w ty contents Hlookup Hcontents).
  - (* Env_extension *)
    intros equations Hvariables Hsymbols vars vars' Hagree.
    simpl in Hagree.
    apply agree_app in Hagree as [Hagree_variables Hagree_symbols].
    rewrite !env_extension_lookup_iff.
    intros Hequations n ty Hlookup.
    destruct (Hequations n ty Hlookup) as [v [Hv Hty]]. exists v.
    destruct n as [x | s]; simpl in Hlookup.
    + pose proof (lookup_in _ _ _ Hlookup) as Hin.
      pose proof (agree_flat_map _ _ _ _ _ Hagree_variables Hin) as Hagree.
      simpl in Hagree. split.
      * unfold value_of_name in *. simpl in *.
        rewrite <- (Hagree x (or_introl eq_refl)). exact Hv.
      * apply (Hvariables x ty Hin vars vars'); [ | exact Hty ].
        intros y Hy. apply Hagree. right. exact Hy.
    + pose proof (lookup_in _ _ _ Hlookup) as Hin. split; [ exact Hv | ].
      apply (Hsymbols s ty Hin vars vars'); [ | exact Hty ].
      exact (agree_flat_map _ _ _ _ _ Hagree_symbols Hin).
Qed.

Lemma agree_sym (vars vars' : env) (xs : list variable) :
  agree vars vars' xs -> agree vars' vars xs.
Proof. intros Hagree x Hin. symmetry. exact (Hagree x Hin). Qed.

Theorem type_satisfied_coincide : type_satisfied_coincide_statement.
Proof.
  intros statics vars vars' v t Hagree.
  destruct (type_satisfied_agree_all statics) as [Htype _].
  split; apply Htype; [ exact Hagree | exact (agree_sym _ _ _ Hagree) ].
Qed.

Theorem env_extension_satisfied_coincide
  : env_extension_satisfied_coincide_statement.
Proof.
  intros statics vars vars' extension Hagree.
  destruct (type_satisfied_agree_all statics)
    as [_ [_ [_ [_ [_ [_ Hextension]]]]]].
  split; apply Hextension; [ exact Hagree | exact (agree_sym _ _ _ Hagree) ].
Qed.

Theorem type_satisfied_bind : type_satisfied_bind_statement.
Proof.
  intros statics vars x w v t Hfresh. apply type_satisfied_coincide.
  intros y Hin. simpl.
  destruct (Pos.eqb_spec y x) as [-> | _]; [ contradiction | reflexivity ].
Qed.

Theorem unknown_is_top : unknown_is_top_statement.
Proof.
  intros statics vars v t Hsatisfied. apply unknown_satisfied.
  exact (type_satisfied_kind _ _ _ _ Hsatisfied).
Qed.

(* ======================================================================== *)
(* Types with no value, and heads with no value in common                   *)
(* ======================================================================== *)

Theorem is_obviously_bottom_satisfied
  : is_obviously_bottom_satisfied_statement.
Proof.
  intros statics vars v t Hbottom.
  destruct t as [ty | ty | k ty | ty | ty]; autorewrite with type_satisfied;
    destruct ty as [ | d | ]; try discriminate; intros [].
Qed.

Theorem is_obviously_unknown_satisfied
  : is_obviously_unknown_satisfied_statement.
Proof.
  intros statics vars v t Hunknown.
  destruct t as [ty | ty | k ty | ty | ty]; autorewrite with type_satisfied;
    destruct ty as [ | d | ]; try discriminate; reflexivity.
Qed.

Theorem row_like_for_blocks_is_bottom_satisfied
  : row_like_for_blocks_is_bottom_satisfied_statement.
Proof.
  intros statics vars tag fields [known_tags other_tags alloc_mode] Hbottom.
  rewrite row_like_for_blocks_find_iff.
  destruct known_tags as [ | case known_tags]; [ | discriminate ].
  destruct other_tags as [case | ]; [ discriminate | ]. simpl. auto.
Qed.

Theorem heads_compatible_satisfied : heads_compatible_satisfied_statement.
Proof.
  intros statics vars v head head' Hhead Hhead'.
  pose proof (observations_disjoint statics v) as [Hblock [Hclosure Hboxed]].
  assert (Hclosure_in_set :
    ∀ closure, closure_in_set statics v = Some closure ->
               closure_of statics v <> None).
  { unfold closure_in_set. intros closure.
    destruct (closure_of statics v); [ discriminate | discriminate ]. }
  destruct head as [is_int immediates get_tag blocks extensions is_unique
                   | alloc_mode | k contents alloc_mode
                   | by_function_slot alloc_mode | strs];
    destruct head' as [is_int' immediates' get_tag' blocks' extensions'
                         is_unique'
                      | alloc_mode' | k' contents' alloc_mode'
                      | by_function_slot' alloc_mode' | strs'];
    autorewrite with type_satisfied in Hhead, Hhead'; simpl; auto;
    repeat
      match goal with
      | H : False |- _ => destruct H
      | H : _ ∨ _ |- _ => destruct H
      | H : ∃ _, _ |- _ => destruct H
      | H : _ ∧ _ |- _ => destruct H
      end;
    subst; try discriminate;
    repeat
      match goal with
      | H : block_of statics v = Some _ |- _ =>
        assert (block_of statics v <> None) by (rewrite H; discriminate);
        clear H
      | H : boxed_number_of statics v = Some ?c,
        H' : boxed_number_of statics v = Some ?c' |- _ =>
        rewrite H in H'; injection H' as <-
      | H : boxed_number_of statics v = Some _ |- _ =>
        assert (boxed_number_of statics v <> None)
          by (rewrite H; discriminate);
        clear H
      | H : string_of statics v = Some _ |- _ =>
        assert (string_of statics v <> None) by (rewrite H; discriminate);
        clear H
      | H : closure_in_set statics v = Some _ |- _ =>
        apply Hclosure_in_set in H
      end;
    try congruence; try tauto.
Qed.
