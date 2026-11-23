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


(* Proofs of the statements of FlambdaTypeMeaningHeapSpec.v. Nothing here
   needs review.

   [type_satisfied] and [type_satisfied_in] are one text but for the
   case [Mutable_block]. [type_satisfied_over] here is that text with
   the case left open: it takes what a value must be to have the type
   [Mutable_block]. Each of the two meanings is it, by computation, at
   one choice of that. So what is proved once of [type_satisfied_over]
   ([type_satisfied_over_grows]) gives the statements that go from one
   meaning to the other, from a heap to a heap that it evolves to, and
   from a static environment to one that it grows to. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaPrimitiveModel FlambdaHeapSpec
  FlambdaSemanticsSpec FlambdaWellFormedSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaTypeMeaningHeapSpec.
Import ListNotations.

(* ======================================================================== *)
(* The meaning, with the case [Mutable_block] left open                     *)
(* ======================================================================== *)

Section Type_satisfied_over.

(* What a value must be to have a type [Mutable_block]. *)
Variable mutable_block_is : value -> Prop.
Variable statics : static_env.
Variable vars : env.

Fixpoint type_satisfied_over (v : value) (t : flambda_type) {struct t}
    : Prop :=
  match t with
  | Type_value ty =>
    descr_satisfied vars Value (head_of_kind_value_satisfied_over v) v ty
  | Type_naked_immediate ty =>
    descr_satisfied vars (Naked_number Kind_naked_immediate)
      (head_of_kind_naked_immediate_satisfied statics vars v) v ty
  | Type_naked_number k ty =>
    descr_satisfied vars (Naked_number k) (naked_numbers_satisfied k v) v ty
  | Type_rec_info ty =>
    descr_satisfied vars Rec_info (fun _ => kind_of_value v = Rec_info) v ty
  | Type_region ty =>
    descr_satisfied vars Region (fun _ => kind_of_value v = Region) v ty
  end

with head_of_kind_value_satisfied_over (v : value)
    (head : head_of_kind_value) {struct head} : Prop :=
  match head with
  | Head_of_kind_value non_null is_null =>
    (v = Value_const Null
     ∧ match is_null with
       | Not_null => False
       | Maybe_null is_null => variable_is vars is_null 1
       end)
    ∨ (v <> Value_const Null
       ∧ match non_null with
         | Unknown => kind_of_value v = Value
         | Bottom => False
         | Ok head => head_of_kind_value_non_null_satisfied_over v head
         end
       ∧ match is_null with
         | Not_null => True
         | Maybe_null is_null => variable_is vars is_null 0
         end)
  end

with head_of_kind_value_non_null_satisfied_over (v : value)
    (head : head_of_kind_value_non_null) {struct head} : Prop :=
  match head with
  | Variant is_int immediates get_tag blocks extensions _ =>
    (∃ i : Z,
      v = Value_const (Tagged_immediate i)
      ∧ variable_is vars is_int 1
      ∧ match immediates with
        | Or_unknown.Unknown => True
        | Or_unknown.Known ty =>
          type_satisfied_over (Value_const (Naked_immediate i)) ty
        end
      ∧ match extensions with
        | No_extensions => True
        | Ext when_immediate _ => env_extension_satisfied_over when_immediate
        end)
    ∨ (∃ (tag : Z) (fields : list value),
        block_of statics v = Some (tag, fields)
        ∧ variable_is vars is_int 0
        ∧ variable_is vars get_tag tag
        ∧ match blocks with
          | Or_unknown.Unknown => True
          | Or_unknown.Known blocks =>
            row_like_for_blocks_satisfied_over tag fields blocks
          end
        ∧ match extensions with
          | No_extensions => True
          | Ext _ when_block => env_extension_satisfied_over when_block
          end)
  | Mutable_block _ => mutable_block_is v
  | Boxed_number k contents _ =>
    ∃ c : const,
      boxed_number_of statics v = Some c
      ∧ kind_of_const c = unboxed_kind k
      ∧ type_satisfied_over (Value_const c) contents
  | Closures by_function_slot _ =>
    ∃ (slot : function_slot) (functions : list (function_slot * code_id))
      (value_slots : list (value_slot * value)),
      closure_in_set statics v = Some (slot, functions, value_slots)
      ∧ row_like_for_closures_satisfied_over v slot functions value_slots
          by_function_slot
  | String strs =>
    ∃ bytes : list Z, string_of statics v = Some bytes ∧ bytes ∈ strs
  end

with row_like_for_blocks_satisfied_over (tag : Z) (fields : list value)
    (blocks : row_like_for_blocks) {struct blocks} : Prop :=
  match blocks with
  | Row_like_for_blocks known_tags other_tags _ =>
    Keyed.at_binding Z.eqb
      (fun case =>
         match case with
         | Or_unknown.Unknown => True
         | Or_unknown.Known case =>
           block_case_satisfied type_satisfied_over
             env_extension_satisfied_over tag fields case
         end)
      tag known_tags
    ∧ (Keyed.lookup Z.eqb tag known_tags = None ->
       match other_tags with
       | Or_bottom.Bottom => False
       | Or_bottom.Ok case =>
         block_case_satisfied type_satisfied_over
           env_extension_satisfied_over tag fields case
       end)
  end

with row_like_for_closures_satisfied_over (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (closures : row_like_for_closures) {struct closures} : Prop :=
  match closures with
  | Row_like_for_closures known_closures =>
    is_bound slot known_closures = true
    ∧ at_binding
        (closures_case_satisfied
           (closures_entry_satisfied_over v slot functions value_slots)
           env_extension_satisfied_over functions value_slots)
        slot known_closures
  end

with closures_entry_satisfied_over (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value)) (entry : closures_entry)
    {struct entry} : Prop :=
  match entry with
  | Closures_entry function_types closure_types value_slot_types =>
    (∀ (g : function_slot) (function_type : function_type) (code : code_id),
      lookup g function_types = Some (Or_unknown.Known function_type) ->
      lookup g functions = Some code ->
      code = function_type_code_id function_type)
    ∧ for_all_bindings
        (fun g ty =>
           ∀ closure : value,
             project_function_slot statics slot g v = Some closure ->
             type_satisfied_over closure ty)
        closure_types
    ∧ for_all_bindings
        (fun w ty =>
           ∀ contents : value,
             lookup w value_slots = Some contents ->
             type_satisfied_over contents ty)
        value_slot_types
  end

with env_extension_satisfied_over (extension : env_extension)
    {struct extension} : Prop :=
  match extension with
  | Env_extension equations =>
    Keyed.for_all_bindings name_eqb
      (fun n ty =>
         ∃ v : value,
           value_of_name vars n = Some v ∧ type_satisfied_over v ty)
      equations
  end.

End Type_satisfied_over.

(* The two meanings are it. *)

Lemma type_satisfied_in_over (statics : static_env) (h : heap) (vars : env)
    (v : value) (t : flambda_type) :
  type_satisfied_in statics h vars v t
  = type_satisfied_over (mutable_block_at h) statics vars v t.
Proof. reflexivity. Qed.

Lemma env_extension_satisfied_in_over (statics : static_env) (h : heap)
    (vars : env) (extension : env_extension) :
  env_extension_satisfied_in statics h vars extension
  = env_extension_satisfied_over (mutable_block_at h) statics vars extension.
Proof. reflexivity. Qed.

Lemma type_satisfied_over_false (statics : static_env) (vars : env)
    (v : value) (t : flambda_type) :
  type_satisfied statics vars v t
  = type_satisfied_over (fun _ => False) statics vars v t.
Proof. reflexivity. Qed.

Lemma env_extension_satisfied_over_false (statics : static_env) (vars : env)
    (extension : env_extension) :
  env_extension_satisfied statics vars extension
  = env_extension_satisfied_over (fun _ => False) statics vars extension.
Proof. reflexivity. Qed.

(* ======================================================================== *)
(* When more values have the type [Mutable_block], and the static           *)
(* environment grows                                                        *)
(* ======================================================================== *)

Section Grows.

Variables mutable_block_is mutable_block_is' : value -> Prop.
Hypothesis Hmutable : ∀ v : value, mutable_block_is v -> mutable_block_is' v.
Variables statics statics' : static_env.
Hypothesis Hextend : statics_extend statics statics'.
Variable vars : env.

Lemma type_satisfied_over_grows_all :
  (∀ (t : flambda_type) (v : value),
    type_satisfied_over mutable_block_is statics vars v t ->
    type_satisfied_over mutable_block_is' statics' vars v t)
  ∧ (∀ (head : head_of_kind_value) (v : value),
      head_of_kind_value_satisfied_over mutable_block_is statics vars v head ->
      head_of_kind_value_satisfied_over mutable_block_is' statics' vars v
        head)
  ∧ (∀ (head : head_of_kind_value_non_null) (v : value),
      head_of_kind_value_non_null_satisfied_over mutable_block_is statics
        vars v head ->
      head_of_kind_value_non_null_satisfied_over mutable_block_is' statics'
        vars v head)
  ∧ (∀ (blocks : row_like_for_blocks) (tag : Z) (fields : list value),
      row_like_for_blocks_satisfied_over mutable_block_is statics vars tag
        fields blocks ->
      row_like_for_blocks_satisfied_over mutable_block_is' statics' vars tag
        fields blocks)
  ∧ (∀ (closures : row_like_for_closures) (v : value) (slot : function_slot)
       (functions : list (function_slot * code_id))
       (value_slots : list (value_slot * value)),
      closure_in_set statics v = Some (slot, functions, value_slots) ->
      row_like_for_closures_satisfied_over mutable_block_is statics vars v
        slot functions value_slots closures ->
      row_like_for_closures_satisfied_over mutable_block_is' statics' vars v
        slot functions value_slots closures)
  ∧ (∀ (entry : closures_entry) (v : value) (slot : function_slot)
       (functions : list (function_slot * code_id))
       (value_slots : list (value_slot * value)),
      closure_in_set statics v = Some (slot, functions, value_slots) ->
      closures_entry_satisfied_over mutable_block_is statics vars v slot
        functions value_slots entry ->
      closures_entry_satisfied_over mutable_block_is' statics' vars v slot
        functions value_slots entry)
  ∧ (∀ extension : env_extension,
      env_extension_satisfied_over mutable_block_is statics vars extension ->
      env_extension_satisfied_over mutable_block_is' statics' vars
        extension).
Proof.
  apply types_induction.
  - (* Type_value *)
    intros [ | [head | s] | ] Hhead v; simpl;
      [ auto | exact (Hhead v) | auto | auto ].
  - (* Type_naked_immediate *)
    intros [ | [head | s] | ] v; simpl; auto.
    intros [i [Hv [Hnumbers Hrelations]]]. exists i.
    split; [ exact Hv | ]. split; [ exact Hnumbers | ].
    intros relation n Hin. destruct (Hrelations relation n Hin) as [w [Hw H]].
    exists w. split; [ exact Hw | ].
    exact (relation_holds_extend _ _ Hextend _ _ _ H).
  - intros k ty v H. exact H.
  - intros ty v H. exact H.
  - intros ty v H. exact H.
  - (* Head_of_kind_value *)
    intros non_null is_null Hnon_null v. simpl.
    intros [Hnull | [Hnot_null [Hhead His_null]]]; [ left; exact Hnull | ].
    right. split; [ exact Hnot_null | ]. split; [ | exact His_null ].
    destruct non_null as [ | head | ];
      [ exact Hhead | exact (Hnon_null v Hhead) | exact Hhead ].
  - (* Variant *)
    intros is_int immediates get_tag blocks extensions is_unique Himmediates
      Hblocks Hextensions v. simpl.
    intros [[i [Hv [His_int [Himmediate Hextension]]]]
           | [tag [fields [Hblock [His_int [Hget_tag [Hrow Hextension]]]]]]].
    + left. exists i. split; [ exact Hv | ]. split; [ exact His_int | ].
      split.
      * destruct immediates as [ty | ];
          [ exact (Himmediates _ Himmediate) | exact I ].
      * destruct extensions as [ | when_immediate when_block]; [ exact I | ].
        exact (proj1 Hextensions Hextension).
    + right. exists tag, fields.
      split; [ exact (block_of_extend _ _ Hextend _ _ Hblock) | ].
      split; [ exact His_int | ]. split; [ exact Hget_tag | ]. split.
      * destruct blocks as [blocks | ];
          [ exact (Hblocks _ _ Hrow) | exact I ].
      * destruct extensions as [ | when_immediate when_block]; [ exact I | ].
        exact (proj2 Hextensions Hextension).
  - (* Mutable_block *)
    intros alloc_mode v. simpl. exact (Hmutable v).
  - (* Boxed_number *)
    intros k contents alloc_mode Hcontents v. simpl.
    intros [c [Hboxed [Hkind Hc]]]. exists c.
    split; [ exact (boxed_number_of_extend _ _ Hextend _ _ Hboxed) | ].
    split; [ exact Hkind | exact (Hcontents _ Hc) ].
  - (* Closures *)
    intros by_function_slot alloc_mode Hclosures v. simpl.
    intros [slot [functions [value_slots [Hclosure Hrow]]]].
    exists slot, functions, value_slots.
    split; [ exact (closure_in_set_extend _ _ Hextend _ _ Hclosure) | ].
    exact (Hclosures v slot functions value_slots Hclosure Hrow).
  - (* String *)
    intros strs v. simpl.
    intros [bytes [Hstring Hin]]. exists bytes.
    split; [ exact (string_of_extend _ _ Hextend _ _ Hstring) | exact Hin ].
  - (* Row_like_for_blocks *)
    intros known_tags other_tags alloc_mode Hknown Hother tag fields. simpl.
    assert (Hcase :
      ∀ case : row_like_block_case,
        P_block_case
          (fun t =>
             ∀ v : value,
               type_satisfied_over mutable_block_is statics vars v t ->
               type_satisfied_over mutable_block_is' statics' vars v t)
          (fun extension =>
             env_extension_satisfied_over mutable_block_is statics vars
               extension ->
             env_extension_satisfied_over mutable_block_is' statics' vars
               extension)
          case ->
        block_case_satisfied
          (type_satisfied_over mutable_block_is statics vars)
          (env_extension_satisfied_over mutable_block_is statics vars) tag
          fields case ->
        block_case_satisfied
          (type_satisfied_over mutable_block_is' statics' vars)
          (env_extension_satisfied_over mutable_block_is' statics' vars) tag
          fields case).
    { intros case [Htypes Hextension] [Hindex [Hfields Hext]].
      split; [ exact Hindex | ]. split; [ | exact (Hextension Hext) ].
      exact (fields_satisfied_impl _ _ _ _ Htypes Hfields). }
    intros [Hat Hnone]. split.
    + apply (proj2 (keyed_at_binding_lookup Z Z.eqb _ _ _ _)).
      intros case Hlookup.
      pose proof
        (proj1 (keyed_at_binding_lookup Z Z.eqb _ _ _ _) Hat case Hlookup)
        as Hsatisfied.
      destruct case as [case | ]; [ | exact I ].
      apply Hcase; [ | exact Hsatisfied ].
      exact (Hknown tag case (keyed_lookup_in Z.eqb Z.eqb_eq _ _ _ Hlookup)).
    + intros Hlookup. specialize (Hnone Hlookup).
      destruct other_tags as [case | ];
        [ exact (Hcase case Hother Hnone) | exact Hnone ].
  - (* Row_like_for_closures *)
    intros known_closures Hknown v slot functions value_slots Hclosure.
    simpl. intros [Hbound Hat]. split; [ exact Hbound | ].
    apply (proj2 (at_binding_lookup _ _ _ _)). intros case Hlookup.
    destruct (proj1 (at_binding_lookup _ _ _ _) Hat case Hlookup)
      as [Hindex [Hentry Hextension]].
    destruct (Hknown slot case (lookup_in _ _ _ Hlookup))
      as [IHentry IHextension].
    split; [ exact Hindex | ]. split; [ | exact (IHextension Hextension) ].
    exact (IHentry v slot functions value_slots Hclosure Hentry).
  - (* Closures_entry *)
    intros function_types closure_types value_slot_types Hclosures Hslots v
      slot functions value_slots Hclosure. simpl.
    intros [Hfunctions [Hclosure_types Hvalue_slots]].
    split; [ exact Hfunctions | ]. split.
    + apply (proj2 (for_all_bindings_lookup _ _ _)).
      intros g ty Hlookup closure Hproject.
      rewrite (project_function_slot_extend _ _ Hextend _ _ _ _ Hclosure)
        in Hproject.
      apply (Hclosures g ty (lookup_in _ _ _ Hlookup)).
      exact
        (proj1 (for_all_bindings_lookup _ _ _) Hclosure_types g ty Hlookup
           closure Hproject).
    + apply (proj2 (for_all_bindings_lookup _ _ _)).
      intros w ty Hlookup contents Hcontents.
      apply (Hslots w ty (lookup_in _ _ _ Hlookup)).
      exact
        (proj1 (for_all_bindings_lookup _ _ _) Hvalue_slots w ty Hlookup
           contents Hcontents).
  - (* Env_extension *)
    intros equations Htypes. simpl. intros Hequations.
    apply
      (proj2 (keyed_for_all_bindings_lookup name name_eqb name_eqb_eq _ _ _)).
    intros n ty Hlookup.
    destruct
      (proj1 (keyed_for_all_bindings_lookup name name_eqb name_eqb_eq _ _ _)
         Hequations n ty Hlookup)
      as [v [Hv Hty]].
    exists v. split; [ exact Hv | ].
    exact
      (Htypes n ty (keyed_lookup_in name_eqb name_eqb_eq _ _ _ Hlookup) v Hty).
Qed.

End Grows.

Lemma type_satisfied_over_grows
    (mutable_block_is mutable_block_is' : value -> Prop)
    (statics statics' : static_env) (vars : env) (v : value)
    (t : flambda_type) :
  (∀ v : value, mutable_block_is v -> mutable_block_is' v) ->
  statics_extend statics statics' ->
  type_satisfied_over mutable_block_is statics vars v t ->
  type_satisfied_over mutable_block_is' statics' vars v t.
Proof.
  intros Hmutable Hextend.
  exact
    (proj1 (type_satisfied_over_grows_all _ _ Hmutable _ _ Hextend vars) t v).
Qed.

Lemma env_extension_satisfied_over_grows
    (mutable_block_is mutable_block_is' : value -> Prop)
    (statics statics' : static_env) (vars : env)
    (extension : env_extension) :
  (∀ v : value, mutable_block_is v -> mutable_block_is' v) ->
  statics_extend statics statics' ->
  env_extension_satisfied_over mutable_block_is statics vars extension ->
  env_extension_satisfied_over mutable_block_is' statics' vars extension.
Proof.
  intros Hmutable Hextend.
  destruct (type_satisfied_over_grows_all _ _ Hmutable _ _ Hextend vars)
    as [_ [_ [_ [_ [_ [_ Hextension]]]]]].
  exact (Hextension extension).
Qed.

Lemma statics_extend_itself (statics : static_env) :
  statics_extend statics statics.
Proof. split; auto. Qed.

(* ======================================================================== *)
(* A block made [Mutable]                                                   *)
(* ======================================================================== *)

Lemma mutable_block_at_kind (h : heap) (v : value) :
  mutable_block_at h v -> kind_of_value v = Value ∧ v <> Value_const Null.
Proof.
  intros [tag [fields Hcell]].
  destruct v; try discriminate Hcell.
  split; [ reflexivity | discriminate ].
Qed.

Lemma mutable_block_at_empty_heap (v : value) :
  ~ mutable_block_at empty_heap v.
Proof. intros [tag [fields Hcell]]. destruct v; discriminate Hcell. Qed.

Lemma mutable_block_at_evolves (h h' : heap) (v : value) :
  heap_evolves h h' -> mutable_block_at h v -> mutable_block_at h' v.
Proof.
  intros [Hblocks _] [tag [fields Hcell]].
  destruct v; try discriminate Hcell. simpl in Hcell.
  destruct (Hblocks _ _ _ _ Hcell) as [fields' [Hcell' _]].
  exists tag, fields'. exact Hcell'.
Qed.

(* ======================================================================== *)
(* The type [Mutable_block]                                                 *)
(* ======================================================================== *)

Theorem mutable_block_satisfied_in : mutable_block_satisfied_in_statement.
Proof.
  intros statics h vars v alloc_mode. simpl. split.
  - intros [[_ []] | [_ [Hat _]]]. exact Hat.
  - intros Hat. right.
    split; [ exact (proj2 (mutable_block_at_kind _ _ Hat)) | ].
    split; [ exact Hat | exact I ].
Qed.

Theorem example_mutable_block : example_mutable_block_statement.
Proof.
  unfold example_mutable_block_statement.
  repeat split.
  - apply mutable_block_satisfied_in.
    exists 0%Z, [Value_const (Tagged_immediate 0%Z)]. reflexivity.
  - intros Hhas. apply mutable_block_satisfied_in in Hhas.
    destruct Hhas as [tag [fields Hcell]]. discriminate Hcell.
  - intros Hhas. apply mutable_block_satisfied_in in Hhas.
    destruct Hhas as [tag [fields Hcell]]. discriminate Hcell.
  - intros Hhas. apply mutable_block_satisfied_in in Hhas.
    destruct Hhas as [tag [fields Hcell]]. discriminate Hcell.
  - compute. right. split; [ discriminate | ]. split; [ | exact I ].
    right. exists 0%Z, [Value_location 1%positive].
    repeat split; try discriminate.
    right. split; [ discriminate | ]. split; [ | exact I ].
    exists 0%Z, [Value_const (Tagged_immediate 0%Z)]. reflexivity.
  - compute.
    intros [[_ []] | [_ [[[i [Hv _]] | [tag [fields [Hblock Hrest]]]] _]]];
      [ discriminate Hv | ].
    injection Hblock as <- <-.
    destruct Hrest as [_ [_ [[[Hcase _] _] _]]].
    destruct (Hcase eq_refl) as [_ [[[[_ []] | [_ [Hat _]]] _] _]].
    destruct Hat as [tag [fields Hat]]. discriminate Hat.
Qed.

(* ======================================================================== *)
(* This meaning and that of FlambdaTypeMeaningSpec.v                        *)
(* ======================================================================== *)

Theorem type_satisfied_in_weakens : type_satisfied_in_weakens_statement.
Proof.
  intros statics h vars v t.
  rewrite type_satisfied_over_false, type_satisfied_in_over.
  apply type_satisfied_over_grows;
    [ intros w [] | apply statics_extend_itself ].
Qed.

Theorem env_extension_satisfied_in_weakens
  : env_extension_satisfied_in_weakens_statement.
Proof.
  intros statics h vars extension.
  rewrite env_extension_satisfied_over_false, env_extension_satisfied_in_over.
  apply env_extension_satisfied_over_grows;
    [ intros w [] | apply statics_extend_itself ].
Qed.

Theorem type_satisfied_in_empty_heap
  : type_satisfied_in_empty_heap_statement.
Proof.
  intros statics vars v t. split.
  - rewrite type_satisfied_over_false, type_satisfied_in_over.
    apply type_satisfied_over_grows;
      [ exact mutable_block_at_empty_heap | apply statics_extend_itself ].
  - apply type_satisfied_in_weakens.
Qed.

Theorem env_extension_satisfied_in_empty_heap
  : env_extension_satisfied_in_empty_heap_statement.
Proof.
  intros statics vars extension. split.
  - rewrite env_extension_satisfied_over_false,
      env_extension_satisfied_in_over.
    apply env_extension_satisfied_over_grows;
      [ exact mutable_block_at_empty_heap | apply statics_extend_itself ].
  - apply env_extension_satisfied_in_weakens.
Qed.

(* ======================================================================== *)
(* What the meaning of a type depends on                                    *)
(* ======================================================================== *)

Lemma head_non_null_in_kind (statics : static_env) (h : heap) (vars : env)
    (v : value) (head : head_of_kind_value_non_null) :
  head_of_kind_value_non_null_satisfied_in statics h vars v head ->
  kind_of_value v = Value ∧ v <> Value_const Null.
Proof.
  destruct head as [is_int immediates get_tag blocks extensions is_unique
                   | alloc_mode | k contents alloc_mode
                   | by_function_slot alloc_mode | strs]; simpl.
  - intros [[i [-> _]] | [tag [fields [Hblock _]]]];
      [ split; [ reflexivity | discriminate ] | ].
    split; [ exact (block_of_kind _ _ _ _ Hblock) | ].
    intros ->. discriminate.
  - apply mutable_block_at_kind.
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

Theorem type_satisfied_in_kind : type_satisfied_in_kind_statement.
Proof.
  intros statics h vars v t.
  assert (Hdescr :
    ∀ (head : Type) (k : flambda_kind) (head_satisfied : head -> Prop)
      (ty : type_descr head),
      (∀ hd : head, head_satisfied hd -> kind_of_value v = k) ->
      descr_satisfied vars k head_satisfied v ty -> kind_of_value v = k).
  { intros head k head_satisfied [ | [hd | s] | ] Hhead; simpl;
      [ auto | apply Hhead | intros [_ Hkind]; exact Hkind | intros [] ]. }
  destruct t as [ty | ty | k ty | ty | ty]; simpl; apply Hdescr.
  - intros [non_null is_null]. simpl.
    intros [[-> _] | [_ [Hnon_null _]]]; [ reflexivity | ].
    destruct non_null as [ | head | ];
      [ exact Hnon_null | | destruct Hnon_null ].
    exact (proj1 (head_non_null_in_kind _ _ _ _ _ Hnon_null)).
  - intros head [i [-> _]]. reflexivity.
  - intros numbers [c [n [-> [Hkind _]]]]. exact Hkind.
  - auto.
  - auto.
Qed.

Theorem type_satisfied_in_heap_evolves
  : type_satisfied_in_heap_evolves_statement.
Proof.
  intros statics h h' vars v t Hevolves.
  rewrite !type_satisfied_in_over.
  apply type_satisfied_over_grows; [ | apply statics_extend_itself ].
  intros w. exact (mutable_block_at_evolves _ _ _ Hevolves).
Qed.

Theorem env_extension_satisfied_in_heap_evolves
  : env_extension_satisfied_in_heap_evolves_statement.
Proof.
  intros statics h h' vars extension Hevolves.
  rewrite !env_extension_satisfied_in_over.
  apply env_extension_satisfied_over_grows; [ | apply statics_extend_itself ].
  intros w. exact (mutable_block_at_evolves _ _ _ Hevolves).
Qed.

Theorem type_satisfied_in_statics_extend
  : type_satisfied_in_statics_extend_statement.
Proof.
  intros statics statics' h vars v t Hextend.
  rewrite !type_satisfied_in_over.
  apply type_satisfied_over_grows; [ auto | exact Hextend ].
Qed.

Theorem env_extension_satisfied_in_statics_extend
  : env_extension_satisfied_in_statics_extend_statement.
Proof.
  intros statics statics' h vars extension Hextend.
  rewrite !env_extension_satisfied_in_over.
  apply env_extension_satisfied_over_grows; [ auto | exact Hextend ].
Qed.
