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


(* What a Flambda type means in a heap: the meaning of
   FlambdaTypeMeaningSpec.v with a value for the type [Mutable_block].

   This file is to be reviewed: [mutable_block_at], the one case of
   [type_satisfied_in] that is not that of [type_satisfied], and the
   statements. The rest of [type_satisfied_in] is the text of
   [type_satisfied], and [type_satisfied_in_empty_heap_statement] says
   that the two are the same where the heap has no cell.

   The compiler gives the type [Mutable_block] to a block that is made
   [Mutable] ([Simplify_variadic_primitive], [Simplify_static_const]).
   The type carries an allocation mode and nothing else: not the tag of
   the block, not its size, no field. In the machine such a block is a
   location, which the heap binds to a cell (FlambdaValueSpec.v, [cell]
   and [cell_of]; FlambdaHeapSpec.exec_heap_primitive, at
   [Make_block_with_identity]). [type_satisfied] takes no heap and gives
   [Mutable_block] no value ([mutable_block_satisfied_statement]). So
   where a name holds a block made [Mutable], no valuation satisfies a
   typing environment that gives the name that type, and what is stated
   of types with [type_satisfied] says nothing there.

   [type_satisfied_in statics h vars v t] is the meaning with the heap
   [h] beside the static environment. A value has a type [Mutable_block]
   if it is a location that [h] binds to a block made [Mutable], of any
   tag and with any fields ([mutable_block_at]). That case is the only
   one that looks at the heap itself. Every other case has the text of
   [type_satisfied]; where that text asks that another value have a
   type (a field of a block, a value slot of a closure, a name of an
   environment extension, and the others), it is asked in the heap. So
   a type that has a type [Mutable_block] inside depends on the heap
   too, as the last two parts of the example show.

   What the case [Mutable_block] reads of a cell is chosen so that no
   store makes it false: it reads that the cell is a block made
   [Mutable], and neither the tag nor a field. A step of a run leaves a
   heap that the heap before it evolves to
   (FlambdaHeapSpec.heap_evolves,
   FlambdaSemanticsSpec.step_evolves_statement): a cell that is bound
   stays bound and a block keeps its mutability, but a block made
   [Mutable] does not keep its fields. Two statements say what the
   meaning is kept by, each with every other argument the same: a
   value that has a type in a heap has it in every heap that the heap
   evolves to ([type_satisfied_in_heap_evolves_statement]), and in
   every static environment that the static environment grows to
   ([type_satisfied_in_statics_extend_statement]).

   What this meaning does not say:
   - Nothing of a run. The two statements above are of a heap or of a
     static environment that changes, with the valuation, the value
     and the type the same. In a run the valuation changes too, and
     what a type means may depend on it: a type that is an alias holds
     of the value that its name has in the valuation.
   - Nothing of the tag, the size or the fields of a block made
     [Mutable]: the compiler's type says nothing of them.
   - The allocation mode means nothing, as in [type_satisfied].
   - A location bound to a block made [Immutable_unique] has not the
     type, nor has one bound to an array ([Cell_array]): the compiler
     gives neither the type [Mutable_block]. A location that the heap
     does not bind has it not.
   - No symbol has the type: the model has no static block that is
     mutable (FlambdaModel.static_const), though the compiler gives the
     type to the symbol of one ([Simplify_static_const]).
   - A [Variant] type, and the relations [Is_int] and [Get_tag], are
     those of [type_satisfied]: they hold of no location. See the CR at
     [type_satisfied_in].

   The definition is written again and not changed in place, so that
   nothing that is stated with [type_satisfied] changes. A value that
   has a type by [type_satisfied] has it in every heap
   ([type_satisfied_in_weakens_statement]). This file is a step:
   [type_satisfied] is to take the heap, and this definition is then to
   go.

   The proofs are in FlambdaTypeMeaningHeapProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaPrimitiveModel FlambdaHeapSpec FlambdaSemanticsSpec
  FlambdaWellFormedSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec.
Import ListNotations.

(* ======================================================================== *)
(* A block made [Mutable]                                                   *)
(* ======================================================================== *)

(* The value is a location that the heap binds to a block made
   [Mutable]. Nothing is asked of the tag or of the fields. *)
Definition mutable_block_at (h : heap) (v : value) : Prop :=
  ∃ (tag : Z) (fields : list value),
    cell_of h v = Some (Cell_block Cell_mutable tag fields).

(* ======================================================================== *)
(* The meaning of a type in a heap                                          *)
(* ======================================================================== *)

Section Type_satisfied_in.

Variable statics : static_env.
Variable h : heap.
Variable vars : env.

(* A value has a type, in the heap [h]. It is [type_satisfied], whose
   comments and CRs are of this definition too, but for the case
   [Mutable_block]. *)
(* CR mshinwell: a [Variant] type holds of no location here, as in
   [type_satisfied]: a block is read through [block_of], which reads no
   heap. The compiler gives a block made [Immutable_unique] a [Variant]
   type with [is_unique], and that block is a location in the machine.
   So a typing environment that gives such a type to a name that holds
   such a block is satisfied by no valuation, as one with
   [Mutable_block] was. The relations [Is_int] and [Get_tag]
   ([relation_holds]) hold of no location either, though the machine
   answers both primitives on a cell
   (FlambdaHeapSpec.exec_unary_on_cell). Is the type [Mutable_block]
   enough for now, with a [Variant] type that holds of a cell to
   follow? What such a type may say of a field of a block made
   [Mutable] waits for the machine to keep the fields that are read as
   immutable. No decision has a number. *)
Fixpoint type_satisfied_in (v : value) (t : flambda_type) {struct t}
    : Prop :=
  match t with
  | Type_value ty =>
    descr_satisfied vars Value (head_of_kind_value_satisfied_in v) v ty
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

with head_of_kind_value_satisfied_in (v : value) (head : head_of_kind_value)
    {struct head} : Prop :=
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
         | Ok head => head_of_kind_value_non_null_satisfied_in v head
         end
       ∧ match is_null with
         | Not_null => True
         | Maybe_null is_null => variable_is vars is_null 0
         end)
  end

with head_of_kind_value_non_null_satisfied_in (v : value)
    (head : head_of_kind_value_non_null) {struct head} : Prop :=
  match head with
  | Variant is_int immediates get_tag blocks extensions _ =>
    (∃ i : Z,
      v = Value_const (Tagged_immediate i)
      ∧ variable_is vars is_int 1
      ∧ match immediates with
        | Or_unknown.Unknown => True
        | Or_unknown.Known ty =>
          type_satisfied_in (Value_const (Naked_immediate i)) ty
        end
      ∧ match extensions with
        | No_extensions => True
        | Ext when_immediate _ => env_extension_satisfied_in when_immediate
        end)
    ∨ (∃ (tag : Z) (fields : list value),
        block_of statics v = Some (tag, fields)
        ∧ variable_is vars is_int 0
        ∧ variable_is vars get_tag tag
        ∧ match blocks with
          | Or_unknown.Unknown => True
          | Or_unknown.Known blocks =>
            row_like_for_blocks_satisfied_in tag fields blocks
          end
        ∧ match extensions with
          | No_extensions => True
          | Ext _ when_block => env_extension_satisfied_in when_block
          end)
  | Mutable_block _ => mutable_block_at h v
  | Boxed_number k contents _ =>
    ∃ c : const,
      boxed_number_of statics v = Some c
      ∧ kind_of_const c = unboxed_kind k
      ∧ type_satisfied_in (Value_const c) contents
  | Closures by_function_slot _ =>
    ∃ (slot : function_slot) (functions : list (function_slot * code_id))
      (value_slots : list (value_slot * value)),
      closure_in_set statics v = Some (slot, functions, value_slots)
      ∧ row_like_for_closures_satisfied_in v slot functions value_slots
          by_function_slot
  | String strs =>
    ∃ bytes : list Z, string_of statics v = Some bytes ∧ bytes ∈ strs
  end

with row_like_for_blocks_satisfied_in (tag : Z) (fields : list value)
    (blocks : row_like_for_blocks) {struct blocks} : Prop :=
  match blocks with
  | Row_like_for_blocks known_tags other_tags _ =>
    Keyed.at_binding Z.eqb
      (fun case =>
         match case with
         | Or_unknown.Unknown => True
         | Or_unknown.Known case =>
           block_case_satisfied type_satisfied_in env_extension_satisfied_in
             tag fields case
         end)
      tag known_tags
    ∧ (Keyed.lookup Z.eqb tag known_tags = None ->
       match other_tags with
       | Or_bottom.Bottom => False
       | Or_bottom.Ok case =>
         block_case_satisfied type_satisfied_in env_extension_satisfied_in
           tag fields case
       end)
  end

with row_like_for_closures_satisfied_in (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (closures : row_like_for_closures) {struct closures} : Prop :=
  match closures with
  | Row_like_for_closures known_closures =>
    is_bound slot known_closures = true
    ∧ at_binding
        (closures_case_satisfied
           (closures_entry_satisfied_in v slot functions value_slots)
           env_extension_satisfied_in functions value_slots)
        slot known_closures
  end

with closures_entry_satisfied_in (v : value) (slot : function_slot)
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
             type_satisfied_in closure ty)
        closure_types
    ∧ for_all_bindings
        (fun w ty =>
           ∀ contents : value,
             lookup w value_slots = Some contents ->
             type_satisfied_in contents ty)
        value_slot_types
  end

with env_extension_satisfied_in (extension : env_extension)
    {struct extension} : Prop :=
  match extension with
  | Env_extension equations =>
    Keyed.for_all_bindings name_eqb
      (fun n ty =>
         ∃ v : value, value_of_name vars n = Some v ∧ type_satisfied_in v ty)
      equations
  end.

End Type_satisfied_in.

(* ======================================================================== *)
(* The type [Mutable_block]                                                 *)
(* ======================================================================== *)

(* A value has the type exactly when it is a block made [Mutable] that
   the heap holds. *)
Definition mutable_block_satisfied_in_statement : Prop :=
  ∀ (statics : static_env) (h : heap) (vars : env) (v : value)
    (alloc_mode : Alloc_mode.t),
    type_satisfied_in statics h vars v (mutable_block alloc_mode)
    <-> mutable_block_at h v.

(* An example: a heap with a block made [Mutable] at the first location
   and one made [Immutable_unique] at the second. The first location
   has the type. The second has it not, nor has a location that the
   heap does not bind, nor an immutable block. The heap is read under
   the other types too: an immutable block whose field is the first
   location has the type of a block with a field of the type, and one
   whose field is the second location has it not. *)
Definition example_mutable_block_heap : heap :=
  [(1%positive,
    Cell_block Cell_mutable 0%Z [Value_const (Tagged_immediate 0%Z)]);
   (2%positive,
    Cell_block Cell_immutable_unique 0%Z
      [Value_const (Tagged_immediate 0%Z)])].

Definition example_mutable_block_statement : Prop :=
  let has (v : value) (t : flambda_type) : Prop :=
    type_satisfied_in empty_static_env example_mutable_block_heap [] v t
  in
  let a_mutable_block : flambda_type := mutable_block Alloc_mode.Heap in
  let a_block_of_one : flambda_type :=
    immutable_block false 0%Z (Scannable Value_only) Alloc_mode.Heap
      [a_mutable_block]
  in
  has (Value_location 1%positive) a_mutable_block
  ∧ ~ has (Value_location 2%positive) a_mutable_block
  ∧ ~ has (Value_location 3%positive) a_mutable_block
  ∧ ~ has (Value_block 0%Z [Value_const (Tagged_immediate 0%Z)])
        a_mutable_block
  ∧ has (Value_block 0%Z [Value_location 1%positive]) a_block_of_one
  ∧ ~ has (Value_block 0%Z [Value_location 2%positive]) a_block_of_one.

(* ======================================================================== *)
(* This meaning and that of FlambdaTypeMeaningSpec.v                        *)
(* ======================================================================== *)

(* Where the heap has no cell the two meanings are the same. *)
Definition type_satisfied_in_empty_heap_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (t : flambda_type),
    type_satisfied_in statics empty_heap vars v t
    <-> type_satisfied statics vars v t.

Definition env_extension_satisfied_in_empty_heap_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (extension : env_extension),
    env_extension_satisfied_in statics empty_heap vars extension
    <-> env_extension_satisfied statics vars extension.

(* A value that has a type by [type_satisfied] has it in every heap. So
   what is stated to give a value a type by [type_satisfied] gives it
   the type here. *)
Definition type_satisfied_in_weakens_statement : Prop :=
  ∀ (statics : static_env) (h : heap) (vars : env) (v : value)
    (t : flambda_type),
    type_satisfied statics vars v t -> type_satisfied_in statics h vars v t.

Definition env_extension_satisfied_in_weakens_statement : Prop :=
  ∀ (statics : static_env) (h : heap) (vars : env)
    (extension : env_extension),
    env_extension_satisfied statics vars extension ->
    env_extension_satisfied_in statics h vars extension.

(* ======================================================================== *)
(* What the meaning of a type depends on                                    *)
(* ======================================================================== *)

(* A value has a type only if it has the kind of the type. *)
Definition type_satisfied_in_kind_statement : Prop :=
  ∀ (statics : static_env) (h : heap) (vars : env) (v : value)
    (t : flambda_type),
    type_satisfied_in statics h vars v t -> kind_of_value v = kind t.

(* A value that has a type in a heap has it in every heap that the
   heap evolves to, with the same static environment and the same
   valuation. A step of a run leaves such a heap
   (FlambdaSemanticsSpec.step_evolves_statement), so no store makes a
   type false of a value. Nothing is said of a valuation that
   changes. *)
Definition type_satisfied_in_heap_evolves_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (vars : env) (v : value)
    (t : flambda_type),
    heap_evolves h h' ->
    type_satisfied_in statics h vars v t ->
    type_satisfied_in statics h' vars v t.

Definition env_extension_satisfied_in_heap_evolves_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (vars : env)
    (extension : env_extension),
    heap_evolves h h' ->
    env_extension_satisfied_in statics h vars extension ->
    env_extension_satisfied_in statics h' vars extension.

(* And in every static environment that the static environment grows
   to, with the same heap and the same valuation. It is
   [type_satisfied_statics_extend_statement], for this meaning. *)
Definition type_satisfied_in_statics_extend_statement : Prop :=
  ∀ (statics statics' : static_env) (h : heap) (vars : env) (v : value)
    (t : flambda_type),
    statics_extend statics statics' ->
    type_satisfied_in statics h vars v t ->
    type_satisfied_in statics' h vars v t.

Definition env_extension_satisfied_in_statics_extend_statement : Prop :=
  ∀ (statics statics' : static_env) (h : heap) (vars : env)
    (extension : env_extension),
    statics_extend statics statics' ->
    env_extension_satisfied_in statics h vars extension ->
    env_extension_satisfied_in statics' h vars extension.
