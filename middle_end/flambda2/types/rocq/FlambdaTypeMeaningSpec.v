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


(* What a Flambda type means: which values of the machine have it.

   This file is to be reviewed: what the meaning reads of a value (the
   first section), [type_satisfied] and what it is made of, and the
   statements. The grammar is FlambdaTypeGrammar.v. The compiler has no
   such definition to compare with: what a type means there is what
   [Meet], [Join] and the provers ([Provers], [Expand_head]) take it to
   mean, and those are the files to read this against, with the creation
   functions of [Type_grammar] and [More_type_creators]. Every later
   statement about types (the environment, meet, join, the provers) is
   made with [type_satisfied], so a mistake here is a mistake in all of
   them.

   The environment. A type mentions names: the [Simple] of an alias, the
   variables that hold the results of [Is_int], [Get_tag] and [Is_null],
   the names an environment extension has equations on. So a value has a
   type relative to an environment, of which the meaning needs two
   things and no more:
   - the values of variables, [vars], an environment of the machine. It
     is used through [eval_simple] and [lookup] only;
   - the static environment, [statics]: what symbols are bound to. A
     symbol is a value by itself, a pointer, and a type says what it
     points to. It is used only through the observations of the first
     section.
   Nothing of the typing environment is needed (levels, binding times,
   canonical aliases): that is what is known, and this is what is true.
   What satisfies a typing environment is for the file that defines one
   to say, with [type_satisfied] for each name it has a type for. A
   variable that exists only in types has to have a value in [vars] all
   the same; to say that there is one is the typing environment's
   business.

   What the meaning is, in short ([type_satisfied]):
   - [Unknown] at a kind: every value of that kind. [Bottom]: none.
   - An alias [Equals s] at a kind: the value of [s], if of that kind.
     So a value has a type only if it has the kind of the type
     ([type_satisfied_kind_statement]).
   - A head of kind value: [Null], if [is_null] allows it; or a value
     that is not [Null] and has the [non_null] part.
   - [Variant]: a tagged immediate whose number has the type
     [immediates], or a block that the row-like structure [blocks]
     admits: the case of its tag, or failing one the case [other_tags],
     fixes its size, its shape and the types of its fields.
   - [Boxed_number]: a boxed number of that kind whose contents have the
     type given. [Closures]: a closure at a function slot whose case
     admits its set of closures. [String]: one of the strings.
     [Mutable_block]: nothing, see below.
   - A set of numbers: a number of the kind that is in the set. For a
     naked immediate, also the result of each relation listed, on the
     value of the name it is listed with ([relation_holds]).
   - An environment extension, where it is attached (a case of a
     row-like structure, the two extensions of a variant): each name has
     the type of its equation.

   Choices to check, each taken from what [Meet] does:
   - The heads of kind value are disjoint: a block, a boxed number, a
     closure and a string are four different things
     ([meet_head_of_kind_value_non_null]: "This assumes that all the
     different constructors are incompatible"). The observations below
     are disjoint to match ([observations_disjoint_statement]).
   - The variables [is_int] and [is_null] of a type hold the result of
     the primitive on every value of the type, and [get_tag] on every
     block of it ([meet_variant] says why the two differ).
   - A product (the fields of a block, the closures and the value slots
     of a set of closures) says something of the components that exist
     and nothing of the others: an absent component is unknown, and what
     exists is for the index of the case to say.
   - The relations are those of the primitives restricted to where the
     compiler records them: [Is_int] relates tagged immediates and
     blocks only, which is [Is_int { variant_only = true }]
     ([Simplify_unary_primitive.simplify_is_int]); [Get_tag] blocks
     only. [reduce_inverse_relations] is sound for these and for no
     wider reading.
   - The code of a function type is the code of the closure, the very
     code id. The compiler means "that code or a newer version of it"
     ([Code_age_relation]); that is for the workstream on calls (S4) to
     put here, with a relation between code ids.
   - Allocation modes and [is_unique] mean nothing here: the machine has
     no regions, and uniqueness is about what may be duplicated.

   Where the machine is behind the grammar. The meaning is that of the
   machine of today (FlambdaSemanticsSpec.v), read through observations
   so that it changes with the machine and not with this file:
   - Blocks and boxed numbers exist only behind symbols ([Static_block],
     [Static_boxed_number]). Workstream C1 adds [Value_block] and
     [Value_boxed_number] and defines [block_of], [boxed_number_of],
     [string_of] and [kind_of_value] in the semantics, as they are
     here; the four definitions here go then.
   - Closures are of sets of one function whose slot has no name. As
     agreed with workstream C3, such a closure is read as the closure at
     [unnamed_function_slot] of a set with that one function. C3 adds
     sets of several functions and defines [closure_in_set] and
     [project_function_slot] in the semantics, as they are here; the
     three definitions here go then. Nothing may rely on which slot the
     unnamed one is.
   - There are no mutable blocks, so [Mutable_block] has no value. With
     a heap (C4) it is to mean a mutable block, and a mutable block is
     then to be a block of [Variant] too, as [Meet] has it.
   - There is no value of kind [Region] or [Rec_info] but [Poison].
   - [Poison] is a value of its kind like another, of which nothing more
     is true: it has the unknown type of its kind, at kind value it is
     not [Null], and it is no immediate and nothing allocated.
   - The relations will be defined by the primitives themselves when
     they are data (C1): [relation_holds] is to become "[eval_prim] of
     the primitive on the value is this number".

   The statements say what each form of type means for the types built
   by the creation functions of the compiler, as an equivalence. The
   proofs, and an example for each constructor of a value that has a
   type and of one that has not, are in FlambdaTypeMeaningProofs.v,
   which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaWellFormedSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar.
Import ListNotations.

(* ======================================================================== *)
(* What the meaning reads of a value                                        *)
(* ======================================================================== *)

(* Every definition of this section but [number_of_const] is to be the
   core's (see the header): it is here until the machine has it. *)

(* The kind of a value. *)
Definition kind_of_value (v : value) : flambda_kind :=
  match v with
  | Value_const c => kind_of_const c
  | Value_closure _ _ | Value_symbol _ => Value
  end.

(* The number that a constant is, if it is one. *)
Definition number_of_const (c : const) : option Z :=
  match c with
  | Naked_immediate i | Tagged_immediate i | Naked_float32 i | Naked_float i
  | Naked_int8 i | Naked_int16 i | Naked_int32 i | Naked_int64 i
  | Naked_nativeint i | Naked_vec128 i | Naked_vec256 i | Naked_vec512 i
  | Naked_mask i => Some i
  | Null | Poison _ => None
  end.

(* A value as an immutable block: its tag and its fields. *)
Definition block_of (statics : static_env) (v : value)
    : option (Z * list value) :=
  match v with
  | Value_symbol s =>
    match lookup s (static_values statics) with
    | Some (Static_block tag fields) => Some (tag, fields)
    | _ => None
    end
  | Value_const _ | Value_closure _ _ => None
  end.

(* A value as a boxed number: the number inside, of a kind that can be
   boxed. *)
Definition boxed_number_of (statics : static_env) (v : value)
    : option const :=
  match v with
  | Value_symbol s =>
    match lookup s (static_values statics) with
    | Some (Static_boxed_number (Value_const c)) =>
      match kind_of_const c with
      | Naked_number k => if boxable_number k then Some c else None
      | _ => None
      end
    | _ => None
    end
  | Value_const _ | Value_closure _ _ => None
  end.

(* A value as a string: its bytes. *)
Definition string_of (statics : static_env) (v : value) : option (list Z) :=
  match v with
  | Value_symbol s =>
    match lookup s (static_values statics) with
    | Some (Static_string bytes) => Some bytes
    | _ => None
    end
  | Value_const _ | Value_closure _ _ => None
  end.

(* The function slot of a closure of the machine of today, whose sets of
   closures have one function. *)
Definition unnamed_function_slot : function_slot := 1%positive.

(* A value as a closure of a set of closures: the function slot it is
   at, the code of each function of the set, and the values of the value
   slots. *)
Definition closure_in_set (statics : static_env) (v : value)
    : option
        (function_slot * list (function_slot * code_id)
         * list (value_slot * value)) :=
  match closure_of statics v with
  | Some (code, value_slots) =>
    Some
      (unnamed_function_slot, [(unnamed_function_slot, code)], value_slots)
  | None => None
  end.

(* The closure at [move_to] of the set of which a value is the closure
   at [move_from]. *)
Definition project_function_slot (statics : static_env)
    (move_from move_to : function_slot) (v : value) : option value :=
  match closure_of statics v with
  | Some _ =>
    if Pos.eqb move_from unnamed_function_slot
       && Pos.eqb move_to unnamed_function_slot
    then Some v
    else None
  | None => None
  end.

(* The four ways in which a value is allocated are exclusive. *)
Definition observations_disjoint_statement : Prop :=
  ∀ (statics : static_env) (v : value),
    (block_of statics v <> None
     -> closure_of statics v = None
        ∧ boxed_number_of statics v = None
        ∧ string_of statics v = None)
    ∧ (closure_of statics v <> None
       -> boxed_number_of statics v = None ∧ string_of statics v = None)
    ∧ (boxed_number_of statics v <> None -> string_of statics v = None).

(* ======================================================================== *)
(* The primitives that types speak of                                       *)
(* ======================================================================== *)

Definition is_tagged_immediate (v : value) : Prop :=
  ∃ i : Z, v = Value_const (Tagged_immediate i).

Definition is_block (statics : static_env) (v : value) : Prop :=
  ∃ (tag : Z) (fields : list value), block_of statics v = Some (tag, fields).

Definition allocated (statics : static_env) (v : value) : Prop :=
  block_of statics v <> None
  ∨ closure_of statics v <> None
  ∨ boxed_number_of statics v <> None
  ∨ string_of statics v <> None.

(* The primitive of a relation gives the number [n] on the value [v]:
   - [Is_null]: 1 on [Null], 0 on a tagged immediate and on what is
     allocated;
   - [Is_int], of a variant: 1 on a tagged immediate, 0 on a block;
   - [Get_tag]: the tag of a block.
   Where none of these holds, the primitive has no result that a type
   may speak of. *)
Definition relation_holds (statics : static_env) (relation : Relation.t)
    (v : value) (n : Z) : Prop :=
  match relation with
  | Relation.Is_null =>
    (v = Value_const Null ∧ n = 1%Z)
    ∨ ((is_tagged_immediate v ∨ allocated statics v) ∧ n = 0%Z)
  | Relation.Is_int =>
    (is_tagged_immediate v ∧ n = 1%Z) ∨ (is_block statics v ∧ n = 0%Z)
  | Relation.Get_tag =>
    ∃ fields : list value, block_of statics v = Some (n, fields)
  end.

(* ======================================================================== *)
(* Going through lists and maps                                             *)
(* ======================================================================== *)

(* The meaning of a type is defined by recursion on the type, and a type
   holds maps of types. Rocq accepts a recursive call on what a map
   binds only if the definition goes through the list that the map is,
   so the three definitions below go through every pair of the list, and
   ask something only of the pairs that [lookup] finds: the bindings
   that count. The statements after them say so. *)

(* [P] holds of every element of a list. *)
Definition every {A : Type} (P : A -> Prop) : list A -> Prop :=
  fix every (l : list A) : Prop :=
    match l with
    | [] => True
    | a :: l => P a ∧ every l
    end.

(* [P] holds of every binding of a map. *)
Definition for_all_bindings {A : Type} (P : positive -> A -> Prop)
    (m : finite_map A) : Prop :=
  every
    (fun binding =>
       lookup (fst binding) m = Some (snd binding)
       -> P (fst binding) (snd binding))
    m.

(* [P] holds of what a map binds [name] to, if it binds it. *)
Definition at_binding {A : Type} (P : A -> Prop) (name : positive)
    (m : finite_map A) : Prop :=
  every (fun binding => lookup name m = Some (snd binding) -> P (snd binding))
    m.

(* [P] holds of the case of [tag], if there is one. *)
Definition at_tag {A : Type} (P : A -> Prop) (tag : Z) (cases : list (Z * A))
    : Prop :=
  every (fun case => find_tag tag cases = Some (snd case) -> P (snd case))
    cases.

(* [P] holds of every binding of a map from names. *)
Definition for_all_names {A : Type} (P : name -> A -> Prop)
    (m : finite_name_map A) : Prop :=
  for_all_bindings (fun x => P (Name_var x)) (on_variables m)
  ∧ for_all_bindings (fun s => P (Name_symbol s)) (on_symbols m).

Definition every_in_statement : Prop :=
  ∀ (A : Type) (P : A -> Prop) (l : list A),
    every P l <-> (∀ a : A, a ∈ l -> P a).

Definition for_all_bindings_lookup_statement : Prop :=
  ∀ (A : Type) (P : positive -> A -> Prop) (m : finite_map A),
    for_all_bindings P m
    <-> (∀ (name : positive) (a : A), lookup name m = Some a -> P name a).

Definition at_binding_lookup_statement : Prop :=
  ∀ (A : Type) (P : A -> Prop) (name : positive) (m : finite_map A),
    at_binding P name m <-> (∀ a : A, lookup name m = Some a -> P a).

Definition at_tag_find_statement : Prop :=
  ∀ (A : Type) (P : A -> Prop) (tag : Z) (cases : list (Z * A)),
    at_tag P tag cases <-> (∀ a : A, find_tag tag cases = Some a -> P a).

Definition for_all_names_lookup_statement : Prop :=
  ∀ (A : Type) (P : name -> A -> Prop) (m : finite_name_map A),
    for_all_names P m
    <-> (∀ (n : name) (a : A), lookup_name n m = Some a -> P n a).

(* ======================================================================== *)
(* The meaning of a type                                                    *)
(* ======================================================================== *)

(* A block has a shape: its tag is one that the shape permits, and its
   fields have the kinds of the shape. *)
Definition block_has_shape (shape : block_shape) (tag : Z)
    (fields : list value) : Prop :=
  match shape with
  | Scannable _ => (tag < no_scan_tag)%Z
  | Float_record => tag = double_array_tag
  end
  ∧ map kind_of_value fields = field_kinds shape (length fields).

(* The index of a case of blocks admits a block: its size, exactly or
   from below, and its shape. *)
Definition block_index_satisfied (tag : Z) (fields : list value)
    (index : row_like_index nat block_shape) : Prop :=
  match index_domain index with
  | Row_like_index_domain.Known size => length fields = size
  | Row_like_index_domain.At_least size => size <= length fields
  end
  ∧ block_has_shape (index_shape index) tag fields.

(* The index of a case of closures admits a set of closures: its
   function slots and its value slots, exactly or at least. *)
Definition closures_index_satisfied
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (index : row_like_index set_of_closures_contents unit) : Prop :=
  match index_domain index with
  | Row_like_index_domain.Known contents =>
    same_names (contents_closures contents) (domain functions)
    ∧ same_names (contents_value_slots contents) (domain value_slots)
  | Row_like_index_domain.At_least contents =>
    all_among (contents_closures contents) (domain functions) = true
    ∧ all_among (contents_value_slots contents) (domain value_slots) = true
  end.

Section Type_satisfied.

Variable statics : static_env.
Variable vars : env.

(* [Simple.name], evaluated. *)
Definition value_of_name (n : name) : option value :=
  eval_simple vars (simple_of_name n).

(* The variable of a type that stands for the result of a primitive on
   the value of the type, if the type has one, holds the number [n]. *)
Definition variable_is (x : option variable) (n : Z) : Prop :=
  match x with
  | Some x => lookup x vars = Some (Value_const (Naked_immediate n))
  | None => True
  end.

(* A type of kind [k] that is unknown, bottom, an alias, or given by a
   head, of which [head_satisfied] is the meaning. *)
Definition descr_satisfied {head : Type} (k : flambda_kind)
    (head_satisfied : head -> Prop) (v : value) (ty : type_descr head)
    : Prop :=
  match ty with
  | Unknown => kind_of_value v = k
  | Bottom => False
  | Ok (No_alias head) => head_satisfied head
  | Ok (Equals s) => eval_simple vars s = Some v ∧ kind_of_value v = k
  end.

(* A naked immediate: one of the numbers, if they are known, which is the
   result of each relation on the value of its name. *)
Definition head_of_kind_naked_immediate_satisfied (v : value)
    (head : head_of_kind_naked_immediate) : Prop :=
  ∃ i : Z,
    v = Value_const (Naked_immediate i)
    ∧ match naked_immediates head with
      | Or_unknown.Unknown => True
      | Or_unknown.Known numbers => i ∈ numbers
      end
    ∧ ∀ (relation : Relation.t) (n : name),
        (relation, n) ∈ inverse_relations head ->
        ∃ w : value,
          value_of_name n = Some w ∧ relation_holds statics relation w i.

(* A naked number of kind [k]: one of the numbers. *)
Definition naked_numbers_satisfied (k : naked_number_kind) (v : value)
    (numbers : list Z) : Prop :=
  ∃ (c : const) (n : Z),
    v = Value_const c
    ∧ kind_of_const c = Naked_number k
    ∧ number_of_const c = Some n
    ∧ n ∈ numbers.

(* The fields of a block have the types given, position by position, as
   far as both go. *)
Definition fields_satisfied (type_satisfied : value -> flambda_type -> Prop)
    : list flambda_type -> list value -> Prop :=
  fix fields_satisfied (tys : list flambda_type) (fields : list value)
      : Prop :=
    match tys, fields with
    | ty :: tys, field :: fields =>
      type_satisfied field ty ∧ fields_satisfied tys fields
    | _, _ => True
    end.

(* A case of blocks admits a block. The two arguments stand for the
   functions being defined below. *)
Definition block_case_satisfied
    (type_satisfied : value -> flambda_type -> Prop)
    (env_extension_satisfied : env_extension -> Prop) (tag : Z)
    (fields : list value) (case : row_like_block_case) : Prop :=
  block_index_satisfied tag fields (case_index case)
  ∧ fields_satisfied type_satisfied (case_maps_to case) fields
  ∧ env_extension_satisfied (case_env_extension case).

(* A case of closures admits the closure [v], which is at [slot] of a
   set of closures with [functions] and [value_slots]. The two
   arguments stand for the functions being defined below. *)
Definition closures_case_satisfied
    (closures_entry_satisfied : closures_entry -> Prop)
    (env_extension_satisfied : env_extension -> Prop)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value)) (case : row_like_closures_case)
    : Prop :=
  closures_index_satisfied functions value_slots (case_index case)
  ∧ closures_entry_satisfied (case_maps_to case)
  ∧ env_extension_satisfied (case_env_extension case).

(* A value has a type. *)
Fixpoint type_satisfied (v : value) (t : flambda_type) {struct t} : Prop :=
  match t with
  | Type_value ty =>
    descr_satisfied Value (head_of_kind_value_satisfied v) v ty
  | Type_naked_immediate ty =>
    descr_satisfied (Naked_number Kind_naked_immediate)
      (head_of_kind_naked_immediate_satisfied v) v ty
  | Type_naked_number k ty =>
    descr_satisfied (Naked_number k) (naked_numbers_satisfied k v) v ty
  | Type_rec_info ty =>
    descr_satisfied Rec_info (fun _ => kind_of_value v = Rec_info) v ty
  | Type_region ty =>
    descr_satisfied Region (fun _ => kind_of_value v = Region) v ty
  end

(* [Null], if it may be; or else a value that is not [Null] and has the
   non-null part. *)
with head_of_kind_value_satisfied (v : value) (head : head_of_kind_value)
    {struct head} : Prop :=
  match head with
  | Head_of_kind_value non_null is_null =>
    (v = Value_const Null
     ∧ match is_null with
       | Not_null => False
       | Maybe_null is_null => variable_is is_null 1
       end)
    ∨ (v <> Value_const Null
       ∧ match non_null with
         | Unknown => kind_of_value v = Value
         | Bottom => False
         | Ok head => head_of_kind_value_non_null_satisfied v head
         end
       ∧ match is_null with
         | Not_null => True
         | Maybe_null is_null => variable_is is_null 0
         end)
  end

with head_of_kind_value_non_null_satisfied (v : value)
    (head : head_of_kind_value_non_null) {struct head} : Prop :=
  match head with
  | Variant is_int immediates get_tag blocks extensions _ =>
    (∃ i : Z,
      v = Value_const (Tagged_immediate i)
      ∧ variable_is is_int 1
      ∧ match immediates with
        | Or_unknown.Unknown => True
        | Or_unknown.Known ty =>
          type_satisfied (Value_const (Naked_immediate i)) ty
        end
      ∧ match extensions with
        | No_extensions => True
        | Ext when_immediate _ => env_extension_satisfied when_immediate
        end)
    ∨ (∃ (tag : Z) (fields : list value),
        block_of statics v = Some (tag, fields)
        ∧ variable_is is_int 0
        ∧ variable_is get_tag tag
        ∧ match blocks with
          | Or_unknown.Unknown => True
          | Or_unknown.Known blocks =>
            row_like_for_blocks_satisfied tag fields blocks
          end
        ∧ match extensions with
          | No_extensions => True
          | Ext _ when_block => env_extension_satisfied when_block
          end)
  | Mutable_block _ => False
  | Boxed_number k contents _ =>
    ∃ c : const,
      boxed_number_of statics v = Some c
      ∧ kind_of_const c = Naked_number k
      ∧ type_satisfied (Value_const c) contents
  | Closures by_function_slot _ =>
    ∃ (slot : function_slot) (functions : list (function_slot * code_id))
      (value_slots : list (value_slot * value)),
      closure_in_set statics v = Some (slot, functions, value_slots)
      ∧ row_like_for_closures_satisfied v slot functions value_slots
          by_function_slot
  | String strs =>
    ∃ bytes : list Z, string_of statics v = Some bytes ∧ bytes ∈ strs
  end

(* The case of the tag of the block admits it; a tag whose case is
   unknown admits every block; a tag with no case goes by [other_tags]. *)
with row_like_for_blocks_satisfied (tag : Z) (fields : list value)
    (blocks : row_like_for_blocks) {struct blocks} : Prop :=
  match blocks with
  | Row_like_for_blocks known_tags other_tags _ =>
    at_tag
      (fun case =>
         match case with
         | Or_unknown.Unknown => True
         | Or_unknown.Known case =>
           block_case_satisfied type_satisfied env_extension_satisfied tag
             fields case
         end)
      tag known_tags
    ∧ (find_tag tag known_tags = None ->
       match other_tags with
       | Or_bottom.Bottom => False
       | Or_bottom.Ok case =>
         block_case_satisfied type_satisfied env_extension_satisfied tag
           fields case
       end)
  end

(* There is a case for the function slot of the closure, and it admits
   it. *)
with row_like_for_closures_satisfied (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (closures : row_like_for_closures) {struct closures} : Prop :=
  match closures with
  | Row_like_for_closures known_closures =>
    is_bound slot known_closures = true
    ∧ at_binding
        (closures_case_satisfied
           (closures_entry_satisfied v slot functions value_slots)
           env_extension_satisfied functions value_slots)
        slot known_closures
  end

(* The functions whose code is known have that code; the closures of the
   set and the value slots that exist have the types given. *)
with closures_entry_satisfied (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value)) (entry : closures_entry)
    {struct entry} : Prop :=
  match entry with
  | Closures_entry function_types closure_types value_slot_types =>
    (∀ (g : function_slot) (function_type : function_type),
      lookup g function_types = Some (Or_unknown.Known function_type) ->
      lookup g functions = Some (function_type_code_id function_type))
    ∧ for_all_bindings
        (fun g ty =>
           ∀ closure : value,
             project_function_slot statics slot g v = Some closure ->
             type_satisfied closure ty)
        closure_types
    ∧ for_all_bindings
        (fun w ty =>
           ∀ contents : value,
             lookup w value_slots = Some contents ->
             type_satisfied contents ty)
        value_slot_types
  end

(* Every name with an equation has a value, of the type of the
   equation. *)
with env_extension_satisfied (extension : env_extension) {struct extension}
    : Prop :=
  match extension with
  | Env_extension equations =>
    for_all_names
      (fun n ty =>
         ∃ v : value, value_of_name n = Some v ∧ type_satisfied v ty)
      equations
  end.

End Type_satisfied.

(* A case of blocks admits a block, and a case of closures a closure. *)
Definition row_like_block_case_satisfied (statics : static_env) (vars : env)
    (tag : Z) (fields : list value) (case : row_like_block_case) : Prop :=
  block_case_satisfied (type_satisfied statics vars)
    (env_extension_satisfied statics vars) tag fields case.

Definition row_like_closures_case_satisfied (statics : static_env)
    (vars : env) (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value)) (case : row_like_closures_case)
    : Prop :=
  closures_case_satisfied
    (closures_entry_satisfied statics vars v slot functions value_slots)
    (env_extension_satisfied statics vars) functions value_slots case.

(* ======================================================================== *)
(* What every kind has: unknown, bottom, aliases                            *)
(* ======================================================================== *)

(* A value has a type only if it has the kind of the type. *)
Definition type_satisfied_kind_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (t : flambda_type),
    type_satisfied statics vars v t -> kind_of_value v = kind t.

Definition unknown_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (k : flambda_kind),
    type_satisfied statics vars v (unknown k) <-> kind_of_value v = k.

Definition bottom_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (k : flambda_kind),
    ~ type_satisfied statics vars v (bottom k).

Definition alias_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (k : flambda_kind)
    (s : simple),
    type_satisfied statics vars v (alias_type_of k s)
    <-> eval_simple vars s = Some v ∧ kind_of_value v = k.

(* The same of any type that is an alias. *)
Definition get_alias_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (t : flambda_type)
    (s : simple),
    get_alias_opt t = Some s ->
    (type_satisfied statics vars v t
     <-> eval_simple vars s = Some v ∧ kind_of_value v = kind t).

Definition this_const_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (c : const),
    type_satisfied statics vars v (this_const c) <-> v = Value_const c.

(* A constant has the type that the compiler gives it. *)
Definition type_for_const_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (c : const),
    type_satisfied statics vars (Value_const c) (type_for_const c).

(* ======================================================================== *)
(* Numbers                                                                  *)
(* ======================================================================== *)

Definition these_naked_immediates_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (imms : list Z),
    type_satisfied statics vars v (these_naked_immediates imms)
    <-> ∃ i : Z, v = Value_const (Naked_immediate i) ∧ i ∈ imms.

(* A set of naked numbers of another kind. *)
Definition type_naked_number_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (k : naked_number_kind)
    (numbers : list Z),
    type_satisfied statics vars v
      (Type_naked_number k (Ok (No_alias numbers)))
    <-> ∃ (c : const) (n : Z),
          v = Value_const c
          ∧ kind_of_const c = Naked_number k
          ∧ number_of_const c = Some n
          ∧ n ∈ numbers.

(* The result of a primitive on the value of a name. *)
Definition is_int_for_scrutinee_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (scrutinee : name),
    type_satisfied statics vars v (is_int_for_scrutinee scrutinee)
    <-> ∃ (i : Z) (w : value),
          v = Value_const (Naked_immediate i)
          ∧ value_of_name vars scrutinee = Some w
          ∧ relation_holds statics Relation.Is_int w i.

Definition get_tag_for_block_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (block : name),
    type_satisfied statics vars v (get_tag_for_block block)
    <-> ∃ (i : Z) (w : value),
          v = Value_const (Naked_immediate i)
          ∧ value_of_name vars block = Some w
          ∧ relation_holds statics Relation.Get_tag w i.

Definition is_null_for_scrutinee_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (scrutinee : name),
    type_satisfied statics vars v (is_null_for_scrutinee scrutinee)
    <-> ∃ (i : Z) (w : value),
          v = Value_const (Naked_immediate i)
          ∧ value_of_name vars scrutinee = Some w
          ∧ relation_holds statics Relation.Is_null w i.

(* ======================================================================== *)
(* Null, immediates and blocks                                              *)
(* ======================================================================== *)

Definition null_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value),
    type_satisfied statics vars v null <-> v = Value_const Null.

Definition any_non_null_value_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value),
    type_satisfied statics vars v any_non_null_value
    <-> kind_of_value v = Value ∧ v <> Value_const Null.

(* A variant with no variables for [Is_int] and [Get_tag]: a tagged
   immediate or a block. *)
Definition create_variant_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (is_unique : bool)
    (immediates : Or_unknown.t flambda_type)
    (blocks : Or_unknown.t row_like_for_blocks)
    (extensions : variant_extensions),
    type_satisfied statics vars v
      (create_variant is_unique immediates blocks extensions)
    <-> (∃ i : Z,
          v = Value_const (Tagged_immediate i)
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
            ∧ match blocks with
              | Or_unknown.Unknown => True
              | Or_unknown.Known blocks =>
                row_like_for_blocks_satisfied statics vars tag fields blocks
              end
            ∧ match extensions with
              | No_extensions => True
              | Ext _ when_block =>
                env_extension_satisfied statics vars when_block
              end).

Definition any_tagged_immediate_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value),
    type_satisfied statics vars v any_tagged_immediate
    <-> is_tagged_immediate v.

Definition tag_immediate_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (t : flambda_type),
    type_satisfied statics vars v (tag_immediate t)
    <-> ∃ i : Z,
          v = Value_const (Tagged_immediate i)
          ∧ type_satisfied statics vars (Value_const (Naked_immediate i)) t.

Definition these_tagged_immediates_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (imms : list Z),
    type_satisfied statics vars v (these_tagged_immediates imms)
    <-> ∃ i : Z, v = Value_const (Tagged_immediate i) ∧ i ∈ imms.

Definition any_block_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value),
    type_satisfied statics vars v any_block <-> is_block statics v.

(* The fields of a block, by position. *)
Definition fields_satisfied_nth_statement : Prop :=
  ∀ (P : value -> flambda_type -> Prop) (tys : list flambda_type)
    (fields : list value),
    fields_satisfied P tys fields
    <-> (∀ (i : nat) (ty : flambda_type) (field : value),
          nth_error tys i = Some ty ->
          nth_error fields i = Some field ->
          P field ty).

(* A row-like structure of blocks, by the case of the tag. *)
Definition row_like_for_blocks_find_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (tag : Z) (fields : list value)
    (known_tags : list (Z * Or_unknown.t row_like_block_case))
    (other_tags : Or_bottom.t row_like_block_case)
    (alloc_mode : Alloc_mode.t),
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

(* A block of a tag whose fields, as many as there are types, have the
   types. *)
Definition immutable_block_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (is_unique : bool)
    (tag : Z) (shape : block_shape) (alloc_mode : Alloc_mode.t)
    (field_tys : list flambda_type),
    type_satisfied statics vars v
      (immutable_block is_unique tag shape alloc_mode field_tys)
    <-> ∃ fields : list value,
          block_of statics v = Some (tag, fields)
          ∧ block_has_shape shape tag fields
          ∧ Forall2 (type_satisfied statics vars) fields field_tys.

(* The machine has no mutable block. *)
Definition mutable_block_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value)
    (alloc_mode : Alloc_mode.t),
    ~ type_satisfied statics vars v (mutable_block alloc_mode).

(* ======================================================================== *)
(* Boxed numbers, strings and closures                                      *)
(* ======================================================================== *)

Definition box_number_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (k : naked_number_kind)
    (contents : flambda_type) (alloc_mode : Alloc_mode.t),
    type_satisfied statics vars v (box_number k contents alloc_mode)
    <-> ∃ c : const,
          boxed_number_of statics v = Some c
          ∧ kind_of_const c = Naked_number k
          ∧ type_satisfied statics vars (Value_const c) contents.

Definition this_immutable_string_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (bytes : list Z),
    type_satisfied statics vars v (this_immutable_string bytes)
    <-> string_of statics v = Some bytes.

(* A row-like structure of closures, by the case of the function slot. *)
Definition row_like_for_closures_lookup_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (known_closures : finite_map row_like_closures_case),
    row_like_for_closures_satisfied statics vars v slot functions
      value_slots (Row_like_for_closures known_closures)
    <-> ∃ case : row_like_closures_case,
          lookup slot known_closures = Some case
          ∧ row_like_closures_case_satisfied statics vars v slot functions
              value_slots case.

(* What is said of the functions, the closures and the value slots of a
   set of closures. *)
Definition closures_entry_lookup_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (function_types : finite_map (Or_unknown.t function_type))
    (closure_types value_slot_types : finite_map flambda_type),
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

(* The closure at a function slot of a set with exactly the functions
   and the value slots given, each as its type says. *)
Definition exactly_this_closure_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (function_types : finite_map (Or_unknown.t function_type))
    (closure_types value_slot_types : finite_map flambda_type)
    (alloc_mode : Alloc_mode.t),
    type_satisfied statics vars v
      (exactly_this_closure slot function_types closure_types
         value_slot_types alloc_mode)
    <-> ∃ (functions : list (function_slot * code_id))
          (value_slots : list (value_slot * value)),
          closure_in_set statics v = Some (slot, functions, value_slots)
          ∧ same_names (domain function_types) (domain functions)
          ∧ same_names (domain value_slot_types) (domain value_slots)
          ∧ closures_entry_satisfied statics vars v slot functions
              value_slots
              (Closures_entry function_types closure_types
                 value_slot_types).

(* ======================================================================== *)
(* Environment extensions                                                   *)
(* ======================================================================== *)

Definition env_extension_lookup_statement : Prop :=
  ∀ (statics : static_env) (vars : env)
    (equations : finite_name_map flambda_type),
    env_extension_satisfied statics vars (Env_extension equations)
    <-> (∀ (n : name) (ty : flambda_type),
          lookup_name n equations = Some ty ->
          ∃ v : value,
            value_of_name vars n = Some v ∧ type_satisfied statics vars v ty).

(* ======================================================================== *)
(* What the meaning of a type depends on                                    *)
(* ======================================================================== *)

(* A type keeps its values when the static environment grows, as it does
   in a run (FlambdaWellFormedSpec.run_extends_statics_statement): what is
   true of a value where a handler is defined is true where it runs. *)
Definition type_satisfied_statics_extend_statement : Prop :=
  ∀ (statics statics' : static_env) (vars : env) (v : value)
    (t : flambda_type),
    statics_extend statics statics' ->
    type_satisfied statics vars v t ->
    type_satisfied statics' vars v t.

Definition env_extension_satisfied_statics_extend_statement : Prop :=
  ∀ (statics statics' : static_env) (vars : env) (extension : env_extension),
    statics_extend statics statics' ->
    env_extension_satisfied statics vars extension ->
    env_extension_satisfied statics' vars extension.

(* The meaning of a type depends on the environment only through the
   values of the variables that the type mentions. *)
Definition type_satisfied_coincide_statement : Prop :=
  ∀ (statics : static_env) (vars vars' : env) (v : value) (t : flambda_type),
    (∀ x : variable, x ∈ free_variables t -> lookup x vars = lookup x vars') ->
    (type_satisfied statics vars v t <-> type_satisfied statics vars' v t).

Definition env_extension_satisfied_coincide_statement : Prop :=
  ∀ (statics : static_env) (vars vars' : env) (extension : env_extension),
    (∀ x : variable,
      x ∈ free_variables_of_env_extension extension ->
      lookup x vars = lookup x vars') ->
    (env_extension_satisfied statics vars extension
     <-> env_extension_satisfied statics vars' extension).

(* So binding a variable that a type does not mention changes nothing:
   what is known stays known under a binder of a fresh name. *)
Definition type_satisfied_bind_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (x : variable) (w v : value)
    (t : flambda_type),
    x ∉ free_variables t ->
    (type_satisfied statics ((x, w) :: vars) v t
     <-> type_satisfied statics vars v t).

(* The unknown type of a kind is the top of the kind. *)
Definition unknown_is_top_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (t : flambda_type),
    type_satisfied statics vars v t ->
    type_satisfied statics vars v (unknown (kind t)).

(* ======================================================================== *)
(* Types with no value, and heads with no value in common                   *)
(* ======================================================================== *)

Definition is_obviously_bottom_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (t : flambda_type),
    is_obviously_bottom t = true -> ~ type_satisfied statics vars v t.

Definition is_obviously_unknown_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (t : flambda_type),
    is_obviously_unknown t = true ->
    (type_satisfied statics vars v t <-> kind_of_value v = kind t).

Definition row_like_for_blocks_is_bottom_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (tag : Z) (fields : list value)
    (blocks : row_like_for_blocks),
    row_like_for_blocks_is_bottom blocks = true ->
    ~ row_like_for_blocks_satisfied statics vars tag fields blocks.

(* The last case of [Meet.meet_head_of_kind_value_non_null]: two heads
   made with different constructors have no value in common, but for a
   variant and a mutable block; nor have boxed numbers of two kinds. *)
Definition heads_compatible (head head' : head_of_kind_value_non_null)
    : Prop :=
  match head, head' with
  | (Variant _ _ _ _ _ _ | Mutable_block _),
    (Variant _ _ _ _ _ _ | Mutable_block _) => True
  | Boxed_number k _ _, Boxed_number k' _ _ => k = k'
  | Closures _ _, Closures _ _ => True
  | String _, String _ => True
  | _, _ => False
  end.

Definition heads_compatible_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value)
    (head head' : head_of_kind_value_non_null),
    head_of_kind_value_non_null_satisfied statics vars v head ->
    head_of_kind_value_non_null_satisfied statics vars v head' ->
    heads_compatible head head'.
