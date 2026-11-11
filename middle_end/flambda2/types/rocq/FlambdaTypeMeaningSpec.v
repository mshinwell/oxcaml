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

   The compiler has two implementations of meet and join: [Meet_and_join]
   (meet_and_join.ml, with join_levels_old.ml), which is the one it runs
   unless told otherwise, at every optimisation level, and
   [Meet_and_n_way_join], which it runs for the n-way join algorithm
   and for match-in-match ([Meet.meet] chooses, by
   [Flambda_features.use_n_way_join]). A function named below is in
   both under that name unless one is said; where the two differ it is
   said.

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
   - The variables [is_int], [get_tag] and [is_null] of a type and the
     relations of a naked immediate say the same thing from two sides,
     and the compiler records the two together
     ([Typing_env.add_is_null_relation] and the two beside it, in
     flambda2_types.ml). So they agree here: the variable of a type
     holds a number that the relation relates to each value of the type
     ([is_null_coherent_statement], [is_int_coherent_statement],
     [get_tag_coherent_statement]). The variables [is_int] and [is_null]
     say so of every value of the type, [get_tag] of its blocks only
     ([meet_variant] says why).
   - A product (the fields of a block, the closures and the value slots
     of a set of closures) says something of the components that exist
     and nothing of the others: an absent component is unknown, and what
     exists is for the index of the case to say ([Type_grammar]:
     "{ 1 => Unknown; 2 => V } is equal to { 2 => V }"). The function
     types of a set of closures are read in the same way: the code of a
     function is said if the set has the function. The n-way join
     needs that: it keeps a function type that only some of the types
     joined have, under an index that no longer says that the set has
     the function ([n_way_join_closures_entry]; the other join,
     [join_closures_entry], keeps a function type only if all have
     it). The closure of a set without the function has to have the
     joined type ([closure_absent_function_has] in the Proofs). The
     code of a function is known where the index says that the set has
     it ([closures_case_function_code_statement]), and always for the
     function at the slot of the closure itself
     ([closures_case_own_code_statement]): those are the two cases in
     which a prover reads a function type
     ([Row_like_for_closures.get_single_tag], [Provers.prove_code_ids]).
     Even read so, the n-way join is not always an upper bound: where
     one type says nothing of the code of the function at the slot of
     the closure and another names it, the joined type names it
     ([nway_join_has_not] in the Proofs).
   - A relation is not the execution of its primitive
     ([relation_holds]). It relates a value and a number wherever the
     compiler records it of them, which is not where the primitive has
     a result:
     - [Is_null] relates every value of kind value: to 1 if it is
       [Null], to 0 if not, poison and a symbol that is not bound
       included. That is the compiler's reading of a constant
       ([Relation.of_const], by [Reg_width_const.is_null];
       [is_null_of_const_statement]), and the type of a scrutinee with
       a variable [is_null] admits all these.
     - [Is_int] relates a tagged immediate to 1 and a block to 0, and
       nothing else. The compiler records it for
       [Is_int { variant_only = true }]
       ([Simplify_unary_primitive.simplify_is_int]) and for a parameter
       that is unboxed as a variant, of a scrutinee that it takes to be
       a variant and not null ([add_is_int_relation]). Its reading of a
       constant is wider, 0 for [Null] and 1 for every other constant
       ([Relation.of_const]); the two agree where this one says
       something ([relation_of_const_sound_statement]).
     - [Get_tag] relates a block to its tag, and a tagged immediate to
       any number. Unboxing records it of a parameter that may be an
       immediate (simplify/unboxing/build_unboxing_denv.ml), and passes
       the tag 0 on the paths where it is one (unboxing_epa.ml,
       [compute_extra_args_for_variant]); [add_get_tag_relation] keeps
       the immediates for that reason, and on a constant
       [reduce_head_of_kind_naked_immediate] drops the relation. The
       primitive has no value on an immediate, and nothing here gives
       it one.
     The result of a primitive, where it has one, is to be related:
     that is for the simplification of the primitives to prove, and is
     all that ties the two. Where a primitive has a result is not said
     here.
   - One reduction of [Meet] is not sound for this meaning, nor for any
     under which the environments that unboxing makes are true: from a
     relation [Get_tag] whose number is among some tags,
     [reduce_inverse_relations] makes the name a block with one of
     those tags, where it may be an immediate.
     [relation_get_tag_statement] has what does follow. Its other
     reductions are sound ([relation_is_null_statement],
     [relation_is_int_statement]).
   - A poison value has no type but the unknown one of its kind, which
     is the type the compiler gives the constant
     ([More_type_creators.type_for_const]). Unboxing does not keep to
     that. For a field of a variant that is unboxed in turn, it passes
     poison on the paths where the argument has no such field, with 0
     for the tag and for [Is_int] of it (unboxing_epa.ml); and the
     environment of the handler has the type and the relations of that
     field on every path (build_unboxing_denv.ml, [denv_of_decision]).
     On such a path they are not true here. Whether a type is to say
     nothing of a poison value is open, and is not for this file alone
     to settle: it asks what it is to put another value where a poison
     value was.
   - The code of a function type is the code of the closure, the very
     code id. The compiler means "that code or a newer version of it"
     ([Code_age_relation]); that is for the workstream on calls (S4) to
     put here, with a relation between code ids. Until then this is a
     restriction and not only something left out: a closure made with
     a newer version of the code has not, here, the type that names
     the older one, and the compiler takes it to have it
     ([meet_code_id] and the join of function types go by the
     relation; [Simplify_apply_expr] compares the code of the type
     with that of the call by it, and may make the call [Invalid]). So
     what is stated of meet, join and reification with this meaning is
     to leave out the types that name code, or to bring the relation
     in; and the code id that a prover answers is not to be read as
     the code of the closure at run time.
   - Allocation modes and [is_unique] mean nothing here: the machine has
     no regions, and uniqueness is about what may be duplicated. They
     matter to the compiler: a prover answers with the allocation mode
     of a type, or that a value holds nothing allocated locally
     ([Provers.never_holds_locally_allocated_values]); [Reify] lifts
     on the strength of that; and uniqueness is kept by meet and join
     and goes from a type to the block that reification makes
     ([Immutable_unique]). So what is stated with this meaning is
     about which values a type has. It says nothing of locality, of
     lifetime, of what may be duplicated or of whether lifting is
     safe: those need an invariant or a richer machine. In particular
     two values with equal contents are not thereby one symbol.

   What the meaning does not need and the operations will. [Meet] makes
   the meet of two products empty as soon as one component has no value
   ([meet_mapping]), and takes two shapes that differ to have no block
   in common ([meet_row_like_for_blocks]). Neither is true of the
   meaning as it stands, for every type of the grammar: an empty block
   has the type of the blocks of at least no field whose first field
   has no value, and a block of one field that is a value has both the
   shape [Value_only] and the shape [Mixed_record 1 []]
   ([wide_product_has] and [mixed_record_of_values_has] in the Proofs).
   They are true of the types in which:
   - the product of a case of blocks is no wider than the size of its
     index ([block_case_empty_statement]), and as wide if the size is
     exact ([Reify] asserts that);
   - the function types, the closure types and the value slot types of
     a case of closures are of slots among those of its index
     ([closures_case_function_code_statement],
     [closures_case_value_slot_statement]), and an exact index has the
     slot of the case among its closures;
   - a shape is written in one way: a mixed record has a flat suffix
     ([block_shapes_disjoint_statement]);
   - the kinds are right: those that the creation functions check
     (FlambdaTypeGrammar.v lists them), and those of the fields of a
     block against its shape, which the compiler checks only with its
     invariant checks on ([Row_like_for_blocks.check_field_tys]).
   The creation functions of the compiler give such types. Its raw
   constructors ([create_raw], which meet and join use) check nothing,
   and the n-way join does not keep the second condition (see above,
   on products). The statements named say what each condition gives,
   for one case. A predicate that says the conditions of a whole type,
   with the proof that the creation functions here establish it, is to
   be in this library before meet is stated. It is not here yet, and
   the meaning does not need it.

   What an answer of a prover is about. The provers of the compiler come
   in two forms ([Provers.gen_value_to_proof] and [gen_value_to_meet]).
   A proof is about every value of the type. A meet shortcut is not: it
   leaves out the alternatives on which the operation asked about has
   no value (of a type that may be [Null] it answers for the part that
   is not), so its answer is about the values of the type on which
   that operation is defined, and is to be stated so.

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
     not [Null], and it is no immediate and nothing allocated (see the
     choices above).
   - The primitives are abstract. When they are data (C1) the relations
     stay as they are, and what is to be proved is that the result of
     [Is_null], of [Is_int] of a variant and of [Get_tag], where there
     is one, is related to the value.

   The statements say what each form of type means for the types built
   by the creation functions of the compiler, as an equivalence. The
   proofs are in FlambdaTypeMeaningProofs.v, which needs no review. It
   also has, for each constructor but [Mutable_block], a value that has
   a type built with it and a value that has not but would have one
   close to it; no value has a [Mutable_block] type. *)

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

(* A closure is the closure of one of the functions of its set. *)
Definition closure_in_set_slot_statement : Prop :=
  ∀ (statics : static_env) (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value)),
    closure_in_set statics v = Some (slot, functions, value_slots) ->
    is_bound slot functions = true.

(* ======================================================================== *)
(* The relations that types speak of                                        *)
(* ======================================================================== *)

Definition is_tagged_immediate (v : value) : Prop :=
  ∃ i : Z, v = Value_const (Tagged_immediate i).

Definition is_block (statics : static_env) (v : value) : Prop :=
  ∃ (tag : Z) (fields : list value), block_of statics v = Some (tag, fields).

(* What a type means by "this number is [Is_null], [Is_int] or [Get_tag]
   of that value". It is a relation of the types, not the execution of
   the primitive (see the header):
   - [Is_null]: the value is of kind value, and the number is 1 if it is
     [Null] and 0 if it is not;
   - [Is_int]: the value is a tagged immediate and the number is 1, or
     it is a block and the number is 0;
   - [Get_tag]: the value is a block and the number is its tag, or it
     is a tagged immediate, and then nothing is said of the number. *)
Definition relation_holds (statics : static_env) (relation : Relation.t)
    (v : value) (n : Z) : Prop :=
  match relation with
  | Relation.Is_null =>
    (v = Value_const Null ∧ n = 1%Z)
    ∨ (kind_of_value v = Value ∧ v <> Value_const Null ∧ n = 0%Z)
  | Relation.Is_int =>
    (is_tagged_immediate v ∧ n = 1%Z) ∨ (is_block statics v ∧ n = 0%Z)
  | Relation.Get_tag =>
    is_tagged_immediate v
    ∨ ∃ fields : list value, block_of statics v = Some (n, fields)
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

(* The functions of the set whose code is known have that code, and the
   closures of the set and the value slots have the types given: each
   if the set has it. What the set has is for the index of the case to
   say, not for the entry. *)
with closures_entry_satisfied (v : value) (slot : function_slot)
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

(* A number that a relation relates to the value of a name. The three
   statements spell [relation_holds] out. *)
Definition is_int_for_scrutinee_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (scrutinee : name),
    type_satisfied statics vars v (is_int_for_scrutinee scrutinee)
    <-> ∃ (i : Z) (w : value),
          v = Value_const (Naked_immediate i)
          ∧ value_of_name vars scrutinee = Some w
          ∧ ((is_tagged_immediate w ∧ i = 1%Z)
             ∨ (is_block statics w ∧ i = 0%Z)).

(* The scrutinee may be an immediate, as a parameter that is unboxed
   may be; the number is then any number. *)
Definition get_tag_for_block_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (block : name),
    type_satisfied statics vars v (get_tag_for_block block)
    <-> ∃ (i : Z) (w : value),
          v = Value_const (Naked_immediate i)
          ∧ value_of_name vars block = Some w
          ∧ (is_tagged_immediate w
             ∨ ∃ fields : list value, block_of statics w = Some (i, fields)).

Definition is_null_for_scrutinee_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (scrutinee : name),
    type_satisfied statics vars v (is_null_for_scrutinee scrutinee)
    <-> ∃ (i : Z) (w : value),
          v = Value_const (Naked_immediate i)
          ∧ value_of_name vars scrutinee = Some w
          ∧ ((w = Value_const Null ∧ i = 1%Z)
             ∨ (kind_of_value w = Value ∧ w <> Value_const Null
                ∧ i = 0%Z)).

(* The two sides of a relation agree: the variable of a type holds a
   number that the relation relates to each value of the type. For
   [Get_tag] the variable need hold nothing where the value is an
   immediate. *)
Definition is_null_coherent_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value)
    (non_null : or_unknown_or_bottom head_of_kind_value_non_null)
    (is_null : variable),
    head_of_kind_value_satisfied statics vars v
      (Head_of_kind_value non_null (Maybe_null (Some is_null))) ->
    ∃ n : Z,
      lookup is_null vars = Some (Value_const (Naked_immediate n))
      ∧ relation_holds statics Relation.Is_null v n.

Definition is_int_coherent_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (is_int : variable)
    (immediates : Or_unknown.t flambda_type) (get_tag : option variable)
    (blocks : Or_unknown.t row_like_for_blocks)
    (extensions : variant_extensions) (is_unique : bool),
    head_of_kind_value_non_null_satisfied statics vars v
      (Variant (Some is_int) immediates get_tag blocks extensions is_unique) ->
    ∃ n : Z,
      lookup is_int vars = Some (Value_const (Naked_immediate n))
      ∧ relation_holds statics Relation.Is_int v n.

Definition get_tag_coherent_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value)
    (is_int : option variable) (immediates : Or_unknown.t flambda_type)
    (get_tag : variable) (blocks : Or_unknown.t row_like_for_blocks)
    (extensions : variant_extensions) (is_unique : bool) (n : Z),
    head_of_kind_value_non_null_satisfied statics vars v
      (Variant is_int immediates (Some get_tag) blocks extensions is_unique) ->
    lookup get_tag vars = Some (Value_const (Naked_immediate n)) ->
    relation_holds statics Relation.Get_tag v n.

(* The compiler's reading of a relation on a constant
   ([Relation.of_const], which [reduce_head_of_kind_naked_immediate]
   uses) is sound: if a relation relates a constant to a number, and the
   compiler gives a number for it, it is that one. For [Is_null] it is
   exact on the constants of kind value. For [Is_int] it is not: the
   compiler gives 0 for [Null] and 1 for every other constant, poison
   and the naked numbers included, and the relation holds of the tagged
   immediates only. *)
Definition relation_of_const_sound_statement : Prop :=
  ∀ (statics : static_env) (relation : Relation.t) (c : const) (i n : Z),
    relation_holds statics relation (Value_const c) i ->
    Relation.of_const relation c = Or_bottom.Ok n ->
    i = n.

Definition is_null_of_const_statement : Prop :=
  ∀ (statics : static_env) (c : const) (n : Z),
    kind_of_const c = Value ->
    (relation_holds statics Relation.Is_null (Value_const c) n
     <-> Relation.of_const Relation.Is_null c = Or_bottom.Ok n).

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

Definition blocks_with_these_tags_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (tags : list Z)
    (alloc_mode : Alloc_mode.t),
    type_satisfied statics vars v (blocks_with_these_tags tags alloc_mode)
    <-> ∃ (tag : Z) (fields : list value),
          block_of statics v = Some (tag, fields) ∧ tag ∈ tags.

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
    <-> (∀ (g : function_slot) (function_type : function_type)
           (code : code_id),
          lookup g function_types = Some (Or_unknown.Known function_type) ->
          lookup g functions = Some code ->
          code = function_type_code_id function_type)
        ∧ (∀ (g : function_slot) (ty : flambda_type) (closure : value),
            lookup g closure_types = Some ty ->
            project_function_slot statics slot g v = Some closure ->
            type_satisfied statics vars closure ty)
        ∧ (∀ (w : value_slot) (ty : flambda_type) (contents : value),
            lookup w value_slot_types = Some ty ->
            lookup w value_slots = Some contents ->
            type_satisfied statics vars contents ty).

(* What a set of closures has for sure, by the index of its case. *)
Definition closures_index_contents
    (index : row_like_index set_of_closures_contents unit)
    : set_of_closures_contents :=
  match index_domain index with
  | Row_like_index_domain.Known contents
  | Row_like_index_domain.At_least contents => contents
  end.

(* A function that the index of a case says the set has, and whose code
   the entry knows, is there with that code. It is what a prover reads:
   [Row_like_for_closures.get_single_tag] asks that the slot be among
   the closures of the index before the function type is looked at. *)
Definition closures_case_function_code_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (function_types : finite_map (Or_unknown.t function_type))
    (closure_types value_slot_types : finite_map flambda_type)
    (index : row_like_index set_of_closures_contents unit)
    (extension : env_extension) (g : function_slot)
    (function_type : function_type),
    row_like_closures_case_satisfied statics vars v slot functions
      value_slots
      (Row_like_case
         (Closures_entry function_types closure_types value_slot_types)
         index extension) ->
    among g (contents_closures (closures_index_contents index)) = true ->
    lookup g function_types = Some (Or_unknown.Known function_type) ->
    lookup g functions = Some (function_type_code_id function_type).

(* The same of the function at the slot of the closure itself, which
   the set has whatever the index says: [Provers.prove_code_ids] reads
   its function type without looking at the index. *)
Definition closures_case_own_code_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (function_types : finite_map (Or_unknown.t function_type))
    (closure_types value_slot_types : finite_map flambda_type)
    (index : row_like_index set_of_closures_contents unit)
    (extension : env_extension) (function_type : function_type),
    closure_in_set statics v = Some (slot, functions, value_slots) ->
    row_like_closures_case_satisfied statics vars v slot functions
      value_slots
      (Row_like_case
         (Closures_entry function_types closure_types value_slot_types)
         index extension) ->
    lookup slot function_types = Some (Or_unknown.Known function_type) ->
    lookup slot functions = Some (function_type_code_id function_type).

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

(* The same of a set with at least the functions and the value slots
   given. *)
Definition at_least_this_closure_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (function_types : finite_map (Or_unknown.t function_type))
    (closure_types value_slot_types : finite_map flambda_type)
    (alloc_mode : Alloc_mode.t),
    type_satisfied statics vars v
      (at_least_this_closure slot function_types closure_types
         value_slot_types alloc_mode)
    <-> ∃ (functions : list (function_slot * code_id))
          (value_slots : list (value_slot * value)),
          closure_in_set statics v = Some (slot, functions, value_slots)
          ∧ all_among (domain function_types) (domain functions) = true
          ∧ all_among (domain value_slot_types) (domain value_slots) = true
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
(* What a relation says of the value it relates                             *)
(* ======================================================================== *)

(* What follows for a value from the number that a relation relates it
   to. For [Is_null] and [Is_int] it is what [Meet] deduces
   ([reduce_inverse_relations]). For [Get_tag] it is less: [Meet] makes
   the value a block with one of the tags, and it may be an immediate
   (see the header). *)
Definition relation_is_null_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (w : value) (n : Z),
    relation_holds statics Relation.Is_null w n ->
    (n = 1%Z ∧ type_satisfied statics vars w null)
    ∨ (n = 0%Z ∧ type_satisfied statics vars w any_non_null_value).

Definition relation_is_int_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (w : value) (n : Z),
    relation_holds statics Relation.Is_int w n ->
    (n = 1%Z ∧ type_satisfied statics vars w any_tagged_immediate)
    ∨ (n = 0%Z ∧ type_satisfied statics vars w any_block).

Definition relation_get_tag_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (w : value) (n : Z)
    (tags : list Z) (alloc_mode : Alloc_mode.t),
    relation_holds statics Relation.Get_tag w n ->
    n ∈ tags ->
    is_tagged_immediate w
    ∨ type_satisfied statics vars w (blocks_with_these_tags tags alloc_mode).

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

(* ======================================================================== *)
(* What the operations on types rely on                                     *)
(* ======================================================================== *)

(* [Meet] makes a product with a component of no value empty, and takes
   two shapes that differ to have no block in common (see the header).
   The statements below say on which conditions that is so, case by
   case. The conditions are not part of the meaning. *)

(* The size that the index of a case of blocks gives, exactly or from
   below. *)
Definition block_index_size (index : row_like_index nat block_shape) : nat :=
  match index_domain index with
  | Row_like_index_domain.Known size
  | Row_like_index_domain.At_least size => size
  end.

(* A case of blocks whose product is no wider than the size of its
   index admits no block if one of the types of the product has no
   value: every type of the product is the type of a field. *)
Definition block_case_empty_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (tag : Z) (fields : list value)
    (case : row_like_block_case) (ty : flambda_type),
    length (case_maps_to case) <= block_index_size (case_index case) ->
    ty ∈ case_maps_to case ->
    (∀ v : value, ~ type_satisfied statics vars v ty) ->
    ~ row_like_block_case_satisfied statics vars tag fields case.

(* A value slot that the index of a case of closures says the set has,
   and of which the entry has a type, is there with contents of that
   type. So the case admits no closure if that type has no value. *)
Definition closures_case_value_slot_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (function_types : finite_map (Or_unknown.t function_type))
    (closure_types value_slot_types : finite_map flambda_type)
    (index : row_like_index set_of_closures_contents unit)
    (extension : env_extension) (w : value_slot) (ty : flambda_type),
    row_like_closures_case_satisfied statics vars v slot functions
      value_slots
      (Row_like_case
         (Closures_entry function_types closure_types value_slot_types)
         index extension) ->
    among w (contents_value_slots (closures_index_contents index)) = true ->
    lookup w value_slot_types = Some ty ->
    ∃ contents : value,
      lookup w value_slots = Some contents
      ∧ type_satisfied statics vars contents ty.

(* A shape as the compiler writes it: a mixed record has a flat suffix,
   and is [Value_only] otherwise. *)
Definition block_shape_canonical (shape : block_shape) : Prop :=
  match shape with
  | Scannable (Mixed_record _ flat_suffix) => flat_suffix <> []
  | Scannable Value_only | Float_record => True
  end.

(* Two such shapes that a block both has are one shape. *)
Definition block_shapes_disjoint_statement : Prop :=
  ∀ (shape shape' : block_shape) (tag : Z) (fields : list value),
    block_shape_canonical shape ->
    block_shape_canonical shape' ->
    block_has_shape shape tag fields ->
    block_has_shape shape' tag fields ->
    shape = shape'.
