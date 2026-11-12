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

(* C4's prototype of the heap. It is evidence for the request
   (requests/C4-heap.md), not the change: the change itself puts the heap
   in the state of FlambdaSemanticsSpec.v, where this file has a machine
   of its own beside the one that exists.

   This file is to be read with the request. It has
   - allocation, and what the primitives of the heap compute
     ([exec_prim], over FlambdaPrimitiveSpec.eval_prim, which is
     unchanged). The mutable arrays of values are cells too
     ([Cell_array]): what their four primitives do to a cell is here,
     over the functions of the section "Arrays" of
     FlambdaPrimitiveSpec.v, which say what they compute on the
     elements;
   - the compiler's classification of primitives by effects and
     coeffects ([effects_of_prim], [coeffects_of_prim]), against
     [Flambda_primitive.effects_and_coeffects], and the laws that tie it
     to [exec_prim];
   - a machine with a heap ([heap_state], [heap_step]): that of
     FlambdaSemanticsSpec.v with one more component, and an exit that
     carries the memory;
   - the relation on what is observed at exit ([outcome_related]), up to
     a correspondence between the locations of two runs, and refinement
     for it;
   - the invariant of a state ([state_closed]);
   - the relation on states that the machine respects
     ([states_related]), with the simulation and what follows from it;
   - the same relation up to symbols that the second state binds and the
     first neither binds nor names ([states_related_except]), which
     lifting needs, with the invariant of the first state
     ([state_code_free_of]) under which the machine respects it;
   - the invariant of states (a step keeps a state closed) and the
     statements that Simplify will need: deleting a binding that is not
     used, exchanging two bindings, sharing two applications of a
     primitive, a load from a block that is known, lifting a block or a
     closure to a symbol. They are proved.

   What is proved is in FlambdaHeapProofs.v: every [_statement] here. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaNormaliseSpec FlambdaUnusedStaticsSpec
  FlambdaClosuresSpec.
From OxCamlFlambda2 Require FlambdaNameAbstractionSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* Allocation                                                               *)
(* ======================================================================== *)

(* A location that the heap does not bind: the name that
   FlambdaNameAbstractionSpec.fresh_name gives outside the domain of the
   heap. [fresh_name] is the one function that looks at the number a
   name is, for locations as for variables, and only
   [fresh_location_statement] is to be used of this one. *)
Definition fresh_location (h : heap) : location :=
  FlambdaNameAbstractionSpec.fresh_name (domain h).

Definition fresh_location_statement : Prop :=
  ∀ h : heap, lookup (fresh_location h) h = None.

(* ======================================================================== *)
(* The primitives of the heap                                               *)
(* ======================================================================== *)

(* The field [field] of a block of values with this tag and these fields,
   under the checks of FlambdaPrimitiveSpec.eval_block_load. *)
Definition load_field (kind : block_access_kind) (field : Z) (block_tag : Z)
    (fields : list value) : option value :=
  match kind with
  | Block_access_values tag size field_kind =>
    if known_is tag block_tag
       && known_is size (Z.of_nat (length fields))
       && (0 <=? field)
    then
      let* loaded := nth_error fields (Z.to_nat field) in
      if
        match field_kind with
        | Any_value => kind_eqb (kind_of_value loaded) Value
        | Immediate => is_tagged_immediate loaded
        end
      then Some loaded
      else None
    else None
  end.

(* The fields with [field] replaced by [new], under the same checks: the
   tag and the size are those the access kind gives, the field is one the
   block has, and the new value is of kind [Value], and a tagged
   immediate where the access kind says so. *)
Definition store_field (kind : block_access_kind) (field : Z) (new : value)
    (block_tag : Z) (fields : list value) : option (list value) :=
  match kind with
  | Block_access_values tag size field_kind =>
    if known_is tag block_tag
       && known_is size (Z.of_nat (length fields))
       && (0 <=? field)
       && match field_kind with
          | Any_value => kind_eqb (kind_of_value new) Value
          | Immediate => is_tagged_immediate new
          end
    then replace_nth (Z.to_nat field) new fields
    else None
  end.

Definition is_location (v : value) : bool :=
  match v with
  | Value_location _ => true
  | _ => false
  end.

(* [Phys_equal] where one of the two values is a location: option (b) of
   the request. Two locations are equal when they are the same location.
   A location differs from a tagged immediate and from an immutable
   allocated value. Against anything else there is no answer: null,
   poison, a number that is not a value, a symbol that is not bound.
   Where neither value is a location the comparison is
   FlambdaPrimitiveSpec.eval_phys_equal, which answers of two tagged
   immediates and of one against an allocated value, and has no value on
   two immutable allocated values. That is a limit of the model and not
   what the compiler does; the CR is there (decision D19; decision 3 of
   requests/C4-heap.md; discrepancies C4-3 and R2-21). *)
Definition eval_phys_equal_location (statics : static_env) (v1 v2 : value)
    : option bool :=
  match v1, v2 with
  | Value_location l1, Value_location l2 => Some (Pos.eqb l1 l2)
  | Value_location _, v | v, Value_location _ =>
    if is_some (int_of_value Standard_tagged_immediate v)
       || is_allocated statics v
    then Some false
    else None
  | _, _ => None
  end.

Definition unit_value : value := Value_const (Tagged_immediate 0).

(* What a primitive of the heap does: its value and the heap after.
   - [Make_block_with_identity] binds a fresh location to a cell holding
     the arguments, which must be of kind [Value].
   - [Block_set] replaces a field of a mutable cell, and its value is
     unit. It has no value on anything else.
   - [Make_mutable_array] binds a fresh location to an array of the
     kind it carries, holding the arguments, of which there is at least
     one and each of which is a value that the kind holds
     (FlambdaPrimitiveSpec.array_made).
   - [Array_set] replaces an element of an array, and its value is
     unit (FlambdaPrimitiveSpec.array_stored: the index is in the
     bounds of the array, and the new value is one that the set kind
     takes and that the kind of the array holds). It has no value on
     anything else. *)
(* CR mshinwell: [Block_set] has no value on a block that was not made
   [Mutable]: an immutable block, a symbol, an [Immutable_unique] cell.
   The machine would write; Simplify keeps the facts it has about the
   block. The front end makes no such store: every store of lambda/ is
   into a record with a mutable field, a [ref], an object, a copy made
   by [Pduprecord] or a placeholder of tail-modulo-cons. [init] does not
   change what the store does; the only stores marked [Initialization]
   are those of tail-modulo-cons, which the conversion refuses
   (decision 4). Decision 5 of requests/C4-heap.md. *)
(* CR mshinwell: [Make_mutable_array] of no argument has no value. The
   compiler does not allocate the empty array: [Closure_conversion]
   makes a [Pmakearray] of no argument the one static empty array of
   its kind ([Static_const.empty_array]), whatever its mutability, so
   two empty arrays of a program may be physically equal, and a
   location for each would tell them apart. No term that the front end
   makes has a [Make_array] of no argument. It would be wrong if a
   pass comes to make one and the term is executed. Decided while the
   owner of the branch was away
   (middle_end/flambda2/rocq/status/P1.md). *)
Definition exec_heap_primitive (statics : static_env) (h : heap)
    (p : heap_primitive) (vs : list value) : option (value * heap) :=
  match p, vs with
  | Make_block_with_identity mut tag, vs =>
    if forallb (fun v => kind_eqb (kind_of_value v) Value) vs
    then
      let l := fresh_location h in
      Some (Value_location l, (l, Cell_block mut tag vs) :: h)
    else None
  | Block_set kind _ field, [v; new] =>
    match v with
    | Value_location l =>
      match lookup l h with
      | Some (Cell_block Cell_mutable tag fields) =>
        let* fields' := store_field kind field new tag fields in
        Some (unit_value, (l, Cell_block Cell_mutable tag fields') :: h)
      | _ => None
      end
    | _ => None
    end
  | Make_mutable_array kind, _ :: _ =>
    let* elements := array_made kind vs in
    let l := fresh_location h in
    Some (Value_location l, (l, Cell_array kind elements) :: h)
  | Array_set _ set_kind, [v; index; new] =>
    match v with
    | Value_location l =>
      match lookup l h with
      | Some (Cell_array kind elements) =>
        let* elements' := array_stored set_kind kind elements index new in
        Some (unit_value, (l, Cell_array kind elements') :: h)
      | _ => None
      end
    | _ => None
    end
  | _, _ => None
  end.

(* Whether a [Block_load] with this mark reads a cell of this
   mutability: one marked [Mutable] reads any cell, and one marked
   [Immutable] or [Immutable_unique] a cell made [Immutable_unique]. *)
Definition load_allowed (load_mut : mutability) (mut : cell_mutability)
    : bool :=
  match load_mut, mut with
  | Mutable, _ | (Immutable | Immutable_unique), Cell_immutable_unique => true
  | (Immutable | Immutable_unique), Cell_mutable => false
  end.

(* A unary primitive of FlambdaPrimitiveModel.v applied to a location: it
   reads the cell, and has no value on a location that is not bound.
   A [Block_load] reads the field as it is now, where its mark allows
   ([load_allowed]). [Get_tag] is the tag of the cell; [Is_int] and
   [Is_null] answer no; [Opaque_identity] is the location. The remaining
   unary primitives are on numbers or on strings, and have no value: a
   cell is neither. A primitive that is added and that reads a cell has
   its case here.
   Of an array, [Array_length] is the number of elements
   (FlambdaPrimitiveSpec.array_length_of), whatever the kind it
   carries; [Is_null] answers no, and so does [Is_int] without
   [variant_only]; [Opaque_identity] is the location. With
   [variant_only], [Is_int] has no value on an array, which is no
   variant: Simplify makes it [Invalid] there
   ([Provers.prove_is_int_generic_value]), as on a closure, a boxed
   number or a string (FlambdaPrimitiveSpec.eval_is_int). [Get_tag] and
   [Block_load] have no value on an array, nor [Array_length] on a
   block. *)
(* CR mshinwell: a [Block_load] marked [Immutable] has no value on a
   block made [Mutable]. Simplify takes a field so read never to change
   afterwards (it records the field in the type of the block and shares
   later loads), and nothing checks that (C4-2, R2-20). This first
   stage excludes more than that assumption does: every record with
   both mutable and immutable fields, from the first read of an
   immutable field.
   Two things that the front end makes are outside the model by ruling,
   at every stage, and the conversion refuses them:
   - the blocks that tail-modulo-cons builds (lambda/tmc.ml:
     placeholders made [Mutable], filled with [Heap_initialization],
     then read with immutable loads; R2-18): "we can ignore TMC for now
     b/c ... the pass produces broken Lambda code, that needs fixing in
     the prod compiler";
   - [Duplicate_block] followed by stores, which is the copy of a large
     record for [{ r with ... }] (lambda/translcore.ml,
     [transl_record]; miscompiled today, C4-4): "I think we can not
     model Pduprecord for the moment, it is broken as you say and is
     being fixed in prod".
   Decision 4 of requests/C4-heap.md. *)
Definition exec_unary_on_cell (p : unary_primitive) (l : location) (c : cell)
    : option value :=
  match c with
  | Cell_block mut tag fields =>
    match p with
    | Block_load kind load_mut field =>
      if load_allowed load_mut mut
      then load_field kind field tag fields
      else None
    | Get_tag => Some (Value_const (Naked_immediate tag))
    | Is_int _ | Is_null => Some (naked_bool false)
    | Opaque_identity kind =>
      if kind_eqb kind Value then Some (Value_location l) else None
    | _ => None
    end
  | Cell_array _ elements =>
    match p with
    | Array_length _ => array_length_of elements
    | Is_int false | Is_null => Some (naked_bool false)
    | Opaque_identity kind =>
      if kind_eqb kind Value then Some (Value_location l) else None
    | _ => None
    end
  end.

(* A binary primitive of FlambdaPrimitiveModel.v whose first argument is
   a location: it reads the cell. The only one is [Array_load], of an
   array: the element at the index, as it is now
   (FlambdaPrimitiveSpec.array_loaded), where the mark of the load
   allows. An array that has an identity is mutable, so that is where
   the load is marked [Mutable] ([load_allowed]). The remaining binary
   primitives have no value: [Phys_equal] with a location is not read
   here ([exec_bound_prim]), and the others are on numbers or on
   strings. *)
(* CR mshinwell: An [Array_load] marked [Immutable] has no value on an
   array that has an identity, as a [Block_load] so marked has none on
   a block made [Mutable] (the CR before [exec_unary_on_cell]). The
   front end makes one for the reads of an immutable array ([iarray]),
   and such an array may be a mutable array seen as immutable
   ([%array_to_iarray], which is the identity): the model refuses
   that program. Whether the reads of an array so frozen are stable is
   the question that decision 4 of requests/C4-heap.md asks of the
   fields of blocks. *)
Definition exec_binary_on_cell (p : binary_primitive) (l : location)
    (c : cell) (v2 : value) : option value :=
  match c, p with
  | Cell_array _ elements, Array_load _ load_kind load_mut =>
    if load_allowed load_mut Cell_mutable
    then array_loaded load_kind elements v2
    else None
  | _, _ => None
  end.

(* An argument that a primitive may be given: anything but a symbol or a
   location that is bound to nothing. *)
Definition argument_bound (statics : static_env) (h : heap) (v : value)
    : bool :=
  match v with
  | Value_symbol s => is_bound s (static_values statics)
  | Value_location l => is_bound l h
  | _ => true
  end.

(* What a primitive does to arguments that are bound. One that does not
   touch the heap is FlambdaPrimitiveSpec.eval_prim, and the heap is
   returned as it came. A unary primitive of a location reads its cell,
   [Phys_equal] with a location among its two arguments is the
   comparison above, and another binary primitive whose first argument
   is a location reads its cell. *)
Definition exec_bound_prim (statics : static_env) (h : heap) (p : prim)
    (vs : list value) : option (value * heap) :=
  match p, vs with
  | Heap p, vs => exec_heap_primitive statics h p vs
  | Unary p, [Value_location l] =>
    let* c := lookup l h in
    let* v := exec_unary_on_cell p l c in
    Some (v, h)
  | Binary (Phys_equal op), [v1; v2] =>
    if is_location v1 || is_location v2
    then
      let* same := eval_phys_equal_location statics v1 v2 in
      Some
        (naked_bool
           match op with
           | Phys_eq => same
           | Phys_neq => negb same
           end,
         h)
    else
      let* v := eval_prim statics p vs in
      Some (v, h)
  | Binary p, [Value_location l; v2] =>
    let* c := lookup l h in
    let* v := exec_binary_on_cell p l c v2 in
    Some (v, h)
  | _, _ =>
    let* v := eval_prim statics p vs in
    Some (v, h)
  end.

(* What a primitive does. It has no value when one of its arguments is a
   symbol or a location that is bound to nothing: any operation on such
   a name is undefined (the ruling on symbols, taken for locations too),
   whether or not the primitive would read what the name is bound to.
   So an allocation and a write take no such name, and [Phys_equal] does
   not compare a location that dangles. No state reached from a closed
   state has a location bound to nothing ([heap_step_closed_statement]).
   For symbols the same is intended and is not so yet:
   FlambdaWellFormedSpec.well_formed_unit does not ask that a unit bind
   the symbols it names (section 6 of the request). The machine relies
   on neither. *)
Definition exec_prim (statics : static_env) (h : heap) (p : prim)
    (vs : list value) : option (value * heap) :=
  if forallb (argument_bound statics h) vs
  then exec_bound_prim statics h p vs
  else None.

(* FlambdaPrimitiveSpec.eval_prim_symbols_bound_statement, of
   [exec_prim], and the same of locations. *)
Definition exec_prim_symbols_bound_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (p : prim) (vs : list value)
    (v : value) (s : symbol),
    exec_prim statics h p vs = Some (v, h') ->
    Value_symbol s ∈ vs ->
    lookup s (static_values statics) <> None.

Definition exec_prim_locations_bound_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (p : prim) (vs : list value)
    (v : value) (l : location),
    exec_prim statics h p vs = Some (v, h') ->
    Value_location l ∈ vs ->
    lookup l h <> None.

(* ======================================================================== *)
(* Effects and coeffects                                                    *)
(* ======================================================================== *)

(* [Effects.t]. *)
Inductive effects : Type :=
  | No_effects
  | Only_generative_effects (mut : mutability)
  | Arbitrary_effects.

(* [Coeffects.t]. *)
Inductive coeffects : Type :=
  | No_coeffects
  | Has_coeffects.

(* [Flambda_primitive.effects_and_coeffects], its first component. *)
Definition effects_of_prim (p : prim) : effects :=
  match p with
  | Unary (Opaque_identity _) => Arbitrary_effects
  | Unary (Box_number _) => Only_generative_effects Immutable
  | Unary _ | Binary _ => No_effects
  | Variadic (Make_block _) => Only_generative_effects Immutable
  | Heap (Make_block_with_identity Cell_mutable _) =>
    Only_generative_effects Mutable
  | Heap (Make_block_with_identity Cell_immutable_unique _) =>
    Only_generative_effects Immutable_unique
  | Heap (Block_set _ _ _) => Arbitrary_effects
  | Heap (Make_mutable_array _) => Only_generative_effects Mutable
  | Heap (Array_set _ _) => Arbitrary_effects
  end.

(* Its second component. *)
Definition coeffects_of_prim (p : prim) : coeffects :=
  match p with
  | Unary (Opaque_identity _) => Has_coeffects
  | Unary (Block_load _ Mutable _) => Has_coeffects
  | Binary (Array_load _ _ Mutable) => Has_coeffects
  | _ => No_coeffects
  end.

(* [Flambda_primitive.at_most_generative_effects]: what Simplify asks
   before it deletes a [Let] whose variable is not used. *)
Definition at_most_generative_effects (p : prim) : bool :=
  match effects_of_prim p with
  | No_effects | Only_generative_effects _ => true
  | Arbitrary_effects => false
  end.

(* The same of a named expression, as [Simplify_let_expr] asks it
   ([Named.at_most_generative_effects]): everything that is not a
   primitive qualifies. This is the premise that a statement which
   erases a binding needs: [FlambdaNominalSpec.unused_let_statement],
   and FlambdaNormaliseSpec.named_may_go. *)
Definition named_at_most_generative_effects (d : named) : bool :=
  match d with
  | Prim p _ => at_most_generative_effects p
  | Simple _ | Set_of_closures _ _ | Closure_of_set _ _ _
  | Project_value_slot _ _ | Project_value_slot_from _ _ _
  | Project_function_slot _ _ _ =>
    true
  end.

(* The stricter test, for as long as exits are compared exactly: an
   allocation that is deleted is then seen. *)
Definition named_has_no_effects (d : named) : bool :=
  match d with
  | Prim p _ =>
    match effects_of_prim p with
    | No_effects => true
    | Only_generative_effects _ | Arbitrary_effects => false
    end
  | Simple _ | Set_of_closures _ _ | Closure_of_set _ _ _
  | Project_value_slot _ _ | Project_value_slot_from _ _ _
  | Project_function_slot _ _ _ =>
    true
  end.

(* What a run may do to a heap: a cell that is bound stays bound. A
   block keeps its mutability, its tag and its number of fields, and
   its fields if it is not mutable. An array keeps its kind and its
   number of elements. *)
Definition heap_evolves (h h' : heap) : Prop :=
  (∀ (l : location) (mut : cell_mutability) (tag : Z) (fields : list value),
    lookup l h = Some (Cell_block mut tag fields) ->
    ∃ fields' : list value,
      lookup l h' = Some (Cell_block mut tag fields')
      ∧ length fields' = length fields
      ∧ (mut = Cell_immutable_unique -> fields' = fields))
  ∧ (∀ (l : location) (kind : array_kind) (elements : list value),
      lookup l h = Some (Cell_array kind elements) ->
      ∃ elements' : list value,
        lookup l h' = Some (Cell_array kind elements')
        ∧ length elements' = length elements).

(* Every primitive leaves a heap that the one it was given evolves to. *)
Definition exec_prim_evolves_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (p : prim) (vs : list value)
    (v : value),
    exec_prim statics h p vs = Some (v, h') -> heap_evolves h h'.

(* The elements of each array of a heap are values that the kind of the
   array holds. It is what the kind of an array is recorded for: the
   type that Simplify gives a mutable array says it of the array for as
   long as the array lives. Every primitive keeps it. *)
Definition arrays_hold_their_kinds (h : heap) : Prop :=
  ∀ (l : location) (kind : array_kind) (elements : list value) (v : value),
    lookup l h = Some (Cell_array kind elements) ->
    v ∈ elements ->
    array_element_ok kind v = true.

Definition exec_prim_arrays_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (p : prim) (vs : list value)
    (v : value),
    arrays_hold_their_kinds h ->
    exec_prim statics h p vs = Some (v, h') ->
    arrays_hold_their_kinds h'.

(* What Simplify knows of a mutable array, from its [Make_array]
   ([Simplify_variadic_primitive.simplify_make_array]): its length. The
   length of an array is the number of arguments it was made of, in
   every heap that the one after the allocation evolves to: an
   [Array_length] of an array whose [Make_array] is in sight is that
   number ([Simplify_unary_primitive.simplify_array_length]). There is
   no length where the number is not a tagged immediate. *)
Definition array_length_known_statement : Prop :=
  ∀ (statics : static_env) (h h1 h2 : heap) (kind : array_kind)
    (length_kind : array_kind_for_length) (vs : list value) (v : value),
    exec_prim statics h (Heap (Make_mutable_array kind)) vs = Some (v, h1) ->
    heap_evolves h1 h2 ->
    exec_prim statics h2 (Unary (Array_length length_kind)) [v]
    = let* n := array_length_of vs in
      Some (n, h2).

(* The array kind that a length, a load or a store carries changes
   nothing. [Simplify_common.specialise_array_kind] replaces [Values]
   and [Gc_ignorable_values] by [Immediates] in a load and in a store,
   where the type of the array says that its elements are immediates,
   and keeps the load kind and the set kind. *)
Definition array_kind_of_access_statement : Prop :=
  ∀ (statics : static_env) (h : heap) (vs : list value)
    (kind kind' : array_kind)
    (length_kind length_kind' : array_kind_for_length)
    (load_kind : array_load_kind) (mut : mutability)
    (set_kind : array_set_kind),
    exec_prim statics h (Unary (Array_length length_kind)) vs
    = exec_prim statics h (Unary (Array_length length_kind')) vs
    ∧ exec_prim statics h (Binary (Array_load kind load_kind mut)) vs
      = exec_prim statics h (Binary (Array_load kind' load_kind mut)) vs
    ∧ exec_prim statics h (Heap (Array_set kind set_kind)) vs
      = exec_prim statics h (Heap (Array_set kind' set_kind)) vs.

(* A primitive with no effects returns the heap as it came. *)
Definition no_effects_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (p : prim) (vs : list value)
    (v : value),
    effects_of_prim p = No_effects ->
    exec_prim statics h p vs = Some (v, h') ->
    h' = h.

(* A primitive with only generative effects returns the heap as it came,
   or with one new cell at a fresh location, which is its value. One
   whose result is immutable allocates nothing. *)
Definition only_generative_effects_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (p : prim) (vs : list value)
    (v : value) (mut : mutability),
    effects_of_prim p = Only_generative_effects mut ->
    exec_prim statics h p vs = Some (v, h') ->
    (mut = Immutable ∧ h' = h)
    ∨ (mut <> Immutable
       ∧ v = Value_location (fresh_location h)
       ∧ ∃ c : cell, h' = (fresh_location h, c) :: h).

(* A primitive with neither effects nor coeffects has the value it had
   in every heap that the one it was run in evolves to: it may be run
   later, or once in place of twice. *)
Definition no_coeffects_statement : Prop :=
  ∀ (statics : static_env) (h1 h1' h2 : heap) (p : prim) (vs : list value)
    (v : value),
    effects_of_prim p = No_effects ->
    coeffects_of_prim p = No_coeffects ->
    heap_evolves h1 h2 ->
    exec_prim statics h1 p vs = Some (v, h1') ->
    exec_prim statics h2 p vs = Some (v, h2).

(* The load marked [Mutable] is not such a primitive: its value changes
   with a write, so it may not be shared with an earlier one. *)
Definition mutable_load_not_stable_statement : Prop :=
  ∃ (statics : static_env) (h1 h2 : heap) (p : prim) (vs : list value)
    (v1 v2 : value),
    effects_of_prim p = No_effects
    ∧ heap_evolves h1 h2
    ∧ exec_prim statics h1 p vs = Some (v1, h1)
    ∧ exec_prim statics h2 p vs = Some (v2, h2)
    ∧ v1 <> v2.

(* ======================================================================== *)
(* A machine with a heap                                                    *)
(* ======================================================================== *)

(* The state of FlambdaSemanticsSpec.v, and a heap. *)
Record heap_state : Type := Heap_state {
  hs_expr : expr;
  hs_vars : env;
  hs_conts : cont_env;
  hs_statics : static_env;
  hs_heap : heap
}.

(* What is observed when a state leaves through a continuation that is
   not bound: the arguments, and the memory they point into. *)
Record outcome : Type := Outcome {
  outcome_values : list value;
  outcome_statics : static_env;
  outcome_heap : heap
}.

Inductive heap_step_result : Type :=
  | Heap_step (s : heap_state)
  | Heap_exit (k : continuation) (o : outcome)
  | Heap_undefined.

(* FlambdaSemanticsSpec.eval_named, with the heap. Only a primitive may
   change it. *)
Definition exec_named (statics : static_env) (h : heap) (vars : env)
    (defining_expr : named) : option (value * heap) :=
  match defining_expr with
  | Prim p args =>
    let* vs := eval_simples vars args in
    exec_prim statics h p vs
  | _ =>
    let* v := eval_named statics vars defining_expr in
    Some (v, h)
  end.

(* FlambdaSemanticsSpec.call_code, with the heap carried along. *)
Definition heap_call_code (closure : value) (c : code) (vs : list value)
    (args_arity return_arity : arity) (return_to exn_to : cont_value)
    (statics : static_env) (h : heap) : heap_step_result :=
  if binds_statics (code_body c) then Heap_undefined
  else if
    negb
      (kinds_eqb (map kind_of_value vs) (unarize args_arity)
       && kinds_per_parameter_eqb (unarize_per_parameter args_arity)
            (unarize_per_parameter (code_params_arity c))
       && arity_eqb return_arity (code_result_arity c))
  then Heap_undefined
  else
    match bind_params (code_params c) vs [(code_my_closure c, closure)] with
    | Some callee_vars =>
      Heap_step
        (Heap_state (code_body c) callee_vars
           [(code_return_continuation c, return_to);
            (code_exn_continuation c, exn_to)]
           statics h)
    | None => Heap_undefined
    end.

(* FlambdaSemanticsSpec.run_call, with the heap carried along. What a
   call is ([FlambdaSemanticsSpec.shape_of_call]) does not depend on the
   heap: no closure and no partial application is a location. *)
Definition heap_run_call (return_partial : value -> heap_step_result)
    (shape : option call_shape) (return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) (h : heap)
    : heap_step_result :=
  match shape with
  | Some (Full_call closure c vs args_arity) =>
    heap_call_code closure c vs args_arity return_arity return_to exn_to
      statics h
  | Some (Over_call closure c vs remaining args_arity remaining_arity) =>
    heap_call_code closure c vs args_arity (code_result_arity c)
      (Over_application remaining remaining_arity return_arity return_to
         exn_to)
      exn_to statics h
  | Some (Partial_call partial) => return_partial partial
  | None => Heap_undefined
  end.

(* FlambdaSemanticsSpec.apply_cont_value, with the heap carried along. *)
Fixpoint heap_apply_cont_value (c : cont_value) (vs : list value)
    (statics : static_env) (h : heap) {struct c} : heap_step_result :=
  match c with
  | Outer k => Heap_exit k (Outcome vs statics h)
  | Closure (Handler params metadata handler) def_vars def_conts recursive =>
    if kinds_eqb (map kind_of_value vs) (hm_params_kinds metadata)
    then
      match bind_params params vs def_vars with
      | Some handler_vars =>
        Heap_step
          (Heap_state handler handler_vars
             (rec_closures recursive def_vars def_conts ++ def_conts) statics
             h)
      | None => Heap_undefined
      end
    else Heap_undefined
  | Extra_args c extra => heap_apply_cont_value c (vs ++ extra) statics h
  | Over_application remaining remaining_arity return_arity return_to exn_to =>
    match vs with
    | [v] =>
      heap_run_call
        (fun partial => heap_apply_cont_value return_to [partial] statics h)
        (shape_of_call statics v Indirect remaining remaining_arity
           return_arity)
        return_arity return_to exn_to statics h
    | _ => Heap_undefined
    end
  end.

(* FlambdaSemanticsSpec.call_function, with the heap carried along. *)
Definition heap_call_function (callee : value) (kind : call_kind)
    (vs : list value) (args_arity return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) (h : heap)
    : heap_step_result :=
  heap_run_call
    (fun partial => heap_apply_cont_value return_to [partial] statics h)
    (shape_of_call statics callee kind vs args_arity return_arity)
    return_arity return_to exn_to statics h.

(* FlambdaSemanticsSpec.step, with the heap carried along. The case of
   [Let] is the only one that may change it. *)
Definition heap_step (s : heap_state) : heap_step_result :=
  match s with
  | Heap_state (Let x kind defining_expr body) vars conts statics h =>
    match exec_named statics h vars defining_expr with
    | Some (v, h') =>
      if kind_eqb (kind_of_value v) kind
      then Heap_step (Heap_state body ((x, v) :: vars) conts statics h')
      else Heap_undefined
    | None => Heap_undefined
    end
  | Heap_state (Let_static bindings body) vars conts statics h =>
    match eval_static_bindings vars bindings statics with
    | Some statics' => Heap_step (Heap_state body vars conts statics' h)
    | None => Heap_undefined
    end
  | Heap_state (Let_cont_non_recursive k handler body) vars conts statics h =>
    Heap_step
      (Heap_state body vars ((k, Closure handler vars conts []) :: conts)
         statics h)
  | Heap_state (Let_cont_recursive handlers body) vars conts statics h =>
    if handlers_bind_statics handlers then Heap_undefined
    else
      Heap_step
        (Heap_state body vars (rec_closures handlers vars conts ++ conts)
           statics h)
  | Heap_state (Apply ap) vars conts statics h =>
    match
      eval_simple vars (ap_callee ap), eval_simples vars (ap_args ap),
      eval_simples vars (exn_extra_simples ap)
    with
    | Some callee, Some vs, Some extra =>
      heap_call_function callee (ap_call_kind ap) vs (ap_args_arity ap)
        (ap_return_arity ap) (resolve (ap_continuation ap) conts)
        (with_extra_args (resolve (ap_exn_continuation ap) conts) extra)
        statics h
    | _, _, _ => Heap_undefined
    end
  | Heap_state (Apply_cont ac) vars conts statics h =>
    match eval_simples vars (ac_args ac) with
    | Some vs =>
      heap_apply_cont_value (resolve (ac_continuation ac) conts) vs statics h
    | None => Heap_undefined
    end
  | Heap_state (Switch scrutinee arms) vars conts statics h =>
    match eval_simple vars scrutinee with
    | Some v =>
      match naked_immediate_of_value v with
      | Some i =>
        match find_arm i arms with
        | Some ac =>
          Heap_step (Heap_state (Apply_cont ac) vars conts statics h)
        | None => Heap_undefined
        end
      | None => Heap_undefined
      end
    | None => Heap_undefined
    end
  | Heap_state Invalid _ _ _ _ => Heap_undefined
  end.

Fixpoint heap_run (fuel : nat) (s : heap_state) : heap_step_result :=
  match fuel with
  | O => Heap_step s
  | S fuel =>
    match heap_step s with
    | Heap_step s' => heap_run fuel s'
    | result => result
    end
  end.

Inductive heap_behaviour : Type :=
  | Heap_exits (k : continuation) (o : outcome)
  | Heap_goes_wrong
  | Heap_diverges.

Definition heap_behaves (s : heap_state) (b : heap_behaviour) : Prop :=
  match b with
  | Heap_exits k o => ∃ fuel : nat, heap_run fuel s = Heap_exit k o
  | Heap_goes_wrong => ∃ fuel : nat, heap_run fuel s = Heap_undefined
  | Heap_diverges =>
    ∀ fuel : nat, ∃ s' : heap_state, heap_run fuel s = Heap_step s'
  end.

(* A step evolves the heap. *)
Definition heap_step_evolves_statement : Prop :=
  ∀ s s' : heap_state,
    heap_step s = Heap_step s' -> heap_evolves (hs_heap s) (hs_heap s').

(* Where no primitive of the heap is run, the machine is that of
   FlambdaSemanticsSpec.v with the heap carried along: a state whose next
   step is not a [Let] of a primitive steps as its projection does. *)
Definition forget_heap (s : heap_state) : state :=
  State (hs_expr s) (hs_vars s) (hs_conts s) (hs_statics s) (hs_heap s).

Definition is_let_prim (e : expr) : bool :=
  match e with
  | Let _ _ (Prim _ _) _ => true
  | _ => false
  end.

Definition heap_step_agrees_statement : Prop :=
  ∀ s : heap_state,
    is_let_prim (hs_expr s) = false ->
    match heap_step s, step (forget_heap s) with
    | Heap_step s', Step t => forget_heap s' = t ∧ hs_heap s' = hs_heap s
    | Heap_exit k o, Exit k' vs _ =>
      k = k' ∧ o = Outcome vs (hs_statics s) (hs_heap s)
    | Heap_undefined, Undefined => True
    | _, _ => False
    end.

(* ======================================================================== *)
(* What is observed at exit, up to a correspondence                         *)
(* ======================================================================== *)

(* A correspondence between the memories of two runs: which location of
   the first is which of the second, and which values of the first are
   which values of the second. The second part is what makes cyclic
   static data comparable: it is a bisimulation, justified one step at a
   time ([correspondence_valid]). *)
Record correspondence : Type := Correspondence {
  corr_locations : location -> location -> Prop;
  corr_values : value -> value -> Prop
}.

Definition partial_bijection {A B : Type} (R : A -> B -> Prop) : Prop :=
  ∀ (a a' : A) (b b' : B), R a b -> R a' b' -> (a = a' <-> b = b').

(* A closure whose set is known in full: one made by a [Let], which holds
   its set; a symbol bound to the closure of one function; or a symbol of
   a static set that names a symbol for each of its functions, each bound
   to the closure of the set at its slot
   (FlambdaClosuresSpec.static_set_bound). The projection of a function
   slot from such a closure is the closure of the same set at that slot.
   Nothing in a static environment says that a static set is such: a
   projection from a symbol gives the symbol that its set names for the
   slot, whatever that symbol is bound to (the CR before
   FlambdaValueSpec.project_function_slot, decision D4). The run of a
   well-formed unit keeps every static set such
   (FlambdaClosuresSpec.well_formed_sets_bound_statement). *)
Definition set_bound (statics : static_env) (v : value) : Prop :=
  match v with
  | Value_symbol s =>
    match lookup s (static_values statics) with
    | Some (Static_closure_of_set _ closure_symbols function_decls slot_values)
      =>
      map fst closure_symbols = map fst function_decls
      ∧ static_set_bound statics closure_symbols function_decls slot_values
    | _ => True
    end
  | _ => True
  end.

Section Related.

Variable poison_refines : bool.
Variable r : correspondence.
Variables statics statics' : static_env.

(* What two related boxed numbers hold: the same number; or, with
   [poison_refines], a poison in the first and any number of its kind in
   the second. It is the one relation on the contents of a boxed number,
   whether the number was boxed by a primitive or is what a symbol is
   bound to. *)
Definition contents_related (c c' : const) : Prop :=
  c = c'
  ∨ (poison_refines = true
     ∧ ∃ kind : flambda_kind, c = Poison kind ∧ kind_of_const c' = kind).

(* What two related values have in common at their heads, with [R] on
   what they hold.
   - A constant is itself.
   - A location is the location that corresponds to it.
   - Immutable values are compared by their contents, read through the
     observations, so through a symbol on either side: a block made by a
     primitive is a symbol bound to a static block with related fields.
   - A closure is read as one of a set ([closure_in_set]): the same
     function slot of a set with the same function declarations, with
     value slots of the same names and related values. And the closures
     at the other function slots of the two sets are related: either the
     two sets are known in full ([set_bound]), and then they are; or a
     function slot can be projected ([project_function_slot]) from both
     or from neither, to related values. So a closure made by a [Let] is
     a symbol of a static set with the same functions and related value
     slots, as a block made by a primitive is a symbol bound to a static
     block.
   - A symbol that is nothing that can be read, in either memory (one
     that is not bound, as a symbol of another unit), is itself.
   - With [poison_refines], a poison of the first run is any value of
     its kind in the second, and a boxed poison any boxed number of its
     kind ([contents_related]).
   - A partial application is a partial application of a related
     callee to related arguments, at the same arity. Only a call reads
     its callee and its arguments; a primitive sees no more of it than
     that it is allocated. (The relation does not relate a partial
     application to a closure. Simplify makes of a partial application
     of a known function the closure of a wrapper,
     [simplify_direct_partial_application]; whoever validates that
     rewrite will need a rule for it.)
   [Step_same_boxed_number] is for a [Value_boxed_number] whose contents
   are not of a kind that has a boxed form, which no observation reads:
   it is itself; and [Step_same_closure_of_set] for a closure at a
   function slot that its set has not got, which no observation reads
   either. *)
Inductive value_step (R : value -> value -> Prop) : value -> value -> Prop :=
  | Step_const (c : const) : value_step R (Value_const c) (Value_const c)
  | Step_location (l l' : location) :
    corr_locations r l l' ->
    value_step R (Value_location l) (Value_location l')
  | Step_block (v v' : value) (tag : Z) (fields fields' : list value) :
    block_of statics v = Some (tag, fields) ->
    block_of statics' v' = Some (tag, fields') ->
    Forall2 R fields fields' ->
    value_step R v v'
  | Step_boxed_number (v v' : value) (c c' : const) :
    boxed_number_of statics v = Some c ->
    boxed_number_of statics' v' = Some c' ->
    contents_related c c' ->
    value_step R v v'
  | Step_same_boxed_number (c : const) :
    value_step R (Value_boxed_number c) (Value_boxed_number c)
  | Step_string (v v' : value) (bytes : list Z) :
    string_of statics v = Some bytes ->
    string_of statics' v' = Some bytes ->
    value_step R v v'
  | Step_closure (v v' : value) (slot : function_slot)
      (function_decls : list (function_slot * code_id))
      (slots slots' : list (value_slot * value)) :
    closure_in_set statics v = Some (slot, function_decls, slots) ->
    closure_in_set statics' v' = Some (slot, function_decls, slots') ->
    map fst slots = map fst slots' ->
    Forall2 R (map snd slots) (map snd slots') ->
    (set_bound statics v ∧ set_bound statics' v')
    ∨ ((∀ (move_to : function_slot) (w : value),
         project_function_slot statics slot move_to v = Some w ->
         ∃ w' : value,
           project_function_slot statics' slot move_to v' = Some w' ∧ R w w')
       ∧ (∀ move_to : function_slot,
           project_function_slot statics slot move_to v = None ->
           project_function_slot statics' slot move_to v' = None))
    ->
    value_step R v v'
  | Step_same_closure_of_set (slot : function_slot)
      (function_decls : list (function_slot * code_id))
      (slots : list (value_slot * value)) :
    lookup slot function_decls = None ->
    value_step R (Value_closure_of_set slot function_decls slots)
      (Value_closure_of_set slot function_decls slots)
  | Step_opaque_symbol (s : symbol) :
    is_allocated statics (Value_symbol s) = false ->
    is_allocated statics' (Value_symbol s) = false ->
    value_step R (Value_symbol s) (Value_symbol s)
  | Step_poison (kind : flambda_kind) (v' : value) :
    poison_refines = true ->
    kind_of_value v' = kind ->
    value_step R (Value_const (Poison kind)) v'
  | Step_partial_application (callee callee' : value)
      (args args' : list value) (args_arity : arity) :
    R callee callee' ->
    Forall2 R args args' ->
    value_step R (Value_partial_application callee args args_arity)
      (Value_partial_application callee' args' args_arity).

(* A value of the first run is a value of the second: the two
   correspond, or they have their heads in common and what they hold is
   related. *)
#[local] Set Warnings "-register-all".
Inductive value_related : value -> value -> Prop :=
  | Related_corr (v v' : value) :
    corr_values r v v' -> value_related v v'
  | Related_step (v v' : value) :
    value_step value_related v v' -> value_related v v'.

Definition cell_related (c c' : cell) : Prop :=
  match c, c' with
  | Cell_block mut tag fields, Cell_block mut' tag' fields' =>
    mut = mut' ∧ tag = tag' ∧ Forall2 value_related fields fields'
  | Cell_array kind elements, Cell_array kind' elements' =>
    kind = kind' ∧ Forall2 value_related elements elements'
  | _, _ => False
  end.

(* The correspondence is one between these two memories: on locations it
   is a partial bijection, and locations that correspond are bound to
   cells with related contents; values that correspond have their heads
   in common and hold related values. *)
Definition correspondence_valid (h h' : heap) : Prop :=
  partial_bijection (corr_locations r)
  ∧ (∀ l l' : location,
      corr_locations r l l' ->
      ∃ c c' : cell,
        lookup l h = Some c ∧ lookup l' h' = Some c' ∧ cell_related c c')
  ∧ (∀ v v' : value,
      corr_values r v v' -> value_step value_related v v').

End Related.

(* Two outcomes are related when some correspondence between their
   memories relates their values. Only what the values reach is
   constrained. *)
Definition outcome_related (poison_refines : bool) (o o' : outcome) : Prop :=
  ∃ r : correspondence,
    correspondence_valid poison_refines r (outcome_statics o)
      (outcome_statics o') (outcome_heap o) (outcome_heap o')
    ∧ Forall2
        (value_related poison_refines r (outcome_statics o)
           (outcome_statics o'))
        (outcome_values o) (outcome_values o').

Definition outcome_refines : outcome -> outcome -> Prop :=
  outcome_related true.

Definition outcome_equivalent : outcome -> outcome -> Prop :=
  outcome_related false.

(* ======================================================================== *)
(* Closed memories                                                          *)
(* ======================================================================== *)

(* The locations of a value. *)
Fixpoint locations_of_value (v : value) : list location :=
  match v with
  | Value_const _ | Value_symbol _ | Value_boxed_number _ => []
  | Value_closure _ slots | Value_closure_of_set _ _ slots =>
    flat_map (fun slot => locations_of_value (snd slot)) slots
  | Value_block _ fields => flat_map locations_of_value fields
  | Value_location l => [l]
  | Value_partial_application callee args _ =>
    locations_of_value callee ++ flat_map locations_of_value args
  end.

(* No location of the value dangles. *)
Definition value_closed (h : heap) (v : value) : Prop :=
  ∀ l : location, l ∈ locations_of_value v -> is_bound l h = true.

Definition values_of_cell (c : cell) : list value :=
  match c with
  | Cell_block _ _ fields => fields
  | Cell_array _ elements => elements
  end.

Definition values_of_static (a : statically_allocated_value) : list value :=
  match a with
  | Static_closure _ slots | Static_closure_of_set _ _ _ slots =>
    map snd slots
  | Static_block _ fields => fields
  | Static_boxed_number v => [v]
  | Static_string _ => []
  end.

(* No location dangles in the heap or in the static environment, and
   every field of a cell is of kind [Value]. *)
Definition memory_closed (statics : static_env) (h : heap) : Prop :=
  (∀ (l : location) (c : cell) (v : value),
    lookup l h = Some c ->
    v ∈ values_of_cell c ->
    value_closed h v ∧ kind_of_value v = Value)
  ∧ (∀ (s : symbol) (a : statically_allocated_value) (v : value),
      lookup s (static_values statics) = Some a ->
      v ∈ values_of_static a ->
      value_closed h v).

Definition outcome_closed (o : outcome) : Prop :=
  memory_closed (outcome_statics o) (outcome_heap o)
  ∧ (∀ v : value, v ∈ outcome_values o -> value_closed (outcome_heap o) v).

(* A closed outcome is related to itself, in both senses. *)
Definition outcome_related_reflexive_statement : Prop :=
  ∀ (poison_refines : bool) (o : outcome),
    outcome_closed o -> outcome_related poison_refines o o.

(* The relation that does not let poison be refined is included in the
   one that does. *)
Definition outcome_equivalent_refines_statement : Prop :=
  ∀ o o' : outcome, outcome_equivalent o o' -> outcome_refines o o'.

(* Without poison the relation is symmetric. *)
Definition outcome_equivalent_symmetric_statement : Prop :=
  ∀ o o' : outcome, outcome_equivalent o o' -> outcome_equivalent o' o.

(* The relation composes: this is what lets refinements be chained. *)
Definition outcome_related_transitive_statement : Prop :=
  ∀ (poison_refines : bool) (o1 o2 o3 : outcome),
    outcome_related poison_refines o1 o2 ->
    outcome_related poison_refines o2 o3 ->
    outcome_related poison_refines o1 o3.

(* The closures at the other function slots of two related closures are
   related: where a function slot can be projected from the first of two
   related values, it can from the second, to a related value. *)
Definition related_projections_statement : Prop :=
  ∀ (poison_refines : bool) (r : correspondence) (statics statics' : static_env)
    (h h' : heap) (v v' w : value) (move_from move_to : function_slot),
    correspondence_valid poison_refines r statics statics' h h' ->
    value_related poison_refines r statics statics' v v' ->
    project_function_slot statics move_from move_to v = Some w ->
    ∃ w' : value,
      project_function_slot statics' move_from move_to v' = Some w'
      ∧ value_related poison_refines r statics statics' w w'.

(* The relation sees the difference between two cells and one cell twice,
   and no difference in which location a cell is at. *)
Definition aliasing_observed_statement : Prop :=
  ∀ (l1 l2 l : location) (c : cell),
    l1 <> l2 ->
    ~ outcome_related true
        (Outcome [Value_location l1; Value_location l2] empty_static_env
           [(l1, c); (l2, c)])
        (Outcome [Value_location l; Value_location l] empty_static_env
           [(l, c)]).

Definition location_names_not_observed_statement : Prop :=
  ∀ (l l' : location) (c : cell),
    values_of_cell c = [Value_const (Tagged_immediate 0)] ->
    outcome_equivalent
      (Outcome [Value_location l] empty_static_env [(l, c)])
      (Outcome [Value_location l'] empty_static_env [(l', c)]).

(* D6: a block made by a primitive and a symbol bound to an equal static
   block are the same at exit. *)
Definition block_and_symbol_related_statement : Prop :=
  ∀ (s : symbol) (tag : Z) (i : Z),
    outcome_equivalent
      (Outcome [Value_block tag [Value_const (Tagged_immediate i)]]
         empty_static_env empty_heap)
      (Outcome [Value_symbol s]
         (Static_env []
            [(s, Static_block tag [Value_const (Tagged_immediate i)])])
         empty_heap).

(* A cell that nothing reaches is not observed. *)
Definition garbage_not_observed_statement : Prop :=
  ∀ (l : location) (c : cell) (vs : list value),
    outcome_closed (Outcome vs empty_static_env empty_heap) ->
    outcome_equivalent (Outcome vs empty_static_env [(l, c)])
      (Outcome vs empty_static_env empty_heap).

(* A boxed poison is refined by a boxed number of its kind, whichever of
   the two is a symbol: the contents of a boxed number are related in
   one way ([contents_related]). *)
Definition boxed_poison_refined_statement : Prop :=
  ∀ (s : symbol) (c : const),
    boxable_contents c = Some c ->
    outcome_refines
      (Outcome [Value_boxed_number (Poison (kind_of_const c))]
         empty_static_env empty_heap)
      (Outcome [Value_symbol s]
         (Static_env [] [(s, Static_boxed_number (Value_const c))])
         empty_heap)
    ∧ outcome_refines
        (Outcome [Value_symbol s]
           (Static_env []
              [(s,
                Static_boxed_number (Value_const (Poison (kind_of_const c))))])
           empty_heap)
        (Outcome [Value_boxed_number c] empty_static_env empty_heap).

(* ======================================================================== *)
(* Refinement                                                               *)
(* ======================================================================== *)

Definition heap_behaviour_refines (b b' : heap_behaviour) : Prop :=
  match b, b' with
  | Heap_exits k o, Heap_exits k' o' => k = k' ∧ outcome_refines o o'
  | Heap_goes_wrong, Heap_goes_wrong | Heap_diverges, Heap_diverges => True
  | _, _ => False
  end.

(* FlambdaSemanticsSpec.refines, with exits compared up to a
   correspondence. *)
Definition heap_refines (source target : heap_state) : Prop :=
  (∀ (k : continuation) (o : outcome),
    heap_behaves source (Heap_exits k o) ->
    ∃ o' : outcome,
      heap_behaves target (Heap_exits k o') ∧ outcome_refines o o')
  ∧ (∀ b' : heap_behaviour,
      b' <> Heap_diverges ->
      heap_behaves target b' ->
      (∃ b : heap_behaviour,
        heap_behaves source b ∧ heap_behaviour_refines b b')
      ∨ heap_behaves source Heap_goes_wrong).

(* The invariant of a state: no location dangles, in the environment, in
   the continuations (in the environments of their closures, in their
   extra arguments and in the arguments that remain of an
   over-application), in the static environment or in the heap. *)
Fixpoint cont_value_closed (h : heap) (c : cont_value) : Prop :=
  match c with
  | Closure _ vars conts _ =>
    (∀ (x : variable) (v : value), (x, v) ∈ vars -> value_closed h v)
    ∧ (fix conts_closed (conts : list (continuation * cont_value)) : Prop :=
         match conts with
         | [] => True
         | (_, c) :: conts => cont_value_closed h c ∧ conts_closed conts
         end)
        conts
  | Outer _ => True
  | Extra_args c extra =>
    (∀ v : value, v ∈ extra -> value_closed h v) ∧ cont_value_closed h c
  | Over_application remaining _ _ return_to exn_to =>
    (∀ v : value, v ∈ remaining -> value_closed h v)
    ∧ cont_value_closed h return_to
    ∧ cont_value_closed h exn_to
  end.

Definition state_closed (s : heap_state) : Prop :=
  memory_closed (hs_statics s) (hs_heap s)
  ∧ (∀ (x : variable) (v : value),
      (x, v) ∈ hs_vars s -> value_closed (hs_heap s) v)
  ∧ (∀ (k : continuation) (c : cont_value),
      (k, c) ∈ hs_conts s -> cont_value_closed (hs_heap s) c).

(* Refinement of expressions: under all environments and memories that
   are closed. *)
Definition heap_expr_refines (source target : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env) (h : heap),
    state_closed (Heap_state source vars conts statics h) ->
    heap_refines (Heap_state source vars conts statics h)
      (Heap_state target vars conts statics h).

(* ======================================================================== *)
(* The machine respects the relation                                        *)
(* ======================================================================== *)

(* The lemma that congruence needs: two states that run the same
   expression under related environments, continuations and memories
   have related behaviours. It is for the relation without poison; the
   form with related code is today's FlambdaContextProofs.transfer. *)

(* Two environments hold related values for the variables that are
   needed: a variable that is needed and bound in the first is bound in
   the second, to a related value. A variable that is not needed may be
   bound on one side only, so a binding that is not used may be
   deleted. *)
Definition env_related (R : value -> value -> Prop)
    (needed : variable -> bool) (vars vars' : env) : Prop :=
  ∀ (x : variable) (v : value),
    needed x = true ->
    lookup x vars = Some v ->
    ∃ v' : value, lookup x vars' = Some v' ∧ R v v'.

(* The variables that a continuation closure may read in the environment
   of its definition: those free in its handler, and in the handlers
   that are in scope in it. *)
Definition needed_by_closure (h : continuation_handler)
    (recursive : list (continuation * continuation_handler)) (x : variable)
    : bool :=
  var_free_in_handler_b x h
  || existsb (fun '(_, h) => var_free_in_handler_b x h) recursive.

(* Two continuations are related: the same way out; or closures of the
   same handlers, under related environments and related continuations;
   or related continuations with related extra arguments; or what is
   left of two over-applications at the same arities, with related
   arguments that remain and related continuations. *)
#[local] Set Warnings "-register-all".
Inductive cont_related (R : value -> value -> Prop)
    : cont_value -> cont_value -> Prop :=
  | Related_outer (k : continuation) : cont_related R (Outer k) (Outer k)
  | Related_closure (h : continuation_handler) (vars vars' : env)
      (conts conts' : list (continuation * cont_value))
      (recursive : list (continuation * continuation_handler)) :
    env_related R (needed_by_closure h recursive) vars vars' ->
    Forall2
      (fun b b' => fst b = fst b' ∧ cont_related R (snd b) (snd b'))
      conts conts' ->
    cont_related R (Closure h vars conts recursive)
      (Closure h vars' conts' recursive)
  | Related_extra_args (c c' : cont_value) (extra extra' : list value) :
    cont_related R c c' ->
    Forall2 R extra extra' ->
    cont_related R (Extra_args c extra) (Extra_args c' extra')
  | Related_over_application (remaining remaining' : list value)
      (remaining_arity return_arity : arity)
      (return_to return_to' exn_to exn_to' : cont_value) :
    Forall2 R remaining remaining' ->
    cont_related R return_to return_to' ->
    cont_related R exn_to exn_to' ->
    cont_related R
      (Over_application remaining remaining_arity return_arity return_to
         exn_to)
      (Over_application remaining' remaining_arity return_arity return_to'
         exn_to').

Definition conts_related (R : value -> value -> Prop)
    (conts conts' : cont_env) : Prop :=
  Forall2
    (fun b b' => fst b = fst b' ∧ cont_related R (snd b) (snd b'))
    conts conts'.

(* Two states are related: they run the same expression, with the same
   code and the same symbols bound, and there is a correspondence
   between their memories, valid without poison, under which each symbol
   is itself (the expression may name any), the environments hold
   related values for the free variables of the expression, and the
   continuations are related. *)
Definition states_related (s s' : heap_state) : Prop :=
  hs_expr s = hs_expr s'
  ∧ static_code (hs_statics s) = static_code (hs_statics s')
  ∧ (∀ sym : symbol,
      is_bound sym (static_values (hs_statics s))
      = is_bound sym (static_values (hs_statics s')))
  ∧ ∃ r : correspondence,
      correspondence_valid false r (hs_statics s) (hs_statics s')
        (hs_heap s) (hs_heap s')
      ∧ (∀ sym : symbol, corr_values r (Value_symbol sym) (Value_symbol sym))
      ∧ env_related (value_related false r (hs_statics s) (hs_statics s'))
          (fun x => var_free_b x (hs_expr s)) (hs_vars s) (hs_vars s')
      ∧ conts_related (value_related false r (hs_statics s) (hs_statics s'))
          (hs_conts s) (hs_conts s').

(* The simulation. Where the first state steps, the second steps to a
   related state; where it exits, the second exits through the same
   continuation with an equivalent outcome. Nothing is asked where the
   first is undefined. *)
Definition heap_run_related_statement : Prop :=
  ∀ (fuel : nat) (s s' : heap_state),
    states_related s s' ->
    match heap_run fuel s with
    | Heap_step s1 =>
      ∃ s1' : heap_state,
        heap_run fuel s' = Heap_step s1' ∧ states_related s1 s1'
    | Heap_exit k o =>
      ∃ o' : outcome,
        heap_run fuel s' = Heap_exit k o' ∧ outcome_equivalent o o'
    | Heap_undefined => True
    end.

(* So a state is refined by every state related to it. *)
Definition machine_respects_relation_statement : Prop :=
  ∀ s s' : heap_state, states_related s s' -> heap_refines s s'.

(* A closed state is related to itself, under the correspondence that is
   the identity on the locations it binds. So refinement is reflexive on
   closed states. *)
Definition closed_state_related_statement : Prop :=
  ∀ s : heap_state, state_closed s -> states_related s s.

Definition heap_refines_reflexive_statement : Prop :=
  ∀ s : heap_state, state_closed s -> heap_refines s s.

(* ======================================================================== *)
(* The relation up to symbols that the second state binds                   *)
(* ======================================================================== *)

(* Lifting makes the second state bind a symbol that the first does not
   bind. [states_related] does not allow it: it asks that the two states
   bind the same symbols, and that every symbol corresponds to itself.
   Here some symbols are left out of both conditions
   (FlambdaUnusedStaticsSpec.dropped; only its symbols are used). What is
   asked of a symbol left out is that the first state neither binds it
   nor names it, and that the second binds it to something allocated.

   The first state may not name such a symbol: a symbol that is bound to
   nothing is a value that may be passed and returned, and the same
   symbol bound to a block is another. For the values of the first state
   this follows from the relation: a value that is related to a value of
   the second state is not a symbol that is bound to nothing in the first
   and allocated in the second. For its expression, its handlers and its
   code it is an invariant ([state_code_free_of]), which steps keep. *)

(* The symbols of two memories under a correspondence, up to those left
   out. A symbol that is not left out corresponds to itself, and is bound
   in both memories or in neither. A symbol that is left out is not bound
   in the first memory and is allocated in the second. *)
Definition names_related (D : dropped) (r : correspondence)
    (statics statics' : static_env) : Prop :=
  (∀ s : symbol,
    symbol_kept D s = true ->
    corr_values r (Value_symbol s) (Value_symbol s))
  ∧ (∀ s : symbol,
      symbol_kept D s = true ->
      is_bound s (static_values statics)
      = is_bound s (static_values statics'))
  ∧ (∀ s : symbol,
      symbol_kept D s = false ->
      lookup s (static_values statics) = None
      ∧ is_allocated statics' (Value_symbol s) = true).

(* Two memories related by a correspondence, valid without poison, up to
   the symbols left out. *)
Definition memories_related (D : dropped) (r : correspondence)
    (statics statics' : static_env) (h h' : heap) : Prop :=
  correspondence_valid false r statics statics' h h'
  ∧ names_related D r statics statics'.

(* Two states related up to symbols left out: [states_related], with the
   conditions of [names_related] on symbols. *)
Definition states_related_except (D : dropped) (s s' : heap_state) : Prop :=
  hs_expr s = hs_expr s'
  ∧ static_code (hs_statics s) = static_code (hs_statics s')
  ∧ ∃ r : correspondence,
      memories_related D r (hs_statics s) (hs_statics s') (hs_heap s)
        (hs_heap s')
      ∧ env_related (value_related false r (hs_statics s) (hs_statics s'))
          (fun x => var_free_b x (hs_expr s)) (hs_vars s) (hs_vars s')
      ∧ conts_related (value_related false r (hs_statics s) (hs_statics s'))
          (hs_conts s) (hs_conts s').

(* With no symbol left out, it is [states_related]. *)
Definition nothing_dropped : dropped := Dropped [] [].

Definition states_related_nothing_statement : Prop :=
  ∀ s s' : heap_state,
    states_related s s' <-> states_related_except nothing_dropped s s'.

(* The handlers that a continuation holds refer to no name left out and
   bind none. It is FlambdaUnusedStaticsSpec.cont_free_of without the
   values. *)
Fixpoint cont_code_free_of (D : dropped) (c : cont_value) : bool :=
  match c with
  | Outer _ => true
  | Closure h _ conts recursive =>
    handler_free_of D h
    && forallb (fun '(_, c) => cont_code_free_of D c) conts
    && forallb (fun '(_, h) => handler_free_of D h) recursive
  | Extra_args c _ => cont_code_free_of D c
  | Over_application _ _ _ return_to exn_to =>
    cont_code_free_of D return_to && cont_code_free_of D exn_to
  end.

Definition conts_code_free_of (D : dropped) (conts : cont_env) : bool :=
  forallb (fun '(_, c) => cont_code_free_of D c) conts.

(* The invariant of the first of two states related up to symbols left
   out: its expression, the handlers of its continuations and its code
   refer to no name left out and bind none. *)
Definition state_code_free_of (D : dropped) (s : heap_state) : Prop :=
  expr_avoids D (hs_expr s) = true
  ∧ binds_only_kept D (hs_expr s) = true
  ∧ conts_code_free_of D (hs_conts s) = true
  ∧ (∀ (id : code_id) (c : code),
      lookup id (static_code (hs_statics s)) = Some c ->
      code_free_of D c = true).

(* A step keeps it. *)
Definition heap_step_code_free_of_statement : Prop :=
  ∀ (D : dropped) (s s1 : heap_state),
    state_code_free_of D s ->
    heap_step s = Heap_step s1 ->
    state_code_free_of D s1.

(* From a state of the invariant, the machine respects the relation: the
   state is refined by every state related to it up to the symbols left
   out. *)
Definition machine_respects_relation_except_statement : Prop :=
  ∀ (D : dropped) (s s' : heap_state),
    state_code_free_of D s ->
    states_related_except D s s' ->
    heap_refines s s'.

(* ======================================================================== *)
(* What Simplify needs                                                      *)
(* ======================================================================== *)

(* What the later streams will have to prove, stated with the definitions
   above. All are proved here. *)

(* A step keeps a state closed: the invariant of states. *)
Definition heap_step_closed_statement : Prop :=
  ∀ s s' : heap_state,
    state_closed s -> heap_step s = Heap_step s' -> state_closed s'.

(* Simplify_let_expr: a [Let] whose variable is not used and whose
   primitive has at most generative effects may be deleted. Coeffects do
   not matter, and nor does whether the primitive has a value. The proof
   needs the relation: after an allocation is deleted, every later
   location is another. *)
Definition delete_unused_let_statement : Prop :=
  ∀ (x : variable) (x_kind : flambda_kind) (p : prim) (args : list simple)
    (body : expr),
    at_most_generative_effects p = true ->
    var_free_b x body = false ->
    heap_expr_refines (Let x x_kind (Prim p args) body) body.

(* It is false of a primitive with arbitrary effects: a write that is
   deleted is seen. This one is proved (FlambdaHeapProofs.v). *)
Definition delete_write_wrong_statement : Prop :=
  ∃ (x : variable) (x_kind : flambda_kind) (p : prim) (args : list simple)
    (body : expr),
    var_free_b x body = false
    ∧ ~ heap_expr_refines (Let x x_kind (Prim p args) body) body.

(* Two bindings may be exchanged when neither uses the other's variable
   and the first has neither effects nor coeffects. *)
Definition exchange_lets_statement : Prop :=
  ∀ (x y : variable) (x_kind y_kind : flambda_kind) (p q : prim)
    (args_p args_q : list simple) (body : expr),
    effects_of_prim p = No_effects ->
    coeffects_of_prim p = No_coeffects ->
    x <> y ->
    var_in_simples x args_q = false ->
    var_in_simples y args_p = false ->
    heap_expr_refines
      (Let x x_kind (Prim p args_p) (Let y y_kind (Prim q args_q) body))
      (Let y y_kind (Prim q args_q) (Let x x_kind (Prim p args_p) body)).

(* CSE: the second of two applications of a primitive with neither
   effects nor coeffects to the same arguments, with any bindings between
   them that do not rebind what it reads, may be replaced by the first.
   The simplest case, with nothing between. For an allocation whose
   result is immutable it holds too, since such a value has no
   identity. *)
Definition cse_adjacent_statement : Prop :=
  ∀ (x y : variable) (x_kind y_kind : flambda_kind) (p : prim)
    (args : list simple) (body : expr),
    (effects_of_prim p = No_effects
     ∨ effects_of_prim p = Only_generative_effects Immutable) ->
    coeffects_of_prim p = No_coeffects ->
    x <> y ->
    var_in_simples x args = false ->
    heap_expr_refines
      (Let x x_kind (Prim p args) (Let y y_kind (Prim p args) body))
      (Let x x_kind (Prim p args) (Let y y_kind (Simple (Var x)) body)).

(* Lifting: an immutable block made by a primitive may be bound to a new
   symbol, and the variable to that symbol. It needs the relation to look
   through symbols (D6), and the second state to bind a symbol that the
   first does not ([states_related_except]). The symbol is new: it is not
   bound, and the body, the environments and the heap neither mention it
   nor bind it (the conditions of FlambdaUnusedStaticsSpec.v on a name
   that is removed, read the other way). Nothing is asked of the fields:
   where one is a symbol that is bound to nothing, or the new symbol
   itself, the primitive has no value. *)
Definition heap_free_of (D : dropped) (h : heap) : bool :=
  forallb
    (fun binding => forallb (value_avoids D) (values_of_cell (snd binding)))
    h.

Definition lift_block_statement : Prop :=
  ∀ (x : variable) (x_kind : flambda_kind) (s : symbol) (tag : Z)
    (fields : list simple) (body : expr) (vars : env) (conts : cont_env)
    (statics : static_env) (h : heap),
    lookup s (static_values statics) = None ->
    expr_avoids (Dropped [s] []) body = true ->
    binds_only_kept (Dropped [s] []) body = true ->
    envs_free_of (Dropped [s] []) vars conts statics = true ->
    heap_free_of (Dropped [s] []) h = true ->
    state_closed (Heap_state body vars conts statics h) ->
    heap_refines
      (Heap_state
         (Let x x_kind
            (Prim (Variadic (Make_block (Block_kind_values tag))) fields)
            body)
         vars conts statics h)
      (Heap_state
         (Let_static [Bind_symbol s (Static_const_block tag fields)]
            (Let x x_kind (Simple (Symbol s)) body))
         vars conts statics h).

(* Lifting the closure of one function, in the same way. Its value slots
   may not name the new symbol: nothing makes the closure undefined where
   one does, and the symbol would be bound to a closure that holds
   itself. *)
Definition lift_closure_statement : Prop :=
  ∀ (x : variable) (x_kind : flambda_kind) (s : symbol) (code : code_id)
    (value_slots : list (value_slot * simple)) (body : expr) (vars : env)
    (conts : cont_env) (statics : static_env) (h : heap),
    lookup s (static_values statics) = None ->
    value_slots_avoid (Dropped [s] []) value_slots = true ->
    expr_avoids (Dropped [s] []) body = true ->
    binds_only_kept (Dropped [s] []) body = true ->
    envs_free_of (Dropped [s] []) vars conts statics = true ->
    heap_free_of (Dropped [s] []) h = true ->
    state_closed (Heap_state body vars conts statics h) ->
    heap_refines
      (Heap_state (Let x x_kind (Set_of_closures code value_slots) body) vars
         conts statics h)
      (Heap_state
         (Let_static
            [Bind_symbol s (Static_const_set_of_closures code value_slots)]
            (Let x x_kind (Simple (Symbol s)) body))
         vars conts statics h).

(* Lifting a closure of a set of several functions. The whole set is
   bound, with a new symbol for each of its functions
   (FlambdaModel.bind_closures), and the variable is bound to the symbol
   of its function slot. The symbols are new, as above, and distinct. *)
Definition lift_closure_of_set_statement : Prop :=
  ∀ (x : variable) (x_kind : flambda_kind) (slot : function_slot)
    (s : symbol) (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) (body : expr) (vars : env)
    (conts : cont_env) (statics : static_env) (h : heap),
    let D := Dropped (map snd closure_symbols) [] in
    lookup slot closure_symbols = Some s ->
    map fst closure_symbols = map fst function_decls ->
    distinct (map snd closure_symbols) = true ->
    (∀ t : symbol,
      t ∈ map snd closure_symbols ->
      lookup t (static_values statics) = None) ->
    value_slots_avoid D value_slots = true ->
    expr_avoids D body = true ->
    binds_only_kept D body = true ->
    envs_free_of D vars conts statics = true ->
    heap_free_of D h = true ->
    state_closed (Heap_state body vars conts statics h) ->
    heap_refines
      (Heap_state
         (Let x x_kind (Closure_of_set slot function_decls value_slots) body)
         vars conts statics h)
      (Heap_state
         (Let_static
            (bind_closures closure_symbols function_decls value_slots)
            (Let x x_kind (Simple (Symbol s)) body))
         vars conts statics h).

(* A load from a block that the environment knows: where a variable holds
   an immutable block whose field is a given value, the load of that
   field, whatever its mark, may be replaced by a [Simple] that has that
   value. The premise is what a [Variant] type that knows the field says
   of the variable (T1); it is about an immutable value, so it does not
   mention the heap, and no write can make it false. *)
Definition load_known_field_statement : Prop :=
  ∀ (x b : variable) (x_kind : flambda_kind) (kind : block_access_kind)
    (mut : mutability) (field : Z) (known : simple)
    (body : expr) (vars : env) (conts : cont_env) (statics : static_env)
    (h : heap) (block loaded : value),
    lookup b vars = Some block ->
    eval_block_load statics kind field block = Some loaded ->
    eval_simple vars known = Some loaded ->
    state_closed (Heap_state body vars conts statics h) ->
    heap_refines
      (Heap_state
         (Let x x_kind (Prim (Unary (Block_load kind mut field)) [Var b])
            body)
         vars conts statics h)
      (Heap_state (Let x x_kind (Simple known) body) vars conts statics h).
