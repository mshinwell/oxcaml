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


(* The grammar of Flambda types, as the model sees it.

   This file is to be reviewed, line by line against
   middle_end/flambda2/types/grammar/type_grammar.ml (the types at its
   head, and the creation functions) and type_descr.ml, as FlambdaModel.v
   is against flambda.mli. It holds definitions only, it is an ordinary
   inductive type, and it extracts: the converter from the compiler's
   types (workstream T7) is to be a case analysis onto it, and the
   operations on types (meet, join, the provers) are functions on it.
   What a type means is FlambdaTypeMeaningSpec.v.

   What the model has of [Type_grammar.t], constructor by constructor.

   - [t]. The fifteen constructors, one for each kind, are five here.
     [Value] is [Type_value] and [Naked_immediate] is
     [Type_naked_immediate]. The eleven of the other naked numbers
     ([Naked_float32] to [Naked_mask]), whose heads are all sets of
     numbers, are the one [Type_naked_number], which carries the kind:
     [Naked_float ty] is [Type_naked_number Kind_naked_float ty].
     [Rec_info] and [Region] are [Type_rec_info] and [Type_region]. The
     prefix is there because [Value], [Naked_number], [Naked_immediate]
     and the others are the kinds and the constants of FlambdaModel.v.
     [Type_naked_number Kind_naked_immediate] corresponds to no type of
     the compiler, and the converter never gives it.
   - ['head Type_descr.t] is [type_descr head], as [Type_descr.descr]
     shows it: [Unknown], [Bottom], or [Ok] of [No_alias head] or of
     [Equals simple]. The cache of free names
     ([With_cached_free_names]) is not modelled. A [Simple] has no
     coercion (FlambdaModel.v).
   - [head_of_kind_value], with [non_null] and [is_null], and [is_null]
     itself: in full.
   - [head_of_kind_value_non_null]:
     - [Variant]: in full, with its six fields.
     - [Mutable_block]: in full.
     - [Boxed_float32], [Boxed_float], [Boxed_int32], [Boxed_int64],
       [Boxed_nativeint], [Boxed_vec128], [Boxed_vec256], [Boxed_vec512]
       and [Boxed_mask] are the one [Boxed_number], which carries the
       kind of the number boxed: [Boxed_float (ty, alloc_mode)] is
       [Boxed_number Kind_naked_float ty alloc_mode].
     - [Closures]: in full.
     - [String]: in full; a string is the list of its bytes.
     - [Array] is left out. Its [element_kind] is a
       [Flambda_kind.With_subkind.t], and the model has no subkinds; the
       machine has no arrays either. It is to be added as a constructor
       when the terms have arrays; until then the converter must refuse
       a type that has one.
   - [head_of_kind_naked_immediate] is the record that
     [Head_of_kind_naked_immediate.descr] gives, [naked_immediates] and
     [inverse_relations], and not the three constructors that represent
     it. [inverse_relations], a [Name.Set.t Relation.Map.t], is the list
     of the pairs of a relation and a name in it.
   - The heads of the other naked numbers are sets of numbers: lists of
     integers, the numbers of the floats and vectors being bit patterns
     as in FlambdaModel.v. Nothing here restricts a number to its range.
   - [head_of_kind_rec_info], a [Rec_info_expr.t], is not modelled: the
     head of a [Type_rec_info] is [unit], as that of a [Type_region] is.
     The terms of the model have no [Rec_info] (FlambdaModel.v).
   - [row_like_index_domain], [row_like_index] and [row_like_case]: in
     full, with the three fields of a case. The index of a case of blocks
     is its size, a [Block_size.t], here a [nat], with its shape; that of
     a case of closures is a [Set_of_closures_contents.t].
   - [row_like_for_blocks]: in full. [Flambda_kind.Block_shape.t] is
     [block_shape]; of a [Mixed_block_shape.t] it keeps the size of the
     prefix of values and the kinds of the flat suffix.
   - [row_like_for_closures], [closures_entry],
     [function_slot_indexed_product] and [value_slot_indexed_product]:
     in full; a product is the map it holds.
   - [function_type]: its [code_id]. Its [rec_info] is left out, as
     [Rec_info] is.
   - [array_contents] is left out with [Array].
   - [env_extension] and [variant_extensions]: in full.
   - [Alloc_mode.For_types.t]: in full, wherever the compiler has it.

   Differences of presentation:
   - A record of the compiler that is defined with the types is a
     constructor with named arguments here ([Head_of_kind_value],
     [Row_like_for_blocks], [Closures_entry], ...), Rocq having no
     records in a mutual definition. The others are records, their
     fields prefixed where the name is taken.
   - [Or_unknown.t], [Or_bottom.t], [Row_like_index_domain.t] and
     [Alloc_mode.For_types.t] are in modules of those names, so that
     [Or_unknown.Unknown], [Or_bottom.Bottom] and
     [Row_like_index_domain.Known] are told from the [Unknown], [Ok] and
     [Bottom] of [Or_unknown_or_bottom.t], which are not in a module, and
     from [Or_unknown.Known]. [Relation.descr] is [Relation.t].
   - Maps and sets keyed by names (function slots, value slots,
     variables, symbols) are those of FlambdaMapSpec.v. A map from names
     that are variables or symbols ([Name.Map.t]) is a map from each
     ([finite_name_map]). Tags and numbers are not names: the cases of
     the known tags are an association list of which the first case of a
     tag counts ([find_tag]), as the arms of a [Switch] are in
     FlambdaModel.v, and a set of numbers is a list of them.
   - Function slots are names ([function_slot]), which FlambdaModel.v
     does not have yet: its sets of closures have one function. The
     definition here goes when it has them (workstream C3).

   The grammar does not enforce what the creation functions of the
   compiler check: that [immediates] is of kind naked immediate, the
   contents of a boxed number of the kind boxed, the closures of a
   product of kind value, the numbers of a head not empty. A type that
   breaks one of these has a meaning all the same (often that of
   bottom). Stating them as a condition is for the operations on types
   that need it. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
Import ListNotations.

(* ======================================================================== *)
(* Names                                                                    *)
(* ======================================================================== *)

(* [Function_slot.t]. *)
Definition function_slot : Type := positive.

(* [Name.t]: a variable or a symbol. *)
Inductive name : Type :=
  | Name_var (x : variable)
  | Name_symbol (s : symbol).

(* [Simple.name]. *)
Definition simple_of_name (n : name) : simple :=
  match n with
  | Name_var x => Var x
  | Name_symbol s => Symbol s
  end.

(* [Name.Map.t]: variables and symbols are different names with the same
   numbers, so a map from names is a map from the variables and one from
   the symbols. *)
Record finite_name_map (A : Type) : Type := Finite_name_map {
  on_variables : finite_map A;
  on_symbols : finite_map A
}.

Arguments Finite_name_map {A} on_variables on_symbols.
Arguments on_variables {A} _.
Arguments on_symbols {A} _.

(* [Name.Map.find_opt]. *)
Definition lookup_name {A : Type} (n : name) (m : finite_name_map A)
    : option A :=
  match n with
  | Name_var x => lookup x (on_variables m)
  | Name_symbol s => lookup s (on_symbols m)
  end.

(* [Name.Map.empty]. *)
Definition empty_name_map {A : Type} : finite_name_map A :=
  Finite_name_map [] [].

(* [Tag.Map.find_opt]: the first case of a tag. *)
Fixpoint find_tag {A : Type} (tag : Z) (cases : list (Z * A)) : option A :=
  match cases with
  | [] => None
  | (tag', a) :: cases => if Z.eqb tag tag' then Some a else find_tag tag cases
  end.

(* ======================================================================== *)
(* What the grammar is built with                                           *)
(* ======================================================================== *)

(* [Or_unknown.t]. *)
Module Or_unknown.
  Inductive t (A : Type) : Type :=
    | Known (a : A)
    | Unknown.
  Arguments Known {A} a.
  Arguments Unknown {A}.
End Or_unknown.

(* [Or_bottom.t]. *)
Module Or_bottom.
  Inductive t (A : Type) : Type :=
    | Ok (a : A)
    | Bottom.
  Arguments Ok {A} a.
  Arguments Bottom {A}.
End Or_bottom.

(* [Or_unknown_or_bottom.t]. *)
Inductive or_unknown_or_bottom (A : Type) : Type :=
  | Unknown
  | Ok (a : A)
  | Bottom.

Arguments Unknown {A}.
Arguments Ok {A} a.
Arguments Bottom {A}.

(* [Type_descr.Descr.t]: a type that is not unknown or bottom is given by
   its head or is an alias, equal to a [Simple]. *)
Inductive descr (head : Type) : Type :=
  | No_alias (h : head)
  | Equals (s : simple).

Arguments No_alias {head} h.
Arguments Equals {head} s.

(* [Type_descr.t], as [Type_descr.descr] shows it. *)
Definition type_descr (head : Type) : Type :=
  or_unknown_or_bottom (descr head).

(* [Alloc_mode.For_types.t]. *)
Module Alloc_mode.
  Inductive t : Type :=
    | Heap
    | Local
    | Heap_or_local.
End Alloc_mode.

(* [Type_grammar.is_null]. The variable, if there is one, holds whether
   the value is null. *)
Inductive is_null : Type :=
  | Not_null
  | Maybe_null (is_null : option variable).

(* [Type_grammar.Relation.descr]: the primitives whose result a type of
   naked immediates can be said to be. *)
Module Relation.
  Inductive t : Type :=
    | Is_null
    | Is_int
    | Get_tag.
End Relation.

(* [head_of_kind_naked_immediate], as [Head_of_kind_naked_immediate.descr]
   shows it: the numbers it may be, and the names of which it is the
   result of a relation. *)
Record head_of_kind_naked_immediate : Type := Head_of_kind_naked_immediate {
  naked_immediates : Or_unknown.t (list Z);
  inverse_relations : list (Relation.t * name)
}.

(* [Flambda_kind.Scannable_block_shape.t], and of a
   [Flambda_kind.Mixed_block_shape.t] what [value_prefix_size] and
   [flat_suffix] give. *)
Inductive scannable_block_shape : Type :=
  | Value_only
  | Mixed_record (value_prefix_size : nat)
      (flat_suffix : list naked_number_kind).

(* [Flambda_kind.Block_shape.t]. *)
Inductive block_shape : Type :=
  | Scannable (shape : scannable_block_shape)
  | Float_record.

(* [Obj.no_scan_tag] and [Tag.double_array_tag]. *)
Definition no_scan_tag : Z := 251.
Definition double_array_tag : Z := 254.

(* [Type_grammar.row_like_index_domain]: [Known x] is [x] alone, and
   [At_least x] everything that includes [x]. *)
Module Row_like_index_domain.
  Inductive t (lattice : Type) : Type :=
    | Known (index : lattice)
    | At_least (index : lattice).
  Arguments Known {lattice} index.
  Arguments At_least {lattice} index.
End Row_like_index_domain.

(* [Type_grammar.row_like_index]. *)
Record row_like_index (lattice shape : Type) : Type := Row_like_index {
  index_domain : Row_like_index_domain.t lattice;
  index_shape : shape
}.

Arguments Row_like_index {lattice shape} index_domain index_shape.
Arguments index_domain {lattice shape} _.
Arguments index_shape {lattice shape} _.

(* [Type_grammar.row_like_case]. The type of environment extensions is a
   parameter because it is defined with the types, below. *)
Record row_like_case (lattice shape maps_to extension : Type) : Type :=
  Row_like_case {
    case_maps_to : maps_to;
    case_index : row_like_index lattice shape;
    case_env_extension : extension
  }.

Arguments Row_like_case {lattice shape maps_to extension} case_maps_to
  case_index case_env_extension.
Arguments case_maps_to {lattice shape maps_to extension} _.
Arguments case_index {lattice shape maps_to extension} _.
Arguments case_env_extension {lattice shape maps_to extension} _.

(* [Set_of_closures_contents.t]: function slots and value slots of a set
   of closures. *)
Record set_of_closures_contents : Type := Set_of_closures_contents {
  contents_closures : list function_slot;
  contents_value_slots : list value_slot
}.

(* [Type_grammar.function_type], without its [rec_info]. *)
Record function_type : Type := Function_type {
  function_type_code_id : code_id
}.

(* ======================================================================== *)
(* The grammar                                                              *)
(* ======================================================================== *)

(* [Type_grammar.t] and the types defined with it. The cases of a
   row-like structure of blocks are [row_like_block_case], and those of
   one of closures have a [Set_of_closures_contents.t] for index and a
   [closures_entry] for what they map to; both are written out, the
   definition being recursive. *)
Inductive flambda_type : Type :=
  | Type_value (ty : type_descr head_of_kind_value)
  | Type_naked_immediate (ty : type_descr head_of_kind_naked_immediate)
  | Type_naked_number (k : naked_number_kind) (ty : type_descr (list Z))
  | Type_rec_info (ty : type_descr unit)
  | Type_region (ty : type_descr unit)

with head_of_kind_value : Type :=
  | Head_of_kind_value
      (non_null : or_unknown_or_bottom head_of_kind_value_non_null)
      (is_null : is_null)

with head_of_kind_value_non_null : Type :=
  | Variant (is_int : option variable)
      (immediates : Or_unknown.t flambda_type) (get_tag : option variable)
      (blocks : Or_unknown.t row_like_for_blocks)
      (extensions : variant_extensions) (is_unique : bool)
  | Mutable_block (alloc_mode : Alloc_mode.t)
  | Boxed_number (k : naked_number_kind) (contents : flambda_type)
      (alloc_mode : Alloc_mode.t)
  | Closures (by_function_slot : row_like_for_closures)
      (alloc_mode : Alloc_mode.t)
  | String (strs : list (list Z))

with row_like_for_blocks : Type :=
  | Row_like_for_blocks
      (known_tags :
        list
          (Z
           * Or_unknown.t
               (row_like_case nat block_shape (list flambda_type)
                  env_extension)))
      (other_tags :
        Or_bottom.t
          (row_like_case nat block_shape (list flambda_type) env_extension))
      (alloc_mode : Alloc_mode.t)

with row_like_for_closures : Type :=
  | Row_like_for_closures
      (known_closures :
        finite_map
          (row_like_case set_of_closures_contents unit closures_entry
             env_extension))

with closures_entry : Type :=
  | Closures_entry (function_types : finite_map (Or_unknown.t function_type))
      (closure_types : finite_map flambda_type)
      (value_slot_types : finite_map flambda_type)

with env_extension : Type :=
  | Env_extension (equations : finite_name_map flambda_type)

with variant_extensions : Type :=
  | No_extensions
  | Ext (when_immediate when_block : env_extension).

(* [Type_grammar.row_like_block_case]. *)
Definition row_like_block_case : Type :=
  row_like_case nat block_shape (list flambda_type) env_extension.

(* The cases of [row_like_for_closures]. *)
Definition row_like_closures_case : Type :=
  row_like_case set_of_closures_contents unit closures_entry env_extension.

(* ======================================================================== *)
(* Kinds                                                                    *)
(* ======================================================================== *)

(* [Type_grammar.kind]. *)
Definition kind (t : flambda_type) : flambda_kind :=
  match t with
  | Type_value _ => Value
  | Type_naked_immediate _ => Naked_number Kind_naked_immediate
  | Type_naked_number k _ => Naked_number k
  | Type_rec_info _ => Rec_info
  | Type_region _ => Region
  end.

(* [Flambda_kind.Boxable_number.t]: the kinds of the numbers that can be
   boxed. *)
Definition boxable_number (k : naked_number_kind) : bool :=
  match k with
  | Kind_naked_float32 | Kind_naked_float | Kind_naked_int32
  | Kind_naked_int64 | Kind_naked_nativeint | Kind_naked_vec128
  | Kind_naked_vec256 | Kind_naked_vec512 | Kind_naked_mask => true
  | Kind_naked_immediate | Kind_naked_int8 | Kind_naked_int16 => false
  end.

(* The kinds of the fields of a block of [size] fields of a shape
   ([Flambda_kind.Block_shape.element_kind], for each field). A mixed
   block has the size that its shape gives it. *)
Definition field_kinds (shape : block_shape) (size : nat)
    : list flambda_kind :=
  match shape with
  | Scannable Value_only => repeat Value size
  | Scannable (Mixed_record value_prefix_size flat_suffix) =>
    repeat Value value_prefix_size ++ map Naked_number flat_suffix
  | Float_record => repeat (Naked_number Kind_naked_float) size
  end.

(* ======================================================================== *)
(* Creation of types                                                        *)
(* ======================================================================== *)

(* A type of a kind that has a description common to every kind, which
   are the unknown type, the bottom type and the aliases. *)
Definition type_of_kind (k : flambda_kind)
    (ty : ∀ head : Type, type_descr head) : flambda_type :=
  match k with
  | Value => Type_value (ty _)
  | Naked_number Kind_naked_immediate => Type_naked_immediate (ty _)
  | Naked_number k => Type_naked_number k (ty _)
  | Rec_info => Type_rec_info (ty _)
  | Region => Type_region (ty _)
  end.

(* [More_type_creators.unknown]: [any_value], [any_naked_immediate], ... *)
Definition unknown (k : flambda_kind) : flambda_type :=
  type_of_kind k (fun _ => Unknown).

(* [More_type_creators.bottom]: [bottom_value], ... *)
Definition bottom (k : flambda_kind) : flambda_type :=
  type_of_kind k (fun _ => Bottom).

(* [Type_grammar.alias_type_of]. *)
Definition alias_type_of (k : flambda_kind) (s : simple) : flambda_type :=
  type_of_kind k (fun _ => Ok (Equals s)).

(* [Type_grammar.get_alias_opt]. *)
Definition get_alias_opt (t : flambda_type) : option simple :=
  let of_descr {head : Type} (ty : type_descr head) : option simple :=
    match ty with
    | Ok (Equals s) => Some s
    | Unknown | Bottom | Ok (No_alias _) => None
    end
  in
  match t with
  | Type_value ty => of_descr ty
  | Type_naked_immediate ty => of_descr ty
  | Type_naked_number _ ty => of_descr ty
  | Type_rec_info ty => of_descr ty
  | Type_region ty => of_descr ty
  end.

(* [More_type_creators.type_for_const], but for [Null] and [Poison]: the
   type of a number is an alias to it ([this_tagged_immediate],
   [this_naked_immediate], [this_naked_float], ...). *)
Definition this_const (c : const) : flambda_type :=
  alias_type_of (kind_of_const c) (Const c).

Definition this_tagged_immediate (i : Z) : flambda_type :=
  this_const (Tagged_immediate i).

Definition this_naked_immediate (i : Z) : flambda_type :=
  this_const (Naked_immediate i).

(* [Type_grammar.null]. *)
Definition null : flambda_type :=
  Type_value (Ok (No_alias (Head_of_kind_value Bottom (Maybe_null None)))).

(* [Type_grammar.any_non_null_value]. *)
Definition any_non_null_value : flambda_type :=
  Type_value (Ok (No_alias (Head_of_kind_value Unknown Not_null))).

(* [More_type_creators.type_for_const]. *)
Definition type_for_const (c : const) : flambda_type :=
  match c with
  | Null => null
  | Poison k => unknown k
  | _ => this_const c
  end.

(* [Type_grammar.non_null_value]. *)
Definition non_null_value (head : head_of_kind_value_non_null)
    : flambda_type :=
  Type_value (Ok (No_alias (Head_of_kind_value (Ok head) Not_null))).

(* [Type_grammar.create_variant]. *)
Definition create_variant (is_unique : bool)
    (immediates : Or_unknown.t flambda_type)
    (blocks : Or_unknown.t row_like_for_blocks)
    (extensions : variant_extensions) : flambda_type :=
  non_null_value (Variant None immediates None blocks extensions is_unique).

(* [Type_grammar.mutable_block]. *)
Definition mutable_block (alloc_mode : Alloc_mode.t) : flambda_type :=
  non_null_value (Mutable_block alloc_mode).

(* [Type_grammar.create_closures]. *)
Definition create_closures (alloc_mode : Alloc_mode.t)
    (by_function_slot : row_like_for_closures) : flambda_type :=
  non_null_value (Closures by_function_slot alloc_mode).

(* [Type_grammar.box_float32], [box_float], [box_int32], ...: the kind is
   that of the type of the contents, which the compiler checks. *)
Definition box_number (k : naked_number_kind) (contents : flambda_type)
    (alloc_mode : Alloc_mode.t) : flambda_type :=
  non_null_value (Boxed_number k contents alloc_mode).

(* [Type_grammar.this_immutable_string]. *)
Definition this_immutable_string (bytes : list Z) : flambda_type :=
  non_null_value (String [bytes]).

(* [Type_grammar.these_naked_immediates]. *)
Definition these_naked_immediates (imms : list Z) : flambda_type :=
  match imms with
  | [] => bottom (Naked_number Kind_naked_immediate)
  | [i] => this_naked_immediate i
  | _ =>
    Type_naked_immediate
      (Ok
         (No_alias (Head_of_kind_naked_immediate (Or_unknown.Known imms) [])))
  end.

(* [Type_grammar.Env_extension.empty]. *)
Definition empty_env_extension : env_extension :=
  Env_extension empty_name_map.

(* [Type_grammar.Row_like_for_blocks.bottom]. *)
Definition row_like_for_blocks_bottom : row_like_for_blocks :=
  Row_like_for_blocks [] Or_bottom.Bottom Alloc_mode.Heap_or_local.

(* [Type_grammar.Row_like_for_blocks.create_exactly],
   [create_at_least] and [create_at_least_unknown_tag]: blocks of one tag
   and of a size that is known, or known from below; and blocks of any
   tag. *)
Definition row_like_for_blocks_create_exactly (tag : Z) (size : nat)
    (shape : block_shape) (maps_to : list flambda_type)
    (alloc_mode : Alloc_mode.t) : row_like_for_blocks :=
  Row_like_for_blocks
    [(tag,
      Or_unknown.Known
        (Row_like_case maps_to
           (Row_like_index (Row_like_index_domain.Known size) shape)
           empty_env_extension))]
    Or_bottom.Bottom alloc_mode.

Definition row_like_for_blocks_create_at_least (tag : Z) (size : nat)
    (shape : block_shape) (maps_to : list flambda_type)
    (alloc_mode : Alloc_mode.t) : row_like_for_blocks :=
  Row_like_for_blocks
    [(tag,
      Or_unknown.Known
        (Row_like_case maps_to
           (Row_like_index (Row_like_index_domain.At_least size) shape)
           empty_env_extension))]
    Or_bottom.Bottom alloc_mode.

Definition row_like_for_blocks_create_at_least_unknown_tag (size : nat)
    (shape : block_shape) (maps_to : list flambda_type)
    (alloc_mode : Alloc_mode.t) : row_like_for_blocks :=
  Row_like_for_blocks []
    (Or_bottom.Ok
       (Row_like_case maps_to
          (Row_like_index (Row_like_index_domain.At_least size) shape)
          empty_env_extension))
    alloc_mode.

(* [Type_grammar.tag_immediate]: the tagged immediates whose numbers have
   the type given, which is of kind naked immediate. *)
Definition tag_immediate (t : flambda_type) : flambda_type :=
  create_variant false (Or_unknown.Known t)
    (Or_unknown.Known row_like_for_blocks_bottom) No_extensions.

(* [More_type_creators.any_tagged_immediate]. *)
Definition any_tagged_immediate : flambda_type :=
  create_variant false Or_unknown.Unknown
    (Or_unknown.Known row_like_for_blocks_bottom) No_extensions.

(* [More_type_creators.these_tagged_immediates]. *)
Definition these_tagged_immediates (imms : list Z) : flambda_type :=
  match imms with
  | [] => bottom Value
  | [i] => this_tagged_immediate i
  | _ => tag_immediate (these_naked_immediates imms)
  end.

(* [More_type_creators.any_block]. *)
Definition any_block : flambda_type :=
  create_variant false
    (Or_unknown.Known (bottom (Naked_number Kind_naked_immediate)))
    Or_unknown.Unknown No_extensions.

(* [More_type_creators.immutable_block]: the blocks of a tag with fields
   of the types given, and no others. *)
Definition immutable_block (is_unique : bool) (tag : Z) (shape : block_shape)
    (alloc_mode : Alloc_mode.t) (fields : list flambda_type) : flambda_type :=
  create_variant is_unique
    (Or_unknown.Known (bottom (Naked_number Kind_naked_immediate)))
    (Or_unknown.Known
       (row_like_for_blocks_create_exactly tag (length fields) shape fields
          alloc_mode))
    No_extensions.

(* [Type_grammar.is_int_for_scrutinee], [get_tag_for_block] and
   [is_null], for a scrutinee that is a name: the result of the primitive
   on the value of the name. *)
Definition is_int_for_scrutinee (scrutinee : name) : flambda_type :=
  Type_naked_immediate
    (Ok
       (No_alias
          (Head_of_kind_naked_immediate (Or_unknown.Known [0%Z; 1%Z])
             [(Relation.Is_int, scrutinee)]))).

Definition get_tag_for_block (block : name) : flambda_type :=
  Type_naked_immediate
    (Ok
       (No_alias
          (Head_of_kind_naked_immediate Or_unknown.Unknown
             [(Relation.Get_tag, block)]))).

Definition is_null_for_scrutinee (scrutinee : name) : flambda_type :=
  Type_naked_immediate
    (Ok
       (No_alias
          (Head_of_kind_naked_immediate (Or_unknown.Known [0%Z; 1%Z])
             [(Relation.Is_null, scrutinee)]))).

(* [More_type_creators.exactly_this_closure]: the closure at a function
   slot of a set of closures with exactly the functions, the closures
   and the value slots given. *)
Definition exactly_this_closure (this_function_slot : function_slot)
    (all_function_slots_in_set : finite_map (Or_unknown.t function_type))
    (all_closure_types_in_set : finite_map flambda_type)
    (all_value_slots_in_set : finite_map flambda_type)
    (alloc_mode : Alloc_mode.t) : flambda_type :=
  create_closures alloc_mode
    (Row_like_for_closures
       [(this_function_slot,
         Row_like_case
           (Closures_entry all_function_slots_in_set all_closure_types_in_set
              all_value_slots_in_set)
           (Row_like_index
              (Row_like_index_domain.Known
                 (Set_of_closures_contents (domain all_function_slots_in_set)
                    (domain all_value_slots_in_set)))
              tt)
           empty_env_extension)]).
