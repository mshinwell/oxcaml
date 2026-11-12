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

(* Checks Simplify against the Rocq semantics of Flambda 2 on one example.

   An [.fl] file is parsed to a Flambda unit, which Simplify then rewrites. The
   unit before and the unit after are each converted to a term of the Rocq model
   (middle_end/flambda2/rocq/FlambdaModel.v) and run on the machine extracted
   from FlambdaSemanticsSpec.v. What the two runs come to is printed and
   compared: Simplify is right on the example if, unless the run before is
   undefined, the run after ends the same way.

   This is a test and not a proof. What is trusted, beyond the semantics itself:
   the conversion below, which must be read against the model. What a primitive
   computes is the model's to say (FlambdaPrimitiveSpec.v); the conversion only
   says which primitive of the model stands for one of the compiler's. A
   construct or a primitive the conversion does not know is reported as
   unsupported, and never run as if it were undefined, as that would make the
   check pass for nothing.

   Kinds. The conversion gives each [Let] the kind of its variable, each handler
   the kinds of its parameters, code its two arities and each call the two it is
   made at, with their unboxed products, and it keeps the kinds of the value
   slots it meets. The machine makes a call undefined that does not agree with
   its code (FlambdaSemanticsSpec.call_code), so a mistake here in the arities
   of a call or of code would make a run undefined that should not be: that is
   trusted too. Two things are cross-checked as the conversion goes: an arity as
   converted, unarized by the model, has the kinds that the compiler's own
   unarizing gives; and the parameter arity of code, unarized, has the kinds of
   the parameters of its body. The check of kinds of FlambdaWellKindedSpec.v is
   run on each of the two units and its answers are printed; nothing depends on
   them.

   Exceptions. The conversion gives each [Apply_cont] its trap action, with the
   continuation it names and its raise kind; each call the extra arguments of
   its exception continuation, with their kinds; and each handler whether it is
   an exception handler. The machine reads the extra arguments only, so a
   mistake there changes a run. The rest is read by the comparison of the
   validator and by the checks of well-formedness, which say whether a unit
   keeps its exception handlers apart and follows the discipline of trap
   actions: a mistake there changes what those accept.

   Partial applications and over-applications are in the model: a call with
   fewer or more arguments than the code of its callee has parameters is one,
   whatever its kind (FlambdaSemanticsSpec.shape_of_closure_call), and an
   application is converted with its arguments and its arities as they are. A
   partial application is a value of the model that the compiler has not got as
   such; at the end of a run it is observed as a function is.

   Tupled functions are in the model, as code that is marked: every call of the
   model gives such code its first argument as the tuple, and any arguments
   after it as they are, for an over-application, as a call of unknown arity
   does in the compiler (FlambdaSemanticsSpec.shape_of_closure_call). The
   compiler's direct call and its call of known arity give code its arguments as
   the code takes them, and the model has not got that of tupled code yet. So a
   direct call of tupled code is reported as unsupported, and so is a call of
   known arity, which names no code, in a unit that has tupled code. *)

(* The matches below name the few constructs and primitives the model has and
   send every other to [unsupported]; they are meant to stay as they are when
   the compiler gains a constructor. *)
[@@@ocaml.warning "-4"]

open Import
open Flambda2_kinds
open Flambda2_numbers
open Flambda2_bound_identifiers
open Flambda2_term_basics
module Maps = Flambda2_rocq_semantics.FlambdaMapSpec
module Kinds = Flambda2_rocq_semantics.FlambdaKindModel
module Primitives = Flambda2_rocq_semantics.FlambdaPrimitiveModel
module Model = Flambda2_rocq_semantics.FlambdaModel
module Values = Flambda2_rocq_semantics.FlambdaValueSpec
module Semantics = Flambda2_rocq_semantics.FlambdaSemanticsSpec
module Normalise = Flambda2_rocq_semantics.FlambdaNormaliseSpec
module Unused_statics = Flambda2_rocq_semantics.FlambdaUnusedStaticsSpec
module Well_formed = Flambda2_rocq_semantics.FlambdaWellFormedSpec
module Well_kinded = Flambda2_rocq_semantics.FlambdaWellKindedSpec
module Binders = Flambda2_rocq_semantics.FlambdaBindersSpec
module Validate = Flambda2_rocq_semantics.FlambdaValidateSpec
module Validate_knowing = Flambda2_rocq_semantics.FlambdaValidateKnowingSpec
module Lift = Flambda2_rocq_semantics.FlambdaLiftSpec
module My_closure = Flambda2_rocq_semantics.FlambdaMyClosureSpec
module Unused_slots = Flambda2_rocq_semantics.FlambdaUnusedSlotsSpec
module Float_code = Flambda2_rocq_semantics.FlambdaFloatCodeSpec
module Loopify = Flambda2_rocq_semantics.FlambdaLoopifySpec
module Statics_order = Flambda2_rocq_semantics.FlambdaStaticsOrderSpec
module Lift_from_code = Flambda2_rocq_semantics.FlambdaLiftFromCodeSpec
module Lift_from_arms = Flambda2_rocq_semantics.FlambdaLiftFromArmsSpec
module Numbers = Flambda2_rocq_semantics.BinNums
module P = Flambda_primitive

exception Unsupported of (Format.formatter -> unit)

let unsupported fmt = Format.kdprintf (fun msg -> raise (Unsupported msg)) fmt

(* ---- Numbers ---------------------------------------------------------- *)

let rec positive_of_int n : Numbers.positive =
  if n <= 1
  then Coq_xH
  else if n land 1 = 0
  then Coq_xO (positive_of_int (n lsr 1))
  else Coq_xI (positive_of_int (n lsr 1))

let rec nat_of_int n : Flambda2_rocq_semantics.Datatypes.nat =
  if n <= 0 then O else S (nat_of_int (n - 1))

let rec int_of_positive (p : Numbers.positive) =
  match p with
  | Coq_xH -> 1
  | Coq_xO p -> 2 * int_of_positive p
  | Coq_xI p -> (2 * int_of_positive p) + 1

let int_of_z (z : Numbers.coq_Z) =
  match z with
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> -int_of_positive p

(* The integers of 64 bits: a positive number of the model is read as, and
   written from, the unsigned reading of an [int64]. *)
let rec positive_of_int64 n : Numbers.positive =
  if Int64.equal n 1L
  then Coq_xH
  else if Int64.equal (Int64.logand n 1L) 0L
  then Coq_xO (positive_of_int64 (Int64.shift_right_logical n 1))
  else Coq_xI (positive_of_int64 (Int64.shift_right_logical n 1))

let z_of_int64 n : Numbers.coq_Z =
  if Int64.equal n 0L
  then Z0
  else if Int64.compare n 0L > 0
  then Zpos (positive_of_int64 n)
  else Zneg (positive_of_int64 (Int64.neg n))

(* Through [int64], as the opposite of the least [int] is not an [int]. *)
let z_of_int n = z_of_int64 (Int64.of_int n)

let rec int64_of_positive (p : Numbers.positive) =
  match p with
  | Coq_xH -> 1L
  | Coq_xO p -> Int64.mul 2L (int64_of_positive p)
  | Coq_xI p -> Int64.add (Int64.mul 2L (int64_of_positive p)) 1L

let int64_of_z (z : Numbers.coq_Z) =
  match z with
  | Z0 -> 0L
  | Zpos p -> int64_of_positive p
  | Zneg p -> Int64.neg (int64_of_positive p)

(* ---- Names ------------------------------------------------------------ *)

(* Each sort of name of the compiler is numbered from 1 as it is met. The names
   the compiler gives when it opens a binder are fresh, so a name stands for one
   thing throughout a unit. *)
module Numbering (Id : sig
  type t

  val compare : t -> t -> int
end) =
struct
  module Map = Map.Make (Id)

  let numbers = ref Map.empty

  let next = ref 1

  let find id =
    match Map.find_opt id !numbers with
    | Some n -> positive_of_int n
    | None ->
      let n = !next in
      incr next;
      numbers := Map.add id n !numbers;
      positive_of_int n

  (* A number that no name has, or will have. *)
  let fresh () =
    let n = !next in
    incr next;
    positive_of_int n

  (* Gives [id] the number of [same_as]. *)
  let alias id ~same_as =
    ignore (find same_as : Numbers.positive);
    numbers := Map.add id (Map.find same_as !numbers) !numbers

  (* Forgets every name numbered so far. *)
  let reset () =
    numbers := Map.empty;
    next := 1

  (* The names numbered so far, each with its number. *)
  let bindings () =
    List.map (fun (id, n) -> id, positive_of_int n) (Map.bindings !numbers)
end

module Variables = Numbering (Variable)
module Continuations = Numbering (Continuation)
module Symbols = Numbering (Symbol)
module Code_ids = Numbering (Code_id)
module Value_slots = Numbering (Value_slot)
module Function_slots = Numbering (Function_slot)

(* The kinds of the value slots met ([Value_slot.kind]): the table that the
   check of kinds is given. *)
let slot_kinds : (Numbers.positive * Flambda_kind.t) list ref = ref []

let find_value_slot slot =
  let n = Value_slots.find slot in
  if not (List.mem_assoc n !slot_kinds)
  then slot_kinds := (n, Value_slot.kind slot) :: !slot_kinds;
  n

(* ---- Primitives ------------------------------------------------------- *)

(* The primitives the model has (FlambdaPrimitiveModel.v), with the fields it
   keeps of each. One that is not there, or that has a field with a value that
   is not there, is unsupported. *)
let convert_kind (kind : Flambda_kind.t) : Kinds.flambda_kind =
  match kind with
  | Value -> Value
  | Naked_number Naked_immediate -> Naked_number Kind_naked_immediate
  | Naked_number Naked_float32 -> Naked_number Kind_naked_float32
  | Naked_number Naked_float -> Naked_number Kind_naked_float
  | Naked_number Naked_int8 -> Naked_number Kind_naked_int8
  | Naked_number Naked_int16 -> Naked_number Kind_naked_int16
  | Naked_number Naked_int32 -> Naked_number Kind_naked_int32
  | Naked_number Naked_int64 -> Naked_number Kind_naked_int64
  | Naked_number Naked_nativeint -> Naked_number Kind_naked_nativeint
  | Naked_number Naked_vec128 -> Naked_number Kind_naked_vec128
  | Naked_number Naked_vec256 -> Naked_number Kind_naked_vec256
  | Naked_number Naked_vec512 -> Naked_number Kind_naked_vec512
  | Naked_number Naked_mask -> Naked_number Kind_naked_mask
  | Region -> Region
  | Rec_info -> Rec_info

(* An arity of the model is the compiler's without its subkinds: one component
   to a parameter, each a kind or an unboxed product of components. It is
   rebuilt through the fold that the compiler gives, a product from the
   components folded so far, the last first. What the model then makes of it
   unarized must be what the compiler makes of the arity unarized. *)
type component_so_far =
  | Kind of Flambda_kind.t
  | Members of Model.arity_component list

let convert_arity (arity : _ Flambda_arity.t) : Model.arity =
  let component (so_far : component_so_far) : Model.arity_component =
    match so_far with
    | Kind kind -> Singleton (convert_kind kind)
    | Members members -> Unboxed_product (List.rev members)
  in
  let converted =
    Flambda_arity.fold_per_parameter arity ~init:(Members [])
      ~singleton:(fun _ kind -> Kind (Flambda_kind.With_subkind.kind kind))
      ~unboxed_product:(fun ~outer ~inner ->
        match outer with
        | Members members -> Members (component inner :: members)
        | Kind _ ->
          Misc.fatal_error "flsemantics: a kind with members, in an arity")
    |> List.map component
  in
  let unarized =
    List.map
      (fun kind -> convert_kind (Flambda_kind.With_subkind.kind kind))
      (Flambda_arity.unarize arity)
  in
  if Model.unarize converted <> unarized
  then
    Misc.fatal_errorf "flsemantics: the arity %a is not converted faithfully"
      Flambda_arity.print arity;
  converted

let convert_standard_int (kind : Flambda_kind.Standard_int.t) :
    Kinds.standard_int =
  match kind with
  | Tagged_immediate -> Standard_tagged_immediate
  | Naked_immediate -> Standard_naked_immediate
  | Naked_int8 -> Standard_naked_int8
  | Naked_int16 -> Standard_naked_int16
  | Naked_int32 -> Standard_naked_int32
  | Naked_int64 -> Standard_naked_int64
  | Naked_nativeint -> Standard_naked_nativeint

(* The integers among the kinds that [Num_conv] converts between: the model has
   not got the conversions to and from the floats. *)
let convert_standard_int_or_float (kind : Flambda_kind.Standard_int_or_float.t)
    : Kinds.standard_int option =
  match kind with
  | Tagged_immediate -> Some Standard_tagged_immediate
  | Naked_immediate -> Some Standard_naked_immediate
  | Naked_int8 -> Some Standard_naked_int8
  | Naked_int16 -> Some Standard_naked_int16
  | Naked_int32 -> Some Standard_naked_int32
  | Naked_int64 -> Some Standard_naked_int64
  | Naked_nativeint -> Some Standard_naked_nativeint
  | Naked_float32 | Naked_float -> None

let convert_boxable_number (kind : Flambda_kind.Boxable_number.t) :
    Kinds.boxable_number =
  match kind with
  | Naked_float32 -> Boxable_naked_float32
  | Naked_float -> Boxable_naked_float
  | Naked_int32 -> Boxable_naked_int32
  | Naked_int64 -> Boxable_naked_int64
  | Naked_nativeint -> Boxable_naked_nativeint
  | Naked_vec128 -> Boxable_naked_vec128
  | Naked_vec256 -> Boxable_naked_vec256
  | Naked_vec512 -> Boxable_naked_vec512
  | Naked_mask -> Boxable_naked_mask

let convert_signed_or_unsigned (signedness : P.signed_or_unsigned) :
    Primitives.signedness =
  match signedness with Signed -> Signed | Unsigned -> Unsigned

let convert_signedness (signedness : Scalar.Signedness.t) :
    Primitives.signedness =
  match signedness with Signed -> Signed | Unsigned -> Unsigned

let convert_or_unknown convert (known : _ Flambda2_lattices.Or_unknown.t) =
  match known with Known a -> Some (z_of_int (convert a)) | Unknown -> None

let convert_unary_primitive (p : P.unary_primitive) :
    Primitives.unary_primitive option =
  match p with
  | Block_load { kind = Values { tag; size; field_kind }; mut; field } ->
    let field_kind : Primitives.block_access_field_kind =
      match field_kind with Any_value -> Any_value | Immediate -> Immediate
    in
    let kind : Primitives.block_access_kind =
      Block_access_values
        ( convert_or_unknown Tag.Scannable.to_int tag,
          convert_or_unknown Target_ocaml_int.to_int size,
          field_kind )
    in
    let mut : Primitives.mutability =
      match mut with
      | Mutable -> Mutable
      | Immutable -> Immutable
      | Immutable_unique -> Immutable_unique
    in
    Some (Block_load (kind, mut, z_of_int (Target_ocaml_int.to_int field)))
  | Block_load _ -> None
  | Is_int { variant_only } -> Some (Is_int variant_only)
  | Is_null -> Some Is_null
  | Get_tag -> Some Get_tag
  | String_length String -> Some String_length
  | String_length Bytes -> None
  | Opaque_identity { middle_end_only = _; kind } ->
    Some (Opaque_identity (convert_kind kind))
  | Int_arith (kind, Not) ->
    Some (Unary_int_arith (convert_standard_int kind, Not))
  | Int_arith (kind, Swap_byte_endianness) ->
    Some (Unary_int_arith (convert_standard_int kind, Swap_byte_endianness))
  | Num_conv { src; dst } -> (
    match
      convert_standard_int_or_float src, convert_standard_int_or_float dst
    with
    | Some src, Some dst -> Some (Num_conv (src, dst))
    | None, _ | _, None -> None)
  | Boolean_not -> Some Boolean_not
  | Unbox_number kind -> Some (Unbox_number (convert_boxable_number kind))
  | Box_number (kind, (Heap _ | Local _)) ->
    (* CR mshinwell: a box made in a region is converted as one made on the
       heap; see [region_variables]. *)
    Some (Box_number (convert_boxable_number kind))
  | Untag_immediate -> Some Untag_immediate
  | Tag_immediate -> Some Tag_immediate
  | Reinterpret_64_bit_word Tagged_int63_as_unboxed_int64 ->
    Some (Reinterpret_64_bit_word Tagged_int63_as_unboxed_int64)
  | Reinterpret_64_bit_word Unboxed_int64_as_tagged_int63 ->
    Some (Reinterpret_64_bit_word Unboxed_int64_as_tagged_int63)
  | Reinterpret_64_bit_word
      (Unboxed_int64_as_unboxed_float64 | Unboxed_float64_as_unboxed_int64) ->
    None
  | _ -> None

let convert_int_arith_op (op : P.binary_int_arith_op) :
    Primitives.binary_int_arith_op =
  match op with
  | Add -> Add
  | Sub -> Sub
  | Mul -> Mul
  | Div signedness -> Div (convert_signedness signedness)
  | Mod signedness -> Mod (convert_signedness signedness)
  | And -> And
  | Or -> Or
  | Xor -> Xor

let convert_int_shift_op (op : P.int_shift_op) : Primitives.int_shift_op =
  match op with Lsl -> Lsl | Lsr -> Lsr | Asr -> Asr

let convert_int_comparison (cmp : P.signed_or_unsigned P.comparison) :
    Primitives.int_comparison =
  match cmp with
  | Eq -> Int_eq
  | Neq -> Int_neq
  | Lt signedness -> Int_lt (convert_signed_or_unsigned signedness)
  | Gt signedness -> Int_gt (convert_signed_or_unsigned signedness)
  | Le signedness -> Int_le (convert_signed_or_unsigned signedness)
  | Ge signedness -> Int_ge (convert_signed_or_unsigned signedness)

let convert_binary_primitive (p : P.binary_primitive) :
    Primitives.binary_primitive option =
  match p with
  | String_or_bigstring_load (String, width) -> (
    (* The loads of an integer; not that of a float, nor those of vectors. *)
    match width with
    | Eight -> Some (String_or_bigstring_load Eight)
    | Eight_signed -> Some (String_or_bigstring_load Eight_signed)
    | Sixteen -> Some (String_or_bigstring_load Sixteen)
    | Sixteen_signed -> Some (String_or_bigstring_load Sixteen_signed)
    | Thirty_two -> Some (String_or_bigstring_load Thirty_two)
    | Sixty_four -> Some (String_or_bigstring_load Sixty_four)
    | Single | One_twenty_eight _ | Two_fifty_six _ | Five_twelve _ | Mask ->
      None)
  | String_or_bigstring_load ((Bytes | Bigstring), _) -> None
  | Phys_equal Eq -> Some (Phys_equal Phys_eq)
  | Phys_equal Neq -> Some (Phys_equal Phys_neq)
  | Int_arith (kind, op) ->
    Some (Int_arith (convert_standard_int kind, convert_int_arith_op op))
  | Int_shift (kind, op) ->
    Some (Int_shift (convert_standard_int kind, convert_int_shift_op op))
  | Int_comp (kind, Yielding_bool cmp) ->
    let behaviour : Primitives.int_comparison_behaviour =
      Yielding_bool (convert_int_comparison cmp)
    in
    Some (Int_comp (convert_standard_int kind, behaviour))
  | Int_comp (kind, Yielding_int_like_compare_functions signedness) ->
    Some
      (Int_comp
         ( convert_standard_int kind,
           Yielding_int_like_compare_functions
             (convert_signed_or_unsigned signedness) ))
  | _ -> None

(* The compiler's [Make_block] carries the kind of each field, one for each
   argument, with its subkind, and Simplify takes an argument that is a variable
   to be of the subkind of its field: where it cannot be, the primitive becomes
   [Invalid] ([Simplify_variadic_primitive]). The model's [Make_block] has no
   such annotation and makes a block of whatever values it is given. So the only
   annotation converted is the one that says nothing, [any_value] for every
   field; a block kind that says more of a field is not in the model. *)
let convert_variadic_primitive (p : P.variadic_primitive) ~num_args :
    Primitives.variadic_primitive option =
  match p with
  | Make_block (Values (tag, kinds), Immutable, (Heap _ | Local _))
  (* CR mshinwell: a block made in a region is converted as one made on the
     heap; see [region_variables]. *)
    when List.compare_length_with kinds num_args = 0
         && List.for_all
              (fun kind ->
                Flambda_kind.With_subkind.equal kind
                  Flambda_kind.With_subkind.any_value)
              kinds ->
    Some (Make_block (Block_kind_values (z_of_int (Tag.Scannable.to_int tag))))
  | _ -> None

(* ---- Conversion of terms ---------------------------------------------- *)

(* A float is its bit pattern, read as a signed integer. *)
let convert_float32 f : Model.const =
  Naked_float32
    (z_of_int64
       (Int64.of_int32 (Numeric_types.Float32_by_bit_pattern.to_bits f)))

let convert_float f : Model.const =
  Naked_float (z_of_int64 (Numeric_types.Float_by_bit_pattern.to_bits f))

let convert_const (c : Reg_width_const.t) : Model.const =
  match Reg_width_const.descr c with
  | Naked_immediate i -> Naked_immediate (z_of_int (Target_ocaml_int.to_int i))
  | Tagged_immediate i ->
    Tagged_immediate (z_of_int (Target_ocaml_int.to_int i))
  | Null -> Null
  | Naked_int8 i -> Naked_int8 (z_of_int (Numeric_types.Int8.to_int i))
  | Naked_int16 i -> Naked_int16 (z_of_int (Numeric_types.Int16.to_int i))
  | Naked_int32 i -> Naked_int32 (z_of_int64 (Int64.of_int32 i))
  | Naked_int64 i -> Naked_int64 (z_of_int64 i)
  | Naked_nativeint i ->
    Naked_nativeint (z_of_int64 (Targetint_32_64.to_int64 i))
  | Naked_float32 f -> convert_float32 f
  | Naked_float f -> convert_float f
  | Poison (kind, _) -> Poison (convert_kind kind)
  | Naked_vec128 _ | Naked_vec256 _ | Naked_vec512 _ | Naked_mask _ ->
    unsupported "constant %a" Reg_width_const.print c

(* CR mshinwell: A hack, so that a unit made from an OCaml source can be
   converted: the model has nothing of [Rec_info]. Every function the front end
   makes begins with [let next_depth = rec_info (succ my_depth)], and a
   recursive call coerces its callee by [depth my_depth -> next_depth]. The
   conversion drops all three: the [Let] of a [Rec_info] (in [convert_let]), the
   [my_depth] of code (in [convert_code]), and every coercion (in
   [convert_simple], which was so before). So the model sees none of what
   Simplify does with depths: unrolling, and the inlining of recursive functions
   up to a depth. What keeps this from passing a unit for nothing: the variables
   dropped are noted here, and one used as a value is refused
   ([convert_variable]); without that it would be a variable that nothing binds,
   the unit before Simplify would be undefined, and anything refines an
   undefined unit. To be replaced when the model has depths and coercions. *)
let depth_variables : Variable.Set.t ref = ref Variable.Set.empty

let drop_depth_variable var =
  depth_variables := Variable.Set.add var !depth_variables

(* CR mshinwell: Regions are dropped, and what is allocated in one is converted
   as if it were allocated on the heap (decision D37). The model has no stack of
   regions and frees nothing. So the conversion drops the [Let] of a
   [Begin_region], makes the [Let] of an [End_region] bind the unit value that
   the primitive returns (in [convert_let]), and forgets the allocation mode of
   a block, a boxed number, a set of closures and a call, and the region of
   code. This is right for a unit in which nothing allocated in a region is used
   after the region has ended, which is what the type checker's modes are for,
   and which nothing in the middle end checks. It is an assumption about both
   units of a check: a validation says nothing about whether Simplify keeps
   every use of a local allocation inside its region, since a term that uses a
   block after its region has ended has, here, the meaning it would have if the
   block were on the heap. What keeps a unit from passing for nothing: the
   region variables dropped are noted here, and one used as a value is refused
   ([convert_variable]). The regions of exception handlers ([Begin_try_region],
   [End_try_region]) are dropped in the same way. One is opened where a handler
   is installed, and the handler ends it, which ends every region that the body
   had open when it raised. So for a unit with a handler the assumption is
   wider: nothing allocated in a region is used after the region has ended,
   whether it ends at its [End_region] or because a raise left it open and the
   handler ended it; and a validation says nothing about whether Simplify keeps
   it so on either way out. To be replaced if the model gains regions. *)
let region_variables : Variable.Set.t ref = ref Variable.Set.empty

let drop_region_variable var =
  region_variables := Variable.Set.add var !region_variables

(* A variable where it is used as a value. *)
let convert_variable var =
  if Variable.Set.mem var !depth_variables
  then unsupported "the depth variable %a used as a value" Variable.print var;
  if Variable.Set.mem var !region_variables
  then unsupported "the region variable %a used as a value" Variable.print var;
  Variables.find var

(* CR mshinwell: the coercions are dropped; see [depth_variables]. *)
let convert_simple (s : Simple.t) : Model.simple =
  Simple.pattern_match' s
    ~var:(fun var ~coercion:_ -> Model.Var (convert_variable var))
    ~symbol:(fun symbol ~coercion:_ -> Model.Symbol (Symbols.find symbol))
    ~const:(fun c -> Model.Const (convert_const c))

let convert_simples = List.map convert_simple

let convert_value_slots (slots : Simple.t Value_slot.Map.t) =
  Value_slot.Map.bindings slots
  |> List.map (fun (slot, s) -> find_value_slot slot, convert_simple s)

(* The model has two presentations of a set of closures (FlambdaModel.v): a set
   of one function whose function slot is not named, and a set of any number of
   functions at named function slots. A unit is converted with the first if all
   its sets have one function and it projects no function slot, so that such a
   unit is converted as it was before the model had function slots; otherwise
   all its sets are converted with the second. The two units of a check are
   converted alike ([convert_both]).

   This switch is to go: once the normalisations know the sets with named
   function slots as well as the others, every unit is to be converted with
   them, and the first presentation deleted from the model. *)
let named_function_slots = ref false

exception Needs_named_function_slots

let needs_named_function_slots () =
  if not !named_function_slots then raise Needs_named_function_slots

(* Runs a conversion; if it meets something that needs named function slots,
   runs it again with them. *)
let with_function_slots convert =
  try convert ()
  with Needs_named_function_slots ->
    named_function_slots := true;
    convert ()

(* The functions of a set, in order, and its value slots. *)
let convert_set_of_closures (set : Set_of_closures.t) =
  let funs =
    Function_declarations.funs_in_order (Set_of_closures.function_decls set)
  in
  let function_decls =
    List.map
      (fun ( function_slot,
             (code_id : Function_declarations.code_id_in_function_declaration)
           ) ->
        match code_id with
        | Code_id { code_id; _ } ->
          Function_slots.find function_slot, Code_ids.find code_id
        | Deleted _ -> unsupported "a closure of deleted code")
      (Function_slot.Lmap.bindings funs)
  in
  function_decls, convert_value_slots (Set_of_closures.value_slots set)

(* The code of a set of one function, whose function slot is then left
   unnamed. *)
let only_function function_decls =
  match function_decls with
  | [(_, code)] when not !named_function_slots -> Some code
  | [] -> unsupported "a set of closures of no function"
  | _ :: _ ->
    needs_named_function_slots ();
    None

let convert_raise_kind (kind : Trap_action.Raise_kind.t) : Model.raise_kind =
  match kind with
  | Regular -> Regular
  | Reraise -> Reraise
  | No_trace -> No_trace

let convert_trap_action (action : Trap_action.t) : Model.trap_action =
  match action with
  | Push { exn_handler } -> Push (Continuations.find exn_handler)
  | Pop { exn_handler; raise_kind } ->
    Pop
      (Continuations.find exn_handler, Option.map convert_raise_kind raise_kind)

(* Tupled code ([let f (a, b) = ...]) has one parameter for each component of
   the tuple. A call of unknown arity gives it the tuple, which the compiler
   takes apart on the way in, and so does every call of the model. A direct
   call, and a call of known arity, give it the components, and the model has
   not got that. What is noted of the conventions of calls as a unit is
   converted: the code that is tupled, the code that a direct call names, and
   whether a call of known arity was met ([check_calls_of_tupled_code]). *)
let tupled_code : Code_id.t list ref = ref []

let directly_called_code : Code_id.t list ref = ref []

let known_arity_call_met : bool ref = ref false

let convert_apply_cont (ac : Apply_cont_expr.t) : Model.apply_cont =
  { ac_continuation = Continuations.find (Apply_cont_expr.continuation ac);
    ac_args = convert_simples (Apply_cont_expr.args ac);
    ac_trap_action =
      Option.map convert_trap_action (Apply_cont_expr.trap_action ac)
  }

let convert_params (params : Bound_parameters.t) =
  List.map Variables.find (Bound_parameters.vars params)

(* The kinds of parameters, which the model keeps beside them. *)
let convert_params_kinds (params : Bound_parameters.t) =
  List.map
    (fun param ->
      let kind = Bound_parameter.kind param in
      convert_kind (Flambda_kind.With_subkind.kind kind))
    (Bound_parameters.to_list params)

let convert_bound_var (bound_var : Bound_var.t) =
  let var = Bound_var.var bound_var in
  Variables.find var, convert_kind (Variable.kind var)

(* The code that is a newer version of other code, with that code, and the code
   that is bound as deleted, noted as a unit is converted. *)
let newer_versions : (Code_id.t * Code_id.t) list ref = ref []

let deleted_code : Code_id.t list ref = ref []

(* The code ids, declared deleted, whose number has been given to a newer
   version of the code ([convert_both]). The number then stands for the code
   that the unit binds, so the declaration is left out: the term of the model
   does not declare deleted a code id that it binds. It is empty except while
   [convert_both] converts the unit after for the second time, so that no other
   conversion leaves a declaration out. *)
let superseded_code : Code_id.t list ref = ref []

(* The code that the front end marks for loopify
   ([Loopify_attribute.should_loopify]), noted as a unit is converted. *)
let loopify_marked : Code_id.t list ref = ref []

(* Forgets everything that the conversion has noted so far, so that a unit is
   converted as if it were the first: the numbers given to names and what is
   kept beside the terms. Whoever gives the conversion more state adds it
   here. *)
let reset_conversion () =
  Variables.reset ();
  Continuations.reset ();
  Symbols.reset ();
  Code_ids.reset ();
  Value_slots.reset ();
  Function_slots.reset ();
  slot_kinds := [];
  depth_variables := Variable.Set.empty;
  named_function_slots := false;
  newer_versions := [];
  deleted_code := [];
  superseded_code := [];
  loopify_marked := [];
  region_variables := Variable.Set.empty;
  tupled_code := [];
  directly_called_code := [];
  known_arity_call_met := false

let rec convert_expr (e : Flambda.Expr.t) : Model.expr =
  match Flambda.Expr.descr e with
  | Let let_expr ->
    Flambda.Let_expr.pattern_match let_expr ~f:(fun pattern ~body ->
        convert_let pattern (Flambda.Let_expr.defining_expr let_expr) body)
  | Let_cont (Non_recursive { handler; _ }) ->
    Flambda.Non_recursive_let_cont_handler.pattern_match handler
      ~f:(fun k ~body ->
        let handler =
          convert_handler ~invariant_params:Bound_parameters.empty
            (Flambda.Non_recursive_let_cont_handler.handler handler)
        in
        Model.Let_cont_non_recursive
          (Continuations.find k, handler, convert_expr body))
  | Let_cont (Recursive handlers) ->
    Flambda.Recursive_let_cont_handlers.pattern_match handlers
      ~f:(fun ~invariant_params ~body handlers ->
        let handlers =
          Flambda.Continuation_handlers.to_map handlers
          |> Continuation.Lmap.bindings
          |> List.map (fun (k, handler) ->
              Continuations.find k, convert_handler ~invariant_params handler)
        in
        Model.Let_cont_recursive (handlers, convert_expr body))
  | Apply apply -> Model.Apply (convert_apply apply)
  | Apply_cont ac -> Model.Apply_cont (convert_apply_cont ac)
  | Switch switch ->
    let arms =
      Target_ocaml_int.Map.bindings (Switch_expr.arms switch)
      |> List.map (fun (discriminant, arm) ->
          ( z_of_int (Target_ocaml_int.to_int discriminant),
            convert_apply_cont (Switch_arm.action arm) ))
    in
    Model.Switch (convert_simple (Switch_expr.scrutinee switch), arms)
  | Invalid _ -> Model.Invalid

and convert_handler ~invariant_params (handler : Flambda.Continuation_handler.t)
    : Model.continuation_handler =
  let is_exn_handler = Flambda.Continuation_handler.is_exn_handler handler in
  Flambda.Continuation_handler.pattern_match handler ~f:(fun params ~handler ->
      let params = Bound_parameters.append invariant_params params in
      let kinds = convert_params_kinds params in
      Model.Handler
        ( convert_params params,
          (if is_exn_handler
           then Model.make_exn_handler_metadata kinds
           else Model.make_handler_metadata kinds),
          convert_expr handler ))

and convert_let (pattern : Bound_pattern.t) (defining_expr : Flambda.Named.t)
    body : Model.expr =
  match pattern, defining_expr with
  | Singleton bound_var, Simple s ->
    let var, kind = convert_bound_var bound_var in
    Model.Let (var, kind, Simple (convert_simple s), convert_expr body)
  | ( Singleton bound_var,
      Prim
        ( Variadic
            ((Begin_region { ghost = _ } | Begin_try_region { ghost = _ }), _),
          _ ) ) ->
    (* CR mshinwell: the binding of a region is dropped, and with it the region
       it is given as its parent, if any; see [region_variables]. *)
    drop_region_variable (Bound_var.var bound_var);
    convert_expr body
  | ( Singleton bound_var,
      Prim
        ( Unary
            ((End_region { ghost = _ } | End_try_region { ghost = _ }), region),
          _ ) ) ->
    (* CR mshinwell: the end of a region does nothing but return the unit value;
       see [region_variables]. *)
    let is_region =
      Simple.pattern_match' region
        ~var:(fun var ~coercion:_ -> Variable.Set.mem var !region_variables)
        ~symbol:(fun _ ~coercion:_ -> false)
        ~const:(fun _ -> false)
    in
    if not is_region
    then unsupported "the end of %a, which is not a region" Simple.print region;
    let var, kind = convert_bound_var bound_var in
    Model.Let
      ( var,
        kind,
        Simple (Const (Tagged_immediate (z_of_int 0))),
        convert_expr body )
  | Singleton bound_var, Prim (prim, _) ->
    let var, kind = convert_bound_var bound_var in
    Model.Let (var, kind, convert_prim prim, convert_expr body)
  | Set_of_closures bound_vars, Set_of_closures (set, _) -> (
    let function_decls, slots = convert_set_of_closures set in
    match only_function function_decls, bound_vars with
    | Some code, [bound_var] ->
      let var, kind = convert_bound_var bound_var in
      Model.Let (var, kind, Set_of_closures (code, slots), convert_expr body)
    | Some _, ([] | _ :: _ :: _) ->
      unsupported "the binding %a" Bound_pattern.print pattern
    | None, _ -> (
      (* [let_closures] gives each variable the kind [Value]. *)
      let bound_vars =
        List.map
          (fun bound_var ->
            match convert_bound_var bound_var with
            | var, Kinds.Value -> var
            | _, (Naked_number _ | Region | Rec_info) ->
              unsupported "the binding %a" Bound_pattern.print pattern)
          bound_vars
      in
      match
        Model.let_closures bound_vars function_decls slots (convert_expr body)
      with
      | Some e -> e
      | None -> unsupported "the binding %a" Bound_pattern.print pattern))
  | Static bound_static, Static_consts group ->
    let bindings =
      Flambda.Static_const_group.match_against_bound_static group bound_static
        ~init:[]
        ~code:(fun bindings code_id code ->
          (match Code0.newer_version_of code with
          | Some older -> newer_versions := (code_id, older) :: !newer_versions
          | None -> ());
          if Loopify_attribute.should_loopify (Code0.loopify code)
          then loopify_marked := code_id :: !loopify_marked;
          let id = Code_ids.find code_id in
          Model.Bind_code (id, convert_code code) :: bindings)
        ~deleted_code:(fun bindings code_id ->
          deleted_code := code_id :: !deleted_code;
          if List.exists (Code_id.equal code_id) !superseded_code
          then bindings
          else Model.Bind_deleted_code (Code_ids.find code_id) :: bindings)
        ~set_of_closures:(fun bindings ~closure_symbols set ->
          let function_decls, slots = convert_set_of_closures set in
          let closure_symbols =
            List.map
              (fun (function_slot, symbol) ->
                Function_slots.find function_slot, Symbols.find symbol)
              (Function_slot.Lmap.bindings closure_symbols)
          in
          match only_function function_decls, closure_symbols with
          | Some code, [(_, symbol)] ->
            Model.Bind_symbol
              (symbol, Static_const_set_of_closures (code, slots))
            :: bindings
          | Some _, ([] | _ :: _ :: _) ->
            unsupported "the binding %a" Bound_pattern.print pattern
          | None, _ ->
            if
              not
                (List.equal ( = )
                   (List.map fst closure_symbols)
                   (List.map fst function_decls))
            then unsupported "the binding %a" Bound_pattern.print pattern;
            List.rev_append
              (Model.bind_closures closure_symbols function_decls slots)
              bindings)
        ~block_like:(fun bindings symbol const ->
          Model.Bind_symbol (Symbols.find symbol, convert_static_const const)
          :: bindings)
    in
    Model.Let_static (List.rev bindings, convert_expr body)
  | Singleton bound_var, Rec_info _ ->
    (* CR mshinwell: the binding of a depth variable is dropped; see
       [depth_variables]. *)
    drop_depth_variable (Bound_var.var bound_var);
    convert_expr body
  | Singleton _, (Set_of_closures _ | Static_consts _)
  | Set_of_closures _, _
  | Static _, _ ->
    unsupported "the binding %a" Bound_pattern.print pattern

and convert_prim (prim : P.t) : Model.named =
  match prim with
  | Unary (Project_value_slot { project_from; value_slot }, closure) ->
    let slot = find_value_slot value_slot in
    if !named_function_slots
    then
      Project_value_slot_from
        (Function_slots.find project_from, slot, convert_simple closure)
    else Project_value_slot (slot, convert_simple closure)
  | Unary (Project_function_slot { move_from; move_to }, closure) ->
    needs_named_function_slots ();
    Project_function_slot
      ( Function_slots.find move_from,
        Function_slots.find move_to,
        convert_simple closure )
  | Unary (p, arg) -> (
    match convert_unary_primitive p with
    | Some p -> Prim (Unary p, [convert_simple arg])
    | None -> unsupported "primitive %a" P.print prim)
  | Binary (p, arg1, arg2) -> (
    match convert_binary_primitive p with
    | Some p -> Prim (Binary p, [convert_simple arg1; convert_simple arg2])
    | None -> unsupported "primitive %a" P.print prim)
  | Variadic (p, args) -> (
    match convert_variadic_primitive p ~num_args:(List.length args) with
    | Some p -> Prim (Variadic p, convert_simples args)
    | None -> unsupported "primitive %a" P.print prim)
  | Nullary _ | Ternary _ | Quaternary _ ->
    unsupported "primitive %a" P.print prim

and convert_or_variable : type a.
    (a -> Model.const) -> a Or_variable.t -> Model.simple =
 fun convert contents ->
  match contents with
  | Const c -> Const (convert c)
  | Var (var, _) -> Var (convert_variable var)

(* A static block of the model is a tag and fields that are values, so a block
   with a mixed shape, whose flat suffix holds naked numbers, is not in the
   model. *)
and convert_static_const (const : Static_const.t) : Model.static_const =
  match const with
  | Block (tag, Immutable, Value_only, fields) ->
    Static_const_block
      ( z_of_int (Tag.Scannable.to_int tag),
        List.map
          (fun field -> convert_simple (Simple.With_debuginfo.simple field))
          fields )
  | Immutable_string s ->
    Static_const_immutable_string
      (List.init (String.length s) (fun i -> z_of_int (Char.code s.[i])))
  | Boxed_float32 contents ->
    Static_const_boxed_number (convert_or_variable convert_float32 contents)
  | Boxed_float contents ->
    Static_const_boxed_number (convert_or_variable convert_float contents)
  | Boxed_int32 contents ->
    Static_const_boxed_number
      (convert_or_variable
         (fun i : Model.const -> Naked_int32 (z_of_int64 (Int64.of_int32 i)))
         contents)
  | Boxed_int64 contents ->
    Static_const_boxed_number
      (convert_or_variable
         (fun i : Model.const -> Naked_int64 (z_of_int64 i))
         contents)
  | Boxed_nativeint contents ->
    Static_const_boxed_number
      (convert_or_variable
         (fun i : Model.const ->
           Naked_nativeint (z_of_int64 (Targetint_32_64.to_int64 i)))
         contents)
  | _ -> unsupported "static constant %a" Static_const.print const

and convert_code (code : Flambda.Function_params_and_body.t Code0.t) :
    Model.code =
  (* A call of unknown arity gives a tupled function the tuple as its first
     argument, whatever the arity of its code: the model's code says whether it
     is tupled. *)
  let is_tupled = Code0.is_tupled code in
  if is_tupled then tupled_code := Code0.code_id code :: !tupled_code;
  Flambda.Function_params_and_body.pattern_match (Code0.params_and_body code)
    ~f:(fun
        ~return_continuation
        ~exn_continuation
        params
        ~body
        ~my_closure
        ~is_my_closure_used:_
        ~my_alloc_mode
        ~my_depth
        ~free_names_of_body:_
      ->
      (* CR mshinwell: the depth of the code is dropped; see
         [depth_variables]. *)
      drop_depth_variable my_depth;
      (* CR mshinwell: the regions of the code are dropped; see
         [region_variables]. *)
      (match (my_alloc_mode : Alloc_mode.For_applications.t) with
      | Not_alloc_stack { alloc_region } -> drop_region_variable alloc_region
      | Maybe_alloc_stack { alloc_region; region; ghost_region } ->
        drop_region_variable alloc_region;
        drop_region_variable region;
        drop_region_variable ghost_region);
      (* The arity that calls are compared with is that of the metadata of the
         code; unarized, it must give the kinds of the parameters. *)
      let params_arity = convert_arity (Code0.params_arity code) in
      let result_arity = convert_arity (Code0.result_arity code) in
      if Model.unarize params_arity <> convert_params_kinds params
      then unsupported "code whose parameters are not those of its arity";
      Model.Code
        ( convert_params params,
          Variables.find my_closure,
          Continuations.find return_continuation,
          Continuations.find exn_continuation,
          (if is_tupled
           then Model.make_tupled_code_metadata params_arity result_arity
           else Model.make_code_metadata params_arity result_arity),
          convert_expr body ))

and convert_apply (apply : Apply_expr.t) : Model.apply_expr =
  let callee =
    match Apply_expr.callee apply with
    | Some callee -> convert_simple callee
    | None -> unsupported "a call with no callee"
  in
  let args_arity = convert_arity (Apply_expr.args_arity apply) in
  let return_arity = convert_arity (Apply_expr.return_arity apply) in
  let call_kind : Model.call_kind =
    match Apply_expr.call_kind apply with
    | Function { function_call = Direct code_id; _ } ->
      directly_called_code := code_id :: !directly_called_code;
      Direct (Code_ids.find code_id)
    | Function { function_call = Indirect_known_arity _; _ } ->
      known_arity_call_met := true;
      Indirect
    | Function { function_call = Indirect_unknown_arity; _ } -> Indirect
    | Method _ | C_call _ | Effect _ ->
      unsupported "the call %a" Apply_expr.print apply
  in
  let continuation =
    match Apply_expr.continuation apply with
    | Return k -> Continuations.find k
    | Never_returns -> unsupported "a call that never returns"
  in
  let exn_continuation = Apply_expr.exn_continuation apply in
  { ap_callee = callee;
    ap_call_kind = call_kind;
    ap_args = convert_simples (Apply_expr.args apply);
    ap_continuation = continuation;
    ap_exn_continuation =
      Continuations.find (Exn_continuation.exn_handler exn_continuation);
    ap_exn_extra_args =
      List.map
        (fun (simple, kind) ->
          ( convert_simple simple,
            convert_kind (Flambda_kind.With_subkind.kind kind) ))
        (Exn_continuation.extra_args exn_continuation);
    ap_args_arity = args_arity;
    ap_return_arity = return_arity
  }

(* ---- Running ---------------------------------------------------------- *)

(* What is observed of a value: what it is, through the symbols it points to. A
   closure is not looked into: its code differs before and after. A partial
   application is observed as a closure is: Simplify makes a closure of one
   whose function it knows. *)
type observation =
  | Tagged of int
  | Naked of string * int64
  | Null
  | Block of int * observation list
  | Boxed of observation
  | String of string
  | Function
  | Dangling
  | Location of int
  | Too_deep

let rec observe depth (statics : Values.static_env) (v : Values.value) :
    observation =
  if depth = 0
  then Too_deep
  else
    match v with
    | Value_const (Tagged_immediate i) -> Tagged (int_of_z i)
    | Value_const (Naked_immediate i) -> Naked ("imm", int64_of_z i)
    | Value_const (Naked_int8 i) -> Naked ("int8", int64_of_z i)
    | Value_const (Naked_int16 i) -> Naked ("int16", int64_of_z i)
    | Value_const (Naked_int32 i) -> Naked ("int32", int64_of_z i)
    | Value_const (Naked_int64 i) -> Naked ("int64", int64_of_z i)
    | Value_const (Naked_nativeint i) -> Naked ("nativeint", int64_of_z i)
    | Value_const (Naked_float32 bits) -> Naked ("float32", int64_of_z bits)
    | Value_const (Naked_float bits) -> Naked ("float", int64_of_z bits)
    | Value_const Null -> Null
    | Value_const _ -> Naked ("number", 0L)
    | Value_closure _ | Value_closure_of_set _ | Value_partial_application _ ->
      Function
    | Value_block (tag, fields) ->
      Block (int_of_z tag, List.map (observe (depth - 1) statics) fields)
    | Value_boxed_number c ->
      Boxed (observe (depth - 1) statics (Values.Value_const c))
    | Value_location l -> Location (int_of_positive l)
    | Value_symbol symbol -> (
      match Maps.lookup symbol statics.static_values with
      | None -> Dangling
      | Some (Static_closure _ | Static_closure_of_set _) -> Function
      | Some (Static_block (tag, fields)) ->
        Block (int_of_z tag, List.map (observe (depth - 1) statics) fields)
      | Some (Static_boxed_number v) -> Boxed (observe (depth - 1) statics v)
      | Some (Static_string bytes) ->
        String
          (String.init (List.length bytes) (fun i ->
               Char.chr (int_of_z (List.nth bytes i)))))

let rec print_observation ppf (o : observation) =
  match o with
  | Tagged i -> Format.fprintf ppf "%d" i
  | Naked (kind, i) -> Format.fprintf ppf "#%Ld:%s" i kind
  | Null -> Format.fprintf ppf "null"
  | Block (tag, fields) ->
    Format.fprintf ppf "@[<hov 1>[%d:@ %a]@]" tag
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
         print_observation)
      fields
  | Boxed o -> Format.fprintf ppf "@[<hov 1>(boxed@ %a)@]" print_observation o
  | String s -> Format.fprintf ppf "%S" s
  | Function -> Format.fprintf ppf "<fun>"
  | Dangling -> Format.fprintf ppf "<unbound symbol>"
  | Location n -> Format.fprintf ppf "<location %d>" n
  | Too_deep -> Format.fprintf ppf "..."

type outcome =
  | Returns of observation list
  | Raises of observation list
  | Exits_elsewhere
  | Undefined
  | Still_running

let print_outcome ppf (outcome : outcome) =
  let print_values ppf values =
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
      print_observation ppf values
  in
  match outcome with
  | Returns values ->
    Format.fprintf ppf "@[<hov 2>returns@ %a@]" print_values values
  | Raises values ->
    Format.fprintf ppf "@[<hov 2>raises@ %a@]" print_values values
  | Exits_elsewhere -> Format.fprintf ppf "applies an unbound continuation"
  | Undefined -> Format.fprintf ppf "undefined"
  | Still_running -> Format.fprintf ppf "still running when the fuel ran out"

let fuel = 1_000_000

(* The calls that are not in code: those of the unit itself, which inlining
   removes. *)
let rec calls_outside_code (e : Model.expr) =
  let in_handler (Model.Handler (_, _, handler)) = calls_outside_code handler in
  match e with
  | Let (_, _, _, body) | Let_static (_, body) -> calls_outside_code body
  | Let_cont_non_recursive (_, handler, body) ->
    in_handler handler + calls_outside_code body
  | Let_cont_recursive (handlers, body) ->
    List.fold_left
      (fun calls (_, handler) -> calls + in_handler handler)
      (calls_outside_code body) handlers
  | Apply _ -> 1
  | Apply_cont _ | Switch _ | Invalid -> 0

(* The code that calls itself, at once or through other code, by direct calls.
   The validation is told not to inline the calls of such code
   ([FlambdaNormaliseSpec.inline_calls]): Simplify leaves them, and to inline
   one is to leave another to inline in the next round. This is a guess that is
   not trusted: the validation is sound whatever code it is told to keep. *)
let rec direct_callees (e : Model.expr) : Model.code_id list =
  let in_handler (Model.Handler (_, _, handler)) = direct_callees handler in
  match e with
  | Let (_, _, _, body) | Let_static (_, body) -> direct_callees body
  | Let_cont_non_recursive (_, handler, body) ->
    in_handler handler @ direct_callees body
  | Let_cont_recursive (handlers, body) ->
    List.concat_map (fun (_, handler) -> in_handler handler) handlers
    @ direct_callees body
  | Apply { ap_call_kind = Direct code; _ } -> [code]
  | Apply { ap_call_kind = Indirect; _ } | Apply_cont _ | Switch _ | Invalid ->
    []

(* Every piece of code that an expression binds, with its body. *)
let rec code_bound (e : Model.expr) : (Model.code_id * Model.expr) list =
  let in_handler (Model.Handler (_, _, handler)) = code_bound handler in
  match e with
  | Let (_, _, _, body) -> code_bound body
  | Let_static (bindings, body) ->
    List.concat_map
      (fun (binding : Model.static_binding) ->
        match binding with
        | Bind_code (id, Code (_, _, _, _, _, body)) ->
          (id, body) :: code_bound body
        | Bind_deleted_code _ | Bind_symbol _ -> [])
      bindings
    @ code_bound body
  | Let_cont_non_recursive (_, handler, body) ->
    in_handler handler @ code_bound body
  | Let_cont_recursive (handlers, body) ->
    List.concat_map (fun (_, handler) -> in_handler handler) handlers
    @ code_bound body
  | Apply _ | Apply_cont _ | Switch _ | Invalid -> []

let recursive_code (e : Model.expr) : Model.code_id list =
  let calls =
    List.map (fun (id, body) -> id, direct_callees body) (code_bound e)
  in
  let reaches_itself id =
    let seen = ref [] in
    let rec from caller =
      match List.assoc_opt caller calls with
      | None -> false
      | Some callees ->
        List.exists
          (fun callee ->
            callee = id
            || (not (List.mem callee !seen))
               &&
               (seen := callee :: !seen;
                from callee))
          callees
    in
    from id
  in
  List.filter reaches_itself (List.map fst calls)

(* The code that an expression calls directly, in the code it binds too. *)
let called_directly (e : Model.expr) : Model.code_id list =
  direct_callees e
  @ List.concat_map (fun (_, body) -> direct_callees body) (code_bound e)

type converted =
  { body : Model.expr;
    return_continuation : Model.continuation;
    exn_continuation : Model.continuation
  }

(* The model's calls give tupled code a tuple. The compiler's direct call, and
   its call of known arity, give code its arguments as the code takes them: for
   tupled code that is another call, which the model has not got. A direct call
   names its code. A call of known arity does not, so it is refused wherever the
   unit has tupled code at all. Code that the unit does not bind cannot be run
   by the model, tupled or not, so a direct call of it stays. *)
let check_calls_of_tupled_code () =
  let is_tupled code_id = List.exists (Code_id.equal code_id) !tupled_code in
  if List.exists is_tupled !directly_called_code
  then unsupported "a direct call of a tupled function";
  match !tupled_code with
  | [] -> ()
  | _ :: _ ->
    if !known_arity_call_met
    then
      unsupported "a call of known arity in a unit that has a tupled function"

let convert_unit (unit : Flambda_unit.t) : converted =
  tupled_code := [];
  directly_called_code := [];
  known_arity_call_met := false;
  (* CR mshinwell: the region of the unit is dropped; see [region_variables]. *)
  drop_region_variable (Flambda_unit.toplevel_my_alloc_region unit);
  let body = convert_expr (Flambda_unit.body unit) in
  check_calls_of_tupled_code ();
  { body;
    return_continuation =
      Continuations.find (Flambda_unit.return_continuation unit);
    exn_continuation = Continuations.find (Flambda_unit.exn_continuation unit)
  }

let run (unit : converted) : outcome * int =
  let rec go steps (state : Semantics.state) =
    if steps >= fuel
    then Still_running, steps
    else
      match Semantics.step state with
      | Step state -> go (steps + 1) state
      | Undefined -> Undefined, steps
      | Exit (k, values) ->
        let values = List.map (observe 50 state.state_statics) values in
        ( (if k = unit.return_continuation
           then Returns values
           else if k = unit.exn_continuation
           then Raises values
           else Exits_elsewhere),
          steps )
  in
  go 0
    { state_expr = unit.body;
      state_vars = [];
      state_conts = [];
      state_statics = Values.empty_static_env
    }

(* ---- Printing model terms ---------------------------------------------- *)

(* For looking at what the normalisation made of the two terms, when an example
   is not validated (set FLSEMANTICS_PRINT_TERMS). *)
let print_list print ppf items =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
    print ppf items

let print_var ppf x = Format.fprintf ppf "v%d" (int_of_positive x)

let print_simple ppf (s : Model.simple) =
  match s with
  | Var x -> print_var ppf x
  | Symbol sym -> Format.fprintf ppf "$%d" (int_of_positive sym)
  | Const (Tagged_immediate i) -> Format.fprintf ppf "%d" (int_of_z i)
  | Const (Naked_immediate i) -> Format.fprintf ppf "#%d" (int_of_z i)
  | Const Null -> Format.fprintf ppf "null"
  | Const _ -> Format.fprintf ppf "<const>"

let print_simples = print_list print_simple

let print_cont ppf k = Format.fprintf ppf "k%d" (int_of_positive k)

let print_value_slots ppf slots =
  print_list
    (fun ppf (slot, s) ->
      Format.fprintf ppf "%d = %a" (int_of_positive slot) print_simple s)
    ppf slots

let print_function_decls ppf function_decls =
  print_list
    (fun ppf (slot, code) ->
      Format.fprintf ppf "f%d = code%d" (int_of_positive slot)
        (int_of_positive code))
    ppf function_decls

let string_of_standard_int (kind : Kinds.standard_int) =
  match kind with
  | Standard_tagged_immediate -> "tagged_imm"
  | Standard_naked_immediate -> "imm"
  | Standard_naked_int8 -> "int8"
  | Standard_naked_int16 -> "int16"
  | Standard_naked_int32 -> "int32"
  | Standard_naked_int64 -> "int64"
  | Standard_naked_nativeint -> "nativeint"

let string_of_signedness (signedness : Primitives.signedness) =
  match signedness with Signed -> "" | Unsigned -> "unsigned_"

let print_prim ppf (p : Primitives.prim) =
  let unary (p : Primitives.unary_primitive) =
    match p with
    | Block_load (_, mut, field) ->
      Printf.sprintf "Block_load%s %d"
        (match mut with
        | Mutable -> " mut"
        | Immutable -> ""
        | Immutable_unique -> " immut_uniq")
        (int_of_z field)
    | Is_int variant_only -> if variant_only then "Is_int" else "Is_int_generic"
    | Is_null -> "Is_null"
    | Get_tag -> "Get_tag"
    | Array_length _ ->
      (* The converter makes no primitive of arrays. *)
      "Array_length"
    | String_length -> "String_length"
    | Opaque_identity _ -> "Opaque_identity"
    | Unary_int_arith (kind, op) ->
      Printf.sprintf "Int_arith %s %s"
        (string_of_standard_int kind)
        (match op with Not -> "not" | Swap_byte_endianness -> "bswap")
    | Num_conv (src, dst) ->
      Printf.sprintf "Num_conv %s %s"
        (string_of_standard_int src)
        (string_of_standard_int dst)
    | Boolean_not -> "Boolean_not"
    | Unbox_number _ -> "Unbox_number"
    | Box_number _ -> "Box_number"
    | Untag_immediate -> "Untag_immediate"
    | Tag_immediate -> "Tag_immediate"
    | Reinterpret_64_bit_word Tagged_int63_as_unboxed_int64 ->
      "Reinterpret_64_bit_word int63_as_int64"
    | Reinterpret_64_bit_word Unboxed_int64_as_tagged_int63 ->
      "Reinterpret_64_bit_word int64_as_int63"
  in
  let int_arith (op : Primitives.binary_int_arith_op) =
    match op with
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "mul"
    | Div signedness -> string_of_signedness signedness ^ "div"
    | Mod signedness -> string_of_signedness signedness ^ "mod"
    | And -> "and"
    | Or -> "or"
    | Xor -> "xor"
  in
  let int_comp (behaviour : Primitives.int_comparison_behaviour) =
    match behaviour with
    | Yielding_bool Int_eq -> "eq"
    | Yielding_bool Int_neq -> "neq"
    | Yielding_bool (Int_lt signedness) ->
      string_of_signedness signedness ^ "lt"
    | Yielding_bool (Int_gt signedness) ->
      string_of_signedness signedness ^ "gt"
    | Yielding_bool (Int_le signedness) ->
      string_of_signedness signedness ^ "le"
    | Yielding_bool (Int_ge signedness) ->
      string_of_signedness signedness ^ "ge"
    | Yielding_int_like_compare_functions signedness ->
      string_of_signedness signedness ^ "compare"
  in
  match p with
  | Unary p -> Format.pp_print_string ppf (unary p)
  | Binary (Array_load _) ->
    (* The converter makes no primitive of arrays. *)
    Format.pp_print_string ppf "Array_load"
  | Binary (String_or_bigstring_load width) ->
    Format.fprintf ppf "String_load %s"
      (match width with
      | Eight -> "8"
      | Eight_signed -> "8s"
      | Sixteen -> "16"
      | Sixteen_signed -> "16s"
      | Thirty_two -> "32"
      | Sixty_four -> "64")
  | Binary (Phys_equal Phys_eq) -> Format.pp_print_string ppf "Phys_equal eq"
  | Binary (Phys_equal Phys_neq) -> Format.pp_print_string ppf "Phys_equal neq"
  | Binary (Int_arith (kind, op)) ->
    Format.fprintf ppf "Int_arith %s %s"
      (string_of_standard_int kind)
      (int_arith op)
  | Binary (Int_shift (kind, op)) ->
    Format.fprintf ppf "Int_shift %s %s"
      (string_of_standard_int kind)
      (match op with Lsl -> "lsl" | Lsr -> "lsr" | Asr -> "asr")
  | Binary (Int_comp (kind, behaviour)) ->
    Format.fprintf ppf "Int_comp %s %s"
      (string_of_standard_int kind)
      (int_comp behaviour)
  | Variadic (Make_block (Block_kind_values tag)) ->
    Format.fprintf ppf "Make_block %d" (int_of_z tag)
  | Heap _ ->
    (* The converter makes no primitive of the heap. *)
    Format.pp_print_string ppf "<primitive of the heap>"

let print_named ppf (d : Model.named) =
  match d with
  | Simple s -> print_simple ppf s
  | Prim (p, args) ->
    Format.fprintf ppf "@[<hov 2>%a@ (%a)@]" print_prim p print_simples args
  | Set_of_closures (code, slots) ->
    Format.fprintf ppf "@[<hov 2>closure code%d@ {%a}@]" (int_of_positive code)
      print_value_slots slots
  | Closure_of_set (slot, function_decls, slots) ->
    Format.fprintf ppf "@[<hov 2>closure f%d of@ {%a}@ {%a}@]"
      (int_of_positive slot) print_function_decls function_decls
      print_value_slots slots
  | Project_value_slot (slot, closure) ->
    Format.fprintf ppf "%a.slot%d" print_simple closure (int_of_positive slot)
  | Project_value_slot_from (project_from, slot, closure) ->
    Format.fprintf ppf "%a.(f%d).slot%d" print_simple closure
      (int_of_positive project_from)
      (int_of_positive slot)
  | Project_function_slot (move_from, move_to, closure) ->
    Format.fprintf ppf "%a.(f%d -> f%d)" print_simple closure
      (int_of_positive move_from)
      (int_of_positive move_to)

let print_trap_action ppf (action : Model.trap_action option) =
  match action with
  | None -> ()
  | Some (Push k) -> Format.fprintf ppf "@ push(%a)" print_cont k
  | Some (Pop (k, kind)) ->
    Format.fprintf ppf "@ pop(%s%a)"
      (match kind with
      | None -> ""
      | Some Regular -> "regular "
      | Some Reraise -> "reraise "
      | Some No_trace -> "notrace ")
      print_cont k

let print_apply_cont ppf (ac : Model.apply_cont) =
  Format.fprintf ppf "@[<hov 2>cont %a%a@ (%a)@]" print_cont ac.ac_continuation
    print_trap_action ac.ac_trap_action print_simples ac.ac_args

let rec print_expr ppf (e : Model.expr) =
  match e with
  | Let (x, _, d, body) ->
    Format.fprintf ppf "@[<hov 2>let %a =@ %a in@]@ %a" print_var x print_named
      d print_expr body
  | Let_static (bindings, body) ->
    Format.fprintf ppf "@[<v 2>let static@ %a@]@ in@ %a"
      (Format.pp_print_list print_binding)
      bindings print_expr body
  | Let_cont_non_recursive (k, handler, body) ->
    Format.fprintf ppf "@[<v 2>let_cont %a %a@]@ in@ %a" print_cont k
      print_handler handler print_expr body
  | Let_cont_recursive (handlers, body) ->
    Format.fprintf ppf "@[<v 2>let_cont rec@ %a@]@ in@ %a"
      (Format.pp_print_list (fun ppf (k, handler) ->
           Format.fprintf ppf "%a %a" print_cont k print_handler handler))
      handlers print_expr body
  | Apply ap ->
    Format.fprintf ppf "@[<hov 2>apply%s %a@ (%a)@ -> %a * %a%a@]"
      (match ap.ap_call_kind with
      | Direct code -> Printf.sprintf " direct(code%d)" (int_of_positive code)
      | Indirect -> "")
      print_simple ap.ap_callee print_simples ap.ap_args print_cont
      ap.ap_continuation print_cont ap.ap_exn_continuation
      (fun ppf extra ->
        match extra with
        | [] -> ()
        | _ :: _ -> Format.fprintf ppf "@ (%a)" print_simples extra)
      (List.map fst ap.ap_exn_extra_args)
  | Apply_cont ac -> print_apply_cont ppf ac
  | Switch (scrutinee, arms) ->
    Format.fprintf ppf "@[<v 2>switch %a@ %a@]" print_simple scrutinee
      (Format.pp_print_list (fun ppf (i, ac) ->
           Format.fprintf ppf "| %d -> %a" (int_of_z i) print_apply_cont ac))
      arms
  | Invalid -> Format.fprintf ppf "invalid"

and print_handler ppf (Model.Handler (params, metadata, handler)) =
  Format.fprintf ppf "%s(%a) =@ @[<v>%a@]"
    (if metadata.hm_is_exn_handler then "exn " else "")
    (print_list print_var) params print_expr handler

and print_binding ppf (binding : Model.static_binding) =
  match binding with
  | Bind_code (id, Code (params, my_closure, ret, exn, metadata, body)) ->
    Format.fprintf ppf "@[<v 2>code%d%s (%a) %a -> %a * %a =@ %a@]"
      (int_of_positive id)
      (if metadata.cm_is_tupled then " tupled" else "")
      (print_list print_var) params print_var my_closure print_cont ret
      print_cont exn print_expr body
  | Bind_deleted_code id ->
    Format.fprintf ppf "code%d deleted" (int_of_positive id)
  | Bind_symbol (sym, Static_const_set_of_closures (code, slots)) ->
    Format.fprintf ppf "@[<hov 2>$%d = closure code%d@ {%a}@]"
      (int_of_positive sym) (int_of_positive code) print_value_slots slots
  | Bind_symbol
      (sym, Static_const_closure_of_set (slot, symbols, function_decls, slots))
    ->
    Format.fprintf ppf "@[<hov 2>$%d = closure f%d of@ {%a}@ at {%a}@ {%a}@]"
      (int_of_positive sym) (int_of_positive slot) print_function_decls
      function_decls
      (print_list (fun ppf (slot, sym) ->
           Format.fprintf ppf "f%d = $%d" (int_of_positive slot)
             (int_of_positive sym)))
      symbols print_value_slots slots
  | Bind_symbol (sym, Static_const_block (tag, fields)) ->
    Format.fprintf ppf "@[<hov 2>$%d = Block %d@ (%a)@]" (int_of_positive sym)
      (int_of_z tag) print_simples fields
  | Bind_symbol (sym, Static_const_boxed_number contents) ->
    Format.fprintf ppf "$%d = boxed %a" (int_of_positive sym) print_simple
      contents
  | Bind_symbol (sym, Static_const_immutable_string _) ->
    Format.fprintf ppf "$%d = <string>" (int_of_positive sym)

(* ---- Static bindings that are not used --------------------------------- *)

(* The symbols and code ids that a term binds and that nothing live refers to:
   not the term outside its static bindings, and not a static binding that is
   itself live. This is only a guess of what may be removed:
   FlambdaUnusedStaticsSpec.drop_statics checks it before removing anything. *)
type static_name =
  | Symbol_name of Model.symbol
  | Code_name of Model.code_id

let unused_statics (e : Model.expr) : Unused_statics.dropped =
  (* What each binding refers to, and what the term refers to outside its
     bindings ([None]). *)
  let references : (static_name option * static_name) list ref = ref [] in
  let bound : static_name list ref = ref [] in
  let refer owner name = references := (owner, name) :: !references in
  let in_simple owner (s : Model.simple) =
    match s with
    | Symbol sym -> refer owner (Symbol_name sym)
    | Var _ | Const _ -> ()
  in
  let in_simples owner = List.iter (in_simple owner) in
  let in_slots owner = List.iter (fun (_, s) -> in_simple owner s) in
  let rec in_expr owner (e : Model.expr) =
    match e with
    | Let (_, _, d, body) ->
      (match d with
      | Simple s
      | Project_value_slot (_, s)
      | Project_value_slot_from (_, _, s)
      | Project_function_slot (_, _, s) ->
        in_simple owner s
      | Prim (_, args) -> in_simples owner args
      | Set_of_closures (code, slots) ->
        refer owner (Code_name code);
        in_slots owner slots
      | Closure_of_set (_, decls, slots) ->
        List.iter (fun (_, code) -> refer owner (Code_name code)) decls;
        in_slots owner slots);
      in_expr owner body
    | Let_static (bindings, body) ->
      List.iter
        (fun (binding : Model.static_binding) ->
          match binding with
          | Bind_code (id, Code (_, _, _, _, _, code_body)) ->
            bound := Code_name id :: !bound;
            in_expr (Some (Code_name id)) code_body
          | Bind_deleted_code _ -> ()
          | Bind_symbol (sym, const) -> (
            bound := Symbol_name sym :: !bound;
            let owner = Some (Symbol_name sym) in
            match const with
            | Static_const_set_of_closures (code, slots) ->
              refer owner (Code_name code);
              in_slots owner slots
            | Static_const_closure_of_set (_, symbols, function_decls, slots) ->
              List.iter (fun (_, sym) -> refer owner (Symbol_name sym)) symbols;
              List.iter
                (fun (_, code) -> refer owner (Code_name code))
                function_decls;
              in_slots owner slots
            | Static_const_block (_, fields) -> in_simples owner fields
            | Static_const_boxed_number contents -> in_simple owner contents
            | Static_const_immutable_string _ -> ()))
        bindings;
      in_expr owner body
    | Let_cont_non_recursive (_, Handler (_, _, handler), body) ->
      in_expr owner handler;
      in_expr owner body
    | Let_cont_recursive (handlers, body) ->
      List.iter
        (fun (_, Model.Handler (_, _, handler)) -> in_expr owner handler)
        handlers;
      in_expr owner body
    | Apply ap -> (
      in_simple owner ap.ap_callee;
      in_simples owner ap.ap_args;
      in_simples owner (List.map fst ap.ap_exn_extra_args);
      match ap.ap_call_kind with
      | Direct code -> refer owner (Code_name code)
      | Indirect -> ())
    | Apply_cont ac -> in_simples owner ac.ac_args
    | Switch (scrutinee, arms) ->
      in_simple owner scrutinee;
      List.iter
        (fun (_, (ac : Model.apply_cont)) -> in_simples owner ac.ac_args)
        arms
    | Invalid -> ()
  in
  in_expr None e;
  let rec live_from live =
    let live' =
      List.fold_left
        (fun live (owner, name) ->
          let owner_is_live =
            match owner with None -> true | Some owner -> List.mem owner live
          in
          if owner_is_live && not (List.mem name live)
          then name :: live
          else live)
        live !references
    in
    if List.length live' = List.length live then live else live_from live'
  in
  let live = live_from [] in
  let unused = List.filter (fun name -> not (List.mem name live)) !bound in
  { dropped_symbols =
      List.filter_map
        (function Symbol_name sym -> Some sym | Code_name _ -> None)
        unused;
    dropped_code =
      List.filter_map
        (function Code_name id -> Some id | Symbol_name _ -> None)
        unused
  }

(* ---- Lets that Simplify made static bindings --------------------------- *)

(* Which [Let]s of the term before to make static bindings, and of which
   symbols. This is only a guess, read off the term after:
   FlambdaLiftSpec.lift_unit checks what it needs of it, and the comparison of
   the two terms the rest. The symbols to give are those that the term after
   binds and the term before does not. Each goes to the first [Let] that makes
   what the symbol is bound to: a closure of the same code, a block of the same
   tag whose fields agree, a boxed number. Two fields agree if the first is a
   variable of which nothing is known, or if they are the same symbol or
   constant; a variable bound to a symbol or a constant, or whose own [Let] is
   lifted here, counts as that symbol or constant. A [Let] is named by its path,
   as FlambdaLiftSpec.lift_expr counts it. A symbol is not given to a [Let] that
   [banned] pairs it with: the caller asks again, with the pair banned, where a
   symbol went to a [Let] whose block nothing uses in the end.

   In a handler that is not at toplevel
   (FlambdaWellFormedSpec.handler_at_toplevel: the arm of a test, say), where no
   static binding may stand, a symbol goes to the first [Let] that makes just
   what the symbol is bound to and mentions no variable:
   FlambdaLiftFromArmsSpec.lift_to_head binds it at the head of the unit. That
   puts the unit under a group of static bindings, and the validation makes it
   first, so the paths of the other [Let]s outside code are then given as they
   are under that group.

   A symbol that no [Let] outside code takes goes to the first [Let] in the body
   of code that makes just what the symbol is bound to and mentions no variable:
   FlambdaLiftFromCodeSpec.lift_from_code lifts it out of the code.

   The guess also says in which code [my_closure] is a symbol: the code of each
   closure that the term after binds statically, if the term before, once
   lifted, makes no other closure of that code
   (FlambdaMyClosureSpec.only_closure_of). *)
let lifting_guess ~unit ~(banned : (Lift.path * Model.symbol) list)
    (before : Model.expr) (after : Model.expr) : Lift.lifting =
  (* The symbols bound outside code, in the order in which they are bound when
     the term runs: the body of a [Let_cont] before its handler. *)
  let rec bound_symbols (e : Model.expr) =
    match e with
    | Let (_, _, _, body) -> bound_symbols body
    | Let_static (bindings, body) ->
      List.filter_map
        (fun (binding : Model.static_binding) ->
          match binding with
          | Bind_symbol (sym, const) -> Some (sym, const)
          | Bind_code _ | Bind_deleted_code _ -> None)
        bindings
      @ bound_symbols body
    | Let_cont_non_recursive (_, Handler (_, _, handler), body) ->
      bound_symbols body @ bound_symbols handler
    | Let_cont_recursive (_, body) -> bound_symbols body
    | Apply _ | Apply_cont _ | Switch _ | Invalid -> []
  in
  let bound_before = List.map fst (bound_symbols before) in
  let to_give =
    ref
      (List.filter
         (fun (sym, _) -> not (List.mem sym bound_before))
         (bound_symbols after))
  in
  (* The path of what is at a path in the unit, once the unit is under a group
     of static bindings. *)
  let rec under_group (path : Numbers.positive) : Numbers.positive =
    match path with
    | Coq_xH -> Coq_xO Coq_xH
    | Coq_xO path -> Coq_xO (under_group path)
    | Coq_xI path -> Coq_xI (under_group path)
  in
  (* A path of [banned] is as an earlier guess gave it: the path of the [Let],
     or that path under the group of the lifting to the head. *)
  let take path matches =
    match
      List.find_opt
        (fun (sym, const) ->
          matches const
          && (not (List.mem (path, sym) banned))
          && not (List.mem (under_group path, sym) banned))
        !to_give
    with
    | None -> None
    | Some (sym, const) ->
      to_give := List.filter (fun (sym', _) -> sym' <> sym) !to_give;
      Some (sym, const)
  in
  (* The variables met that stand for a symbol or a constant: those bound to
     one, and those whose [Let] is lifted. *)
  let known_simples : (Model.variable * Model.simple) list ref = ref [] in
  let fields_agree fields fields' =
    List.length fields = List.length fields'
    && List.for_all2
         (fun (field : Model.simple) (field' : Model.simple) ->
           let field =
             match field with
             | Var x -> (
               match List.assoc_opt x !known_simples with
               | Some known -> known
               | None -> field)
             | Symbol _ | Const _ -> field
           in
           match field, field' with
           | Var _, _ -> true
           | (Symbol _ | Const _), Var _ -> false
           | (Symbol _ | Const _), (Symbol _ | Const _) -> field = field')
         fields fields'
  in
  let lets = ref [] in
  let lift x path (target : Lift.lift_to) =
    lets := (path, target) :: !lets;
    match target with
    | Lift_to_symbol sym ->
      known_simples := (x, Model.Symbol sym) :: !known_simples
    | Lift_to_closure_symbols _ -> ()
  in
  (* The [Let]s that mention no variable, in the body of code or in a handler
     that is not at toplevel. *)
  let plain (s : Model.simple) =
    match s with Symbol _ | Const _ -> true | Var _ -> false
  in
  let plain_slots slots = List.for_all (fun (_, s) -> plain s) slots in
  let rec in_code code_lets (path : Numbers.positive) (e : Model.expr) =
    match e with
    | Let (_, _, d, body) ->
      let lift_out target = code_lets := (path, target) :: !code_lets in
      (match d with
      | Set_of_closures (code, slots) when plain_slots slots -> (
        match
          take path (fun (const : Model.static_const) ->
              match const with
              | Static_const_set_of_closures (code', slots') ->
                code = code' && slots = slots'
              | _ -> false)
        with
        | Some (sym, _) -> lift_out (Lift.Lift_to_symbol sym)
        | None -> ())
      | Closure_of_set (_, decls, slots) when plain_slots slots -> (
        match
          take path (fun (const : Model.static_const) ->
              match const with
              | Static_const_closure_of_set (_, _, decls', slots') ->
                decls = decls' && slots = slots'
              | _ -> false)
        with
        | Some (_, Static_const_closure_of_set (_, symbols, _, _)) ->
          to_give
            := List.filter
                 (fun (sym, _) ->
                   not (List.exists (fun (_, sym') -> sym = sym') symbols))
                 !to_give;
          lift_out (Lift.Lift_to_closure_symbols symbols)
        | Some _ | None -> ())
      | Prim (Variadic (Make_block (Block_kind_values tag)), fields)
        when List.for_all plain fields -> (
        match
          take path (fun (const : Model.static_const) ->
              match const with
              | Static_const_block (tag', fields') ->
                tag = tag' && fields = fields'
              | _ -> false)
        with
        | Some (sym, _) -> lift_out (Lift.Lift_to_symbol sym)
        | None -> ())
      | Prim (Unary (Box_number _), [contents]) when plain contents -> (
        match
          take path (fun (const : Model.static_const) ->
              match const with
              | Static_const_boxed_number contents' -> contents = contents'
              | _ -> false)
        with
        | Some (sym, _) -> lift_out (Lift.Lift_to_symbol sym)
        | None -> ())
      | _ -> ());
      in_code code_lets (Numbers.Coq_xO path) body
    | Let_static (_, body) -> in_code code_lets (Numbers.Coq_xO path) body
    | Let_cont_non_recursive (_, Handler (_, _, handler), body) ->
      in_code code_lets (Numbers.Coq_xO path) body;
      in_code code_lets (Numbers.Coq_xI path) handler
    | Let_cont_recursive (_, body) ->
      in_code code_lets (Numbers.Coq_xO path) body
    | Apply _ | Apply_cont _ | Switch _ | Invalid -> ()
  in
  let to_head = ref [] in
  let rec in_expr (path : Numbers.positive) (e : Model.expr) =
    match e with
    | Let (x, _, d, body) ->
      (match d with
      | Simple ((Symbol _ | Const _) as known) ->
        known_simples := (x, known) :: !known_simples
      | Set_of_closures (code, _) -> (
        match
          take path (fun (const : Model.static_const) ->
              match const with
              | Static_const_set_of_closures (code', _) -> code = code'
              | _ -> false)
        with
        | Some (sym, _) -> lift x path (Lift_to_symbol sym)
        | None -> ())
      | Closure_of_set (slot, decls, _) -> (
        match
          take path (fun (const : Model.static_const) ->
              match const with
              | Static_const_closure_of_set (_, _, decls', _) -> decls = decls'
              | _ -> false)
        with
        | Some (_, Static_const_closure_of_set (_, symbols, _, _)) ->
          (* The symbols of the other closures of the set go with it. *)
          to_give
            := List.filter
                 (fun (sym, _) ->
                   not (List.exists (fun (_, sym') -> sym = sym') symbols))
                 !to_give;
          (match List.assoc_opt slot symbols with
          | Some sym -> known_simples := (x, Model.Symbol sym) :: !known_simples
          | None -> ());
          lift x path (Lift_to_closure_symbols symbols)
        | Some _ | None -> ())
      | Prim (Variadic (Make_block (Block_kind_values tag)), fields) -> (
        match
          take path (fun (const : Model.static_const) ->
              match const with
              | Static_const_block (tag', fields') ->
                tag = tag' && fields_agree fields fields'
              | _ -> false)
        with
        | Some (sym, _) -> lift x path (Lift_to_symbol sym)
        | None -> ())
      | Prim (Unary (Box_number _), [contents]) -> (
        match
          take path (fun (const : Model.static_const) ->
              match const with
              | Static_const_boxed_number contents' ->
                fields_agree [contents] [contents']
              | _ -> false)
        with
        | Some (sym, _) -> lift x path (Lift_to_symbol sym)
        | None -> ())
      | _ -> ());
      in_expr (Numbers.Coq_xO path) body
    | Let_static (_, body) -> in_expr (Numbers.Coq_xO path) body
    | Let_cont_non_recursive (k, (Handler (_, _, handler) as h), body) ->
      in_expr (Numbers.Coq_xO path) body;
      if Well_formed.handler_at_toplevel unit.Well_formed.unit_exn k h body
      then in_expr (Numbers.Coq_xI path) handler
      else in_code to_head (Numbers.Coq_xI path) handler
    | Let_cont_recursive (_, body) -> in_expr (Numbers.Coq_xO path) body
    | Apply _ | Apply_cont _ | Switch _ | Invalid -> ()
  in
  in_expr Lift.root before;
  let to_head = List.rev !to_head in
  let lets =
    match Lift_from_code.lifted_out_bindings to_head Lift.root before with
    | [] -> List.rev !lets
    | _ :: _ ->
      List.rev_map (fun (path, target) -> under_group path, target) !lets
  in
  let out_of_code = ref [] in
  let rec in_groups (e : Model.expr) =
    match e with
    | Let (_, _, _, body) -> in_groups body
    | Let_static (bindings, body) ->
      List.iter
        (fun (binding : Model.static_binding) ->
          match binding with
          | Bind_code (id, Code (_, _, _, _, _, code_body)) -> (
            let code_lets = ref [] in
            in_code code_lets Lift.root code_body;
            match !code_lets with
            | [] -> ()
            | _ :: _ -> out_of_code := (id, List.rev !code_lets) :: !out_of_code
            )
          | Bind_deleted_code _ | Bind_symbol _ -> ())
        bindings;
      in_groups body
    | Let_cont_non_recursive (_, Handler (_, _, handler), body) ->
      in_groups body;
      in_groups handler
    | Let_cont_recursive (_, body) -> in_groups body
    | Apply _ | Apply_cont _ | Switch _ | Invalid -> ()
  in
  in_groups before;
  let out_of_code = List.rev !out_of_code in
  let lifted =
    Lift.lift_expr lets Lift.root
      (Lift_from_code.lift_from_code out_of_code [] Lift.root
         (Lift_from_arms.lift_to_head to_head before))
  in
  let my_closures =
    List.filter_map
      (fun (sym, (const : Model.static_const)) ->
        let code =
          match const with
          | Static_const_set_of_closures (code, _) -> Some code
          | Static_const_closure_of_set (slot, _, decls, _) ->
            List.assoc_opt slot decls
          | Static_const_block _ | Static_const_boxed_number _
          | Static_const_immutable_string _ ->
            None
        in
        match code with
        | Some code when My_closure.only_closure_of code sym lifted ->
          Some (code, sym)
        | Some _ | None -> None)
      (bound_symbols after)
  in
  { lifting_unit = unit;
    lifted_lets = lets;
    lifted_my_closures = my_closures;
    lifted_out_of_code = out_of_code;
    lifted_to_head = to_head
  }

(* ---- Value slots that Simplify removed --------------------------------- *)

(* The value slots that the static sets of closures of the term before have and
   those of the term after have not, and that nothing in the term before
   projects. This is a guess: FlambdaUnusedSlotsSpec.drop_unused_slots checks
   that nothing projects them, and the comparison of the two terms the rest. *)
let unused_slots_guess (before : Model.expr) (after : Model.expr) :
    Model.value_slot list =
  let rec static_slots (e : Model.expr) =
    match e with
    | Let (_, _, _, body) -> static_slots body
    | Let_static (bindings, body) ->
      List.concat_map
        (fun (binding : Model.static_binding) ->
          match binding with
          | Bind_symbol (_, Static_const_set_of_closures (_, slots))
          | Bind_symbol (_, Static_const_closure_of_set (_, _, _, slots)) ->
            List.map fst slots
          | Bind_symbol
              ( _,
                ( Static_const_block _ | Static_const_boxed_number _
                | Static_const_immutable_string _ ) )
          | Bind_code _ | Bind_deleted_code _ ->
            [])
        bindings
      @ static_slots body
    | Let_cont_non_recursive (_, Handler (_, _, handler), body) ->
      static_slots body @ static_slots handler
    | Let_cont_recursive (_, body) -> static_slots body
    | Apply _ | Apply_cont _ | Switch _ | Invalid -> []
  in
  let kept = static_slots after in
  List.sort_uniq compare (static_slots before)
  |> List.filter (fun slot ->
      (not (List.mem slot kept)) && Unused_slots.slots_unused [slot] before)

(* ---- The check -------------------------------------------------------- *)

(* Whether a code id is used: called, made a closure of, or bound to code. Being
   bound as deleted is not a use. *)
let rec code_id_used (id : Model.code_id) (e : Model.expr) =
  let in_handler (Model.Handler (_, _, handler)) = code_id_used id handler in
  let in_binding (binding : Model.static_binding) =
    match binding with
    | Bind_code (bound, Code (_, _, _, _, _, body)) ->
      bound = id || code_id_used id body
    | Bind_deleted_code _ -> false
    | Bind_symbol (_, Static_const_set_of_closures (code, _)) -> code = id
    | Bind_symbol (_, Static_const_closure_of_set (_, _, function_decls, _)) ->
      List.exists (fun (_, code) -> code = id) function_decls
    | Bind_symbol
        ( _,
          ( Static_const_block _ | Static_const_boxed_number _
          | Static_const_immutable_string _ ) ) ->
      false
  in
  match e with
  | Let (_, _, Set_of_closures (code, _), body) ->
    code = id || code_id_used id body
  | Let (_, _, Closure_of_set (_, function_decls, _), body) ->
    List.exists (fun (_, code) -> code = id) function_decls
    || code_id_used id body
  | Let
      ( _,
        _,
        ( Simple _ | Prim _ | Project_value_slot _ | Project_value_slot_from _
        | Project_function_slot _ ),
        body ) ->
    code_id_used id body
  | Let_static (bindings, body) ->
    List.exists in_binding bindings || code_id_used id body
  | Let_cont_non_recursive (_, handler, body) ->
    in_handler handler || code_id_used id body
  | Let_cont_recursive (handlers, body) ->
    List.exists (fun (_, handler) -> in_handler handler) handlers
    || code_id_used id body
  | Apply { ap_call_kind = Direct code; _ } -> code = id
  | Apply { ap_call_kind = Indirect; _ } | Apply_cont _ | Switch _ | Invalid ->
    false

(* The two units are converted with one numbering of names, the continuations of
   the second unit standing for those of the first, so that the verified
   comparison can be made of the two bodies as they are.

   Simplify gives a new code id to each new version of a piece of code, and
   binds the old one as deleted. The comparison wants code ids to be the same,
   so the new id is given the number of the old where that changes nothing:
   where the unit after binds the old one as deleted and does not otherwise use
   it. The unit after is converted once to find that out, and again with the
   numbers settled; the second time, the declaration that such an old one is
   deleted is left out, as its number now stands for the new code.

   CR mshinwell: This identification is part of what is trusted, and will most
   likely not be enough: it does nothing for code that has no older version, or
   whose older version is still used. The comparison should relate code ids
   itself; see the CR in middle_end/flambda2/rocq/FlambdaCompareSpec.v for what
   that takes. *)
let convert_both (before : Flambda_unit.t) (after : Flambda_unit.t) =
  with_function_slots @@ fun () ->
  superseded_code := [];
  let before_converted = convert_unit before in
  Continuations.alias
    (Flambda_unit.return_continuation after)
    ~same_as:(Flambda_unit.return_continuation before);
  Continuations.alias
    (Flambda_unit.exn_continuation after)
    ~same_as:(Flambda_unit.exn_continuation before);
  newer_versions := [];
  deleted_code := [];
  superseded_code := [];
  let first_pass = convert_unit after in
  List.iter
    (fun (newer, older) ->
      if
        List.exists (Code_id.equal older) !deleted_code
        && not (code_id_used (Code_ids.find older) first_pass.body)
      then (
        Code_ids.alias newer ~same_as:older;
        superseded_code := older :: !superseded_code))
    !newer_versions;
  let after_converted =
    Fun.protect
      ~finally:(fun () -> superseded_code := [])
      (fun () -> convert_unit after)
  in
  before_converted, after_converted

(* What the check of kinds answers for a unit (FlambdaWellKindedSpec.v), given
   the kinds of the value slots met in the two units. *)
let well_kinded (unit : converted) =
  Well_kinded.well_kinded_unit
    (List.map (fun (slot, kind) -> slot, convert_kind kind) !slot_kinds)
    unit.return_continuation unit.exn_continuation unit.body

(* Static bindings at toplevel only, each name bound once, the sets of closures
   whole, the numbers in range, exception handlers apart from the other
   continuations, and the discipline of trap actions
   (FlambdaWellFormedSpec.v). *)
let well_formed (unit : converted) =
  Well_formed.well_formed_unit
    { unit_return = unit.return_continuation; unit_exn = unit.exn_continuation }
    unit.body

(* A condition of well-formedness that a unit which is not well-formed fails. *)
let why_not_well_formed (unit : converted) =
  let exn = unit.exn_continuation in
  if not (Well_formed.numbers_in_range unit.body)
  then
    (* The compiler's numbers are in range by their types, so this is a fault of
       the conversion. *)
    "a number out of its range: the tag of a block, a constant, the field or \
     the size of a block load, a discriminant or a byte of a string"
  else if not (Binders.names_in_scope unit.return_continuation exn unit.body)
  then "a variable or a continuation that is used where nothing binds it"
  else if not (Binders.binders_distinct unit.body)
  then
    "a name bound twice by one binder, the closure of code among its \
     parameters, or a recursive group of no continuation"
  else if not (Binders.code_closed unit.body)
  then "code that uses a variable or a continuation that it does not bind"
  else if not (Well_formed.sets_well_formed unit.body)
  then
    "a closure at a function slot that its set has not got, a function slot or \
     a code id given twice in a set, the same code in two static sets of one \
     group, or a static set of closures that is not bound whole"
  else if not (Well_formed.unit_exn_handlers_well_formed exn unit.body)
  then
    "an exception handler that is applied as an ordinary continuation, takes \
     no parameter or is recursive; a continuation that is used as an exception \
     handler and is not marked as one; a continuation that the unit or code \
     does not bind and that is used as an exception handler without being its \
     exception continuation, or is given extra arguments; or the exception \
     continuation of the unit or of code named by a trap action that is not \
     that of a raise"
  else if not (Well_formed.traps_well_formed exn unit.body)
  then
    "a trap action, a raise or a call that names a handler other than the one \
     installed last, or a continuation entered with two stacks of handlers"
  else "a static binding that is not at toplevel, or a name bound twice"

(* What a unit is given by where it is run: the continuation that it returns to
   and its exception continuation. *)
let interface (unit : converted) : Well_formed.unit_interface =
  { unit_return = unit.return_continuation; unit_exn = unit.exn_continuation }

(* The term before is checked before Simplify sees it, which is entitled to fail
   on one that is not well-formed. *)
let well_formed_before ~filename (before : Flambda_unit.t) =
  match with_function_slots (fun () -> convert_unit before) with
  | exception Unsupported _ -> true
  | before ->
    let ok = well_formed before in
    if not ok
    then
      Format.printf "%s: not checked: the term is not well-formed (%s)@."
        filename
        (why_not_well_formed before);
    ok

(* What the comparison of the two runs shows of one run, this shows of all. The
   whole check is [validate_unit], extracted from FlambdaValidateSpec.v, where
   it is proved that what it accepts is correct for the unit run on its own from
   empty environments. It normalises the two terms, compares them up to bound
   names and, failing that, removes from the term before the static bindings
   named here and compares again. Which names those are is a guess that it
   checks. Failing that too, it is asked again, with the [Let]s that Simplify
   seems to have made static bindings, in one or more liftings: it lifts them in
   the term before as it was given, if it may, normalises the result, reads the
   value slots of static closures and uses what the unit binds its symbols to,
   removes the value slots of its static sets of closures that the term after
   has not got, moves the bindings of code of both terms up, and compares again.
   What is lifted and which slots are guesses too. Before any of this, where the
   two terms are not the same as they are given, [validate_unit] makes jumps of
   the self tail calls of the code named here, as Simplify does for the code
   that the front end marks for loopify; which code that is, with a name for
   each loop, is a guess again, and the guesses above are made of the term that
   this gives. Failing all of that, the whole is asked a second time, of
   [validate_unit_knowing], extracted from FlambdaValidateKnowingSpec.v, where
   it is proved that what it accepts is correct for the unit in the same way. It
   is [validate_unit] of the two terms normalised by rounds in front of each of
   which the aliases are followed knowing what the symbols are bound to; the
   guesses are made again, from those two terms. *)

(* The code that the front end marks for loopify, each with a name for its loop
   that no continuation of the two units has. *)
let loopify_guess () =
  List.map
    (fun code_id -> Code_ids.find code_id, Continuations.fresh ())
    (List.sort_uniq Code_id.compare !loopify_marked)

let validate ~(outcome_before : outcome) (before : converted)
    (after : converted) =
  let recursive = recursive_code before.body @ recursive_code after.body in
  let inlined = Normalise.inline_calls recursive [] before.body in
  Format.printf
    "  calls outside code once those of known code are inlined: %d@."
    (calls_outside_code inlined);
  let rounds = nat_of_int 50 in
  let nothing_lifted : Lift.lifting =
    { lifting_unit = interface before;
      lifted_lets = [];
      lifted_my_closures = [];
      lifted_out_of_code = [];
      lifted_to_head = []
    }
  in
  (* The code to loopify. *)
  let loops = loopify_guess () in
  (* The validation asked once, with the code whose calls it is told to leave.
     [validate_unit] is the function asked, which has the two terms of the unit
     already and takes the other guesses; [before] and [after] are the two terms
     that it compares once it has made the loops and normalised, from which the
     guesses are made. It gives the verdict; a term before that the function
     asked compared, with how it was made, to show where a unit that is not
     validated differs; whether value slots were removed from it; and the term
     after as it was compared with it. Which pair: where nothing is guessed to
     lift, that of the third comparison (the term before normalised, with its
     unused static bindings removed); where something is lifted and nothing to
     the head of the unit, that of the fourth (the bindings of code of both
     terms moved up); where something is lifted to the head, that of the fifth,
     which is the last. *)
  let ask validate_unit (before : converted) (after : converted) kept =
    (* The term before with its self tail calls made jumps: the term that the
       function asked normalises and lifts in. *)
    let looped = Loopify.loopify_unit loops before.body in
    let normalised_before = Validate.normalise_before rounds kept looped in
    let normalised_after = Validate.normalise_after rounds kept after.body in
    let unused = unused_statics normalised_before in
    let validation : Validate.validation =
      validate_unit unused [] [nothing_lifted]
    in
    let not_lifted =
      ( validation,
        Validate.without_statics unused normalised_before,
        "normalised",
        false,
        normalised_after )
    in
    match validation with
    | Not_validated -> (
      (* The liftings, in turn, as [validate_unit] makes them. The first is
         guessed from the term before after its self tail calls are made jumps;
         each one after it from the term that those before it give, normalised:
         for the [Let]s that inlining a call has brought out of a function. One
         is tried after the first only if it lifts something, and there are
         three at most. After each, as [validate_unit] does, the value slots of
         static closures are read and what the unit binds its symbols to is used
         in every round of the normalisation. The rounds are told, as
         [validate_unit] tells them, not to make a name that is one of the two
         continuations of the unit: every lifting has the unit of the term
         before, and a name made is the one after the greatest of those to avoid
         and of the term, so the names made here are those that [validate_unit]
         makes whatever the number of liftings it is given. [banned] has, for
         the liftings by their place in the sequence, the [Let]s that a symbol
         is not to go to. *)
      let avoid =
        let unit = interface before in
        [unit.unit_return; unit.unit_exn]
      in
      let rec liftings_from banned stage made lifted remaining =
        let lifting =
          lifting_guess ~unit:(interface before)
            ~banned:
              (List.filter_map
                 (fun (stage', path, sym) ->
                   if stage' = stage then Some (path, sym) else None)
                 banned)
            lifted normalised_after
        in
        let stop =
          match
            ( remaining,
              made,
              lifting.lifted_lets,
              lifting.lifted_my_closures,
              lifting.lifted_out_of_code,
              lifting.lifted_to_head )
          with
          | 0, _, _, _, _, _ | _, _ :: _, [], [], [], [] -> true
          | _, _, _, _, _, _ -> false
        in
        if stop
        then List.rev made, lifted
        else
          (* As [validate_unit] applies a lifting: to the head of the unit, out
             of code, then where the [Let]s stand. The sequence ends here if the
             term comes back as the same value in memory. That comparison of two
             pointers is a shortcut of this search, which is bounded and not
             trusted. It says nothing of the checks of a lifting: a lifting
             whose checks pass may give the same term back, and then the search
             stops; one that gives a term rebuilt but equal may continue. *)
          let lifted' = Validate.with_lifting lifting lifted in
          if lifted' == lifted
          then List.rev made, lifted
          else
            liftings_from banned (stage + 1) (lifting :: made)
              (Validate.normalise_lifted rounds avoid kept lifted')
              (remaining - 1)
      in
      (* The guess gives a symbol to the first [Let] that makes a block of its
         shape, and a field that is a variable agrees with anything. So the
         symbol may go to a block that the normalisation then finds no use for
         (the argument of a match that is resolved, say), where the term after
         binds it to a block made later. Such a symbol is not used in the term
         lifted: the sequence is guessed again with that [Let] banned for it, a
         few times at most. *)
      let rec guessed banned again =
        let liftings, lifted = liftings_from banned 0 [] looped 3 in
        let slots = unused_slots_guess lifted normalised_after in
        let lifted = Validate.without_slots slots lifted in
        let unused = unused_statics lifted in
        let wrong =
          List.concat
            (List.mapi
               (fun stage (lifting : Lift.lifting) ->
                 List.filter_map
                   (fun (path, (target : Lift.lift_to)) ->
                     match target with
                     | Lift_to_symbol sym
                       when List.mem sym unused.dropped_symbols ->
                       Some (stage, path, sym)
                     | Lift_to_symbol _ | Lift_to_closure_symbols _ -> None)
                   lifting.lifted_lets)
               liftings)
        in
        match wrong with
        | _ :: _ when again > 0 -> guessed (wrong @ banned) (again - 1)
        | _ -> liftings, lifted, slots, unused
      in
      match guessed [] 5 with
      | [], _, _, _ -> not_lifted
      | (_ :: _ as liftings), lifted, slots, unused ->
        let validation = validate_unit unused slots liftings in
        let slots_removed = match slots with [] -> false | _ :: _ -> true in
        if
          List.exists
            (fun (lifting : Lift.lifting) ->
              match lifting.lifted_to_head with [] -> false | _ :: _ -> true)
            liftings
        then
          (* Something was lifted to the head of the unit: the pair shown is
             that of the last comparison, of the two terms with their static
             bindings that mention no variable bound first. An earlier
             comparison may be the one that holds: the verdict is that of the
             function asked alone. *)
          ( validation,
            Validate.with_statics_first liftings
              (Validate.without_statics unused lifted),
            "lifted and normalised, with the static bindings that mention no \
             variable first",
            slots_removed,
            Validate.with_statics_first liftings normalised_after )
        else
          ( (* The pair shown is that of the fourth comparison: the bindings of
               code of both terms are moved up. *)
            validation,
            Float_code.float_code (Validate.without_statics unused lifted),
            "lifted and normalised",
            slots_removed,
            Float_code.float_code (Validate.with_code_first normalised_after) ))
    | Same_up_to_bound_names | Same_once_normalised
    | Same_once_unused_statics_removed | Same_once_lifted ->
      not_lifted
  in
  (* One attempt, with the code whose calls the validation is told to leave:
     [validate_unit] is asked of the two terms and, where it fails,
     [validate_unit_knowing] is asked of the same two terms. That one compares
     the two terms normalised with what their symbols are bound to used, each by
     its own round, so the guesses for it are made from those, which are
     computed here a second time for the purpose. The round of the term before
     avoids the continuations of the units of the liftings and those of the
     loops; every lifting made here has the unit of the term before, and the
     names that the round makes depend only on the greatest of the names to
     avoid and of the term, so the term that the guesses are made from is the
     one that [validate_unit_knowing] compares. Nothing rests on that but
     whether a guess fits: the verdict is that of [validate_unit_knowing] on the
     two terms as converted. *)
  let asked_again = ref false in
  let attempt kept =
    let first =
      ask
        (fun unused slots liftings ->
          Validate.validate_unit rounds unused slots loops liftings kept
            before.body after.body)
        before after kept
    in
    match first with
    | Not_validated, _, _, _, _ -> (
      let knowing round (unit : converted) =
        { unit with
          body = Validate_knowing.normalise_knowing round rounds unit.body
        }
      in
      let avoid =
        Validate.unit_continuations [nothing_lifted] @ List.map snd loops
      in
      match
        ask
          (fun unused slots liftings ->
            Validate_knowing.validate_unit_knowing rounds unused slots loops
              liftings kept before.body after.body)
          (knowing (Validate.normalise_before_round_avoiding avoid kept) before)
          (knowing (Validate.normalise_after_round kept) after)
          kept
      with
      | Not_validated, _, _, _, _ -> first
      | ( ( Same_up_to_bound_names | Same_once_normalised
          | Same_once_unused_statics_removed | Same_once_lifted ),
          _,
          _,
          _,
          _ ) as second ->
        asked_again := true;
        second)
    | ( ( Same_up_to_bound_names | Same_once_normalised
        | Same_once_unused_statics_removed | Same_once_lifted ),
        _,
        _,
        _,
        _ ) ->
      first
  in
  (* Which calls the validation is told to leave: two guesses, tried in turn.
     First the recursive code and the code that the term after still calls
     directly, which Simplify chose not to inline. Then the recursive code
     alone, for a function that Simplify inlines at one call and not at another:
     there every call inlined on both sides is what makes the two terms the
     same. *)
  let first = attempt (recursive @ called_directly after.body) in
  let attempts, (validation, _, _, slots_removed, _) =
    match first with
    | Not_validated, _, _, _, _ ->
      let second = attempt recursive in
      ( [ ( "leaving the calls of recursive code and of the code that the term \
             after calls",
            first );
          "leaving the calls of recursive code", second ],
        second )
    | ( ( Same_up_to_bound_names | Same_once_normalised
        | Same_once_unused_statics_removed | Same_once_lifted ),
        _,
        _,
        _,
        _ ) ->
      [], first
  in
  Format.printf "  %s@."
    (match validation with
    | Same_up_to_bound_names -> "validated: the same up to bound names"
    | Same_once_normalised -> "validated: the same once normalised"
    | Same_once_unused_statics_removed ->
      "validated: the same once normalised and unused static bindings removed"
    | Same_once_lifted ->
      if slots_removed
      then
        "validated: the same once closures and blocks are lifted to symbols, \
         the terms normalised and unused value slots removed"
      else
        "validated: the same once closures and blocks are lifted to symbols \
         and the terms normalised"
    | Not_validated ->
      if outcome_before = Undefined
      then "nothing to validate, as the term before is undefined"
      else "not validated");
  if !asked_again
  then
    Format.printf
      "  (at the second asking, of the two terms normalised with what their \
       symbols are bound to used)@.";
  (* A term before that is undefined is refined by anything: the validation is
     right and says nothing. *)
  (match validation with
  | Not_validated -> ()
  | Same_up_to_bound_names | Same_once_normalised
  | Same_once_unused_statics_removed | Same_once_lifted ->
    if outcome_before = Undefined
    then
      Format.printf
        "  the term before is undefined in the model, so the validation says \
         nothing of this unit@.");
  match validation with
  | Not_validated when Sys.getenv_opt "FLSEMANTICS_PRINT_TERMS" <> None ->
    (* A pair of terms that the validation compared, for each guess of the calls
       to leave ([ask] says which pair): the static bindings of the term before
       are in the order of those of the term after. *)
    List.iter
      (fun (which, (_, compared, how, _, normalised_after)) ->
        Format.printf
          "@[<v 2>  %s:@ @[<v 2>the term before, %s:@ %a@]@ @[<v 2>the term \
           after, as it was compared:@ %a@]@]@."
          which how print_expr
          (Statics_order.order_statics_as normalised_after compared)
          print_expr normalised_after)
      attempts
  | Not_validated | Same_up_to_bound_names | Same_once_normalised
  | Same_once_unused_statics_removed | Same_once_lifted ->
    ()

let check ~filename (before : Flambda_unit.t) (after : Flambda_unit.t) =
  match convert_both before after with
  | exception Unsupported what ->
    Format.printf "%s: not checked: the model has not got %s@." filename
      (Format.asprintf "%t" what)
  | _, after when not (well_formed after) ->
    Format.printf "%s: the term after Simplify is NOT WELL-FORMED (%s)@."
      filename
      (why_not_well_formed after);
    exit 1
  | before, after ->
    let outcome_before, steps_before = run before in
    let outcome_after, steps_after = run after in
    Format.printf "%s:@.  before Simplify (%d steps): %a@." filename
      steps_before print_outcome outcome_before;
    Format.printf "  after Simplify (%d steps): %a@." steps_after print_outcome
      outcome_after;
    let passes ok = if ok then "passes" else "fails" in
    Format.printf "  the check of kinds: %s before, %s after@."
      (passes (well_kinded before))
      (passes (well_kinded after));
    Format.printf "  calls outside code: %d before, %d after@."
      (calls_outside_code before.body)
      (calls_outside_code after.body);
    let verdict, ok =
      match outcome_before, outcome_after with
      | Undefined, _ -> "anything goes, as the run before is undefined", true
      | Still_running, _ | _, Still_running -> "not decided", true
      | _, _ ->
        if outcome_before = outcome_after
        then "the same", true
        else "DIFFERENT", false
    in
    Format.printf "  %s@." verdict;
    validate ~outcome_before before after;
    if not ok then exit 1

let check_file filename =
  match Parse_flambda.parse_fexpr filename with
  | Error e ->
    Test_utils.dump_error e;
    exit 1
  | Ok unit ->
    named_function_slots := false;
    let unit_info = Parse_flambda.make_unit_info ~filename in
    let comp_unit = Unit_info.modname unit_info in
    Env.set_current_unit unit_info;
    let fl2 = Fexpr_to_flambda.conv comp_unit unit in
    let filename_shown = Filename.basename filename in
    if well_formed_before ~filename:filename_shown fl2.unit
    then
      let null_formatter =
        Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
      in
      let result =
        Flambda2.flambda_to_flambda ~ppf_dump:null_formatter
          ~prefixname:(Filename.chop_extension filename)
          ~machine_width:Sixty_four ~code_slot_offsets:fl2.code_slot_offsets
          fl2.unit
      in
      check ~filename:filename_shown fl2.unit result.flambda

(* The conversion, for the check that takes a term of the model through fexpr
   and back (flroundtrip.ml). *)
let conversion_for_round_trip : Flroundtrip.conversion =
  let names numbered name =
    List.map (fun (id, number) -> name id, number) (numbered ())
  in
  { convert =
      (fun unit ->
        match with_function_slots (fun () -> convert_unit unit) with
        | exception Unsupported what -> Error (Format.asprintf "%t" what)
        | { body; return_continuation; exn_continuation } ->
          Ok { body; return_continuation; exn_continuation });
    reset = reset_conversion;
    value_slot_kind =
      (fun slot -> Option.map convert_kind (List.assoc_opt slot !slot_kinds));
    symbols =
      (fun () ->
        names Symbols.bindings (fun symbol ->
            Linkage_name.to_string (Symbol.linkage_name symbol)));
    code_ids = (fun () -> names Code_ids.bindings Code_id.name);
    value_slots = (fun () -> names Value_slots.bindings Value_slot.name);
    function_slots =
      (fun () -> names Function_slots.bindings Function_slot.name)
  }

(* Simplify, for that check: run as [check_file] runs it, and on the same
   units. *)
let simplify_for_round_trip ~filename (parsed : Fexpr_to_flambda.conv_result) =
  let well_formed_or_not_converted =
    match with_function_slots (fun () -> convert_unit parsed.unit) with
    | exception Unsupported _ -> true
    | before -> well_formed before
  in
  if not well_formed_or_not_converted
  then None
  else
    let null_formatter =
      Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
    in
    let result =
      Flambda2.flambda_to_flambda ~ppf_dump:null_formatter
        ~prefixname:(Filename.chop_extension filename)
        ~machine_width:Sixty_four ~code_slot_offsets:parsed.code_slot_offsets
        parsed.unit
    in
    Some result.flambda

module Options = Oxcaml_args.Make_optcomp_options (Oxcaml_args.Default.Optmain)

let () =
  Clflags.set_target Clflags.Target.Native;
  let round_trip = ref false in
  let files = ref [] in
  let defer_file file =
    match Filename.extension file with
    | ".fl" -> files := file :: !files
    | ext -> Misc.fatal_errorf "Unrecognized extension %s" ext
  in
  Compenv.warnings_for_discarded_params := true;
  Compenv.set_extra_params (Some Oxcaml_args.Extra_params.read_param);
  Compenv.readenv Format.err_formatter Before_args;
  Clflags.add_arguments __LOC__
    (( "-round-trip",
       Arg.Set round_trip,
       " Check that the conversion to the Rocq model survives a round trip \
        through fexpr, for the unit and for what Simplify makes of it" )
    :: (Arch.command_line_options @ Options.list));
  Clflags.Opt_flag_handler.set Oxcaml_flags.opt_flag_handler;
  Compenv.parse_arguments (ref Sys.argv) defer_file "flsemantics";
  Location.read_clflags_from_env ();
  (* One unit to a process: the symbols of a unit stay in the tables of the
     compiler, so a second unit that used the name of one would be refused for a
     reason that is not its own. *)
  match !files with
  | [] -> ()
  | [file] ->
    if !round_trip
    then (
      reset_conversion ();
      Flroundtrip.check_file conversion_for_round_trip
        ~simplify:(simplify_for_round_trip ~filename:file)
        file)
    else check_file file
  | _ :: _ :: _ ->
    Misc.fatal_error
      "flsemantics checks one .fl file: run it once for each file"
