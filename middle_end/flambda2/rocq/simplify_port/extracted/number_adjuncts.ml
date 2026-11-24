(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Number_adjuncts.v, which follows
   middle_end/flambda2/simplify/number_adjuncts.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Flambda.Import
module K = Flambda_kind
module T = Flambda2_types
module Float32_by_bit_pattern = Numeric_types.Float32_by_bit_pattern
module Float_by_bit_pattern = Numeric_types.Float_by_bit_pattern
module Int8 = Numeric_types.Int8
module Int16 = Numeric_types.Int16
module Int32 = Numeric_types.Int32
module Int64 = Numeric_types.Int64

module type Num_common = sig
  include Container_types.S

  module Pair : sig
    type nonrec t = t * t

    include Container_types.S with type t := t
  end

  val cross_product : Set.t -> Set.t -> Pair.Set.t

  val zero : Target_system.Machine_width.t -> t

  val one : Target_system.Machine_width.t -> t

  val minus_one : Target_system.Machine_width.t -> t

  val add : t -> t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val div : t -> t -> t option

  val mod_ : t -> t -> t option

  val to_const : t -> Reg_width_const.t

  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t

  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t

  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t

  val to_naked_int8 : t -> Numeric_types.Int8.t

  val to_naked_int16 : t -> Numeric_types.Int16.t

  val to_naked_int32 : t -> Numeric_types.Int32.t

  val to_naked_int64 : t -> Numeric_types.Int64.t

  val to_naked_nativeint :
    t -> Target_system.Machine_width.t -> Targetint_32_64.t
end

module type Number_kind_common = sig
  module Num : Container_types.S

  val standard_int_or_float_kind : K.Standard_int_or_float.t

  val unboxed_prover :
    Flambda2_types.Typing_env.t ->
    Flambda2_types.t ->
    Num.Set.t Flambda2_types.meet_shortcut

  val this_unboxed : Num.t -> Flambda2_types.t

  val these_unboxed : Num.Set.t -> Flambda2_types.t

  val term_unboxed : Num.t -> Flambda.Named.t
end

module type Number_kind = sig
  module Num : Num_common

  include Number_kind_common with module Num := Num
end

module type Int_number_kind = sig
  module Num : sig
    include Num_common

    val and_ : t -> t -> t

    val or_ : t -> t -> t

    val xor : t -> t -> t

    val not_ : t -> t

    val unsigned_div : t -> t -> t option

    val unsigned_mod : t -> t -> t option

    val shift_left : t -> Target_ocaml_int.t -> t

    val shift_right : t -> Target_ocaml_int.t -> t

    val shift_right_logical : t -> Target_ocaml_int.t -> t

    val swap_byte_endianness : t -> t

    val neg : t -> t

    val compare_unsigned : t -> t -> int
  end

  include Number_kind_common with module Num := Num

  val standard_int_kind : K.Standard_int.t
end

module type Boxable = sig
  module Num : Container_types.S

  val boxable_number_kind : K.Boxable_number.t

  val this_boxed : Num.t -> Alloc_mode.For_types.t -> Flambda2_types.t

  val these_boxed : Num.Set.t -> Alloc_mode.For_types.t -> Flambda2_types.t

  val box : Flambda2_types.t -> Alloc_mode.For_types.t -> Flambda2_types.t
end

module type Boxable_number_kind = sig
  include Number_kind

  include Boxable with module Num := Num
end

module type Boxable_int_number_kind = sig
  include Int_number_kind

  include Boxable with module Num := Num
end

open Port_monad

(** val with_shift : Target_ocaml_int.t -> 'a1 -> (int -> 'a1 coq_M) -> int ->
    'a1 coq_M **)

let with_shift shift if_undefined f integer_bit_width0 =
  match Target_ocaml_int.to_int_option shift with
  | Some shift0 ->
    if shift0 < 0 || shift0 >= integer_bit_width0
    then if_undefined
    else f shift0
  | None -> if_undefined

(** val compare_unsigned_generic : 'a1 -> 'a1 -> ('a1 -> 'a1 -> int coq_M) ->
    ('a1 -> bool coq_M) -> int coq_M **)

let compare_unsigned_generic n1 n2 compare strictly_negative0 =
  let n2_is_negative = strictly_negative0 n2 in
  let n1_is_negative = strictly_negative0 n1 in
  if n1_is_negative
  then if n2_is_negative then compare n1 n2 else 1
  else if n2_is_negative
  then -1
  else compare n1 n2

module For_tagged_immediates = struct
  module Num = struct
    (** val include_Target_ocaml_int : unit **)

    let include_Target_ocaml_int = ()

    include Target_ocaml_int

    (** val zero : Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let zero = Target_ocaml_int.zero

    (** val one : Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let one = Target_ocaml_int.one

    (** val minus_one : Target_system.Machine_width.t -> Target_ocaml_int.t
        coq_M **)

    let minus_one = Target_ocaml_int.minus_one

    (** val not_ : Target_ocaml_int.t -> Target_ocaml_int.t coq_M **)

    let not_ t =
      Target_ocaml_int.xor t (minus_one (Target_ocaml_int.machine_width t))

    (** val strictly_negative : Target_ocaml_int.t -> bool coq_M **)

    let strictly_negative t =
      Target_ocaml_int.( < ) t
        (Target_ocaml_int.zero (Target_ocaml_int.machine_width t))

    (** val compare_unsigned : Target_ocaml_int.t -> Target_ocaml_int.t -> int
        coq_M **)

    let compare_unsigned t1 t2 =
      compare_unsigned_generic t1 t2 Target_ocaml_int.compare strictly_negative

    (** val checked_div : (Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t coq_M) -> Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t option coq_M **)

    let checked_div f t1 t2 =
      let () =
        assert (
          Target_system.Machine_width.equal
            (Target_ocaml_int.machine_width t1)
            (Target_ocaml_int.machine_width t2))
      in
      if
        Target_ocaml_int.equal t2
          (Target_ocaml_int.zero (Target_ocaml_int.machine_width t1))
      then None
      else Some (f t1 t2)

    (** val div : Target_ocaml_int.t -> Target_ocaml_int.t -> Target_ocaml_int.t
        option coq_M **)

    let div = checked_div Target_ocaml_int.div

    (** val unsigned_div : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t option coq_M **)

    let unsigned_div = checked_div Target_ocaml_int.unsigned_div

    (** val mod_ : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t option coq_M **)

    let mod_ = checked_div Target_ocaml_int.mod_

    (** val unsigned_mod : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t option coq_M **)

    let unsigned_mod = checked_div Target_ocaml_int.unsigned_mod

    (** val integer_bit_width : int **)

    let integer_bit_width = if Target_system.is_32_bit () then 32 else 64

    (** val shift_left : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t coq_M **)

    let shift_left t shift =
      with_shift shift
        (Target_ocaml_int.zero (Target_ocaml_int.machine_width t))
        (fun shift_int -> Target_ocaml_int.shift_left t shift_int)
        integer_bit_width

    (** val shift_right : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t coq_M **)

    let shift_right t shift =
      with_shift shift
        (Target_ocaml_int.zero (Target_ocaml_int.machine_width t))
        (fun shift_int -> Target_ocaml_int.shift_right t shift_int)
        integer_bit_width

    (** val shift_right_logical : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t coq_M **)

    let shift_right_logical t shift =
      with_shift shift
        (Target_ocaml_int.zero (Target_ocaml_int.machine_width t))
        (fun shift_int -> Target_ocaml_int.shift_right_logical t shift_int)
        integer_bit_width

    (** val swap_byte_endianness : Target_ocaml_int.t -> Target_ocaml_int.t
        coq_M **)

    let swap_byte_endianness =
      Target_ocaml_int.get_least_significant_16_bits_then_byte_swap

    (** val to_const : Target_ocaml_int.t -> Reg_width_const.t coq_M **)

    let to_const = Reg_width_const.tagged_immediate

    (** val to_immediate : Target_ocaml_int.t -> Target_system.Machine_width.t
        -> Target_ocaml_int.t coq_M **)

    let to_immediate t _ = t

    (** val to_naked_float32 : Target_ocaml_int.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 t =
      Numeric_types.Float32_by_bit_pattern.of_int64
        (Target_ocaml_int.to_int64 t)

    (** val to_naked_float : Target_ocaml_int.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t =
      Numeric_types.Float_by_bit_pattern.create (Target_ocaml_int.to_float t)

    (** val to_naked_int8 : Target_ocaml_int.t -> Numeric_types.Int8.t coq_M **)

    let to_naked_int8 t = Numeric_types.Int8.of_int (Target_ocaml_int.to_int t)

    (** val to_naked_int16 : Target_ocaml_int.t -> Numeric_types.Int16.t coq_M **)

    let to_naked_int16 t =
      Numeric_types.Int16.of_int (Target_ocaml_int.to_int t)

    (** val to_naked_int32 : Target_ocaml_int.t -> Numeric_types.Int32.t coq_M **)

    let to_naked_int32 = Target_ocaml_int.to_int32

    (** val to_naked_int64 : Target_ocaml_int.t -> Numeric_types.Int64.t coq_M **)

    let to_naked_int64 = Target_ocaml_int.to_int64

    (** val to_naked_nativeint : Target_ocaml_int.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t machine_width =
      Target_ocaml_int.to_targetint machine_width t
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind =
    Flambda_kind.Standard_int_or_float.Tagged_immediate

  (** val standard_int_kind : Flambda_kind.Standard_int.t **)

  let standard_int_kind = Flambda_kind.Standard_int.Tagged_immediate

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Target_ocaml_int.Set.t Flambda2_types.meet_shortcut coq_M **)

  let unboxed_prover = Flambda2_types.meet_equals_tagged_immediates

  (** val this_unboxed : Target_ocaml_int.t -> Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_tagged_immediate

  (** val these_unboxed : Target_ocaml_int.Set.t -> Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_tagged_immediates

  (** val term_unboxed : Target_ocaml_int.t -> Flambda.Import.Named.t coq_M **)

  let term_unboxed imm =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.tagged_immediate imm))
end

module For_naked_immediates = struct
  module Num = struct
    (** val include_Target_ocaml_int : unit **)

    let include_Target_ocaml_int = ()

    include Target_ocaml_int

    (** val zero : Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let zero = Target_ocaml_int.zero

    (** val one : Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let one = Target_ocaml_int.one

    (** val minus_one : Target_system.Machine_width.t -> Target_ocaml_int.t
        coq_M **)

    let minus_one = Target_ocaml_int.minus_one

    (** val not_ : Target_ocaml_int.t -> Target_ocaml_int.t coq_M **)

    let not_ t =
      Target_ocaml_int.xor t (minus_one (Target_ocaml_int.machine_width t))

    (** val strictly_negative : Target_ocaml_int.t -> bool coq_M **)

    let strictly_negative t =
      Target_ocaml_int.( < ) t
        (Target_ocaml_int.zero (Target_ocaml_int.machine_width t))

    (** val compare_unsigned : Target_ocaml_int.t -> Target_ocaml_int.t -> int
        coq_M **)

    let compare_unsigned t1 t2 =
      compare_unsigned_generic t1 t2 Target_ocaml_int.compare strictly_negative

    (** val checked_div : (Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t coq_M) -> Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t option coq_M **)

    let checked_div f t1 t2 =
      let () =
        assert (
          Target_system.Machine_width.equal
            (Target_ocaml_int.machine_width t1)
            (Target_ocaml_int.machine_width t2))
      in
      if
        Target_ocaml_int.equal t2
          (Target_ocaml_int.zero (Target_ocaml_int.machine_width t1))
      then None
      else Some (f t1 t2)

    (** val div : Target_ocaml_int.t -> Target_ocaml_int.t -> Target_ocaml_int.t
        option coq_M **)

    let div = checked_div Target_ocaml_int.div

    (** val unsigned_div : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t option coq_M **)

    let unsigned_div = checked_div Target_ocaml_int.unsigned_div

    (** val mod_ : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t option coq_M **)

    let mod_ = checked_div Target_ocaml_int.mod_

    (** val unsigned_mod : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t option coq_M **)

    let unsigned_mod = checked_div Target_ocaml_int.unsigned_mod

    (** val integer_bit_width : int **)

    let integer_bit_width = if Target_system.is_32_bit () then 31 else 63

    (** val shift_left : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t coq_M **)

    let shift_left t shift =
      let machine_width = Target_ocaml_int.machine_width t in
      with_shift shift
        (Target_ocaml_int.zero machine_width)
        (fun shift0 -> Target_ocaml_int.shift_left t shift0)
        integer_bit_width

    (** val shift_right : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t coq_M **)

    let shift_right t shift =
      let machine_width = Target_ocaml_int.machine_width t in
      with_shift shift
        (Target_ocaml_int.zero machine_width)
        (fun shift0 -> Target_ocaml_int.shift_right t shift0)
        integer_bit_width

    (** val shift_right_logical : Target_ocaml_int.t -> Target_ocaml_int.t ->
        Target_ocaml_int.t coq_M **)

    let shift_right_logical t shift =
      let machine_width = Target_ocaml_int.machine_width t in
      with_shift shift
        (Target_ocaml_int.zero machine_width)
        (fun shift0 -> Target_ocaml_int.shift_right_logical t shift0)
        integer_bit_width

    (** val swap_byte_endianness : Target_ocaml_int.t -> Target_ocaml_int.t
        coq_M **)

    let swap_byte_endianness =
      Target_ocaml_int.get_least_significant_16_bits_then_byte_swap

    (** val to_const : Target_ocaml_int.t -> Reg_width_const.t coq_M **)

    let to_const = Reg_width_const.naked_immediate

    (** val to_immediate : Target_ocaml_int.t -> Target_system.Machine_width.t
        -> Target_ocaml_int.t coq_M **)

    let to_immediate t _ = t

    (** val to_naked_float32 : Target_ocaml_int.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 t =
      Numeric_types.Float32_by_bit_pattern.of_int64
        (Target_ocaml_int.to_int64 t)

    (** val to_naked_float : Target_ocaml_int.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t =
      Numeric_types.Float_by_bit_pattern.create (Target_ocaml_int.to_float t)

    (** val to_naked_int8 : Target_ocaml_int.t -> Numeric_types.Int8.t coq_M **)

    let to_naked_int8 t = Numeric_types.Int8.of_int (Target_ocaml_int.to_int t)

    (** val to_naked_int16 : Target_ocaml_int.t -> Numeric_types.Int16.t coq_M **)

    let to_naked_int16 t =
      Numeric_types.Int16.of_int (Target_ocaml_int.to_int t)

    (** val to_naked_int32 : Target_ocaml_int.t -> int32 coq_M **)

    let to_naked_int32 = Target_ocaml_int.to_int32

    (** val to_naked_int64 : Target_ocaml_int.t -> int64 coq_M **)

    let to_naked_int64 = Target_ocaml_int.to_int64

    (** val to_naked_nativeint : Target_ocaml_int.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t machine_width =
      Target_ocaml_int.to_targetint machine_width t
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind =
    Flambda_kind.Standard_int_or_float.Naked_immediate

  (** val standard_int_kind : Flambda_kind.Standard_int.t **)

  let standard_int_kind = Flambda_kind.Standard_int.Naked_immediate

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Target_ocaml_int.Set.t Flambda2_types.meet_shortcut coq_M **)

  let unboxed_prover = Flambda2_types.meet_naked_immediates

  (** val this_unboxed : Target_ocaml_int.t -> Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_naked_immediate

  (** val these_unboxed : Target_ocaml_int.Set.t -> Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_naked_immediates

  (** val term_unboxed : Target_ocaml_int.t -> Flambda.Import.Named.t coq_M **)

  let term_unboxed imm =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.naked_immediate imm))
end

module For_float32s = Flambda2_simplify.Number_adjuncts.For_float32s
module For_floats = Flambda2_simplify.Number_adjuncts.For_floats
module For_int8s = Flambda2_simplify.Number_adjuncts.For_int8s
module For_int16s = Flambda2_simplify.Number_adjuncts.For_int16s
module For_int32s = Flambda2_simplify.Number_adjuncts.For_int32s
module For_int64s = Flambda2_simplify.Number_adjuncts.For_int64s
module For_nativeints = Flambda2_simplify.Number_adjuncts.For_nativeints
