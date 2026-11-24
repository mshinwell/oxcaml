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

module For_float32s = struct
  module Num = struct
    (** val include_Float32_by_bit_pattern : unit **)

    let include_Float32_by_bit_pattern = ()

    include Float32_by_bit_pattern

    (** val zero : Target_system.Machine_width.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let zero _ = Numeric_types.Float32_by_bit_pattern.zero

    (** val one : Target_system.Machine_width.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let one _ = Numeric_types.Float32_by_bit_pattern.one

    (** val minus_one : Target_system.Machine_width.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let minus_one _ = Numeric_types.Float32_by_bit_pattern.minus_one

    (** val add : Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t coq_M **)

    let add = Numeric_types.Float32_by_bit_pattern.IEEE_semantics.add

    (** val sub : Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t coq_M **)

    let sub = Numeric_types.Float32_by_bit_pattern.IEEE_semantics.sub

    (** val mul : Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t coq_M **)

    let mul = Numeric_types.Float32_by_bit_pattern.IEEE_semantics.mul

    (** val div : Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Float32_by_bit_pattern.t option coq_M **)

    let div t1 t2 =
      Some (Numeric_types.Float32_by_bit_pattern.IEEE_semantics.div t1 t2)

    (** val mod_ : Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Float32_by_bit_pattern.t option coq_M **)

    let mod_ t1 t2 =
      Some (Numeric_types.Float32_by_bit_pattern.IEEE_semantics.mod_ t1 t2)

    (** val to_const : Numeric_types.Float32_by_bit_pattern.t ->
        Reg_width_const.t coq_M **)

    let to_const = Reg_width_const.naked_float32

    (** val to_immediate : Numeric_types.Float32_by_bit_pattern.t ->
        Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let to_immediate t machine_width =
      Target_ocaml_int.of_float machine_width
        (Numeric_types.Float32_by_bit_pattern.to_float t)

    (** val to_naked_float32 : Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 t = t

    (** val to_naked_float : Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t =
      Numeric_types.Float_by_bit_pattern.create
        (Numeric_types.Float32_by_bit_pattern.to_float t)

    (** val to_naked_int8 : Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Int8.t coq_M **)

    let to_naked_int8 t =
      Numeric_types.Int8.of_float
        (Numeric_types.Float32_by_bit_pattern.to_float t)

    (** val to_naked_int16 : Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Int16.t coq_M **)

    let to_naked_int16 t =
      Numeric_types.Int16.of_float
        (Numeric_types.Float32_by_bit_pattern.to_float t)

    (** val to_naked_int32 : Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Int32.t coq_M **)

    let to_naked_int32 t =
      Numeric_types.Int32.of_float
        (Numeric_types.Float32_by_bit_pattern.to_float t)

    (** val to_naked_int64 : Numeric_types.Float32_by_bit_pattern.t ->
        Numeric_types.Int64.t coq_M **)

    let to_naked_int64 t =
      Numeric_types.Int64.of_float
        (Numeric_types.Float32_by_bit_pattern.to_float t)

    (** val to_naked_nativeint : Numeric_types.Float32_by_bit_pattern.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t machine_width =
      Targetint_32_64.of_float machine_width
        (Numeric_types.Float32_by_bit_pattern.to_float t)
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind =
    Flambda_kind.Standard_int_or_float.Naked_float32

  (** val boxable_number_kind : Flambda_kind.Boxable_number.t **)

  let boxable_number_kind = Flambda_kind.Boxable_number.Naked_float32

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Numeric_types.Float32_by_bit_pattern.Set.t Flambda2_types.meet_shortcut
      coq_M **)

  let unboxed_prover = Flambda2_types.meet_naked_float32s

  (** val this_unboxed : Numeric_types.Float32_by_bit_pattern.t ->
      Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_naked_float32

  (** val these_unboxed : Numeric_types.Float32_by_bit_pattern.Set.t ->
      Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_naked_float32s

  (** val this_boxed : Numeric_types.Float32_by_bit_pattern.t ->
      Alloc_mode.For_types.t -> Flambda2_types.t coq_M **)

  let this_boxed = Flambda2_types.this_boxed_float32

  (** val these_boxed : Numeric_types.Float32_by_bit_pattern.Set.t ->
      Alloc_mode.For_types.t -> Flambda2_types.t coq_M **)

  let these_boxed = Flambda2_types.these_boxed_float32s

  (** val box : Flambda2_types.t -> Alloc_mode.For_types.t -> Flambda2_types.t
      coq_M **)

  let box = Flambda2_types.box_float32

  (** val term_unboxed : Numeric_types.Float32_by_bit_pattern.t ->
      Flambda.Import.Named.t coq_M **)

  let term_unboxed f =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.naked_float32 f))
end

module For_floats = struct
  module Num = struct
    (** val include_Float_by_bit_pattern : unit **)

    let include_Float_by_bit_pattern = ()

    include Float_by_bit_pattern

    (** val zero : Target_system.Machine_width.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let zero _ = Numeric_types.Float_by_bit_pattern.zero

    (** val one : Target_system.Machine_width.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let one _ = Numeric_types.Float_by_bit_pattern.one

    (** val minus_one : Target_system.Machine_width.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let minus_one _ = Numeric_types.Float_by_bit_pattern.minus_one

    (** val add : Numeric_types.Float_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float_by_bit_pattern.IEEE_semantics.t coq_M **)

    let add = Numeric_types.Float_by_bit_pattern.IEEE_semantics.add

    (** val sub : Numeric_types.Float_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float_by_bit_pattern.IEEE_semantics.t coq_M **)

    let sub = Numeric_types.Float_by_bit_pattern.IEEE_semantics.sub

    (** val mul : Numeric_types.Float_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float_by_bit_pattern.IEEE_semantics.t ->
        Numeric_types.Float_by_bit_pattern.IEEE_semantics.t coq_M **)

    let mul = Numeric_types.Float_by_bit_pattern.IEEE_semantics.mul

    (** val div : Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Float_by_bit_pattern.t option coq_M **)

    let div t1 t2 =
      Some (Numeric_types.Float_by_bit_pattern.IEEE_semantics.div t1 t2)

    (** val mod_ : Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Float_by_bit_pattern.t option coq_M **)

    let mod_ t1 t2 =
      Some (Numeric_types.Float_by_bit_pattern.IEEE_semantics.mod_ t1 t2)

    (** val to_const : Numeric_types.Float_by_bit_pattern.t -> Reg_width_const.t
        coq_M **)

    let to_const = Reg_width_const.naked_float

    (** val to_immediate : Numeric_types.Float_by_bit_pattern.t ->
        Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let to_immediate t machine_width =
      Target_ocaml_int.of_float machine_width
        (Numeric_types.Float_by_bit_pattern.to_float t)

    (** val to_naked_float32 : Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 t =
      Numeric_types.Float32_by_bit_pattern.create
        (Numeric_types.Float_by_bit_pattern.to_float t)

    (** val to_naked_float : Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t = t

    (** val to_naked_int8 : Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Int8.t coq_M **)

    let to_naked_int8 t =
      Numeric_types.Int8.of_float
        (Numeric_types.Float_by_bit_pattern.to_float t)

    (** val to_naked_int16 : Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Int16.t coq_M **)

    let to_naked_int16 t =
      Numeric_types.Int16.of_float
        (Numeric_types.Float_by_bit_pattern.to_float t)

    (** val to_naked_int32 : Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Int32.t coq_M **)

    let to_naked_int32 t =
      Numeric_types.Int32.of_float
        (Numeric_types.Float_by_bit_pattern.to_float t)

    (** val to_naked_int64 : Numeric_types.Float_by_bit_pattern.t ->
        Numeric_types.Int64.t coq_M **)

    let to_naked_int64 t =
      Numeric_types.Int64.of_float
        (Numeric_types.Float_by_bit_pattern.to_float t)

    (** val to_naked_nativeint : Numeric_types.Float_by_bit_pattern.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t machine_width =
      Targetint_32_64.of_float machine_width
        (Numeric_types.Float_by_bit_pattern.to_float t)
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind =
    Flambda_kind.Standard_int_or_float.Naked_float

  (** val boxable_number_kind : Flambda_kind.Boxable_number.t **)

  let boxable_number_kind = Flambda_kind.Boxable_number.Naked_float

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Numeric_types.Float_by_bit_pattern.Set.t Flambda2_types.meet_shortcut
      coq_M **)

  let unboxed_prover = Flambda2_types.meet_naked_floats

  (** val this_unboxed : Numeric_types.Float_by_bit_pattern.t ->
      Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_naked_float

  (** val these_unboxed : Numeric_types.Float_by_bit_pattern.Set.t ->
      Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_naked_floats

  (** val this_boxed : Numeric_types.Float_by_bit_pattern.t ->
      Alloc_mode.For_types.t -> Flambda2_types.t coq_M **)

  let this_boxed = Flambda2_types.this_boxed_float

  (** val these_boxed : Numeric_types.Float_by_bit_pattern.Set.t ->
      Alloc_mode.For_types.t -> Flambda2_types.t coq_M **)

  let these_boxed = Flambda2_types.these_boxed_floats

  (** val box : Flambda2_types.t -> Alloc_mode.For_types.t -> Flambda2_types.t
      coq_M **)

  let box = Flambda2_types.box_float

  (** val term_unboxed : Numeric_types.Float_by_bit_pattern.t ->
      Flambda.Import.Named.t coq_M **)

  let term_unboxed f =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.naked_float f))
end

module For_int8s = struct
  module Num = struct
    (** val include_Int8 : unit **)

    let include_Int8 = ()

    include Int8

    (** val strictly_negative : Numeric_types.Int8.t -> bool coq_M **)

    let strictly_negative t =
      Numeric_types.Int8.compare t Numeric_types.Int8.zero < 0

    (** val compare_unsigned : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        int coq_M **)

    let compare_unsigned t1 t2 =
      compare_unsigned_generic t1 t2 Numeric_types.Int8.compare
        strictly_negative

    (** val zero : Target_system.Machine_width.t -> Numeric_types.Int8.t coq_M **)

    let zero _ = Numeric_types.Int8.zero

    (** val one : Target_system.Machine_width.t -> Numeric_types.Int8.t coq_M **)

    let one _ = Numeric_types.Int8.one

    (** val minus_one : Target_system.Machine_width.t -> Numeric_types.Int8.t
        coq_M **)

    let minus_one _ = Numeric_types.Int8.of_int (-1)

    (** val neg : Numeric_types.Int8.t -> Numeric_types.Int8.t coq_M **)

    let neg x =
      Numeric_types.Int8.of_int (Int.neg (Numeric_types.Int8.to_int x))

    (** val add : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let add x y =
      Numeric_types.Int8.of_int
        (Int.add (Numeric_types.Int8.to_int x) (Numeric_types.Int8.to_int y))

    (** val sub : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let sub x y =
      Numeric_types.Int8.of_int
        (Int.sub (Numeric_types.Int8.to_int x) (Numeric_types.Int8.to_int y))

    (** val mul : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let mul x y =
      Numeric_types.Int8.of_int
        (Int.mul (Numeric_types.Int8.to_int x) (Numeric_types.Int8.to_int y))

    (** val div_0 : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let div_0 x y =
      Numeric_types.Int8.of_int
        (Int.div (Numeric_types.Int8.to_int x) (Numeric_types.Int8.to_int y))

    (** val unsigned_div_0 : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let unsigned_div_0 x y =
      Numeric_types.Int8.of_int
        (Int.div
           (Numeric_types.Int8.unsigned_to_int x)
           (Numeric_types.Int8.unsigned_to_int y))

    (** val rem : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let rem x y =
      Numeric_types.Int8.of_int
        (Int.rem (Numeric_types.Int8.to_int x) (Numeric_types.Int8.to_int y))

    (** val unsigned_rem : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let unsigned_rem x y =
      Numeric_types.Int8.of_int
        (Int.rem
           (Numeric_types.Int8.unsigned_to_int x)
           (Numeric_types.Int8.unsigned_to_int y))

    (** val logand : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let logand x y =
      Numeric_types.Int8.of_int
        (Int.logand (Numeric_types.Int8.to_int x) (Numeric_types.Int8.to_int y))

    (** val logor : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let logor x y =
      Numeric_types.Int8.of_int
        (Int.logor (Numeric_types.Int8.to_int x) (Numeric_types.Int8.to_int y))

    (** val logxor : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let logxor x y =
      Numeric_types.Int8.of_int
        (Int.logxor (Numeric_types.Int8.to_int x) (Numeric_types.Int8.to_int y))

    (** val shift_left_0 : Numeric_types.Int8.t -> int -> Numeric_types.Int8.t
        coq_M **)

    let shift_left_0 x y =
      Numeric_types.Int8.of_int (Int.shift_left (Numeric_types.Int8.to_int x) y)

    (** val shift_right_0 : Numeric_types.Int8.t -> int -> Numeric_types.Int8.t
        coq_M **)

    let shift_right_0 x y =
      Numeric_types.Int8.of_int
        (Int.shift_right (Numeric_types.Int8.to_int x) y)

    (** val shift_right_logical_0 : Numeric_types.Int8.t -> int ->
        Numeric_types.Int8.t coq_M **)

    let shift_right_logical_0 x y =
      Numeric_types.Int8.of_int
        (Int.shift_right_logical (Numeric_types.Int8.to_int x land 0xff) y)

    (** val xor : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let xor = logxor

    (** val or_ : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let or_ = logor

    (** val and_ : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M **)

    let and_ = logand

    (** val not_ : Numeric_types.Int8.t -> Numeric_types.Int8.t coq_M **)

    let not_ x =
      Numeric_types.Int8.of_int (Int.lognot (Numeric_types.Int8.to_int x))

    (** val checked_div : (Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t coq_M) -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t -> Numeric_types.Int8.t option coq_M **)

    let checked_div f t1 t2 =
      if Numeric_types.Int8.equal t2 (Numeric_types.Int8.of_int 0)
      then None
      else Some (f t1 t2)

    (** val div : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t option coq_M **)

    let div = checked_div div_0

    (** val unsigned_div : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t option coq_M **)

    let unsigned_div = checked_div unsigned_div_0

    (** val mod_ : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t option coq_M **)

    let mod_ = checked_div rem

    (** val unsigned_mod : Numeric_types.Int8.t -> Numeric_types.Int8.t ->
        Numeric_types.Int8.t option coq_M **)

    let unsigned_mod = checked_div unsigned_rem

    (** val shift_left : Numeric_types.Int8.t -> Target_ocaml_int.t ->
        Numeric_types.Int8.t coq_M **)

    let shift_left t shift =
      with_shift shift
        (Numeric_types.Int8.of_int 0)
        (fun shift0 -> shift_left_0 t shift0)
        8

    (** val shift_right : Numeric_types.Int8.t -> Target_ocaml_int.t ->
        Numeric_types.Int8.t coq_M **)

    let shift_right t shift =
      with_shift shift Numeric_types.Int8.zero
        (fun shift0 -> shift_right_0 t shift0)
        8

    (** val shift_right_logical : Numeric_types.Int8.t -> Target_ocaml_int.t ->
        Numeric_types.Int8.t coq_M **)

    let shift_right_logical t shift =
      with_shift shift Numeric_types.Int8.zero
        (fun shift0 -> shift_right_logical_0 t shift0)
        8

    (** val to_const : Numeric_types.Int8.t -> Reg_width_const.t coq_M **)

    let to_const = Reg_width_const.naked_int8

    (** val to_immediate : Numeric_types.Int8.t -> Target_system.Machine_width.t
        -> Target_ocaml_int.t coq_M **)

    let to_immediate t machine_width =
      Target_ocaml_int.of_int machine_width (Numeric_types.Int8.to_int t)

    (** val to_naked_float32 : Numeric_types.Int8.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 t =
      Numeric_types.Float32_by_bit_pattern.of_int64
        (Numeric_types.Int64.of_int (Numeric_types.Int8.to_int t))

    (** val to_naked_float : Numeric_types.Int8.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t =
      Numeric_types.Float_by_bit_pattern.create (Numeric_types.Int8.to_float t)

    (** val to_naked_int8 : Numeric_types.Int8.t -> Numeric_types.Int8.t coq_M **)

    let to_naked_int8 t =
      Numeric_types.Int8.of_int (Numeric_types.Int8.to_int t)

    (** val to_naked_int16 : Numeric_types.Int8.t -> Numeric_types.Int16.t coq_M
        **)

    let to_naked_int16 t =
      Numeric_types.Int16.of_int (Numeric_types.Int8.to_int t)

    (** val to_naked_int32 : Numeric_types.Int8.t -> Numeric_types.Int32.t coq_M
        **)

    let to_naked_int32 t =
      Numeric_types.Int32.of_int (Numeric_types.Int8.to_int t)

    (** val to_naked_int64 : Numeric_types.Int8.t -> Numeric_types.Int64.t coq_M
        **)

    let to_naked_int64 t =
      Numeric_types.Int64.of_int (Numeric_types.Int8.to_int t)

    (** val to_naked_nativeint : Numeric_types.Int8.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t machine_width =
      Targetint_32_64.of_int machine_width (Numeric_types.Int8.to_int t)

    (** val module_Pair : unit **)

    let module_Pair = ()

    module Pair = struct
      type nonrec t = t * t

      include Container_types.Make_pair (Int8) (Int8)
    end

    (** val cross_product : Numeric_types.Int8.Set.t -> Numeric_types.Int8.Set.t
        -> Pair.Set.t coq_M **)

    let cross_product = Pair.create_from_cross_product

    (** val swap_byte_endianness : Numeric_types.Int8.t -> Numeric_types.Int8.t
        coq_M **)

    let swap_byte_endianness t = t
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind = Flambda_kind.Standard_int_or_float.Naked_int8

  (** val standard_int_kind : Flambda_kind.Standard_int.t **)

  let standard_int_kind = Flambda_kind.Standard_int.Naked_int8

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Numeric_types.Int8.Set.t Flambda2_types.meet_shortcut coq_M **)

  let unboxed_prover = Flambda2_types.meet_naked_int8s

  (** val this_unboxed : Numeric_types.Int8.t -> Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_naked_int8

  (** val these_unboxed : Numeric_types.Int8.Set.t -> Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_naked_int8s

  (** val term_unboxed : Numeric_types.Int8.t -> Flambda.Import.Named.t coq_M **)

  let term_unboxed i =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.naked_int8 i))
end

module For_int16s = struct
  module Num = struct
    (** val include_Int16 : unit **)

    let include_Int16 = ()

    include Int16

    (** val strictly_negative : Numeric_types.Int16.t -> bool coq_M **)

    let strictly_negative t =
      Numeric_types.Int16.compare t Numeric_types.Int16.zero < 0

    (** val compare_unsigned : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        int coq_M **)

    let compare_unsigned t1 t2 =
      compare_unsigned_generic t1 t2 Numeric_types.Int16.compare
        strictly_negative

    (** val zero : Target_system.Machine_width.t -> Numeric_types.Int16.t coq_M
        **)

    let zero _ = Numeric_types.Int16.zero

    (** val one : Target_system.Machine_width.t -> Numeric_types.Int16.t coq_M **)

    let one _ = Numeric_types.Int16.one

    (** val minus_one : Target_system.Machine_width.t -> Numeric_types.Int16.t
        coq_M **)

    let minus_one _ = Numeric_types.Int16.of_int (-1)

    (** val neg : Numeric_types.Int16.t -> Numeric_types.Int16.t coq_M **)

    let neg x =
      Numeric_types.Int16.of_int (Int.neg (Numeric_types.Int16.to_int x))

    (** val add : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let add x y =
      Numeric_types.Int16.of_int
        (Int.add (Numeric_types.Int16.to_int x) (Numeric_types.Int16.to_int y))

    (** val sub : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let sub x y =
      Numeric_types.Int16.of_int
        (Int.sub (Numeric_types.Int16.to_int x) (Numeric_types.Int16.to_int y))

    (** val mul : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let mul x y =
      Numeric_types.Int16.of_int
        (Int.mul (Numeric_types.Int16.to_int x) (Numeric_types.Int16.to_int y))

    (** val div_0 : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let div_0 x y =
      Numeric_types.Int16.of_int
        (Int.div (Numeric_types.Int16.to_int x) (Numeric_types.Int16.to_int y))

    (** val unsigned_div_0 : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let unsigned_div_0 x y =
      Numeric_types.Int16.of_int
        (Int.div
           (Numeric_types.Int16.unsigned_to_int x)
           (Numeric_types.Int16.unsigned_to_int y))

    (** val rem : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let rem x y =
      Numeric_types.Int16.of_int
        (Int.rem (Numeric_types.Int16.to_int x) (Numeric_types.Int16.to_int y))

    (** val unsigned_rem : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let unsigned_rem x y =
      Numeric_types.Int16.of_int
        (Int.rem
           (Numeric_types.Int16.unsigned_to_int x)
           (Numeric_types.Int16.unsigned_to_int y))

    (** val logand : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let logand x y =
      Numeric_types.Int16.of_int
        (Int.logand
           (Numeric_types.Int16.to_int x)
           (Numeric_types.Int16.to_int y))

    (** val logor : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let logor x y =
      Numeric_types.Int16.of_int
        (Int.logor
           (Numeric_types.Int16.to_int x)
           (Numeric_types.Int16.to_int y))

    (** val logxor : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let logxor x y =
      Numeric_types.Int16.of_int
        (Int.logxor
           (Numeric_types.Int16.to_int x)
           (Numeric_types.Int16.to_int y))

    (** val shift_left_0 : Numeric_types.Int16.t -> int -> Numeric_types.Int16.t
        coq_M **)

    let shift_left_0 x y =
      Numeric_types.Int16.of_int
        (Int.shift_left (Numeric_types.Int16.to_int x) y)

    (** val shift_right_0 : Numeric_types.Int16.t -> int ->
        Numeric_types.Int16.t coq_M **)

    let shift_right_0 x y =
      Numeric_types.Int16.of_int
        (Int.shift_right (Numeric_types.Int16.to_int x) y)

    (** val shift_right_logical_0 : Numeric_types.Int16.t -> int ->
        Numeric_types.Int16.t coq_M **)

    let shift_right_logical_0 x y =
      Numeric_types.Int16.of_int
        (Int.shift_right_logical (Numeric_types.Int16.to_int x land 0xffff) y)

    (** val xor : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let xor = logxor

    (** val or_ : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let or_ = logor

    (** val and_ : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let and_ = logand

    (** val not_ : Numeric_types.Int16.t -> Numeric_types.Int16.t coq_M **)

    let not_ x =
      Numeric_types.Int16.of_int (Int.lognot (Numeric_types.Int16.to_int x))

    (** val checked_div : (Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M) -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t -> Numeric_types.Int16.t option coq_M **)

    let checked_div f t1 t2 =
      if Numeric_types.Int16.equal t2 Numeric_types.Int16.zero
      then None
      else Some (f t1 t2)

    (** val div : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t option coq_M **)

    let div = checked_div div_0

    (** val unsigned_div : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t option coq_M **)

    let unsigned_div = checked_div unsigned_div_0

    (** val mod_ : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t option coq_M **)

    let mod_ = checked_div rem

    (** val unsigned_mod : Numeric_types.Int16.t -> Numeric_types.Int16.t ->
        Numeric_types.Int16.t option coq_M **)

    let unsigned_mod = checked_div unsigned_rem

    (** val shift_left : Numeric_types.Int16.t -> Target_ocaml_int.t ->
        Numeric_types.Int16.t coq_M **)

    let shift_left t shift =
      with_shift shift Numeric_types.Int16.zero
        (fun shift0 -> shift_left_0 t shift0)
        16

    (** val shift_right : Numeric_types.Int16.t -> Target_ocaml_int.t ->
        Numeric_types.Int16.t coq_M **)

    let shift_right t shift =
      with_shift shift Numeric_types.Int16.zero
        (fun shift0 -> shift_right_0 t shift0)
        16

    (** val shift_right_logical : Numeric_types.Int16.t -> Target_ocaml_int.t ->
        Numeric_types.Int16.t coq_M **)

    let shift_right_logical t shift =
      with_shift shift Numeric_types.Int16.zero
        (fun shift0 -> shift_right_logical_0 t shift0)
        16

    (** val to_const : Numeric_types.Int16.t -> Reg_width_const.t coq_M **)

    let to_const = Reg_width_const.naked_int16

    (** val to_immediate : Numeric_types.Int16.t ->
        Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let to_immediate t machine_width =
      Target_ocaml_int.of_int machine_width (Numeric_types.Int16.to_int t)

    (** val to_naked_float32 : Numeric_types.Int16.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 t =
      Numeric_types.Float32_by_bit_pattern.of_int64
        (Numeric_types.Int64.of_int (Numeric_types.Int16.to_int t))

    (** val to_naked_float : Numeric_types.Int16.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t =
      Numeric_types.Float_by_bit_pattern.create (Numeric_types.Int16.to_float t)

    (** val to_naked_int8 : Numeric_types.Int16.t -> Numeric_types.Int8.t coq_M
        **)

    let to_naked_int8 t =
      Numeric_types.Int8.of_int (Numeric_types.Int16.to_int t)

    (** val to_naked_int16 : Numeric_types.Int16.t -> Numeric_types.Int16.t
        coq_M **)

    let to_naked_int16 t =
      Numeric_types.Int16.of_int (Numeric_types.Int16.to_int t)

    (** val to_naked_int32 : Numeric_types.Int16.t -> Numeric_types.Int32.t
        coq_M **)

    let to_naked_int32 t =
      Numeric_types.Int32.of_int (Numeric_types.Int16.to_int t)

    (** val to_naked_int64 : Numeric_types.Int16.t -> Numeric_types.Int64.t
        coq_M **)

    let to_naked_int64 t =
      Numeric_types.Int64.of_int (Numeric_types.Int16.to_int t)

    (** val to_naked_nativeint : Numeric_types.Int16.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t machine_width =
      Targetint_32_64.of_int machine_width (Numeric_types.Int16.to_int t)

    (** val module_Pair : unit **)

    let module_Pair = ()

    module Pair = struct
      type nonrec t = t * t

      include Container_types.Make_pair (Int16) (Int16)
    end

    (** val cross_product : Numeric_types.Int16.Set.t ->
        Numeric_types.Int16.Set.t -> Pair.Set.t coq_M **)

    let cross_product = Pair.create_from_cross_product

    (** val swap_byte_endianness : Numeric_types.Int16.t ->
        Numeric_types.Int16.t coq_M **)

    let swap_byte_endianness t =
      let i = Numeric_types.Int16.to_int t in
      let lo = i land 0xff in
      let hi = (i lsr 8) land 0xff in
      Numeric_types.Int16.of_int (hi lor (lo lsl 8))
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind =
    Flambda_kind.Standard_int_or_float.Naked_int16

  (** val standard_int_kind : Flambda_kind.Standard_int.t **)

  let standard_int_kind = Flambda_kind.Standard_int.Naked_int16

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Numeric_types.Int16.Set.t Flambda2_types.meet_shortcut coq_M **)

  let unboxed_prover = Flambda2_types.meet_naked_int16s

  (** val this_unboxed : Numeric_types.Int16.t -> Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_naked_int16

  (** val these_unboxed : Numeric_types.Int16.Set.t -> Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_naked_int16s

  (** val term_unboxed : Numeric_types.Int16.t -> Flambda.Import.Named.t coq_M **)

  let term_unboxed i =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.naked_int16 i))
end

module For_int32s = struct
  module Num = struct
    (** val include_Int32 : unit **)

    let include_Int32 = ()

    include Int32

    (** val strictly_negative : Numeric_types.Int32.t -> bool coq_M **)

    let strictly_negative t =
      Numeric_types.Int32.compare t Numeric_types.Int32.zero < 0

    (** val compare_unsigned : Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        int coq_M **)

    let compare_unsigned t1 t2 =
      compare_unsigned_generic t1 t2 Numeric_types.Int32.compare
        strictly_negative

    (** val zero : Target_system.Machine_width.t -> Numeric_types.Int32.t coq_M
        **)

    let zero _ = Numeric_types.Int32.zero

    (** val one : Target_system.Machine_width.t -> Numeric_types.Int32.t coq_M **)

    let one _ = Numeric_types.Int32.one

    (** val minus_one : Target_system.Machine_width.t -> Numeric_types.Int32.t
        coq_M **)

    let minus_one _ = Numeric_types.Int32.minus_one

    (** val xor : Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t coq_M **)

    let xor = Numeric_types.Int32.logxor

    (** val or_ : Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t coq_M **)

    let or_ = Numeric_types.Int32.logor

    (** val and_ : Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t coq_M **)

    let and_ = Numeric_types.Int32.logand

    (** val not_ : Numeric_types.Int32.t -> Numeric_types.Int32.t coq_M **)

    let not_ = Numeric_types.Int32.lognot

    (** val checked_div : (Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t coq_M) -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t -> Numeric_types.Int32.t option coq_M **)

    let checked_div f t1 t2 =
      if Numeric_types.Int32.equal t2 (Numeric_types.Int32.of_int 0)
      then None
      else Some (f t1 t2)

    (** val div : Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t option coq_M **)

    let div = checked_div Numeric_types.Int32.div

    (** val unsigned_div : Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t option coq_M **)

    let unsigned_div = checked_div Numeric_types.Int32.unsigned_div

    (** val mod_ : Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t option coq_M **)

    let mod_ = checked_div Numeric_types.Int32.rem

    (** val unsigned_mod : Numeric_types.Int32.t -> Numeric_types.Int32.t ->
        Numeric_types.Int32.t option coq_M **)

    let unsigned_mod = checked_div Numeric_types.Int32.unsigned_rem

    (** val shift_left : Numeric_types.Int32.t -> Target_ocaml_int.t ->
        Numeric_types.Int32.t coq_M **)

    let shift_left t shift =
      with_shift shift
        (Numeric_types.Int32.of_int 0)
        (fun shift0 -> Numeric_types.Int32.shift_left t shift0)
        32

    (** val shift_right : Numeric_types.Int32.t -> Target_ocaml_int.t ->
        Numeric_types.Int32.t coq_M **)

    let shift_right t shift =
      with_shift shift
        (Numeric_types.Int32.of_int 0)
        (fun shift0 -> Numeric_types.Int32.shift_right t shift0)
        32

    (** val shift_right_logical : Numeric_types.Int32.t -> Target_ocaml_int.t ->
        Numeric_types.Int32.t coq_M **)

    let shift_right_logical t shift =
      with_shift shift
        (Numeric_types.Int32.of_int 0)
        (fun shift0 -> Numeric_types.Int32.shift_right_logical t shift0)
        32

    (** val to_const : Numeric_types.Int32.t -> Reg_width_const.t coq_M **)

    let to_const = Reg_width_const.naked_int32

    (** val to_immediate : Numeric_types.Int32.t ->
        Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let to_immediate t machine_width = Target_ocaml_int.of_int32 machine_width t

    (** val to_naked_float32 : Numeric_types.Int32.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 t =
      Numeric_types.Float32_by_bit_pattern.of_int64
        (Numeric_types.Int64.of_int32 t)

    (** val to_naked_float : Numeric_types.Int32.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t =
      Numeric_types.Float_by_bit_pattern.create (Numeric_types.Int32.to_float t)

    (** val to_naked_int8 : Numeric_types.Int32.t -> Numeric_types.Int8.t coq_M
        **)

    let to_naked_int8 t =
      Numeric_types.Int8.of_int (Numeric_types.Int32.to_int t)

    (** val to_naked_int16 : Numeric_types.Int32.t -> Numeric_types.Int16.t
        coq_M **)

    let to_naked_int16 t =
      Numeric_types.Int16.of_int (Numeric_types.Int32.to_int t)

    (** val to_naked_int32 : Numeric_types.Int32.t -> Numeric_types.Int32.t
        coq_M **)

    let to_naked_int32 t = t

    (** val to_naked_int64 : Numeric_types.Int32.t -> Numeric_types.Int64.t
        coq_M **)

    let to_naked_int64 = Numeric_types.Int64.of_int32

    (** val to_naked_nativeint : Numeric_types.Int32.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t machine_width =
      Targetint_32_64.of_int32 machine_width t
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind =
    Flambda_kind.Standard_int_or_float.Naked_int32

  (** val standard_int_kind : Flambda_kind.Standard_int.t **)

  let standard_int_kind = Flambda_kind.Standard_int.Naked_int32

  (** val boxable_number_kind : Flambda_kind.Boxable_number.t **)

  let boxable_number_kind = Flambda_kind.Boxable_number.Naked_int32

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Numeric_types.Int32.Set.t Flambda2_types.meet_shortcut coq_M **)

  let unboxed_prover = Flambda2_types.meet_naked_int32s

  (** val this_unboxed : Numeric_types.Int32.t -> Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_naked_int32

  (** val these_unboxed : Numeric_types.Int32.Set.t -> Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_naked_int32s

  (** val this_boxed : Numeric_types.Int32.t -> Alloc_mode.For_types.t ->
      Flambda2_types.t coq_M **)

  let this_boxed = Flambda2_types.this_boxed_int32

  (** val these_boxed : Numeric_types.Int32.Set.t -> Alloc_mode.For_types.t ->
      Flambda2_types.t coq_M **)

  let these_boxed = Flambda2_types.these_boxed_int32s

  (** val box : Flambda2_types.t -> Alloc_mode.For_types.t -> Flambda2_types.t
      coq_M **)

  let box = Flambda2_types.box_int32

  (** val term_unboxed : Numeric_types.Int32.t -> Flambda.Import.Named.t coq_M **)

  let term_unboxed i =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.naked_int32 i))
end

module For_int64s = struct
  module Num = struct
    (** val include_Int64 : unit **)

    let include_Int64 = ()

    include Int64

    (** val strictly_negative : Numeric_types.Int64.t -> bool coq_M **)

    let strictly_negative t =
      Numeric_types.Int64.compare t Numeric_types.Int64.zero < 0

    (** val compare_unsigned : Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        int coq_M **)

    let compare_unsigned t1 t2 =
      compare_unsigned_generic t1 t2 Numeric_types.Int64.compare
        strictly_negative

    (** val zero : Target_system.Machine_width.t -> Numeric_types.Int64.t coq_M
        **)

    let zero _ = Numeric_types.Int64.zero

    (** val one : Target_system.Machine_width.t -> Numeric_types.Int64.t coq_M **)

    let one _ = Numeric_types.Int64.one

    (** val minus_one : Target_system.Machine_width.t -> Numeric_types.Int64.t
        coq_M **)

    let minus_one _ = Numeric_types.Int64.minus_one

    (** val xor : Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t coq_M **)

    let xor = Numeric_types.Int64.logxor

    (** val or_ : Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t coq_M **)

    let or_ = Numeric_types.Int64.logor

    (** val and_ : Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t coq_M **)

    let and_ = Numeric_types.Int64.logand

    (** val not_ : Numeric_types.Int64.t -> Numeric_types.Int64.t coq_M **)

    let not_ = Numeric_types.Int64.lognot

    (** val checked_div : (Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t coq_M) -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t -> Numeric_types.Int64.t option coq_M **)

    let checked_div f t1 t2 =
      if Numeric_types.Int64.equal t2 Numeric_types.Int64.zero
      then None
      else Some (f t1 t2)

    (** val div : Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t option coq_M **)

    let div = checked_div Numeric_types.Int64.div

    (** val unsigned_div : Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t option coq_M **)

    let unsigned_div = checked_div Numeric_types.Int64.unsigned_div

    (** val mod_ : Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t option coq_M **)

    let mod_ = checked_div Numeric_types.Int64.rem

    (** val unsigned_mod : Numeric_types.Int64.t -> Numeric_types.Int64.t ->
        Numeric_types.Int64.t option coq_M **)

    let unsigned_mod = checked_div Numeric_types.Int64.unsigned_rem

    (** val shift_left : Numeric_types.Int64.t -> Target_ocaml_int.t ->
        Numeric_types.Int64.t coq_M **)

    let shift_left t shift =
      with_shift shift Numeric_types.Int64.zero
        (fun shift0 -> Numeric_types.Int64.shift_left t shift0)
        64

    (** val shift_right : Numeric_types.Int64.t -> Target_ocaml_int.t ->
        Numeric_types.Int64.t coq_M **)

    let shift_right t shift =
      with_shift shift Numeric_types.Int64.zero
        (fun shift0 -> Numeric_types.Int64.shift_right t shift0)
        64

    (** val shift_right_logical : Numeric_types.Int64.t -> Target_ocaml_int.t ->
        Numeric_types.Int64.t coq_M **)

    let shift_right_logical t shift =
      with_shift shift Numeric_types.Int64.zero
        (fun shift0 -> Numeric_types.Int64.shift_right_logical t shift0)
        64

    (** val to_const : Numeric_types.Int64.t -> Reg_width_const.t coq_M **)

    let to_const = Reg_width_const.naked_int64

    (** val to_immediate : Numeric_types.Int64.t ->
        Target_system.Machine_width.t -> Target_ocaml_int.t coq_M **)

    let to_immediate t machine_width = Target_ocaml_int.of_int64 machine_width t

    (** val to_naked_float32 : Numeric_types.Int64.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 = Numeric_types.Float32_by_bit_pattern.of_int64

    (** val to_naked_float : Numeric_types.Int64.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t =
      Numeric_types.Float_by_bit_pattern.create (Numeric_types.Int64.to_float t)

    (** val to_naked_int8 : Numeric_types.Int64.t -> Numeric_types.Int8.t coq_M
        **)

    let to_naked_int8 t =
      Numeric_types.Int8.of_int (Numeric_types.Int64.to_int t)

    (** val to_naked_int16 : Numeric_types.Int64.t -> Numeric_types.Int16.t
        coq_M **)

    let to_naked_int16 t =
      Numeric_types.Int16.of_int (Numeric_types.Int64.to_int t)

    (** val to_naked_int32 : Numeric_types.Int64.t -> Numeric_types.Int32.t
        coq_M **)

    let to_naked_int32 = Numeric_types.Int64.to_int32

    (** val to_naked_int64 : Numeric_types.Int64.t -> Numeric_types.Int64.t
        coq_M **)

    let to_naked_int64 t = t

    (** val to_naked_nativeint : Numeric_types.Int64.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t machine_width =
      Targetint_32_64.of_int64 machine_width t
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind =
    Flambda_kind.Standard_int_or_float.Naked_int64

  (** val standard_int_kind : Flambda_kind.Standard_int.t **)

  let standard_int_kind = Flambda_kind.Standard_int.Naked_int64

  (** val boxable_number_kind : Flambda_kind.Boxable_number.t **)

  let boxable_number_kind = Flambda_kind.Boxable_number.Naked_int64

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Numeric_types.Int64.Set.t Flambda2_types.meet_shortcut coq_M **)

  let unboxed_prover = Flambda2_types.meet_naked_int64s

  (** val this_unboxed : Numeric_types.Int64.t -> Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_naked_int64

  (** val these_unboxed : Numeric_types.Int64.Set.t -> Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_naked_int64s

  (** val this_boxed : Numeric_types.Int64.t -> Alloc_mode.For_types.t ->
      Flambda2_types.t coq_M **)

  let this_boxed = Flambda2_types.this_boxed_int64

  (** val these_boxed : Numeric_types.Int64.Set.t -> Alloc_mode.For_types.t ->
      Flambda2_types.t coq_M **)

  let these_boxed = Flambda2_types.these_boxed_int64s

  (** val box : Flambda2_types.t -> Alloc_mode.For_types.t -> Flambda2_types.t
      coq_M **)

  let box = Flambda2_types.box_int64

  (** val term_unboxed : Numeric_types.Int64.t -> Flambda.Import.Named.t coq_M **)

  let term_unboxed i =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.naked_int64 i))
end

module For_nativeints = struct
  module Num = struct
    (** val include_Targetint_32_64 : unit **)

    let include_Targetint_32_64 = ()

    include Targetint_32_64

    (** val strictly_negative : Targetint_32_64.t -> bool coq_M **)

    let strictly_negative t =
      let zero_val = Targetint_32_64.zero_like t in
      Targetint_32_64.compare t zero_val < 0

    (** val compare_unsigned : Targetint_32_64.t -> Targetint_32_64.t -> int
        coq_M **)

    let compare_unsigned t1 t2 =
      compare_unsigned_generic t1 t2 Targetint_32_64.compare strictly_negative

    (** val xor : Targetint_32_64.t -> Targetint_32_64.t -> Targetint_32_64.t
        coq_M **)

    let xor = Targetint_32_64.logxor

    (** val or_ : Targetint_32_64.t -> Targetint_32_64.t -> Targetint_32_64.t
        coq_M **)

    let or_ = Targetint_32_64.logor

    (** val and_ : Targetint_32_64.t -> Targetint_32_64.t -> Targetint_32_64.t
        coq_M **)

    let and_ = Targetint_32_64.logand

    (** val not_ : Targetint_32_64.t -> Targetint_32_64.t coq_M **)

    let not_ = Targetint_32_64.lognot

    (** val checked_div : (Targetint_32_64.t -> Targetint_32_64.t ->
        Targetint_32_64.t coq_M) -> Targetint_32_64.t -> Targetint_32_64.t ->
        Targetint_32_64.t option coq_M **)

    let checked_div f t1 t2 =
      if Targetint_32_64.equal t2 (Targetint_32_64.zero_like t1)
      then None
      else Some (f t1 t2)

    (** val div : Targetint_32_64.t -> Targetint_32_64.t -> Targetint_32_64.t
        option coq_M **)

    let div = checked_div Targetint_32_64.div

    (** val unsigned_div : Targetint_32_64.t -> Targetint_32_64.t ->
        Targetint_32_64.t option coq_M **)

    let unsigned_div = checked_div Targetint_32_64.unsigned_div

    (** val mod_ : Targetint_32_64.t -> Targetint_32_64.t -> Targetint_32_64.t
        option coq_M **)

    let mod_ = checked_div Targetint_32_64.rem

    (** val unsigned_mod : Targetint_32_64.t -> Targetint_32_64.t ->
        Targetint_32_64.t option coq_M **)

    let unsigned_mod = checked_div Targetint_32_64.unsigned_rem

    (** val integer_bit_width : int **)

    let integer_bit_width = if Target_system.is_32_bit () then 32 else 64

    (** val shift_left : Targetint_32_64.t -> Target_ocaml_int.t ->
        Targetint_32_64.t coq_M **)

    let shift_left t shift =
      with_shift shift
        (Targetint_32_64.zero_like t)
        (fun shift0 -> Targetint_32_64.shift_left t shift0)
        integer_bit_width

    (** val shift_right : Targetint_32_64.t -> Target_ocaml_int.t ->
        Targetint_32_64.t coq_M **)

    let shift_right t shift =
      with_shift shift
        (Targetint_32_64.zero_like t)
        (fun shift0 -> Targetint_32_64.shift_right t shift0)
        integer_bit_width

    (** val shift_right_logical : Targetint_32_64.t -> Target_ocaml_int.t ->
        Targetint_32_64.t coq_M **)

    let shift_right_logical t shift =
      with_shift shift
        (Targetint_32_64.zero_like t)
        (fun shift0 -> Targetint_32_64.shift_right_logical t shift0)
        integer_bit_width

    (** val to_const : Targetint_32_64.t -> Reg_width_const.t coq_M **)

    let to_const = Reg_width_const.naked_nativeint

    (** val to_immediate : Targetint_32_64.t -> Target_system.Machine_width.t ->
        Target_ocaml_int.t coq_M **)

    let to_immediate t machine_width =
      Target_ocaml_int.of_targetint machine_width t

    (** val to_naked_float32 : Targetint_32_64.t ->
        Numeric_types.Float32_by_bit_pattern.t coq_M **)

    let to_naked_float32 t =
      Numeric_types.Float32_by_bit_pattern.of_int64 (Targetint_32_64.to_int64 t)

    (** val to_naked_float : Targetint_32_64.t ->
        Numeric_types.Float_by_bit_pattern.t coq_M **)

    let to_naked_float t =
      Numeric_types.Float_by_bit_pattern.create (Targetint_32_64.to_float t)

    (** val to_naked_int8 : Targetint_32_64.t -> Numeric_types.Int8.t coq_M **)

    let to_naked_int8 t = Numeric_types.Int8.of_int (Targetint_32_64.to_int t)

    (** val to_naked_int16 : Targetint_32_64.t -> Numeric_types.Int16.t coq_M **)

    let to_naked_int16 t = Numeric_types.Int16.of_int (Targetint_32_64.to_int t)

    (** val to_naked_int32 : Targetint_32_64.t -> Numeric_types.Int32.t coq_M **)

    let to_naked_int32 = Targetint_32_64.to_int32

    (** val to_naked_int64 : Targetint_32_64.t -> Numeric_types.Int64.t coq_M **)

    let to_naked_int64 = Targetint_32_64.to_int64

    (** val to_naked_nativeint : Targetint_32_64.t ->
        Target_system.Machine_width.t -> Targetint_32_64.t coq_M **)

    let to_naked_nativeint t _ = t
  end

  (** val standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t **)

  let standard_int_or_float_kind =
    Flambda_kind.Standard_int_or_float.Naked_nativeint

  (** val standard_int_kind : Flambda_kind.Standard_int.t **)

  let standard_int_kind = Flambda_kind.Standard_int.Naked_nativeint

  (** val boxable_number_kind : Flambda_kind.Boxable_number.t **)

  let boxable_number_kind = Flambda_kind.Boxable_number.Naked_nativeint

  (** val unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Targetint_32_64.Set.t Flambda2_types.meet_shortcut coq_M **)

  let unboxed_prover = Flambda2_types.meet_naked_nativeints

  (** val this_unboxed : Targetint_32_64.t -> Flambda2_types.t coq_M **)

  let this_unboxed = Flambda2_types.this_naked_nativeint

  (** val these_unboxed : Targetint_32_64.Set.t -> Flambda2_types.t coq_M **)

  let these_unboxed = Flambda2_types.these_naked_nativeints

  (** val this_boxed : Targetint_32_64.t -> Alloc_mode.For_types.t ->
      Flambda2_types.t coq_M **)

  let this_boxed = Flambda2_types.this_boxed_nativeint

  (** val these_boxed : Targetint_32_64.Set.t -> Alloc_mode.For_types.t ->
      Flambda2_types.t coq_M **)

  let these_boxed = Flambda2_types.these_boxed_nativeints

  (** val box : Flambda2_types.t -> Alloc_mode.For_types.t -> Flambda2_types.t
      coq_M **)

  let box = Flambda2_types.box_nativeint

  (** val term_unboxed : Targetint_32_64.t -> Flambda.Import.Named.t coq_M **)

  let term_unboxed i =
    Flambda.Import.Named.create_simple
      (Simple.const (Reg_width_const.naked_nativeint i))
end
