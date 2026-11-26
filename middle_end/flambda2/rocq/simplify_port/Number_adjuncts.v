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

(* This file follows middle_end/flambda2/simplify/number_adjuncts.ml
   (Git blob 52f4c782af5d40a6c8cfc343a7fa9c1881d76106), definition by definition
   under the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries
   [tmpN] and their order) is that of GUIDE.md; and the form of the modules,
   which is this:

   - Each module of the compiler's file is a Rocq [Module] of the same name,
     with the compiler's definitions in the compiler's order.
   - The modules are not sealed by their module types (the mark is below).
   - The abbreviations of modules (18-25) are a Rocq library of the file's
     own (abbrev/number_adjuncts), and a name is written through one where
     the compiler's file writes it so; the compiler's own lines are in the
     OCaml head. The module types (50-176) are OCaml text, verbatim; [make
     given] compares it with the compiler's lines.
   - An [include] of a module of the compiler, and a module made with a
     functor inside a module, cannot be said in Rocq, and the kit copies
     verbatim text to the head or the end of the file only. Here such a line
     is the realisation string of a constant of type [unit] at its place
     ([let include_Target_ocaml_int = () include Target_ocaml_int]); [make
     given] compares the line with the compiler's. A name of the included
     module is written with the
     name that the [include] gives that module ([Target_ocaml_int.xor] for
     [xor], [Int8.compare] for [compare]).
   - Where the compiler defines a name twice in one module ([let div x y =
     ...] and later [let div = checked_div ~f:div]), the first definition
     has the name with [_0] here: marked PORT-GAP(loose).
   No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda Flambda2_types Flambda_kind Int
  Number_adjuncts__local Numeric_types Reg_width_const Simple Stdlib_
  Target_ocaml_int Target_system Targetint_32_64.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* PORT-GAP(loose): 197, 292, 386, 447, 508, 634, 764, 855 and 946, the
   modules are not sealed by their module types ([module
   For_tagged_immediates : Int_number_kind = struct]): Rocq prints [module
   For_tagged_immediates = struct]. The check of the types compares each
   with the compiler's interface. *)

(* 17 *)
(*OCAML
open! Flambda.Import
OCAML*)
Import Flambda.Import_.

(* 18-25 *)
From SimplifyPort.abbrev.number_adjuncts Require Import Port_abbreviations.
(*OCAML
module K = Flambda_kind
module T = Flambda2_types
module Float32_by_bit_pattern = Numeric_types.Float32_by_bit_pattern
module Float_by_bit_pattern = Numeric_types.Float_by_bit_pattern
module Int8 = Numeric_types.Int8
module Int16 = Numeric_types.Int16
module Int32 = Numeric_types.Int32
module Int64 = Numeric_types.Int64
OCAML*)

(* 38-44 *)
(* Regarding int <-> float conversions, xclerc and mshinwell established with
   reasonable certainty that the OCaml backend (at least on x86-64) emits the
   same instructions as C compilers use for compiling the runtime float
   conversion functions. This means that, even though the results of certain of
   these conversions are undefined by the C standard (e.g. when NaN is
   involved), the semantics of the Flambda 2 compile-time evaluation should
   always match that of runtime evaluation by the processor. *)

(* 50-176. The module types of the compiler's file. (Rocq's module types
   cannot say [include Container_types.S].) *)
(*OCAML
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
OCAML*)

(* The literal integers of the file. *)
Definition im1 : int := (-1).
Extract Inlined Constant im1 => "(-1)".
Definition i31 : int := 31.
Extract Inlined Constant i31 => "31".
Definition i32 : int := 32.
Extract Inlined Constant i32 => "32".
Definition i63 : int := 63.
Extract Inlined Constant i63 => "63".
Definition i64 : int := 64.
Extract Inlined Constant i64 => "64".
Definition i0xff : int := 255.
Extract Inlined Constant i0xff => "0xff".
Definition i0xffff : int := 65535.
Extract Inlined Constant i0xffff => "0xffff".

(* 178-185 *)
Definition with_shift {A : Type} (shift : Target_ocaml_int.t)
    (if_undefined : A) (f : int -> M A) (integer_bit_width : int) : M A :=
  let! tmp1 := Target_ocaml_int.to_int_option shift in
  match tmp1 with
  | None =>
    (* As per a similar case in [Simplify_binary_primitive], we are here
       assigning a semantics to an operation which has undefined semantics. *)
    ret if_undefined
  | Some shift =>
    if (shift <? 0) || (shift >=? integer_bit_width)
    then ret if_undefined
    else f shift
  end.

(* 187-195 *)
Definition compare_unsigned_generic {A : Type} (n1 n2 : A)
    (compare : A -> A -> M int) (strictly_negative : A -> M bool) : M int :=
  (* This relies on the two's complement encoding, take care! *)
  (* 191: [match strictly_negative n1, strictly_negative n2 with]: the two
     calls of the tuple, the second first, each bound by [let*]. *)
  let* n2_is_negative := strictly_negative n2 in
  let* n1_is_negative := strictly_negative n1 in
  match n1_is_negative, n2_is_negative with
  | true, true => compare n1 n2
  | true, false => ret 1
  | false, true => ret im1
  | false, false => compare n1 n2
  end.

(* 197-290 *)
Module For_tagged_immediates.
  (* 198-276 *)
  Module Num.
    (* 199. [include Target_ocaml_int]. *)
    Definition include_Target_ocaml_int : unit := tt.
    Extract Constant include_Target_ocaml_int => "() include Target_ocaml_int".

    (* 201 *)
    Definition zero (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.zero machine_width.

    (* 203 *)
    Definition one (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.one machine_width.

    (* 205 *)
    Definition minus_one (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.minus_one machine_width.

    (* 207 *)
    Definition not_ (t : Target_ocaml_int.t) : M Target_ocaml_int.t :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := minus_one tmp1 in
      Target_ocaml_int.xor t tmp2.

    (* Shift functions inherit correct signature from Target_ocaml_int *)

    (* 211. [<] is that of [Target_ocaml_int]. *)
    Definition strictly_negative (t : Target_ocaml_int.t) : M bool :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      Target_ocaml_int.op_lt t tmp2.

    (* 213-214 *)
    Definition compare_unsigned (t1 t2 : Target_ocaml_int.t) : M int :=
      compare_unsigned_generic t1 t2 Target_ocaml_int.compare strictly_negative.

    (* 216-221 *)
    Definition checked_div
        (f : Target_ocaml_int.t -> Target_ocaml_int.t -> M Target_ocaml_int.t)
        (t1 t2 : Target_ocaml_int.t) : M (option Target_ocaml_int.t) :=
      (let! tmp1 := Target_ocaml_int.machine_width t2 in
       let! tmp2 := Target_ocaml_int.machine_width t1 in
       let! tmp3 := Target_system.Machine_width.equal tmp2 tmp1 in
       assert_ tmp3) ;;
      let! tmp1 := Target_ocaml_int.machine_width t1 in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      let! tmp3 := Target_ocaml_int.equal t2 tmp2 in
      if tmp3
      then ret None
      else
        let! tmp4 := f t1 t2 in
        ret (Some tmp4).

    (* 223 *)
    Definition div := checked_div Target_ocaml_int.div.

    (* 225 *)
    Definition unsigned_div := checked_div Target_ocaml_int.unsigned_div.

    (* 227 *)
    Definition mod_ := checked_div Target_ocaml_int.mod_.

    (* 229 *)
    Definition unsigned_mod := checked_div Target_ocaml_int.unsigned_mod.

    (* Note this doesn't say 31 and 63! See the comments on the shift
       operations e.g. [lsl] in stdlib.mli. *)
    (* PORT-GAP(init): 233, a value that the compiler computes by a call
       when the module starts; its text is the compiler's. *)
    Parameter integer_bit_width : int.
    Extract Constant integer_bit_width => "if Target_system.is_32_bit () then 32 else 64".

    (* 235-239 *)
    Definition shift_left (t shift : Target_ocaml_int.t)
        : M Target_ocaml_int.t :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      with_shift shift tmp2
        (fun shift_int => Target_ocaml_int.shift_left t shift_int)
        integer_bit_width.

    (* 241-245 *)
    Definition shift_right (t shift : Target_ocaml_int.t)
        : M Target_ocaml_int.t :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      with_shift shift tmp2
        (fun shift_int => Target_ocaml_int.shift_right t shift_int)
        integer_bit_width.

    (* 247-251 *)
    Definition shift_right_logical (t shift : Target_ocaml_int.t)
        : M Target_ocaml_int.t :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      with_shift shift tmp2
        (fun shift_int => Target_ocaml_int.shift_right_logical t shift_int)
        integer_bit_width.

    (* 253-254 *)
    Definition swap_byte_endianness :=
      Target_ocaml_int.get_least_significant_16_bits_then_byte_swap.

    (* 256 *)
    Definition to_const (t : Target_ocaml_int.t) : M Reg_width_const.t :=
      Reg_width_const.tagged_immediate t.

    (* 258 *)
    Definition to_immediate (t : Target_ocaml_int.t)
        (_machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      ret t.

    (* 260-261 *)
    Definition to_naked_float32 (t : Target_ocaml_int.t)
        : M Float32_by_bit_pattern.t :=
      let! tmp1 := Target_ocaml_int.to_int64 t in
      Float32_by_bit_pattern.of_int64 tmp1.

    (* 263-264 *)
    Definition to_naked_float (t : Target_ocaml_int.t)
        : M Float_by_bit_pattern.t :=
      let! tmp1 := Target_ocaml_int.to_float t in
      Float_by_bit_pattern.create tmp1.

    (* 266 *)
    Definition to_naked_int8 (t : Target_ocaml_int.t) : M Int8.t :=
      let! tmp1 := Target_ocaml_int.to_int t in
      Int8.of_int tmp1.

    (* 268 *)
    Definition to_naked_int16 (t : Target_ocaml_int.t) : M Int16.t :=
      let! tmp1 := Target_ocaml_int.to_int t in
      Int16.of_int tmp1.

    (* 270 *)
    Definition to_naked_int32 (t : Target_ocaml_int.t) : M Int32.t :=
      Target_ocaml_int.to_int32 t.

    (* 272 *)
    Definition to_naked_int64 (t : Target_ocaml_int.t) : M Int64.t :=
      Target_ocaml_int.to_int64 t.

    (* 274-275 *)
    Definition to_naked_nativeint (t : Target_ocaml_int.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      Target_ocaml_int.to_targetint machine_width t.
  End Num.

  (* 278 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Tagged_immediate.

  (* 280 *)
  Definition standard_int_kind : K.Standard_int.t :=
    K.Standard_int.Tagged_immediate.

  (* 282 *)
  Definition unboxed_prover := T.meet_equals_tagged_immediates.

  (* 284 *)
  Definition this_unboxed := T.this_tagged_immediate.

  (* 286 *)
  Definition these_unboxed := T.these_tagged_immediates.

  (* 288-289 *)
  Definition term_unboxed (imm : Target_ocaml_int.t) : M Named.t :=
    let! tmp1 := Reg_width_const.tagged_immediate imm in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_tagged_immediates.

(* 292-384 *)
Module For_naked_immediates.
  (* 293-370 *)
  Module Num.
    (* 294. [include Target_ocaml_int]. *)
    Definition include_Target_ocaml_int : unit := tt.
    Extract Constant include_Target_ocaml_int => "() include Target_ocaml_int".

    (* 296 *)
    Definition zero (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.zero machine_width.

    (* 298 *)
    Definition one (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.one machine_width.

    (* 300 *)
    Definition minus_one (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.minus_one machine_width.

    (* 302 *)
    Definition not_ (t : Target_ocaml_int.t) : M Target_ocaml_int.t :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := minus_one tmp1 in
      Target_ocaml_int.xor t tmp2.

    (* 304. [<] is that of [Target_ocaml_int]. *)
    Definition strictly_negative (t : Target_ocaml_int.t) : M bool :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      Target_ocaml_int.op_lt t tmp2.

    (* 306-307 *)
    Definition compare_unsigned (t1 t2 : Target_ocaml_int.t) : M int :=
      compare_unsigned_generic t1 t2 Target_ocaml_int.compare strictly_negative.

    (* 309-314 *)
    Definition checked_div
        (f : Target_ocaml_int.t -> Target_ocaml_int.t -> M Target_ocaml_int.t)
        (t1 t2 : Target_ocaml_int.t) : M (option Target_ocaml_int.t) :=
      (let! tmp1 := Target_ocaml_int.machine_width t2 in
       let! tmp2 := Target_ocaml_int.machine_width t1 in
       let! tmp3 := Target_system.Machine_width.equal tmp2 tmp1 in
       assert_ tmp3) ;;
      let! tmp1 := Target_ocaml_int.machine_width t1 in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      let! tmp3 := Target_ocaml_int.equal t2 tmp2 in
      if tmp3
      then ret None
      else
        let! tmp4 := f t1 t2 in
        ret (Some tmp4).

    (* 316 *)
    Definition div := checked_div Target_ocaml_int.div.

    (* 318 *)
    Definition unsigned_div := checked_div Target_ocaml_int.unsigned_div.

    (* 320 *)
    Definition mod_ := checked_div Target_ocaml_int.mod_.

    (* 322 *)
    Definition unsigned_mod := checked_div Target_ocaml_int.unsigned_mod.

    (* PORT-GAP(init): 324, a value that the compiler computes by a call
       when the module starts; its text is the compiler's. *)
    Parameter integer_bit_width : int.
    Extract Constant integer_bit_width => "if Target_system.is_32_bit () then 31 else 63".

    (* 326-331 *)
    Definition shift_left (t shift : Target_ocaml_int.t)
        : M Target_ocaml_int.t :=
      let* machine_width := Target_ocaml_int.machine_width t in
      let! tmp1 := Target_ocaml_int.zero machine_width in
      with_shift shift tmp1
        (fun shift => Target_ocaml_int.shift_left t shift)
        integer_bit_width.

    (* 333-338 *)
    Definition shift_right (t shift : Target_ocaml_int.t)
        : M Target_ocaml_int.t :=
      let* machine_width := Target_ocaml_int.machine_width t in
      let! tmp1 := Target_ocaml_int.zero machine_width in
      with_shift shift tmp1
        (fun shift => Target_ocaml_int.shift_right t shift)
        integer_bit_width.

    (* 340-345 *)
    Definition shift_right_logical (t shift : Target_ocaml_int.t)
        : M Target_ocaml_int.t :=
      let* machine_width := Target_ocaml_int.machine_width t in
      let! tmp1 := Target_ocaml_int.zero machine_width in
      with_shift shift tmp1
        (fun shift => Target_ocaml_int.shift_right_logical t shift)
        integer_bit_width.

    (* 347-348 *)
    Definition swap_byte_endianness :=
      Target_ocaml_int.get_least_significant_16_bits_then_byte_swap.

    (* 350 *)
    Definition to_const (t : Target_ocaml_int.t) : M Reg_width_const.t :=
      Reg_width_const.naked_immediate t.

    (* 352 *)
    Definition to_immediate (t : Target_ocaml_int.t)
        (_machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      ret t.

    (* 354-355 *)
    Definition to_naked_float32 (t : Target_ocaml_int.t)
        : M Float32_by_bit_pattern.t :=
      let! tmp1 := Target_ocaml_int.to_int64 t in
      Float32_by_bit_pattern.of_int64 tmp1.

    (* 357-358 *)
    Definition to_naked_float (t : Target_ocaml_int.t)
        : M Float_by_bit_pattern.t :=
      let! tmp1 := Target_ocaml_int.to_float t in
      Float_by_bit_pattern.create tmp1.

    (* 360 *)
    Definition to_naked_int8 (t : Target_ocaml_int.t) : M Int8.t :=
      let! tmp1 := Target_ocaml_int.to_int t in
      Int8.of_int tmp1.

    (* 362 *)
    Definition to_naked_int16 (t : Target_ocaml_int.t) : M Int16.t :=
      let! tmp1 := Target_ocaml_int.to_int t in
      Int16.of_int tmp1.

    (* 364 *)
    Definition to_naked_int32 := Target_ocaml_int.to_int32.

    (* 366 *)
    Definition to_naked_int64 := Target_ocaml_int.to_int64.

    (* 368-369 *)
    Definition to_naked_nativeint (t : Target_ocaml_int.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      Target_ocaml_int.to_targetint machine_width t.
  End Num.

  (* 372 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Naked_immediate.

  (* 374 *)
  Definition standard_int_kind : K.Standard_int.t :=
    K.Standard_int.Naked_immediate.

  (* 376 *)
  Definition unboxed_prover := T.meet_naked_immediates.

  (* 378 *)
  Definition this_unboxed := T.this_naked_immediate.

  (* 380 *)
  Definition these_unboxed := T.these_naked_immediates.

  (* 382-383 *)
  Definition term_unboxed (imm : Target_ocaml_int.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_immediate imm in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_naked_immediates.

(* 386-445 *)
Module For_float32s.
  (* 387-425 *)
  Module Num.
    (* 388. [include Float32_by_bit_pattern]. *)
    Definition include_Float32_by_bit_pattern : unit := tt.
    Extract Constant include_Float32_by_bit_pattern => "() include Float32_by_bit_pattern".

    (* 390 *)
    Definition zero (_machine_width : Target_system.Machine_width.t)
        : M Float32_by_bit_pattern.t :=
      ret Float32_by_bit_pattern.zero.

    (* 392 *)
    Definition one (_machine_width : Target_system.Machine_width.t)
        : M Float32_by_bit_pattern.t :=
      ret Float32_by_bit_pattern.one.

    (* 394 *)
    Definition minus_one (_machine_width : Target_system.Machine_width.t)
        : M Float32_by_bit_pattern.t :=
      ret Float32_by_bit_pattern.minus_one.

    (* 396 *)
    Definition add := Float32_by_bit_pattern.IEEE_semantics.add.

    (* 398 *)
    Definition sub := Float32_by_bit_pattern.IEEE_semantics.sub.

    (* 400 *)
    Definition mul := Float32_by_bit_pattern.IEEE_semantics.mul.

    (* 402 *)
    Definition div (t1 t2 : Float32_by_bit_pattern.t)
        : M (option Float32_by_bit_pattern.t) :=
      let! tmp1 := Float32_by_bit_pattern.IEEE_semantics.div t1 t2 in
      ret (Some tmp1).

    (* 404 *)
    Definition mod_ (t1 t2 : Float32_by_bit_pattern.t)
        : M (option Float32_by_bit_pattern.t) :=
      let! tmp1 := Float32_by_bit_pattern.IEEE_semantics.mod_ t1 t2 in
      ret (Some tmp1).

    (* 406 *)
    Definition to_const (t : Float32_by_bit_pattern.t) : M Reg_width_const.t :=
      Reg_width_const.naked_float32 t.

    (* 408-409 *)
    Definition to_immediate (t : Float32_by_bit_pattern.t)
        (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      let! tmp1 := Float32_by_bit_pattern.to_float t in
      Target_ocaml_int.of_float machine_width tmp1.

    (* 411 *)
    Definition to_naked_float32 (t : Float32_by_bit_pattern.t)
        : M Float32_by_bit_pattern.t :=
      ret t.

    (* 413 *)
    Definition to_naked_float (t : Float32_by_bit_pattern.t)
        : M Float_by_bit_pattern.t :=
      let! tmp1 := Float32_by_bit_pattern.to_float t in
      Float_by_bit_pattern.create tmp1.

    (* 415 *)
    Definition to_naked_int8 (t : Float32_by_bit_pattern.t) : M Int8.t :=
      let! tmp1 := Float32_by_bit_pattern.to_float t in
      Int8.of_float tmp1.

    (* 417 *)
    Definition to_naked_int16 (t : Float32_by_bit_pattern.t) : M Int16.t :=
      let! tmp1 := Float32_by_bit_pattern.to_float t in
      Int16.of_float tmp1.

    (* 419 *)
    Definition to_naked_int32 (t : Float32_by_bit_pattern.t) : M Int32.t :=
      let! tmp1 := Float32_by_bit_pattern.to_float t in
      Int32.of_float tmp1.

    (* 421 *)
    Definition to_naked_int64 (t : Float32_by_bit_pattern.t) : M Int64.t :=
      let! tmp1 := Float32_by_bit_pattern.to_float t in
      Int64.of_float tmp1.

    (* 423-424 *)
    Definition to_naked_nativeint (t : Float32_by_bit_pattern.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      let! tmp1 := Float32_by_bit_pattern.to_float t in
      Targetint_32_64.of_float machine_width tmp1.
  End Num.

  (* 427 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Naked_float32.

  (* 429 *)
  Definition boxable_number_kind := K.Boxable_number.Naked_float32.

  (* 431 *)
  Definition unboxed_prover := T.meet_naked_float32s.

  (* 433 *)
  Definition this_unboxed := T.this_naked_float32.

  (* 435 *)
  Definition these_unboxed := T.these_naked_float32s.

  (* 437 *)
  Definition this_boxed := T.this_boxed_float32.

  (* 439 *)
  Definition these_boxed := T.these_boxed_float32s.

  (* 441 *)
  Definition box := T.box_float32.

  (* 443-444 *)
  Definition term_unboxed (f : Float32_by_bit_pattern.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_float32 f in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_float32s.

(* 447-506 *)
Module For_floats.
  (* 448-486 *)
  Module Num.
    (* 449. [include Float_by_bit_pattern]. *)
    Definition include_Float_by_bit_pattern : unit := tt.
    Extract Constant include_Float_by_bit_pattern => "() include Float_by_bit_pattern".

    (* 451 *)
    Definition zero (_machine_width : Target_system.Machine_width.t)
        : M Float_by_bit_pattern.t :=
      ret Float_by_bit_pattern.zero.

    (* 453 *)
    Definition one (_machine_width : Target_system.Machine_width.t)
        : M Float_by_bit_pattern.t :=
      ret Float_by_bit_pattern.one.

    (* 455 *)
    Definition minus_one (_machine_width : Target_system.Machine_width.t)
        : M Float_by_bit_pattern.t :=
      ret Float_by_bit_pattern.minus_one.

    (* 457 *)
    Definition add := Float_by_bit_pattern.IEEE_semantics.add.

    (* 459 *)
    Definition sub := Float_by_bit_pattern.IEEE_semantics.sub.

    (* 461 *)
    Definition mul := Float_by_bit_pattern.IEEE_semantics.mul.

    (* 463 *)
    Definition div (t1 t2 : Float_by_bit_pattern.t)
        : M (option Float_by_bit_pattern.t) :=
      let! tmp1 := Float_by_bit_pattern.IEEE_semantics.div t1 t2 in
      ret (Some tmp1).

    (* 465 *)
    Definition mod_ (t1 t2 : Float_by_bit_pattern.t)
        : M (option Float_by_bit_pattern.t) :=
      let! tmp1 := Float_by_bit_pattern.IEEE_semantics.mod_ t1 t2 in
      ret (Some tmp1).

    (* 467 *)
    Definition to_const (t : Float_by_bit_pattern.t) : M Reg_width_const.t :=
      Reg_width_const.naked_float t.

    (* 469-470. [(Target_ocaml_int.of_float machine_width) (to_float t)] *)
    Definition to_immediate (t : Float_by_bit_pattern.t)
        (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      let! tmp1 := Float_by_bit_pattern.to_float t in
      Target_ocaml_int.of_float machine_width tmp1.

    (* 472 *)
    Definition to_naked_float32 (t : Float_by_bit_pattern.t)
        : M Float32_by_bit_pattern.t :=
      let! tmp1 := Float_by_bit_pattern.to_float t in
      Float32_by_bit_pattern.create tmp1.

    (* 474 *)
    Definition to_naked_float (t : Float_by_bit_pattern.t)
        : M Float_by_bit_pattern.t :=
      ret t.

    (* 476 *)
    Definition to_naked_int8 (t : Float_by_bit_pattern.t) : M Int8.t :=
      let! tmp1 := Float_by_bit_pattern.to_float t in
      Int8.of_float tmp1.

    (* 478 *)
    Definition to_naked_int16 (t : Float_by_bit_pattern.t) : M Int16.t :=
      let! tmp1 := Float_by_bit_pattern.to_float t in
      Int16.of_float tmp1.

    (* 480 *)
    Definition to_naked_int32 (t : Float_by_bit_pattern.t) : M Int32.t :=
      let! tmp1 := Float_by_bit_pattern.to_float t in
      Int32.of_float tmp1.

    (* 482 *)
    Definition to_naked_int64 (t : Float_by_bit_pattern.t) : M Int64.t :=
      let! tmp1 := Float_by_bit_pattern.to_float t in
      Int64.of_float tmp1.

    (* 484-485 *)
    Definition to_naked_nativeint (t : Float_by_bit_pattern.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      let! tmp1 := Float_by_bit_pattern.to_float t in
      Targetint_32_64.of_float machine_width tmp1.
  End Num.

  (* 488 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Naked_float.

  (* 490 *)
  Definition boxable_number_kind := K.Boxable_number.Naked_float.

  (* 492 *)
  Definition unboxed_prover := T.meet_naked_floats.

  (* 494 *)
  Definition this_unboxed := T.this_naked_float.

  (* 496 *)
  Definition these_unboxed := T.these_naked_floats.

  (* 498 *)
  Definition this_boxed := T.this_boxed_float.

  (* 500 *)
  Definition these_boxed := T.these_boxed_floats.

  (* 502 *)
  Definition box := T.box_float.

  (* 504-505 *)
  Definition term_unboxed (f : Float_by_bit_pattern.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_float f in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_floats.

(* 508-632 *)
Module For_int8s.
  (* 509-618 *)
  Module Num.
    (* 510. [include Int8]. *)
    Definition include_Int8 : unit := tt.
    Extract Constant include_Int8 => "() include Int8".

    (* 512 *)
    Definition strictly_negative (t : Int8.t) : M bool :=
      let! tmp1 := Int8.compare t Int8.zero in
      ret (tmp1 <? 0).

    (* 514-515 *)
    Definition compare_unsigned (t1 t2 : Int8.t) : M int :=
      compare_unsigned_generic t1 t2 Int8.compare strictly_negative.

    (* 517 *)
    Definition zero (_machine_width : Target_system.Machine_width.t)
        : M Int8.t :=
      ret Int8.zero.

    (* 519 *)
    Definition one (_machine_width : Target_system.Machine_width.t)
        : M Int8.t :=
      ret Int8.one.

    (* 521 *)
    Definition minus_one (_machine_width : Target_system.Machine_width.t)
        : M Int8.t :=
      Int8.of_int im1.

    (* 523 *)
    Definition neg (x : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int x in
      let! tmp2 := Int.neg tmp1 in
      Int8.of_int tmp2.

    (* 525 *)
    Definition add (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int y in
      let! tmp2 := Int8.to_int x in
      let! tmp3 := Int.add tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 527 *)
    Definition sub (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int y in
      let! tmp2 := Int8.to_int x in
      let! tmp3 := Int.sub tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 529 *)
    Definition mul (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int y in
      let! tmp2 := Int8.to_int x in
      let! tmp3 := Int.mul tmp2 tmp1 in
      Int8.of_int tmp3.

    (* PORT-GAP(loose): 531, 533-534, 547, 549 and 551-552, the compiler defines [div],
       [unsigned_div], [shift_left], [shift_right] and [shift_right_logical]
       twice in this module (the second time at 565, 567, 573-576, 578-581 and 583-586);
       the first definition of each has the name with [_0] here. *)
    (* 531 *)
    Definition div_0 (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int y in
      let! tmp2 := Int8.to_int x in
      let! tmp3 := Int.div tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 533-534 *)
    Definition unsigned_div_0 (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.unsigned_to_int y in
      let! tmp2 := Int8.unsigned_to_int x in
      let! tmp3 := Int.div tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 536 *)
    Definition rem (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int y in
      let! tmp2 := Int8.to_int x in
      let! tmp3 := Int.rem tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 538-539 *)
    Definition unsigned_rem (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.unsigned_to_int y in
      let! tmp2 := Int8.unsigned_to_int x in
      let! tmp3 := Int.rem tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 541 *)
    Definition logand (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int y in
      let! tmp2 := Int8.to_int x in
      let! tmp3 := Int.logand tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 543 *)
    Definition logor (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int y in
      let! tmp2 := Int8.to_int x in
      let! tmp3 := Int.logor tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 545 *)
    Definition logxor (x y : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int y in
      let! tmp2 := Int8.to_int x in
      let! tmp3 := Int.logxor tmp2 tmp1 in
      Int8.of_int tmp3.

    (* 547 *)
    Definition shift_left_0 (x : Int8.t) (y : int) : M Int8.t :=
      let! tmp1 := Int8.to_int x in
      let! tmp2 := Int.shift_left tmp1 y in
      Int8.of_int tmp2.

    (* 549 *)
    Definition shift_right_0 (x : Int8.t) (y : int) : M Int8.t :=
      let! tmp1 := Int8.to_int x in
      let! tmp2 := Int.shift_right tmp1 y in
      Int8.of_int tmp2.

    (* 551-552 *)
    Definition shift_right_logical_0 (x : Int8.t) (y : int) : M Int8.t :=
      let! tmp1 := Int8.to_int x in
      let! tmp2 := Stdlib_.land tmp1 i0xff in
      let! tmp3 := Int.shift_right_logical tmp2 y in
      Int8.of_int tmp3.

    (* 554 *)
    Definition xor := logxor.

    (* 556 *)
    Definition or_ := logor.

    (* 558 *)
    Definition and_ := logand.

    (* 560 *)
    Definition not_ (x : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int x in
      let! tmp2 := Int.lognot tmp1 in
      Int8.of_int tmp2.

    (* 562-563 *)
    Definition checked_div
        (f : Int8.t -> Int8.t -> M Int8.t)
        (t1 t2 : Int8.t) : M (option Int8.t) :=
      let! tmp1 := Int8.of_int 0 in
      let! tmp2 := Int8.equal t2 tmp1 in
      if tmp2
      then ret None
      else
        let! tmp3 := f t1 t2 in
        ret (Some tmp3).

    (* 565 *)
    Definition div := checked_div div_0.

    (* 567 *)
    Definition unsigned_div := checked_div unsigned_div_0.

    (* 569 *)
    Definition mod_ := checked_div rem.

    (* 571 *)
    Definition unsigned_mod := checked_div unsigned_rem.

    (* 573-576 *)
    Definition shift_left (t : Int8.t) (shift : Target_ocaml_int.t)
        : M Int8.t :=
      let! tmp1 := Int8.of_int 0 in
      with_shift shift tmp1
        (fun shift => shift_left_0 t shift)
        i8.

    (* 578-581 *)
    Definition shift_right (t : Int8.t) (shift : Target_ocaml_int.t)
        : M Int8.t :=
      with_shift shift Int8.zero
        (fun shift => shift_right_0 t shift)
        i8.

    (* 583-586 *)
    Definition shift_right_logical (t : Int8.t)
        (shift : Target_ocaml_int.t) : M Int8.t :=
      with_shift shift Int8.zero
        (fun shift => shift_right_logical_0 t shift)
        i8.

    (* 588 *)
    Definition to_const (t : Int8.t) : M Reg_width_const.t :=
      Reg_width_const.naked_int8 t.

    (* 590-591 *)
    Definition to_immediate (t : Int8.t)
        (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      let! tmp1 := Int8.to_int t in
      Target_ocaml_int.of_int machine_width tmp1.

    (* 593-594 *)
    Definition to_naked_float32 (t : Int8.t) : M Float32_by_bit_pattern.t :=
      let! tmp1 := Int8.to_int t in
      let! tmp2 := Int64.of_int tmp1 in
      Float32_by_bit_pattern.of_int64 tmp2.

    (* 596 *)
    Definition to_naked_float (t : Int8.t) : M Float_by_bit_pattern.t :=
      let! tmp1 := Int8.to_float t in
      Float_by_bit_pattern.create tmp1.

    (* 598 *)
    Definition to_naked_int8 (t : Int8.t) : M Int8.t :=
      let! tmp1 := Int8.to_int t in
      Int8.of_int tmp1.

    (* 600 *)
    Definition to_naked_int16 (t : Int8.t) : M Int16.t :=
      let! tmp1 := Int8.to_int t in
      Int16.of_int tmp1.

    (* 602 *)
    Definition to_naked_int32 (t : Int8.t) : M Int32.t :=
      let! tmp1 := Int8.to_int t in
      Int32.of_int tmp1.

    (* 604 *)
    Definition to_naked_int64 (t : Int8.t) : M Int64.t :=
      let! tmp1 := Int8.to_int t in
      Int64.of_int tmp1.

    (* 606-607 *)
    Definition to_naked_nativeint (t : Int8.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      let! tmp1 := Int8.to_int t in
      Targetint_32_64.of_int machine_width tmp1.

    (* 609-613. The module [Pair], which the compiler makes with a functor of
       another part of the compiler (decl/Number_adjuncts__local.v declares
       what the file uses of it). *)
    Definition module_Pair : unit := tt.
    Extract Constant module_Pair => "() module Pair = struct type nonrec t = t * t include Container_types.Make_pair (Int8) (Int8) end".

    (* 615 *)
    Definition cross_product :=
      Number_adjuncts__local.For_int8s.Num.Pair.create_from_cross_product.

    (* 617 *)
    Definition swap_byte_endianness (t : Int8.t) : M Int8.t :=
      ret t.
  End Num.

  (* 620 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Naked_int8.

  (* 622 *)
  Definition standard_int_kind : K.Standard_int.t :=
    K.Standard_int.Naked_int8.

  (* 624 *)
  Definition unboxed_prover := T.meet_naked_int8s.

  (* 626 *)
  Definition this_unboxed := T.this_naked_int8.

  (* 628 *)
  Definition these_unboxed := T.these_naked_int8s.

  (* 630-631 *)
  Definition term_unboxed (i : Int8.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_int8 i in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_int8s.

(* 634-762 *)
Module For_int16s.
  (* 635-748 *)
  Module Num.
    (* 636. [include Int16]. *)
    Definition include_Int16 : unit := tt.
    Extract Constant include_Int16 => "() include Int16".

    (* 638 *)
    Definition strictly_negative (t : Int16.t) : M bool :=
      let! tmp1 := Int16.compare t Int16.zero in
      ret (tmp1 <? 0).

    (* 640-641 *)
    Definition compare_unsigned (t1 t2 : Int16.t) : M int :=
      compare_unsigned_generic t1 t2 Int16.compare strictly_negative.

    (* 643 *)
    Definition zero (_machine_width : Target_system.Machine_width.t)
        : M Int16.t :=
      ret Int16.zero.

    (* 645 *)
    Definition one (_machine_width : Target_system.Machine_width.t)
        : M Int16.t :=
      ret Int16.one.

    (* 647 *)
    Definition minus_one (_machine_width : Target_system.Machine_width.t)
        : M Int16.t :=
      Int16.of_int im1.

    (* 649 *)
    Definition neg (x : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int x in
      let! tmp2 := Int.neg tmp1 in
      Int16.of_int tmp2.

    (* 651 *)
    Definition add (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int y in
      let! tmp2 := Int16.to_int x in
      let! tmp3 := Int.add tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 653 *)
    Definition sub (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int y in
      let! tmp2 := Int16.to_int x in
      let! tmp3 := Int.sub tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 655 *)
    Definition mul (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int y in
      let! tmp2 := Int16.to_int x in
      let! tmp3 := Int.mul tmp2 tmp1 in
      Int16.of_int tmp3.

    (* PORT-GAP(loose): 657, 659-660, 673, 675 and 677-678, the compiler defines [div],
       [unsigned_div], [shift_left], [shift_right] and [shift_right_logical]
       twice in this module (the second time at 691, 693, 699-702, 704-707 and 709-712);
       the first definition of each has the name with [_0] here. *)
    (* 657 *)
    Definition div_0 (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int y in
      let! tmp2 := Int16.to_int x in
      let! tmp3 := Int.div tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 659-660 *)
    Definition unsigned_div_0 (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.unsigned_to_int y in
      let! tmp2 := Int16.unsigned_to_int x in
      let! tmp3 := Int.div tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 662 *)
    Definition rem (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int y in
      let! tmp2 := Int16.to_int x in
      let! tmp3 := Int.rem tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 664-665 *)
    Definition unsigned_rem (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.unsigned_to_int y in
      let! tmp2 := Int16.unsigned_to_int x in
      let! tmp3 := Int.rem tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 667 *)
    Definition logand (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int y in
      let! tmp2 := Int16.to_int x in
      let! tmp3 := Int.logand tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 669 *)
    Definition logor (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int y in
      let! tmp2 := Int16.to_int x in
      let! tmp3 := Int.logor tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 671 *)
    Definition logxor (x y : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int y in
      let! tmp2 := Int16.to_int x in
      let! tmp3 := Int.logxor tmp2 tmp1 in
      Int16.of_int tmp3.

    (* 673 *)
    Definition shift_left_0 (x : Int16.t) (y : int) : M Int16.t :=
      let! tmp1 := Int16.to_int x in
      let! tmp2 := Int.shift_left tmp1 y in
      Int16.of_int tmp2.

    (* 675 *)
    Definition shift_right_0 (x : Int16.t) (y : int) : M Int16.t :=
      let! tmp1 := Int16.to_int x in
      let! tmp2 := Int.shift_right tmp1 y in
      Int16.of_int tmp2.

    (* 677-678 *)
    Definition shift_right_logical_0 (x : Int16.t) (y : int) : M Int16.t :=
      let! tmp1 := Int16.to_int x in
      let! tmp2 := Stdlib_.land tmp1 i0xffff in
      let! tmp3 := Int.shift_right_logical tmp2 y in
      Int16.of_int tmp3.

    (* 680 *)
    Definition xor := logxor.

    (* 682 *)
    Definition or_ := logor.

    (* 684 *)
    Definition and_ := logand.

    (* 686 *)
    Definition not_ (x : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int x in
      let! tmp2 := Int.lognot tmp1 in
      Int16.of_int tmp2.

    (* 688-689 *)
    Definition checked_div
        (f : Int16.t -> Int16.t -> M Int16.t)
        (t1 t2 : Int16.t) : M (option Int16.t) :=
      let! tmp2 := Int16.equal t2 Int16.zero in
      if tmp2
      then ret None
      else
        let! tmp3 := f t1 t2 in
        ret (Some tmp3).

    (* 691 *)
    Definition div := checked_div div_0.

    (* 693 *)
    Definition unsigned_div := checked_div unsigned_div_0.

    (* 695 *)
    Definition mod_ := checked_div rem.

    (* 697 *)
    Definition unsigned_mod := checked_div unsigned_rem.

    (* 699-702 *)
    Definition shift_left (t : Int16.t) (shift : Target_ocaml_int.t)
        : M Int16.t :=
      with_shift shift Int16.zero
        (fun shift => shift_left_0 t shift)
        i16.

    (* 704-707 *)
    Definition shift_right (t : Int16.t) (shift : Target_ocaml_int.t)
        : M Int16.t :=
      with_shift shift Int16.zero
        (fun shift => shift_right_0 t shift)
        i16.

    (* 709-712 *)
    Definition shift_right_logical (t : Int16.t)
        (shift : Target_ocaml_int.t) : M Int16.t :=
      with_shift shift Int16.zero
        (fun shift => shift_right_logical_0 t shift)
        i16.

    (* 714 *)
    Definition to_const (t : Int16.t) : M Reg_width_const.t :=
      Reg_width_const.naked_int16 t.

    (* 716-717 *)
    Definition to_immediate (t : Int16.t)
        (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      let! tmp1 := Int16.to_int t in
      Target_ocaml_int.of_int machine_width tmp1.

    (* 719-720 *)
    Definition to_naked_float32 (t : Int16.t) : M Float32_by_bit_pattern.t :=
      let! tmp1 := Int16.to_int t in
      let! tmp2 := Int64.of_int tmp1 in
      Float32_by_bit_pattern.of_int64 tmp2.

    (* 722 *)
    Definition to_naked_float (t : Int16.t) : M Float_by_bit_pattern.t :=
      let! tmp1 := Int16.to_float t in
      Float_by_bit_pattern.create tmp1.

    (* 724 *)
    Definition to_naked_int8 (t : Int16.t) : M Int8.t :=
      let! tmp1 := Int16.to_int t in
      Int8.of_int tmp1.

    (* 726 *)
    Definition to_naked_int16 (t : Int16.t) : M Int16.t :=
      let! tmp1 := Int16.to_int t in
      Int16.of_int tmp1.

    (* 728 *)
    Definition to_naked_int32 (t : Int16.t) : M Int32.t :=
      let! tmp1 := Int16.to_int t in
      Int32.of_int tmp1.

    (* 730 *)
    Definition to_naked_int64 (t : Int16.t) : M Int64.t :=
      let! tmp1 := Int16.to_int t in
      Int64.of_int tmp1.

    (* 732-733 *)
    Definition to_naked_nativeint (t : Int16.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      let! tmp1 := Int16.to_int t in
      Targetint_32_64.of_int machine_width tmp1.

    (* 735-739. The module [Pair], which the compiler makes with a functor of
       another part of the compiler (decl/Number_adjuncts__local.v declares
       what the file uses of it). *)
    Definition module_Pair : unit := tt.
    Extract Constant module_Pair => "() module Pair = struct type nonrec t = t * t include Container_types.Make_pair (Int16) (Int16) end".

    (* 741 *)
    Definition cross_product :=
      Number_adjuncts__local.For_int16s.Num.Pair.create_from_cross_product.

    (* 743-747 *)
    Definition swap_byte_endianness (t : Int16.t) : M Int16.t :=
      let* i := Int16.to_int t in
      let* lo := Stdlib_.land i i0xff in
      let* hi :=
        let! tmp1 := Stdlib_.lsr i i8 in
        Stdlib_.land tmp1 i0xff
      in
      let! tmp1 := Stdlib_.lsl lo i8 in
      let! tmp2 := Stdlib_.lor hi tmp1 in
      Int16.of_int tmp2.
  End Num.

  (* 750 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Naked_int16.

  (* 752 *)
  Definition standard_int_kind : K.Standard_int.t :=
    K.Standard_int.Naked_int16.

  (* 754 *)
  Definition unboxed_prover := T.meet_naked_int16s.

  (* 756 *)
  Definition this_unboxed := T.this_naked_int16.

  (* 758 *)
  Definition these_unboxed := T.these_naked_int16s.

  (* 760-761 *)
  Definition term_unboxed (i : Int16.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_int16 i in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_int16s.

(* 764-853 *)
Module For_int32s.
  (* 765-831 *)
  Module Num.
    (* 766. [include Int32]. *)
    Definition include_Int32 : unit := tt.
    Extract Constant include_Int32 => "() include Int32".

    (* 768 *)
    Definition strictly_negative (t : Int32.t) : M bool :=
      let! tmp1 := Int32.compare t Int32.zero in
      ret (tmp1 <? 0).

    (* 770-771 *)
    Definition compare_unsigned (t1 t2 : Int32.t) : M int :=
      compare_unsigned_generic t1 t2 Int32.compare strictly_negative.

    (* 773 *)
    Definition zero (_machine_width : Target_system.Machine_width.t)
        : M Int32.t :=
      ret Int32.zero.

    (* 775 *)
    Definition one (_machine_width : Target_system.Machine_width.t)
        : M Int32.t :=
      ret Int32.one.

    (* 777 *)
    Definition minus_one (_machine_width : Target_system.Machine_width.t)
        : M Int32.t :=
      ret Int32.minus_one.

    (* 779 *)
    Definition xor := Int32.logxor.

    (* 781 *)
    Definition or_ := Int32.logor.

    (* 783 *)
    Definition and_ := Int32.logand.

    (* 785 *)
    Definition not_ := Int32.lognot.

    (* 787-788 *)
    Definition checked_div
        (f : Int32.t -> Int32.t -> M Int32.t)
        (t1 t2 : Int32.t) : M (option Int32.t) :=
      let! tmp1 := Int32.of_int 0 in
      let! tmp2 := Int32.equal t2 tmp1 in
      if tmp2
      then ret None
      else
        let! tmp3 := f t1 t2 in
        ret (Some tmp3).

    (* 790 *)
    Definition div := checked_div Int32.div.

    (* 792 *)
    Definition unsigned_div := checked_div Int32.unsigned_div.

    (* 794 *)
    Definition mod_ := checked_div Int32.rem.

    (* 796 *)
    Definition unsigned_mod := checked_div Int32.unsigned_rem.

    (* 798-801 *)
    Definition shift_left (t : Int32.t) (shift : Target_ocaml_int.t)
        : M Int32.t :=
      let! tmp1 := Int32.of_int 0 in
      with_shift shift tmp1
        (fun shift => Int32.shift_left t shift)
        i32.

    (* 803-806 *)
    Definition shift_right (t : Int32.t) (shift : Target_ocaml_int.t)
        : M Int32.t :=
      let! tmp1 := Int32.of_int 0 in
      with_shift shift tmp1
        (fun shift => Int32.shift_right t shift)
        i32.

    (* 808-811 *)
    Definition shift_right_logical (t : Int32.t) (shift : Target_ocaml_int.t)
        : M Int32.t :=
      let! tmp1 := Int32.of_int 0 in
      with_shift shift tmp1
        (fun shift => Int32.shift_right_logical t shift)
        i32.

    (* 813 *)
    Definition to_const (t : Int32.t) : M Reg_width_const.t :=
      Reg_width_const.naked_int32 t.

    (* 815 *)
    Definition to_immediate (t : Int32.t)
        (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.of_int32 machine_width t.

    (* 817 *)
    Definition to_naked_float32 (t : Int32.t) : M Float32_by_bit_pattern.t :=
      let! tmp1 := Int64.of_int32 t in
      Float32_by_bit_pattern.of_int64 tmp1.

    (* 819 *)
    Definition to_naked_float (t : Int32.t) : M Float_by_bit_pattern.t :=
      let! tmp1 := Int32.to_float t in
      Float_by_bit_pattern.create tmp1.

    (* 821 *)
    Definition to_naked_int8 (t : Int32.t) : M Int8.t :=
      let! tmp1 := Int32.to_int t in
      Int8.of_int tmp1.

    (* 823 *)
    Definition to_naked_int16 (t : Int32.t) : M Int16.t :=
      let! tmp1 := Int32.to_int t in
      Int16.of_int tmp1.

    (* 825 *)
    Definition to_naked_int32 (t : Int32.t) : M Int32.t :=
      ret t.

    (* 827 *)
    Definition to_naked_int64 (t : Int32.t) : M Int64.t :=
      Int64.of_int32 t.

    (* 829-830 *)
    Definition to_naked_nativeint (t : Int32.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      Targetint_32_64.of_int32 machine_width t.
  End Num.

  (* 833 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Naked_int32.

  (* 835 *)
  Definition standard_int_kind : K.Standard_int.t :=
    K.Standard_int.Naked_int32.

  (* 837 *)
  Definition boxable_number_kind := K.Boxable_number.Naked_int32.

  (* 839 *)
  Definition unboxed_prover := T.meet_naked_int32s.

  (* 841 *)
  Definition this_unboxed := T.this_naked_int32.

  (* 843 *)
  Definition these_unboxed := T.these_naked_int32s.

  (* 845 *)
  Definition this_boxed := T.this_boxed_int32.

  (* 847 *)
  Definition these_boxed := T.these_boxed_int32s.

  (* 849 *)
  Definition box := T.box_int32.

  (* 851-852 *)
  Definition term_unboxed (i : Int32.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_int32 i in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_int32s.

(* 855-944 *)
Module For_int64s.
  (* 856-922 *)
  Module Num.
    (* 857. [include Int64]. *)
    Definition include_Int64 : unit := tt.
    Extract Constant include_Int64 => "() include Int64".

    (* 859 *)
    Definition strictly_negative (t : Int64.t) : M bool :=
      let! tmp1 := Int64.compare t Int64.zero in
      ret (tmp1 <? 0).

    (* 861-862 *)
    Definition compare_unsigned (t1 t2 : Int64.t) : M int :=
      compare_unsigned_generic t1 t2 Int64.compare strictly_negative.

    (* 864 *)
    Definition zero (_machine_width : Target_system.Machine_width.t)
        : M Int64.t :=
      ret Int64.zero.

    (* 866 *)
    Definition one (_machine_width : Target_system.Machine_width.t)
        : M Int64.t :=
      ret Int64.one.

    (* 868 *)
    Definition minus_one (_machine_width : Target_system.Machine_width.t)
        : M Int64.t :=
      ret Int64.minus_one.

    (* 870 *)
    Definition xor := Int64.logxor.

    (* 872 *)
    Definition or_ := Int64.logor.

    (* 874 *)
    Definition and_ := Int64.logand.

    (* 876 *)
    Definition not_ := Int64.lognot.

    (* 878-879 *)
    Definition checked_div
        (f : Int64.t -> Int64.t -> M Int64.t)
        (t1 t2 : Int64.t) : M (option Int64.t) :=
      let! tmp2 := Int64.equal t2 Int64.zero in
      if tmp2
      then ret None
      else
        let! tmp3 := f t1 t2 in
        ret (Some tmp3).

    (* 881 *)
    Definition div := checked_div Int64.div.

    (* 883 *)
    Definition unsigned_div := checked_div Int64.unsigned_div.

    (* 885 *)
    Definition mod_ := checked_div Int64.rem.

    (* 887 *)
    Definition unsigned_mod := checked_div Int64.unsigned_rem.

    (* 889-892 *)
    Definition shift_left (t : Int64.t) (shift : Target_ocaml_int.t)
        : M Int64.t :=
      with_shift shift Int64.zero
        (fun shift => Int64.shift_left t shift)
        i64.

    (* 894-897 *)
    Definition shift_right (t : Int64.t) (shift : Target_ocaml_int.t)
        : M Int64.t :=
      with_shift shift Int64.zero
        (fun shift => Int64.shift_right t shift)
        i64.

    (* 899-902 *)
    Definition shift_right_logical (t : Int64.t) (shift : Target_ocaml_int.t)
        : M Int64.t :=
      with_shift shift Int64.zero
        (fun shift => Int64.shift_right_logical t shift)
        i64.

    (* 904 *)
    Definition to_const (t : Int64.t) : M Reg_width_const.t :=
      Reg_width_const.naked_int64 t.

    (* 906 *)
    Definition to_immediate (t : Int64.t)
        (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.of_int64 machine_width t.

    (* 908 *)
    Definition to_naked_float32 (t : Int64.t) : M Float32_by_bit_pattern.t :=
      Float32_by_bit_pattern.of_int64 t.

    (* 910 *)
    Definition to_naked_float (t : Int64.t) : M Float_by_bit_pattern.t :=
      let! tmp1 := Int64.to_float t in
      Float_by_bit_pattern.create tmp1.

    (* 912 *)
    Definition to_naked_int8 (t : Int64.t) : M Int8.t :=
      let! tmp1 := Int64.to_int t in
      Int8.of_int tmp1.

    (* 914 *)
    Definition to_naked_int16 (t : Int64.t) : M Int16.t :=
      let! tmp1 := Int64.to_int t in
      Int16.of_int tmp1.

    (* 916 *)
    Definition to_naked_int32 (t : Int64.t) : M Int32.t :=
      Int64.to_int32 t.

    (* 918 *)
    Definition to_naked_int64 (t : Int64.t) : M Int64.t :=
      ret t.

    (* 920-921 *)
    Definition to_naked_nativeint (t : Int64.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      Targetint_32_64.of_int64 machine_width t.
  End Num.

  (* 924 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Naked_int64.

  (* 926 *)
  Definition standard_int_kind : K.Standard_int.t :=
    K.Standard_int.Naked_int64.

  (* 928 *)
  Definition boxable_number_kind := K.Boxable_number.Naked_int64.

  (* 930 *)
  Definition unboxed_prover := T.meet_naked_int64s.

  (* 932 *)
  Definition this_unboxed := T.this_naked_int64.

  (* 934 *)
  Definition these_unboxed := T.these_naked_int64s.

  (* 936 *)
  Definition this_boxed := T.this_boxed_int64.

  (* 938 *)
  Definition these_boxed := T.these_boxed_int64s.

  (* 940 *)
  Definition box := T.box_int64.

  (* 942-943 *)
  Definition term_unboxed (i : Int64.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_int64 i in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_int64s.

(* 946-1035 *)
Module For_nativeints.
  (* 947-1013 *)
  Module Num.
    (* 948. [include Targetint_32_64]. *)
    Definition include_Targetint_32_64 : unit := tt.
    Extract Constant include_Targetint_32_64 => "() include Targetint_32_64".

    (* 950-952 *)
    Definition strictly_negative (t : Targetint_32_64.t) : M bool :=
      let* zero_val := Targetint_32_64.zero_like t in
      let! tmp1 := Targetint_32_64.compare t zero_val in
      ret (tmp1 <? 0).

    (* 954-955 *)
    Definition compare_unsigned (t1 t2 : Targetint_32_64.t) : M int :=
      compare_unsigned_generic t1 t2 Targetint_32_64.compare strictly_negative.

    (* 957 *)
    Definition xor := Targetint_32_64.logxor.

    (* 959 *)
    Definition or_ := Targetint_32_64.logor.

    (* 961 *)
    Definition and_ := Targetint_32_64.logand.

    (* 963 *)
    Definition not_ := Targetint_32_64.lognot.

    (* 965-966 *)
    Definition checked_div
        (f : Targetint_32_64.t -> Targetint_32_64.t -> M Targetint_32_64.t)
        (t1 t2 : Targetint_32_64.t) : M (option Targetint_32_64.t) :=
      let! tmp1 := Targetint_32_64.zero_like t1 in
      let! tmp2 := Targetint_32_64.equal t2 tmp1 in
      if tmp2
      then ret None
      else
        let! tmp3 := f t1 t2 in
        ret (Some tmp3).

    (* 968 *)
    Definition div := checked_div Targetint_32_64.div.

    (* 970 *)
    Definition unsigned_div := checked_div Targetint_32_64.unsigned_div.

    (* 972 *)
    Definition mod_ := checked_div Targetint_32_64.rem.

    (* 974 *)
    Definition unsigned_mod := checked_div Targetint_32_64.unsigned_rem.

    (* PORT-GAP(init): 976, a value that the compiler computes by a call
       when the module starts; its text is the compiler's. *)
    Parameter integer_bit_width : int.
    Extract Constant integer_bit_width => "if Target_system.is_32_bit () then 32 else 64".

    (* 978-981 *)
    Definition shift_left (t : Targetint_32_64.t) (shift : Target_ocaml_int.t)
        : M Targetint_32_64.t :=
      let! tmp1 := Targetint_32_64.zero_like t in
      with_shift shift tmp1
        (fun shift => Targetint_32_64.shift_left t shift)
        integer_bit_width.

    (* 983-986 *)
    Definition shift_right (t : Targetint_32_64.t) (shift : Target_ocaml_int.t)
        : M Targetint_32_64.t :=
      let! tmp1 := Targetint_32_64.zero_like t in
      with_shift shift tmp1
        (fun shift => Targetint_32_64.shift_right t shift)
        integer_bit_width.

    (* 988-991 *)
    Definition shift_right_logical (t : Targetint_32_64.t) (shift : Target_ocaml_int.t)
        : M Targetint_32_64.t :=
      let! tmp1 := Targetint_32_64.zero_like t in
      with_shift shift tmp1
        (fun shift => Targetint_32_64.shift_right_logical t shift)
        integer_bit_width.

    (* 993 *)
    Definition to_const (t : Targetint_32_64.t) : M Reg_width_const.t :=
      Reg_width_const.naked_nativeint t.

    (* 995-996 *)
    Definition to_immediate (t : Targetint_32_64.t)
        (machine_width : Target_system.Machine_width.t)
        : M Target_ocaml_int.t :=
      Target_ocaml_int.of_targetint machine_width t.

    (* 998-999 *)
    Definition to_naked_float32 (t : Targetint_32_64.t)
        : M Float32_by_bit_pattern.t :=
      let! tmp1 := Targetint_32_64.to_int64 t in
      Float32_by_bit_pattern.of_int64 tmp1.

    (* 1001-1002 *)
    Definition to_naked_float (t : Targetint_32_64.t)
        : M Float_by_bit_pattern.t :=
      let! tmp1 := Targetint_32_64.to_float t in
      Float_by_bit_pattern.create tmp1.

    (* 1004 *)
    Definition to_naked_int8 (t : Targetint_32_64.t) : M Int8.t :=
      let! tmp1 := Targetint_32_64.to_int t in
      Int8.of_int tmp1.

    (* 1006 *)
    Definition to_naked_int16 (t : Targetint_32_64.t) : M Int16.t :=
      let! tmp1 := Targetint_32_64.to_int t in
      Int16.of_int tmp1.

    (* 1008 *)
    Definition to_naked_int32 (t : Targetint_32_64.t) : M Int32.t :=
      Targetint_32_64.to_int32 t.

    (* 1010 *)
    Definition to_naked_int64 (t : Targetint_32_64.t) : M Int64.t :=
      Targetint_32_64.to_int64 t.

    (* 1012 *)
    Definition to_naked_nativeint (t : Targetint_32_64.t)
        (_machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      ret t.
  End Num.

  (* 1015 *)
  Definition standard_int_or_float_kind : K.Standard_int_or_float.t
    := K.Standard_int_or_float.Naked_nativeint.

  (* 1017 *)
  Definition standard_int_kind : K.Standard_int.t :=
    K.Standard_int.Naked_nativeint.

  (* 1019 *)
  Definition boxable_number_kind := K.Boxable_number.Naked_nativeint.

  (* 1021 *)
  Definition unboxed_prover := T.meet_naked_nativeints.

  (* 1023 *)
  Definition this_unboxed := T.this_naked_nativeint.

  (* 1025 *)
  Definition these_unboxed := T.these_naked_nativeints.

  (* 1027 *)
  Definition this_boxed := T.this_boxed_nativeint.

  (* 1029 *)
  Definition these_boxed := T.these_boxed_nativeints.

  (* 1031 *)
  Definition box := T.box_nativeint.

  (* 1033-1034 *)
  Definition term_unboxed (i : Targetint_32_64.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_nativeint i in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.
End For_nativeints.
