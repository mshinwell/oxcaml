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

(* This file follows middle_end/flambda2/simplify/number_adjuncts.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition under
   the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries
   [tmpN] and their order) is that of GUIDE.md; the declarations, marked
   PORT-GAP(decl), of what the file takes from a module that it includes and
   decl/ does not declare, after the interfaces of those modules
   (middle_end/flambda2/numbers/target_ocaml_int.mli, numeric_types.mli,
   targetint_32_64.mli and the standard library's int32.mli and int64.mli);
   and the form of the modules, which is this:

   - Each module of the compiler's file is a Rocq [Module] of the same name,
     with the compiler's definitions in the compiler's order.
   - PORT-GAP(loose): the modules are not sealed by their module types
     ([module For_tagged_immediates : Int_number_kind = struct]): Rocq
     prints [module For_tagged_immediates = struct]. The check of the types
     compares each with the compiler's interface.
   - The module types (50-176) and the abbreviations of modules (17-25) are
     the compiler's text, verbatim.
   - An [include] of a module of the compiler, and a module made with a
     functor inside a module, cannot be said in Rocq, and the kit copies
     verbatim text to the head or the end of the file only. Here such a line
     is the realisation string of a constant of type [unit] at its place
     ([let include_Target_ocaml_int = () include Target_ocaml_int]): marked
     PORT-GAP(verbatim). A name of the included module is written with the
     name of that module ([Target_ocaml_int.xor] for [xor]).
   - Where the compiler defines a name twice in one module ([let div x y =
     ...] and later [let div = checked_div ~f:div]), the first definition
     has the name with [_0] here: marked PORT-GAP(loose).
   No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda Flambda2_types Flambda_kind Int Int32
  Int64 Number_adjuncts__local Numeric_types Reg_width_const Simple Stdlib_
  Target_ocaml_int Target_system Targetint_32_64.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* PORT-GAP(verbatim): 17-25 and 50-176, the abbreviations of modules and the
   module types of the compiler's file. (Rocq's module types cannot say
   [include Container_types.S].) *)
(*OCAML
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

(* PORT-GAP(decl): what the file takes from [Target_ocaml_int] by [include
   Target_ocaml_int] (199, 294) under its short name, and decl/ does not
   declare. *)
Parameter Target_ocaml_int_compare :
  Target_ocaml_int.t -> Target_ocaml_int.t -> M int.
Extract Inlined Constant Target_ocaml_int_compare => "Target_ocaml_int.compare".
Parameter Target_ocaml_int_unsigned_div :
  Target_ocaml_int.t -> Target_ocaml_int.t -> M Target_ocaml_int.t.
Extract Inlined Constant Target_ocaml_int_unsigned_div => "Target_ocaml_int.unsigned_div".
Parameter Target_ocaml_int_unsigned_mod :
  Target_ocaml_int.t -> Target_ocaml_int.t -> M Target_ocaml_int.t.
Extract Inlined Constant Target_ocaml_int_unsigned_mod => "Target_ocaml_int.unsigned_mod".
Parameter Target_ocaml_int_xor :
  Target_ocaml_int.t -> Target_ocaml_int.t -> M Target_ocaml_int.t.
Extract Inlined Constant Target_ocaml_int_xor => "Target_ocaml_int.xor".

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
  let! tmp1 := strictly_negative n2 in
  let! tmp2 := strictly_negative n1 in
  match (tmp2, tmp1) with
  | (true, true) => compare n1 n2
  | (true, false) => ret 1
  | (false, true) => ret im1
  | (false, false) => compare n1 n2
  end.

(* 197-290 *)
Module For_tagged_immediates.
  (* 198-276 *)
  Module Num.
    (* PORT-GAP(verbatim): 199, [include Target_ocaml_int]. *)
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
      Target_ocaml_int_xor t tmp2.

    (* Shift functions inherit correct signature from Target_ocaml_int *)

    (* 211: [<] is that of [Target_ocaml_int]. *)
    Definition strictly_negative (t : Target_ocaml_int.t) : M bool :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      Target_ocaml_int.op_lt t tmp2.

    (* 213-214 *)
    Definition compare_unsigned (t1 t2 : Target_ocaml_int.t) : M int :=
      compare_unsigned_generic t1 t2 Target_ocaml_int_compare
        strictly_negative.

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
    Definition unsigned_div := checked_div Target_ocaml_int_unsigned_div.

    (* 227 *)
    Definition mod_ := checked_div Target_ocaml_int.mod_.

    (* 229 *)
    Definition unsigned_mod := checked_div Target_ocaml_int_unsigned_mod.

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
        : M Numeric_types.Float32_by_bit_pattern.t :=
      let! tmp1 := Target_ocaml_int.to_int64 t in
      Numeric_types.Float32_by_bit_pattern.of_int64 tmp1.

    (* 263-264 *)
    Definition to_naked_float (t : Target_ocaml_int.t)
        : M Numeric_types.Float_by_bit_pattern.t :=
      let! tmp1 := Target_ocaml_int.to_float t in
      Numeric_types.Float_by_bit_pattern.create tmp1.

    (* 266 *)
    Definition to_naked_int8 (t : Target_ocaml_int.t)
        : M Numeric_types.Int8.t :=
      let! tmp1 := Target_ocaml_int.to_int t in
      Numeric_types.Int8.of_int tmp1.

    (* 268 *)
    Definition to_naked_int16 (t : Target_ocaml_int.t)
        : M Numeric_types.Int16.t :=
      let! tmp1 := Target_ocaml_int.to_int t in
      Numeric_types.Int16.of_int tmp1.

    (* 270 *)
    Definition to_naked_int32 (t : Target_ocaml_int.t)
        : M Numeric_types.Int32.t :=
      Target_ocaml_int.to_int32 t.

    (* 272 *)
    Definition to_naked_int64 (t : Target_ocaml_int.t)
        : M Numeric_types.Int64.t :=
      Target_ocaml_int.to_int64 t.

    (* 274-275 *)
    Definition to_naked_nativeint (t : Target_ocaml_int.t)
        (machine_width : Target_system.Machine_width.t)
        : M Targetint_32_64.t :=
      Target_ocaml_int.to_targetint machine_width t.
  End Num.

  (* 278 *)
  Definition standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t
    := Flambda_kind.Standard_int_or_float.Tagged_immediate.

  (* 280 *)
  Definition standard_int_kind : Flambda_kind.Standard_int.t :=
    Flambda_kind.Standard_int.Tagged_immediate.

  (* 282 *)
  Definition unboxed_prover := Flambda2_types.meet_equals_tagged_immediates.

  (* 284 *)
  Definition this_unboxed := Flambda2_types.this_tagged_immediate.

  (* 286 *)
  Definition these_unboxed := Flambda2_types.these_tagged_immediates.

  (* 288-289 *)
  Definition term_unboxed (imm : Target_ocaml_int.t)
      : M Flambda.Import_.Named.t :=
    let! tmp1 := Reg_width_const.tagged_immediate imm in
    let! tmp2 := Simple.const tmp1 in
    Flambda.Import_.Named.create_simple tmp2.
End For_tagged_immediates.

(* 292-384 *)
Module For_naked_immediates.
  (* 293-370 *)
  Module Num.
    (* PORT-GAP(verbatim): 294, [include Target_ocaml_int]. *)
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
      Target_ocaml_int_xor t tmp2.

    (* 304: [<] is that of [Target_ocaml_int]. *)
    Definition strictly_negative (t : Target_ocaml_int.t) : M bool :=
      let! tmp1 := Target_ocaml_int.machine_width t in
      let! tmp2 := Target_ocaml_int.zero tmp1 in
      Target_ocaml_int.op_lt t tmp2.

    (* 306-307 *)
    Definition compare_unsigned (t1 t2 : Target_ocaml_int.t) : M int :=
      compare_unsigned_generic t1 t2 Target_ocaml_int_compare
        strictly_negative.

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
    Definition unsigned_div := checked_div Target_ocaml_int_unsigned_div.

    (* 320 *)
    Definition mod_ := checked_div Target_ocaml_int.mod_.

    (* 322 *)
    Definition unsigned_mod := checked_div Target_ocaml_int_unsigned_mod.

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
        : M Numeric_types.Float32_by_bit_pattern.t :=
      let! tmp1 := Target_ocaml_int.to_int64 t in
      Numeric_types.Float32_by_bit_pattern.of_int64 tmp1.

    (* 357-358 *)
    Definition to_naked_float (t : Target_ocaml_int.t)
        : M Numeric_types.Float_by_bit_pattern.t :=
      let! tmp1 := Target_ocaml_int.to_float t in
      Numeric_types.Float_by_bit_pattern.create tmp1.

    (* 360 *)
    Definition to_naked_int8 (t : Target_ocaml_int.t)
        : M Numeric_types.Int8.t :=
      let! tmp1 := Target_ocaml_int.to_int t in
      Numeric_types.Int8.of_int tmp1.

    (* 362 *)
    Definition to_naked_int16 (t : Target_ocaml_int.t)
        : M Numeric_types.Int16.t :=
      let! tmp1 := Target_ocaml_int.to_int t in
      Numeric_types.Int16.of_int tmp1.

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
  Definition standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t
    := Flambda_kind.Standard_int_or_float.Naked_immediate.

  (* 374 *)
  Definition standard_int_kind : Flambda_kind.Standard_int.t :=
    Flambda_kind.Standard_int.Naked_immediate.

  (* 376 *)
  Definition unboxed_prover := Flambda2_types.meet_naked_immediates.

  (* 378 *)
  Definition this_unboxed := Flambda2_types.this_naked_immediate.

  (* 380 *)
  Definition these_unboxed := Flambda2_types.these_naked_immediates.

  (* 382-383 *)
  Definition term_unboxed (imm : Target_ocaml_int.t)
      : M Flambda.Import_.Named.t :=
    let! tmp1 := Reg_width_const.naked_immediate imm in
    let! tmp2 := Simple.const tmp1 in
    Flambda.Import_.Named.create_simple tmp2.
End For_naked_immediates.

(* The seven modules that are not ported yet. So that the extracted file has
   the whole interface (the check of the types of a module that is sealed
   with abstract types needs the whole file), each is, for now, the
   compiler's own module, named in the verbatim text at the end. *)

(* PORT-GAP(unported): 386-445, the module [For_float32s]. *)

(* PORT-GAP(unported): 447-506, the module [For_floats]. *)

(* PORT-GAP(unported): 508-632, the module [For_int8s]. *)

(* PORT-GAP(unported): 634-762, the module [For_int16s]. *)

(* PORT-GAP(unported): 764-853, the module [For_int32s]. *)

(* PORT-GAP(unported): 855-944, the module [For_int64s]. *)

(* PORT-GAP(unported): 946-1035, the module [For_nativeints]. *)

(*OCAML-END
module For_float32s = Flambda2_simplify.Number_adjuncts.For_float32s
module For_floats = Flambda2_simplify.Number_adjuncts.For_floats
module For_int8s = Flambda2_simplify.Number_adjuncts.For_int8s
module For_int16s = Flambda2_simplify.Number_adjuncts.For_int16s
module For_int32s = Flambda2_simplify.Number_adjuncts.For_int32s
module For_int64s = Flambda2_simplify.Number_adjuncts.For_int64s
module For_nativeints = Flambda2_simplify.Number_adjuncts.For_nativeints
OCAML-END*)
