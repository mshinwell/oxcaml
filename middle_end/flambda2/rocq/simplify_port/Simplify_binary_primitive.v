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

(* This file follows
   middle_end/flambda2/simplify/simplify_binary_primitive.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order) is that of GUIDE.md. In this form of the file the twelve
   functions at the left margin (984-1270) are ported; the functors of the
   file and their instances (18-979) are the compiler's text. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Array Bound_var Comparison_result Debuginfo
  Int_ids Mutability Or_bottom Or_unknown_or_bottom Simple Simplify_common
  Target_ocaml_int.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 18-979 *)
(* PORT-GAP(verbatim): the type [binary_arith_outcome_for_one_side_only],
   the module type [Binary_arith_like_sig], the functor [Binary_arith_like],
   the five functors of operations and the 25 instances are the compiler's
   text, without its comments that begin with a review marker, and with
   two calls (948 and 957, [result_of_comparison_with_nan op
   ~machine_width]) whose arguments are put in the order of the definition:
   the check of the types does not know labels. Of each instance of
   [Binary_arith_like] the function [simplify] is declared below, in the
   form of decl/. *)
(*OCAML
module A = Number_adjuncts

type 'a binary_arith_outcome_for_one_side_only =
  | Exactly of 'a
  | The_other_side
  | Negation_of_the_other_side
  | Bitwise_not_of_the_other_side of K.Standard_int.t
  | Float_negation_of_the_other_side of Flambda_primitive.float_bitwidth
  | Cannot_simplify
  | Invalid

module type Binary_arith_like_sig = sig
  module Lhs : Container_types.S

  module Rhs : Container_types.S

  module Pair : Container_types.S with type t = Lhs.t * Rhs.t

  module Result : Container_types.S

  val ok_to_evaluate : DE.t -> bool

  val cross_product : Lhs.Set.t -> Rhs.Set.t -> Pair.Set.t

  val arg_kind : K.Standard_int_or_float.t

  val result_kind : K.t

  val term : Result.t -> Named.t

  val prover_lhs : T.Typing_env.t -> T.t -> Lhs.Set.t T.meet_shortcut

  val prover_rhs : T.Typing_env.t -> T.t -> Rhs.Set.t T.meet_shortcut

  type op

  val unknown : machine_width:Target_system.Machine_width.t -> op -> T.t

  val these : Result.Set.t -> T.t * Simple.t option

  val op :
    machine_width:Target_system.Machine_width.t ->
    op ->
    Lhs.t ->
    Rhs.t ->
    Result.t option

  val op_lhs_unknown :
    machine_width:Target_system.Machine_width.t ->
    op ->
    rhs:Rhs.t ->
    Result.t binary_arith_outcome_for_one_side_only

  val op_rhs_unknown :
    machine_width:Target_system.Machine_width.t ->
    op ->
    lhs:Lhs.t ->
    Result.t binary_arith_outcome_for_one_side_only
end

module Binary_arith_like (N : Binary_arith_like_sig) : sig
  val simplify :
    N.op ->
    DA.t ->
    original_term:Named.t ->
    Debuginfo.t ->
    arg1:Simple.t ->
    arg1_ty:Flambda2_types.t ->
    arg2:Simple.t ->
    arg2_ty:Flambda2_types.t ->
    result_var:Bound_var.t ->
    SPR.t
end = struct
  module Possible_result = struct
    type t =
      | Simple of Simple.t
      | Prim of P.t
      | Exactly of N.Result.t

    (* This signature aims to constrain the size of the [Set] module block,
       since this is duplicated a lot via inlining in the rest of this file. *)
    module Set : sig
      type elt = t

      type t

      val empty : t

      val add : elt -> t -> t

      val is_empty : t -> bool

      val cardinal : t -> int

      val get_singleton : t -> elt option

      val elements : t -> elt list
    end = Container_types.Make_set [@inlined hint] (struct
      type nonrec t = t

      let compare t1 t2 =
        match t1, t2 with
        | Simple simple1, Simple simple2 -> Simple.compare simple1 simple2
        | Prim prim1, Prim prim2 -> P.compare prim1 prim2
        | Exactly i1, Exactly i2 -> N.Result.compare i1 i2
        | Simple _, (Prim _ | Exactly _) -> -1
        | Prim _, Simple _ -> 1
        | Prim _, Exactly _ -> -1
        | Exactly _, (Simple _ | Prim _) -> 1

      let print _ _ = Misc.fatal_error "Not implemented"
    end)
  end

  let max_num_possible_results = 10

  let simplify op dacc ~original_term dbg ~arg1 ~arg1_ty ~arg2 ~arg2_ty
      ~result_var =
    let module PR = Possible_result in
    let denv = DA.denv dacc in
    let typing_env = DE.typing_env denv in
    let proof1 = N.prover_lhs typing_env arg1_ty in
    let proof2 = N.prover_rhs typing_env arg2_ty in
    let kind = N.result_kind in
    let[@inline always] result_unknown () =
      let machine_width = DE.machine_width denv in
      let dacc =
        DA.add_variable dacc result_var (N.unknown ~machine_width op)
      in
      SPR.create original_term ~try_reify:false dacc
    in
    let[@inline always] result_invalid () =
      let dacc = DA.add_variable dacc result_var (T.bottom kind) in
      SPR.create_invalid dacc
    in
    let check_possible_results ~possible_results =
      if PR.Set.is_empty possible_results
      then result_invalid ()
      else
        let named =
          match PR.Set.get_singleton possible_results with
          | Some (Exactly i) -> N.term i
          | Some (Prim prim) -> Named.create_prim prim dbg
          | Some (Simple simple) -> Named.create_simple simple
          | None -> original_term
        in
        let ty, simple_opt =
          let is =
            List.filter_map
              (fun (possible_result : PR.t) ->
                match possible_result with
                | Exactly i -> Some i
                | Prim _ | Simple _ -> None)
              (PR.Set.elements possible_results)
          in
          if List.length is = PR.Set.cardinal possible_results
          then N.these (N.Result.Set.of_list is)
          else
            match PR.Set.get_singleton possible_results with
            | Some (Simple simple) -> T.alias_type_of kind simple, Some simple
            | Some (Exactly _) | Some (Prim _) | None ->
              let machine_width = DE.machine_width denv in
              N.unknown ~machine_width op, None
        in
        let dacc = DA.add_variable dacc result_var ty in
        match simple_opt with
        | None -> SPR.create named ~try_reify:false dacc
        | Some simple ->
          let named = Named.create_simple simple in
          SPR.create named ~try_reify:false dacc
    in
    let only_one_side_known op nums ~folder ~other_side =
      let possible_results =
        folder
          (fun i possible_results ->
            match possible_results with
            | None -> None
            | Some possible_results -> (
              match op i with
              | Exactly result ->
                Some (PR.Set.add (Exactly result) possible_results)
              | The_other_side ->
                Some (PR.Set.add (Simple other_side) possible_results)
              | Negation_of_the_other_side ->
                let standard_int_kind : K.Standard_int.t =
                  match N.arg_kind with
                  | Tagged_immediate -> Tagged_immediate
                  | Naked_immediate -> Naked_immediate
                  | Naked_int8 -> Naked_int8
                  | Naked_int16 -> Naked_int16
                  | Naked_int32 -> Naked_int32
                  | Naked_int64 -> Naked_int64
                  | Naked_nativeint -> Naked_nativeint
                  | Naked_float | Naked_float32 ->
                    Misc.fatal_error
                      "Cannot use [Negation_of_the_other_side] with floats; \
                       use the float version instead"
                in
                let machine_width = DE.machine_width denv in
                let zero =
                  Simple.const_int_of_kind ~machine_width
                    (K.Standard_int.to_kind standard_int_kind)
                    0
                in
                let prim : P.t =
                  Binary (Int_arith (standard_int_kind, Sub), zero, other_side)
                in
                Some (PR.Set.add (Prim prim) possible_results)
              | Bitwise_not_of_the_other_side kind ->
                let prim : P.t = Unary (Int_arith (kind, Not), other_side) in
                Some (PR.Set.add (Prim prim) possible_results)
              | Float_negation_of_the_other_side width ->
                let prim : P.t = Unary (Float_arith (width, Neg), other_side) in
                Some (PR.Set.add (Prim prim) possible_results)
              | Cannot_simplify -> None
              | Invalid -> Some possible_results))
          nums (Some PR.Set.empty)
      in
      match possible_results with
      | Some results -> check_possible_results ~possible_results:results
      | None -> result_unknown ()
    in
    match proof1, proof2 with
    | Known_result nums1, Known_result nums2 when N.ok_to_evaluate denv ->
      assert (not (N.Lhs.Set.is_empty nums1));
      assert (not (N.Rhs.Set.is_empty nums2));
      if
        N.Lhs.Set.cardinal nums1 > max_num_possible_results
        || N.Rhs.Set.cardinal nums2 > max_num_possible_results
      then result_unknown ()
      else
        let all_pairs = N.cross_product nums1 nums2 in
        let possible_results =
          N.Pair.Set.fold
            (fun (i1, i2) possible_results ->
              let machine_width = DE.machine_width denv in
              match N.op ~machine_width op i1 i2 with
              | None -> possible_results
              | Some result -> PR.Set.add (Exactly result) possible_results)
            all_pairs PR.Set.empty
        in
        check_possible_results ~possible_results
    | Known_result nums1, Need_meet when N.ok_to_evaluate denv ->
      assert (not (N.Lhs.Set.is_empty nums1));
      let machine_width = DE.machine_width denv in
      only_one_side_known
        (fun i -> N.op_rhs_unknown ~machine_width op ~lhs:i)
        nums1 ~folder:N.Lhs.Set.fold ~other_side:arg2
    | Need_meet, Known_result nums2 when N.ok_to_evaluate denv ->
      assert (not (N.Rhs.Set.is_empty nums2));
      let machine_width = DE.machine_width denv in
      only_one_side_known
        (fun i -> N.op_lhs_unknown ~machine_width op ~rhs:i)
        nums2 ~folder:N.Rhs.Set.fold ~other_side:arg1
    | (Known_result _ | Need_meet), (Known_result _ | Need_meet) ->
      result_unknown ()
    | Invalid, _ | _, Invalid -> result_invalid ()
end
[@@inline always]

module Int_ops_for_binary_arith (I : A.Int_number_kind) : sig
  include Binary_arith_like_sig with type op = P.binary_int_arith_op
end = struct
  module Lhs = I.Num
  module Rhs = I.Num
  module Result = I.Num

  type op = P.binary_int_arith_op

  (* There are never any restrictions on the constant propagation of integers,
     unlike for floats. *)
  let ok_to_evaluate _env = true

  let arg_kind = I.standard_int_or_float_kind

  let result_kind = K.Standard_int_or_float.to_kind arg_kind

  let prover_lhs = I.unboxed_prover

  let prover_rhs = I.unboxed_prover

  let unknown ~machine_width:_ _ =
    match arg_kind with
    | Tagged_immediate -> T.any_tagged_immediate
    | Naked_immediate -> T.any_naked_immediate
    | Naked_float32 -> T.any_naked_float32
    | Naked_float -> T.any_naked_float
    | Naked_int8 -> T.any_naked_int8
    | Naked_int16 -> T.any_naked_int16
    | Naked_int32 -> T.any_naked_int32
    | Naked_int64 -> T.any_naked_int64
    | Naked_nativeint -> T.any_naked_nativeint

  let these s =
    let ty = I.these_unboxed s in
    let simple_opt =
      match I.Num.Set.get_singleton s with
      | None -> None
      | Some i -> Some (Simple.const (I.Num.to_const i))
    in
    ty, simple_opt

  let term = I.term_unboxed

  module Pair = I.Num.Pair

  let cross_product = I.Num.cross_product

  let op ~machine_width:_ (op : P.binary_int_arith_op) n1 n2 =
    let always_some f = Some (f n1 n2) in
    match op with
    | Add -> always_some I.Num.add
    | Sub -> always_some I.Num.sub
    | Mul -> always_some I.Num.mul
    | Div Signed -> I.Num.div n1 n2
    | Mod Signed -> I.Num.mod_ n1 n2
    | Div Unsigned -> I.Num.unsigned_div n1 n2
    | Mod Unsigned -> I.Num.unsigned_mod n1 n2
    | And -> always_some I.Num.and_
    | Or -> always_some I.Num.or_
    | Xor -> always_some I.Num.xor

  type symmetric_op =
    | Add
    | Mul
    | And
    | Or
    | Xor

  module Num = I.Num

  let symmetric_op_one_side_unknown ~machine_width (op : symmetric_op)
      ~this_side : Num.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add ->
      if Num.equal this_side (Num.zero machine_width)
      then The_other_side
      else Cannot_simplify
    | Mul ->
      if Num.equal this_side (Num.zero machine_width)
      then Exactly (Num.zero machine_width)
      else if Num.equal this_side (Num.one machine_width)
      then The_other_side
      else if Num.equal this_side (Num.minus_one machine_width)
      then Negation_of_the_other_side
      else Cannot_simplify
    | And ->
      if Num.equal this_side (Num.minus_one machine_width)
      then The_other_side
      else if Num.equal this_side (Num.zero machine_width)
      then Exactly (Num.zero machine_width)
      else Cannot_simplify
    | Or ->
      if Num.equal this_side (Num.minus_one machine_width)
      then Exactly (Num.minus_one machine_width)
      else if Num.equal this_side (Num.zero machine_width)
      then The_other_side
      else Cannot_simplify
    | Xor ->
      if Num.equal this_side (Num.zero machine_width)
      then The_other_side
      else if Num.equal this_side (Num.minus_one machine_width)
      then Bitwise_not_of_the_other_side I.standard_int_kind
      else Cannot_simplify

  let op_lhs_unknown ~machine_width (op : P.binary_int_arith_op) ~rhs :
      Num.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add -> symmetric_op_one_side_unknown ~machine_width Add ~this_side:rhs
    | Mul -> symmetric_op_one_side_unknown ~machine_width Mul ~this_side:rhs
    | And -> symmetric_op_one_side_unknown ~machine_width And ~this_side:rhs
    | Or -> symmetric_op_one_side_unknown ~machine_width Or ~this_side:rhs
    | Xor -> symmetric_op_one_side_unknown ~machine_width Xor ~this_side:rhs
    | Sub ->
      if Num.equal rhs (Num.zero machine_width)
      then The_other_side
      else Cannot_simplify
    | Div signedness ->
      (* Division ("safe" division, strictly speaking, in Lambda terminology) is
         translated to a conditional on the denominator followed by an unsafe
         division (the "Div" seen here) on the way into Flambda 2. So if the
         denominator turns out to be zero here, via the typing or whatever, then
         we're in unreachable code. *)
      if Num.equal rhs (Num.zero machine_width)
      then Invalid
      else if Num.equal rhs (Num.one machine_width)
      then The_other_side
      else if
        Num.equal rhs (Num.minus_one machine_width)
        && match signedness with Signed -> true | Unsigned -> false
      then
        Negation_of_the_other_side
      else Cannot_simplify
    | Mod signedness ->
      if Num.equal rhs (Num.zero machine_width)
      then Invalid
      else if Num.equal rhs (Num.one machine_width)
      then Exactly (Num.zero machine_width)
      else if
        Num.equal rhs (Num.minus_one machine_width)
        && match signedness with Signed -> true | Unsigned -> false
      then Exactly (Num.zero machine_width)
      else Cannot_simplify

  let op_rhs_unknown ~machine_width (op : P.binary_int_arith_op) ~lhs :
      Num.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add -> symmetric_op_one_side_unknown ~machine_width Add ~this_side:lhs
    | Mul -> symmetric_op_one_side_unknown ~machine_width Mul ~this_side:lhs
    | And -> symmetric_op_one_side_unknown ~machine_width And ~this_side:lhs
    | Or -> symmetric_op_one_side_unknown ~machine_width Or ~this_side:lhs
    | Xor -> symmetric_op_one_side_unknown ~machine_width Xor ~this_side:lhs
    | Sub ->
      if Num.equal lhs (Num.zero machine_width)
      then Negation_of_the_other_side
      else Cannot_simplify
    | Div (Signed | Unsigned) | Mod (Signed | Unsigned) -> Cannot_simplify
end
[@@inline always]

module Int_ops_for_binary_arith_tagged_immediate =
  Int_ops_for_binary_arith (A.For_tagged_immediates)
module Int_ops_for_binary_arith_naked_immediate =
  Int_ops_for_binary_arith (A.For_naked_immediates)
module Int_ops_for_binary_arith_int8 = Int_ops_for_binary_arith (A.For_int8s)
module Int_ops_for_binary_arith_int16 = Int_ops_for_binary_arith (A.For_int16s)
module Int_ops_for_binary_arith_int32 = Int_ops_for_binary_arith (A.For_int32s)
module Int_ops_for_binary_arith_int64 = Int_ops_for_binary_arith (A.For_int64s)
module Int_ops_for_binary_arith_nativeint =
  Int_ops_for_binary_arith (A.For_nativeints)
module Binary_int_arith_tagged_immediate =
  Binary_arith_like (Int_ops_for_binary_arith_tagged_immediate)
module Binary_int_arith_naked_immediate =
  Binary_arith_like (Int_ops_for_binary_arith_naked_immediate)
module Binary_int_arith_int8 = Binary_arith_like (Int_ops_for_binary_arith_int8)
module Binary_int_arith_int16 =
  Binary_arith_like (Int_ops_for_binary_arith_int16)
module Binary_int_arith_int32 =
  Binary_arith_like (Int_ops_for_binary_arith_int32)
module Binary_int_arith_int64 =
  Binary_arith_like (Int_ops_for_binary_arith_int64)
module Binary_int_arith_nativeint =
  Binary_arith_like (Int_ops_for_binary_arith_nativeint)

module Int_ops_for_binary_shift (I : A.Int_number_kind) : sig
  include Binary_arith_like_sig with type op = P.int_shift_op
end = struct
  module Lhs = I.Num
  module Rhs = Target_ocaml_int
  module Result = I.Num

  type op = P.int_shift_op

  let arg_kind = I.standard_int_or_float_kind

  let result_kind = K.Standard_int_or_float.to_kind arg_kind

  let ok_to_evaluate _env = true

  let prover_lhs = I.unboxed_prover

  let prover_rhs = T.meet_naked_immediates

  let unknown ~machine_width:_ _ =
    match arg_kind with
    | Tagged_immediate -> T.any_tagged_immediate
    | Naked_immediate -> T.any_naked_immediate
    | Naked_float32 -> T.any_naked_float32
    | Naked_float -> T.any_naked_float
    | Naked_int8 -> T.any_naked_int8
    | Naked_int16 -> T.any_naked_int16
    | Naked_int32 -> T.any_naked_int32
    | Naked_int64 -> T.any_naked_int64
    | Naked_nativeint -> T.any_naked_nativeint

  let these s =
    let ty = I.these_unboxed s in
    let simple_opt =
      match I.Num.Set.get_singleton s with
      | None -> None
      | Some i -> Some (Simple.const (I.Num.to_const i))
    in
    ty, simple_opt

  let term = I.term_unboxed

  module Pair = struct
    type nonrec t = Lhs.t * Rhs.t

    include Container_types.Make_pair (Lhs) (Rhs)
  end

  let cross_product set1 set2 =
    Lhs.Set.fold
      (fun elt1 result ->
        Rhs.Set.fold
          (fun elt2 result -> Pair.Set.add (elt1, elt2) result)
          set2 result)
      set1 Pair.Set.empty

  module Num = I.Num

  let op ~machine_width:_ (op : P.int_shift_op) n1 n2 =
    let always_some f = Some (f n1 n2) in
    match op with
    | Lsl -> always_some Num.shift_left
    | Lsr -> always_some Num.shift_right_logical
    | Asr -> always_some Num.shift_right

  let op_lhs_unknown ~machine_width (op : P.int_shift_op) ~rhs :
      Num.t binary_arith_outcome_for_one_side_only =
    let module O = Target_ocaml_int in
    let rhs = rhs in
    match op with
    | Lsl | Lsr | Asr ->
      (* Shifting either way by [Targetint_32_64.size] or above, or by a
         negative amount, is undefined.

         However note that we cannot produce [Invalid] unless the code is type
         unsafe, which it is not here. (Otherwise a GADT match might be reduced
         to only one possible case which it would be wrong to take.) *)
      if O.equal rhs (O.zero machine_width)
      then The_other_side
      else Cannot_simplify

  let op_rhs_unknown ~machine_width (op : P.int_shift_op) ~lhs :
      Num.t binary_arith_outcome_for_one_side_only =
    (* In these cases we are giving a semantics for some cases where the
       right-hand side may be less than zero or greater than or equal to
       [Targetint_32_64.size]. These cases have undefined semantics, as above;
       however, it seems fine to give them a semantics since there is benefit to
       doing so in this particular case. (This is not the case for the situation
       in [op_lhs_unknown], above, where there would be no such benefit.) *)
    match op with
    | Lsl | Lsr ->
      if Num.equal lhs (Num.zero machine_width)
      then Exactly (Num.zero machine_width)
      else Cannot_simplify
    | Asr ->
      if Num.equal lhs (Num.zero machine_width)
      then Exactly (Num.zero machine_width)
      else if Num.equal lhs (Num.minus_one machine_width)
      then Exactly (Num.minus_one machine_width)
      else Cannot_simplify
end
[@@inline always]

module Int_ops_for_binary_shift_tagged_immediate =
  Int_ops_for_binary_shift (A.For_tagged_immediates)
module Int_ops_for_binary_shift_naked_immediate =
  Int_ops_for_binary_shift (A.For_naked_immediates)
module Int_ops_for_binary_shift_int8 = Int_ops_for_binary_shift (A.For_int8s)
module Int_ops_for_binary_shift_int16 = Int_ops_for_binary_shift (A.For_int16s)
module Int_ops_for_binary_shift_int32 = Int_ops_for_binary_shift (A.For_int32s)
module Int_ops_for_binary_shift_int64 = Int_ops_for_binary_shift (A.For_int64s)
module Int_ops_for_binary_shift_nativeint =
  Int_ops_for_binary_shift (A.For_nativeints)
module Binary_int_shift_tagged_immediate =
  Binary_arith_like (Int_ops_for_binary_shift_tagged_immediate)
module Binary_int_shift_naked_immediate =
  Binary_arith_like (Int_ops_for_binary_shift_naked_immediate)
module Binary_int_shift_int8 = Binary_arith_like (Int_ops_for_binary_shift_int8)
module Binary_int_shift_int16 =
  Binary_arith_like (Int_ops_for_binary_shift_int16)
module Binary_int_shift_int32 =
  Binary_arith_like (Int_ops_for_binary_shift_int32)
module Binary_int_shift_int64 =
  Binary_arith_like (Int_ops_for_binary_shift_int64)
module Binary_int_shift_nativeint =
  Binary_arith_like (Int_ops_for_binary_shift_nativeint)

module Int_ops_for_binary_comp (I : A.Int_number_kind) : sig
  include
    Binary_arith_like_sig
      with type op = P.signed_or_unsigned P.comparison_behaviour
end = struct
  module Lhs = I.Num
  module Rhs = I.Num
  module Result = Target_ocaml_int

  type op = P.signed_or_unsigned P.comparison_behaviour

  let arg_kind = I.standard_int_or_float_kind

  let result_kind = K.naked_immediate

  let ok_to_evaluate _env = true

  let prover_lhs = I.unboxed_prover

  let prover_rhs = I.unboxed_prover

  let unknown ~machine_width (op : op) =
    match op with
    | Yielding_bool _ ->
      T.these_naked_immediates (Target_ocaml_int.all_bools machine_width)
    | Yielding_int_like_compare_functions _signedness ->
      T.these_naked_immediates
        (Target_ocaml_int.zero_one_and_minus_one machine_width)

  let these s =
    let ty = T.these_naked_immediates s in
    let simple_opt =
      match Target_ocaml_int.Set.get_singleton s with
      | None -> None
      | Some i -> Some (Simple.const (Reg_width_const.naked_immediate i))
    in
    ty, simple_opt

  let term imm : Named.t =
    Named.create_simple (Simple.const (Reg_width_const.naked_immediate imm))

  module Pair = I.Num.Pair

  let cross_product = I.Num.cross_product

  module Num = I.Num

  let op ~machine_width (op : P.signed_or_unsigned P.comparison_behaviour) n1 n2
      =
    match op with
    | Yielding_bool op -> (
      let bool b = Target_ocaml_int.bool machine_width b in
      match op with
      | Eq -> Some (bool (Num.compare n1 n2 = 0))
      | Neq -> Some (bool (Num.compare n1 n2 <> 0))
      | Lt Signed -> Some (bool (Num.compare n1 n2 < 0))
      | Gt Signed -> Some (bool (Num.compare n1 n2 > 0))
      | Le Signed -> Some (bool (Num.compare n1 n2 <= 0))
      | Ge Signed -> Some (bool (Num.compare n1 n2 >= 0))
      | Lt Unsigned -> Some (bool (Num.compare_unsigned n1 n2 < 0))
      | Gt Unsigned -> Some (bool (Num.compare_unsigned n1 n2 > 0))
      | Le Unsigned -> Some (bool (Num.compare_unsigned n1 n2 <= 0))
      | Ge Unsigned -> Some (bool (Num.compare_unsigned n1 n2 >= 0)))
    | Yielding_int_like_compare_functions signed_or_unsigned -> (
      match signed_or_unsigned with
      | Signed ->
        let int i = Target_ocaml_int.of_int machine_width i in
        let c = Num.compare n1 n2 in
        if c < 0
        then Some (int (-1))
        else if c = 0
        then Some (int 0)
        else Some (int 1)
      | Unsigned ->
        let int i = Target_ocaml_int.of_int machine_width i in
        let c = Num.compare_unsigned n1 n2 in
        if c < 0
        then Some (int (-1))
        else if c = 0
        then Some (int 0)
        else Some (int 1))

  let op_lhs_unknown ~machine_width:_ _op ~rhs:_ = Cannot_simplify

  let op_rhs_unknown ~machine_width:_ _op ~lhs:_ = Cannot_simplify
end
[@@inline always]

module Int_ops_for_binary_comp_tagged_immediate =
  Int_ops_for_binary_comp (A.For_tagged_immediates)
module Int_ops_for_binary_comp_naked_immediate =
  Int_ops_for_binary_comp (A.For_naked_immediates)
module Int_ops_for_binary_comp_int8 = Int_ops_for_binary_comp (A.For_int8s)
module Int_ops_for_binary_comp_int16 = Int_ops_for_binary_comp (A.For_int16s)
module Int_ops_for_binary_comp_int32 = Int_ops_for_binary_comp (A.For_int32s)
module Int_ops_for_binary_comp_int64 = Int_ops_for_binary_comp (A.For_int64s)
module Int_ops_for_binary_comp_nativeint =
  Int_ops_for_binary_comp (A.For_nativeints)
module Binary_int_comp_tagged_immediate =
  Binary_arith_like (Int_ops_for_binary_comp_tagged_immediate)
module Binary_int_comp_naked_immediate =
  Binary_arith_like (Int_ops_for_binary_comp_naked_immediate)
module Binary_int_comp_int8 = Binary_arith_like (Int_ops_for_binary_comp_int8)
module Binary_int_comp_int16 = Binary_arith_like (Int_ops_for_binary_comp_int16)
module Binary_int_comp_int32 = Binary_arith_like (Int_ops_for_binary_comp_int32)
module Binary_int_comp_int64 = Binary_arith_like (Int_ops_for_binary_comp_int64)
module Binary_int_comp_nativeint =
  Binary_arith_like (Int_ops_for_binary_comp_nativeint)

module Float_ops_for_binary_arith_gen (FP : sig
  module F : Numeric_types.Float_by_bit_pattern

  val width : Flambda_primitive.float_bitwidth

  val arg_kind : K.Standard_int_or_float.t

  val result_kind : Flambda_kind.t

  val prover : T.Typing_env.t -> T.t -> F.Set.t T.meet_shortcut

  val unknown : T.t

  val these : F.Set.t -> T.t

  val const : F.t -> Const.t
end) : sig
  include Binary_arith_like_sig with type op = P.binary_float_arith_op
end = struct
  module F = FP.F
  module Lhs = F
  module Rhs = F
  module Result = F

  type op = P.binary_float_arith_op

  let arg_kind = FP.arg_kind

  let result_kind = FP.result_kind

  let ok_to_evaluate denv = DE.propagating_float_consts denv

  let prover_lhs = FP.prover

  let prover_rhs = FP.prover

  let unknown ~machine_width:_ _ = FP.unknown

  let these s =
    let ty = FP.these s in
    let simple_opt =
      match F.Set.get_singleton s with
      | None -> None
      | Some f -> Some (Simple.const (FP.const f))
    in
    ty, simple_opt

  let term f = Named.create_simple (Simple.const (FP.const f))

  module Pair = F.Pair

  let cross_product = F.cross_product

  let op ~machine_width:_ (op : op) n1 n2 =
    let always_some f = Some (f n1 n2) in
    match op with
    | Add -> always_some F.IEEE_semantics.add
    | Sub -> always_some F.IEEE_semantics.sub
    | Mul -> always_some F.IEEE_semantics.mul
    | Div -> always_some F.IEEE_semantics.div

  type symmetric_op =
    | Add
    | Mul

  (* To be certain of correctness we restrict identities on floating-point
     numbers to those that preserve the _bit pattern_. *)

  let symmetric_op_one_side_unknown (op : symmetric_op) ~this_side :
      F.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add ->
      (* You might think that "x + 0" has the same representation as "x".
         However it doesn't in the case where that constant zero is +0 and x is
         equal to -0. *)
      Cannot_simplify
    | Mul ->
      if F.equal this_side F.one
      then
        The_other_side
        [@z3 check_float_binary_neutral `Mul 1.0 `Right]
        [@z3 check_float_binary_neutral `Mul 1.0 `Left]
      else if F.equal this_side F.minus_one
      then
        Float_negation_of_the_other_side FP.width
        [@z3 check_float_binary_opposite `Mul (-1.0) `Left]
        [@z3 check_float_binary_opposite `Mul (-1.0) `Right]
      else Cannot_simplify

  let op_lhs_unknown ~machine_width:_ (op : op) ~rhs :
      F.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add -> symmetric_op_one_side_unknown Add ~this_side:rhs
    | Mul -> symmetric_op_one_side_unknown Mul ~this_side:rhs
    | Sub -> Cannot_simplify
    | Div ->
      if F.equal rhs F.one
      then The_other_side [@z3 check_float_binary_neutral `Div 1.0 `Right]
      else if F.equal rhs F.minus_one
      then
        Float_negation_of_the_other_side FP.width
        [@z3 check_float_binary_opposite `Div (-1.0) `Right]
      else Cannot_simplify

  let op_rhs_unknown ~machine_width:_ (op : op) ~lhs :
      F.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add -> symmetric_op_one_side_unknown Add ~this_side:lhs
    | Mul -> symmetric_op_one_side_unknown Mul ~this_side:lhs
    | Sub -> Cannot_simplify
    | Div -> Cannot_simplify
end

module Float_ops_for_binary_arith = Float_ops_for_binary_arith_gen (struct
  module F = Numeric_types.Float_by_bit_pattern

  let width = Flambda_primitive.Float64

  let arg_kind = K.Standard_int_or_float.Naked_float

  let result_kind = K.naked_float

  let prover = T.meet_naked_floats

  let unknown = T.any_naked_float

  let these = T.these_naked_floats

  let const = Reg_width_const.naked_float
end)

module Float32_ops_for_binary_arith = Float_ops_for_binary_arith_gen (struct
  module F = Numeric_types.Float32_by_bit_pattern

  let width = Flambda_primitive.Float32

  let arg_kind = K.Standard_int_or_float.Naked_float32

  let result_kind = K.naked_float32

  let prover = T.meet_naked_float32s

  let unknown = T.any_naked_float32

  let these = T.these_naked_float32s

  let const = Reg_width_const.naked_float32
end)

module Binary_float_arith = Binary_arith_like (Float_ops_for_binary_arith)
module Binary_float32_arith = Binary_arith_like (Float32_ops_for_binary_arith)

module Float_ops_for_binary_comp_gen (FP : sig
  module F : Numeric_types.Float_by_bit_pattern

  val arg_kind : K.Standard_int_or_float.t

  val prover : T.Typing_env.t -> T.t -> F.Set.t T.meet_shortcut
end) : sig
  include Binary_arith_like_sig with type op = unit P.comparison_behaviour
end = struct
  module F = FP.F
  module Lhs = F
  module Rhs = F
  module Result = Target_ocaml_int

  type op = unit P.comparison_behaviour

  let arg_kind = FP.arg_kind

  let result_kind = K.naked_immediate

  let ok_to_evaluate denv = DE.propagating_float_consts denv

  let prover_lhs = FP.prover

  let prover_rhs = FP.prover

  let unknown ~machine_width (op : op) =
    match op with
    | Yielding_bool _ ->
      T.these_naked_immediates (Target_ocaml_int.all_bools machine_width)
    | Yielding_int_like_compare_functions () ->
      T.these_naked_immediates
        (Target_ocaml_int.zero_one_and_minus_one machine_width)

  let these s =
    let ty = T.these_naked_immediates s in
    let simple_opt =
      match Target_ocaml_int.Set.get_singleton s with
      | None -> None
      | Some i -> Some (Simple.const (Reg_width_const.naked_immediate i))
    in
    ty, simple_opt

  let term imm : Named.t =
    Named.create_simple (Simple.const (Reg_width_const.naked_immediate imm))

  module Pair = F.Pair

  let cross_product = F.cross_product

  let op ~machine_width (op : op) n1 n2 =
    match op with
    | Yielding_bool op -> (
      let has_nan = F.is_any_nan n1 || F.is_any_nan n2 in
      let bool b = Target_ocaml_int.bool machine_width b in
      match op with
      | Eq -> Some (bool (F.IEEE_semantics.equal n1 n2))
      | Neq -> Some (bool (not (F.IEEE_semantics.equal n1 n2)))
      | Lt () ->
        if has_nan
        then Some (bool false)
        else Some (bool (F.IEEE_semantics.compare n1 n2 < 0))
      | Gt () ->
        if has_nan
        then Some (bool false)
        else Some (bool (F.IEEE_semantics.compare n1 n2 > 0))
      | Le () ->
        if has_nan
        then Some (bool false)
        else Some (bool (F.IEEE_semantics.compare n1 n2 <= 0))
      | Ge () ->
        if has_nan
        then Some (bool false)
        else Some (bool (F.IEEE_semantics.compare n1 n2 >= 0)))
    | Yielding_int_like_compare_functions () ->
      let int i = Target_ocaml_int.of_int machine_width i in
      let c = F.IEEE_semantics.compare n1 n2 in
      if c < 0
      then Some (int (-1))
      else if c = 0
      then Some (int 0)
      else Some (int 1)

  let result_of_comparison_with_nan ~machine_width (op : unit P.comparison) =
    match op with
    | Neq -> Exactly (Target_ocaml_int.bool_true machine_width)
    | Eq | Lt () | Gt () | Le () | Ge () ->
      Exactly (Target_ocaml_int.bool_false machine_width)

  let op_lhs_unknown ~machine_width (op : op) ~rhs :
      _ binary_arith_outcome_for_one_side_only =
    match op with
    | Yielding_bool op ->
      if F.is_any_nan rhs
      then result_of_comparison_with_nan ~machine_width op
      else Cannot_simplify
    | Yielding_int_like_compare_functions () -> Cannot_simplify

  let op_rhs_unknown ~machine_width (op : op) ~lhs :
      _ binary_arith_outcome_for_one_side_only =
    match op with
    | Yielding_bool op ->
      if F.is_any_nan lhs
      then result_of_comparison_with_nan ~machine_width op
      else Cannot_simplify
    | Yielding_int_like_compare_functions () -> Cannot_simplify
end

module Float_ops_for_binary_comp = Float_ops_for_binary_comp_gen (struct
  module F = Numeric_types.Float_by_bit_pattern

  let arg_kind = K.Standard_int_or_float.Naked_float

  let prover = T.meet_naked_floats
end)

module Float32_ops_for_binary_comp = Float_ops_for_binary_comp_gen (struct
  module F = Numeric_types.Float32_by_bit_pattern

  let arg_kind = K.Standard_int_or_float.Naked_float32

  let prover = T.meet_naked_float32s
end)

module Binary_float_comp = Binary_arith_like (Float_ops_for_binary_comp)
module Binary_float32_comp = Binary_arith_like (Float32_ops_for_binary_comp)
OCAML*)
Parameter Binary_int_arith_tagged_immediate_simplify :
  P.binary_int_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_arith_tagged_immediate_simplify => "Binary_int_arith_tagged_immediate.simplify".
Parameter Binary_int_arith_naked_immediate_simplify :
  P.binary_int_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_arith_naked_immediate_simplify => "Binary_int_arith_naked_immediate.simplify".
Parameter Binary_int_arith_int8_simplify :
  P.binary_int_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_arith_int8_simplify => "Binary_int_arith_int8.simplify".
Parameter Binary_int_arith_int16_simplify :
  P.binary_int_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_arith_int16_simplify => "Binary_int_arith_int16.simplify".
Parameter Binary_int_arith_int32_simplify :
  P.binary_int_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_arith_int32_simplify => "Binary_int_arith_int32.simplify".
Parameter Binary_int_arith_int64_simplify :
  P.binary_int_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_arith_int64_simplify => "Binary_int_arith_int64.simplify".
Parameter Binary_int_arith_nativeint_simplify :
  P.binary_int_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_arith_nativeint_simplify => "Binary_int_arith_nativeint.simplify".
Parameter Binary_int_shift_tagged_immediate_simplify :
  P.int_shift_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_shift_tagged_immediate_simplify => "Binary_int_shift_tagged_immediate.simplify".
Parameter Binary_int_shift_naked_immediate_simplify :
  P.int_shift_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_shift_naked_immediate_simplify => "Binary_int_shift_naked_immediate.simplify".
Parameter Binary_int_shift_int8_simplify :
  P.int_shift_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_shift_int8_simplify => "Binary_int_shift_int8.simplify".
Parameter Binary_int_shift_int16_simplify :
  P.int_shift_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_shift_int16_simplify => "Binary_int_shift_int16.simplify".
Parameter Binary_int_shift_int32_simplify :
  P.int_shift_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_shift_int32_simplify => "Binary_int_shift_int32.simplify".
Parameter Binary_int_shift_int64_simplify :
  P.int_shift_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_shift_int64_simplify => "Binary_int_shift_int64.simplify".
Parameter Binary_int_shift_nativeint_simplify :
  P.int_shift_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_shift_nativeint_simplify => "Binary_int_shift_nativeint.simplify".
Parameter Binary_int_comp_tagged_immediate_simplify :
  P.comparison_behaviour P.signed_or_unsigned -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_comp_tagged_immediate_simplify => "Binary_int_comp_tagged_immediate.simplify".
Parameter Binary_int_comp_naked_immediate_simplify :
  P.comparison_behaviour P.signed_or_unsigned -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_comp_naked_immediate_simplify => "Binary_int_comp_naked_immediate.simplify".
Parameter Binary_int_comp_int8_simplify :
  P.comparison_behaviour P.signed_or_unsigned -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_comp_int8_simplify => "Binary_int_comp_int8.simplify".
Parameter Binary_int_comp_int16_simplify :
  P.comparison_behaviour P.signed_or_unsigned -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_comp_int16_simplify => "Binary_int_comp_int16.simplify".
Parameter Binary_int_comp_int32_simplify :
  P.comparison_behaviour P.signed_or_unsigned -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_comp_int32_simplify => "Binary_int_comp_int32.simplify".
Parameter Binary_int_comp_int64_simplify :
  P.comparison_behaviour P.signed_or_unsigned -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_comp_int64_simplify => "Binary_int_comp_int64.simplify".
Parameter Binary_int_comp_nativeint_simplify :
  P.comparison_behaviour P.signed_or_unsigned -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_int_comp_nativeint_simplify => "Binary_int_comp_nativeint.simplify".
Parameter Binary_float_arith_simplify :
  P.binary_float_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_float_arith_simplify => "Binary_float_arith.simplify".
Parameter Binary_float32_arith_simplify :
  P.binary_float_arith_op -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_float32_arith_simplify => "Binary_float32_arith.simplify".
Parameter Binary_float_comp_simplify :
  P.comparison_behaviour unit -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_float_comp_simplify => "Binary_float_comp.simplify".
Parameter Binary_float32_comp_simplify :
  P.comparison_behaviour unit -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t ->
  Bound_var.t -> M SPR.t.
Extract Inlined Constant Binary_float32_comp_simplify => "Binary_float32_comp.simplify".

(* 981-983: Unlike in the language specification, the compiler defines
   physical equality as referential equality on all values, including
   immediates and immutable blocks. *)
(* 984-1007. In the compiler: [op dacc ~original_term _dbg ~arg1:_ ~arg1_ty
   ~arg2:_ ~arg2_ty ~result_var]. *)
Definition simplify_phys_equal (op : P.equality_comparison) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t)
    (arg1_ty : T.t) (_ : Simple.t) (arg2_ty : T.t) (result_var : Bound_var.t)
    : M SPR.t :=
  (* This primitive is only used for arguments of kind [Value]. *)
  let* typing_env := DA.typing_env dacc in
  (* Note: We don't compare the arguments themselves for equality. Instead, we
     know that [simplify_simple] always returns alias types, so we let the
     prover do the matching. *)
  let* machine_width :=
    let! tmp1 := DA.denv dacc in
    DE.machine_width tmp1
  in
  let! tmp1 := T.prove_physical_equality typing_env arg1_ty arg2_ty in
  match tmp1 with
  | T.Proved bool =>
    let& result := match op with P.Eq_ => bool | P.Neq_ => negb bool end in
    let* dacc :=
      let! tmp2 := Target_ocaml_int.bool_ machine_width result in
      let! tmp3 := T.this_naked_immediate tmp2 in
      DA.add_variable dacc result_var tmp3
    in
    let! tmp4 := Simple.untagged_const_bool machine_width result in
    let! tmp5 := Named.create_simple tmp4 in
    SPR.create tmp5 false dacc
  | T.Unknown =>
    let* dacc :=
      let! tmp2 := Target_ocaml_int.all_bools machine_width in
      let! tmp3 := T.these_naked_immediates tmp2 in
      DA.add_variable dacc result_var tmp3
    in
    SPR.create original_term false dacc
  end.

(* 1009-1080. In the compiler: [array_kind array_load_kind mutability dacc
   ~original_term:_ dbg ~arg1:array ~arg1_ty:array_ty ~arg2:index
   ~arg2_ty:index_ty ~result_var]. *)
Definition simplify_array_load (array_kind : P.Array_kind.t)
    (array_load_kind : P.Array_load_kind.t) (mutability : Mutability.t)
    (dacc : DA.t) (_ : Named.t) (dbg : Debuginfo.t) (array : Simple.t)
    (array_ty : T.t) (index : Simple.t) (index_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let& result_kind :=
    match array_load_kind with
    | P.Array_load_kind.Immediates => K.value
    | P.Array_load_kind.Gc_ignorable_values | P.Array_load_kind.Values =>
      K.value
    | P.Array_load_kind.Naked_floats => K.naked_float
    | P.Array_load_kind.Naked_float32s => K.naked_float32
    | P.Array_load_kind.Naked_ints => K.naked_immediate
    | P.Array_load_kind.Naked_int8s => K.naked_int8
    | P.Array_load_kind.Naked_int16s => K.naked_int16
    | P.Array_load_kind.Naked_int32s => K.naked_int32
    | P.Array_load_kind.Naked_int64s => K.naked_int64
    | P.Array_load_kind.Naked_nativeints => K.naked_nativeint
    | P.Array_load_kind.Naked_vec128s => K.naked_vec128
    | P.Array_load_kind.Naked_vec256s => K.naked_vec256
    | P.Array_load_kind.Naked_vec512s => K.naked_vec512
    | P.Array_load_kind.Naked_masks => K.naked_mask
    end
  in
  let* array_kind :=
    Simplify_common.specialise_array_kind dacc array_kind array_ty
  in
  match array_kind with
  | Or_bottom.Bottom =>
    let* ty := T.bottom result_kind in
    let* dacc := DA.add_variable dacc result_var ty in
    SPR.create_invalid dacc
  | Or_bottom.Ok array_kind =>
    let& prim :=
      P.Binary (P.Array_load array_kind array_load_kind mutability) array index
    in
    (* PORT-GAP(loose): 1042, the attribute [@inline] is not kept. *)
    let& return_given_type :=
      fun (ty : T.t) (try_reify : bool) =>
      let* named := Named.create_prim prim dbg in
      let* dacc := DA.add_variable dacc result_var ty in
      SPR.create named try_reify dacc
    in
    (* PORT-GAP(loose): 1047, the attribute [@inline] is not kept. *)
    let& contents_unknown :=
      fun (_ : unit) =>
      let! tmp1 := P.result_kind' prim in
      let! tmp2 := T.unknown tmp1 in
      return_given_type tmp2 false
    in
    let! tmp1 := DA.typing_env dacc in
    let! tmp2 := T.prove_is_immutable_array tmp1 array_ty in
    match tmp2 with
    | T.Unknown => contents_unknown tt
    | T.Proved (T3 elt_kind fields _mode) =>
      match elt_kind with
      | Or_unknown_or_bottom.Unknown | Or_unknown_or_bottom.Bottom =>
        contents_unknown tt
      | Or_unknown_or_bottom.Ok elt_kind =>
        let! tmp3 := K.With_subkind.kind elt_kind in
        let! tmp4 := K.equal tmp3 result_kind in
        if negb tmp4
        then contents_unknown tt
        else
          let! tmp5 := DA.typing_env dacc in
          let! tmp6 := T.prove_equals_tagged_immediates tmp5 index_ty in
          match tmp6 with
          | T.Unknown => contents_unknown tt
          | T.Proved imms =>
            let! tmp7 := Target_ocaml_int.Set_.get_singleton imms in
            match tmp7 with
            | None => contents_unknown tt
            | Some imm =>
              let* machine_width :=
                let! tmp8 := DA.denv dacc in
                DE.machine_width tmp8
              in
              (* 1070-1074: [Array.length fields |> Target_ocaml_int.of_int
                 machine_width] is [Target_ocaml_int.of_int machine_width
                 (Array.length fields)]. *)
              let! tmp9 := Target_ocaml_int.zero machine_width in
              let! tmp10 := Target_ocaml_int.op_lt imm tmp9 in
              let! tmp11 :=
                or_else tmp10
                  (let! tmp12 := Array.length fields in
                   let! tmp13 := Target_ocaml_int.of_int machine_width tmp12 in
                   Target_ocaml_int.op_gt_eq imm tmp13)
              in
              if tmp11
              then SPR.create_invalid dacc
              else
                (* 1078: [fields.(i)] is [Array.get fields i]. *)
                let! tmp14 := Target_ocaml_int.to_int imm in
                let! tmp15 := Array.get fields tmp14 in
                return_given_type tmp15 true
            end
          end
      end
    end
  end.

(* 1082-1088. In the compiler: [_string_like_value _string_accessor_width
   ~original_prim dacc ~original_term _dbg ~arg1:_ ~arg1_ty:_ ~arg2:_
   ~arg2_ty:_ ~result_var]. 1086-1088, [SPR.create_unknown dacc ~result_var
   kind ~original_term]: the arguments are in the order of the interface. *)
Definition simplify_string_or_bigstring_load
    (_string_like_value : P.string_like_value)
    (_string_accessor_width : P.string_accessor_width) (original_prim : P.t)
    (dacc : DA.t) (original_term : Named.t) (_dbg : Debuginfo.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1090-1095 *)
Definition simplify_bigarray_load (_num_dimensions : P.num_dimensions)
    (_bigarray_kind : P.Bigarray_kind.t)
    (_bigarray_layout : P.Bigarray_layout.t) (original_prim : P.t)
    (dacc : DA.t) (original_term : Named.t) (_dbg : Debuginfo.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1097-1101 *)
Definition simplify_bigarray_get_alignment (_align : int)
    (original_prim : P.t) (dacc : DA.t) (original_term : Named.t)
    (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1103-1107 *)
Definition simplify_atomic_load (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1109-1111. In the compiler: [_block_access_kind _init_or_assign ~field:_
   dacc ~original_term _dbg ~arg1:_ ~arg1_ty:_ ~arg2:_ ~arg2_ty:_
   ~result_var]. *)
Definition simplify_block_set (_block_access_kind : P.Block_access_kind.t)
    (_init_or_assign : P.Init_or_assign.t) (_ : Target_ocaml_int.t)
    (dacc : DA.t) (original_term : Named.t) (_dbg : Debuginfo.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unit dacc result_var original_term.

(* 1113-1115 *)
Definition simplify_poke (dacc : DA.t) (original_term : Named.t)
    (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unit dacc result_var original_term.

(* 1117-1121 *)
Definition simplify_read_offset (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1123-1179. In the compiler: [dacc original_prim prim ~arg1 ~arg1_ty ~arg2
   ~arg2_ty dbg ~result_var]. *)
Definition simplify_binary_primitive0 (dacc : DA.t) (original_prim : P.t)
    (prim : P.binary_primitive) (arg1 : Simple.t) (arg1_ty : T.t)
    (arg2 : Simple.t) (arg2_ty : T.t) (dbg : Debuginfo.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* original_term := Named.create_prim original_prim dbg in
  (* 1126-1177: a function of the file given its first arguments is a
     value. *)
  (* PORT-GAP(papp): 1132-1163, the function [simplify] of each instance of
     [Binary_arith_like], which is declared above, is given its first
     argument only. *)
  let* simplifier :=
    match prim with
    | P.Block_set kind init field => ret (simplify_block_set kind init field)
    | P.Array_load array_kind width mutability =>
      ret (simplify_array_load array_kind width mutability)
    | P.Int_arith_ kind op =>
      match kind with
      | K.Standard_int.Tagged_immediate => papp1 Binary_int_arith_tagged_immediate_simplify op
      | K.Standard_int.Naked_immediate => papp1 Binary_int_arith_naked_immediate_simplify op
      | K.Standard_int.Naked_int8 => papp1 Binary_int_arith_int8_simplify op
      | K.Standard_int.Naked_int16 => papp1 Binary_int_arith_int16_simplify op
      | K.Standard_int.Naked_int32 => papp1 Binary_int_arith_int32_simplify op
      | K.Standard_int.Naked_int64 => papp1 Binary_int_arith_int64_simplify op
      | K.Standard_int.Naked_nativeint => papp1 Binary_int_arith_nativeint_simplify op
      end
    | P.Int_shift kind op =>
      match kind with
      | K.Standard_int.Tagged_immediate => papp1 Binary_int_shift_tagged_immediate_simplify op
      | K.Standard_int.Naked_immediate => papp1 Binary_int_shift_naked_immediate_simplify op
      | K.Standard_int.Naked_int8 => papp1 Binary_int_shift_int8_simplify op
      | K.Standard_int.Naked_int16 => papp1 Binary_int_shift_int16_simplify op
      | K.Standard_int.Naked_int32 => papp1 Binary_int_shift_int32_simplify op
      | K.Standard_int.Naked_int64 => papp1 Binary_int_shift_int64_simplify op
      | K.Standard_int.Naked_nativeint => papp1 Binary_int_shift_nativeint_simplify op
      end
    | P.Int_comp kind op =>
      match kind with
      | K.Standard_int.Tagged_immediate => papp1 Binary_int_comp_tagged_immediate_simplify op
      | K.Standard_int.Naked_immediate => papp1 Binary_int_comp_naked_immediate_simplify op
      | K.Standard_int.Naked_int8 => papp1 Binary_int_comp_int8_simplify op
      | K.Standard_int.Naked_int16 => papp1 Binary_int_comp_int16_simplify op
      | K.Standard_int.Naked_int32 => papp1 Binary_int_comp_int32_simplify op
      | K.Standard_int.Naked_int64 => papp1 Binary_int_comp_int64_simplify op
      | K.Standard_int.Naked_nativeint => papp1 Binary_int_comp_nativeint_simplify op
      end
    | P.Float_arith_ P.Float64 op => papp1 Binary_float_arith_simplify op
    | P.Float_comp P.Float64 op => papp1 Binary_float_comp_simplify op
    (* Note: despite the fact that all float32s are representable as float64s,
       float32 arithmetic operations need to be performed in 32-bit precision to
       preserve rounding behavior. Such 32-bit operations are implemented by
       flambda2_floats. *)
    | P.Float_arith_ P.Float32 op => papp1 Binary_float32_arith_simplify op
    | P.Float_comp P.Float32 op => papp1 Binary_float32_comp_simplify op
    | P.Phys_equal op => ret (simplify_phys_equal op)
    | P.String_or_bigstring_load string_like_value string_accessor_width =>
      ret
        (simplify_string_or_bigstring_load string_like_value
           string_accessor_width original_prim)
    | P.Bigarray_load num_dimensions bigarray_kind bigarray_layout =>
      ret
        (simplify_bigarray_load num_dimensions bigarray_kind bigarray_layout
           original_prim)
    | P.Bigarray_get_alignment align =>
      ret (simplify_bigarray_get_alignment align original_prim)
    | P.Atomic_load _ _ => ret (simplify_atomic_load original_prim)
    | P.Poke _ => ret simplify_poke
    | P.Read_offset _ _ => ret (simplify_read_offset original_prim)
    end
  in
  simplifier dacc original_term dbg arg1 arg1_ty arg2 arg2_ty result_var.

(* 1181-1239. In the compiler: [dacc prim ~arg1 ~arg2]. *)
Definition recover_comparison_primitive (dacc : DA.t)
    (prim : P.binary_primitive) (arg1 arg2 : Simple.t) : M (option P.t) :=
  let& try_one_direction :=
    fun (left right : Simple.t) (op : P.comparison P.signed_or_unsigned) =>
    Simple.pattern_match right
      (fun _ _ => ret None)
      (fun const =>
        (* PORT-GAP(loose): 1186, the attribute [@warning "-fragile-match"]
           is not kept. *)
        let! tmp1 := Const.descr const in
        match tmp1 with
        | Int_ids.Const.Descr.Tagged_immediate i =>
          (* 1188-1189: [when Target_ocaml_int.(equal i (zero (DE.machine_width
             (DA.denv dacc))))] *)
          let! tmp2 := DA.denv dacc in
          let! tmp3 := DE.machine_width tmp2 in
          let! tmp4 := Target_ocaml_int.zero tmp3 in
          let! tmp5 := Target_ocaml_int.equal i tmp4 in
          if tmp5
          then
            (* 1190-1198, [Simple.pattern_match' left ~const ~symbol ~var]:
               the arguments are in the order of the interface. *)
            Simple.pattern_match' left
              (fun var _ =>
                let! tmp6 := DA.denv dacc in
                let! tmp7 := DE.find_comparison_result tmp6 var in
                match tmp7 with
                | None => ret None
                | Some comp =>
                  Comparison_result.convert_result_compared_to_tagged_zero comp
                    op
                end)
              (fun _ _ => ret None)
              (fun _ => ret None)
          else ret None
        | _ => ret None
        end)
  in
  let& try_both_directions :=
    fun (op swapped_op : P.comparison P.signed_or_unsigned) =>
    let! tmp1 := try_one_direction arg1 arg2 op in
    match tmp1 with
    | Some p => ret (Some p)
    | None => try_one_direction arg2 arg1 swapped_op
    end
  in
  match prim with
  | P.Block_set _ _ _ | P.Array_load _ _ _ | P.Int_arith_ _ _ | P.Int_shift _ _
  | P.Int_comp _ (P.Yielding_int_like_compare_functions _)
  | P.Float_arith_ _ _ | P.Float_comp _ _ | P.String_or_bigstring_load _ _
  | P.Bigarray_load _ _ _ | P.Bigarray_get_alignment _ | P.Atomic_load _ _
  | P.Poke _ | P.Read_offset _ _ =>
    ret None
  | P.Phys_equal op =>
    (* Integer (in)equality reaches Flambda2 as [Phys_equal] (cf.
       [Lambda_to_flambda_primitives]), so this is the form taken by e.g.
       [compare x y = 0]. The result of a comparison is always a tagged
       immediate, for which physical equality is value equality, so it collapses
       like [Int_comp] equality does. *)
    let& op :=
      (match op with P.Eq_ => P.Eq | P.Neq_ => P.Neq end
        : P.comparison P.signed_or_unsigned)
    in
    try_both_directions op op
  | P.Int_comp kind (P.Yielding_bool op) =>
    match kind with
    | K.Standard_int.Naked_immediate | K.Standard_int.Naked_int8
    | K.Standard_int.Naked_int16 | K.Standard_int.Naked_int32
    | K.Standard_int.Naked_int64 | K.Standard_int.Naked_nativeint =>
      ret None
    | K.Standard_int.Tagged_immediate =>
      let& swapped_op :=
        match op with
        | P.Eq => P.Eq
        | P.Neq => P.Neq
        (* Note that this is not handling a negation of an inequality, it is
           simply a pattern match for when the inequality appears the other way
           around. So e.g. [Lt] maps to [Gt], not [Ge]. *)
        | P.Lt s => P.Gt s
        | P.Gt s => P.Lt s
        | P.Le s => P.Ge s
        | P.Ge s => P.Le s
        end
      in
      try_both_directions op swapped_op
    end
  end.

(* 1241-1270. In the compiler: [dacc original_prim prim ~arg1 ~arg1_ty ~arg2
   ~arg2_ty dbg ~result_var]. *)
Definition simplify_binary_primitive (dacc : DA.t) (original_prim : P.t)
    (prim : P.binary_primitive) (arg1 : Simple.t) (arg1_ty : T.t)
    (arg2 : Simple.t) (arg2_ty : T.t) (dbg : Debuginfo.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* '(T6 original_prim prim arg1 arg1_ty arg2 arg2_ty) :=
    (* PORT-GAP(loose): 1244, the attribute [@warning "-fragile-match"] is
       not kept. *)
    let! tmp1 := recover_comparison_primitive dacc prim arg1 arg2 in
    match tmp1 with
    | None => ret (T6 original_prim prim arg1 arg1_ty arg2 arg2_ty)
    | Some (P.Binary new_prim new_arg1 new_arg2 as new_original_prim) =>
      let* min_name_mode := Bound_var.name_mode result_var in
      let* arg1_ty_opt :=
        S.simplify_simple_if_in_scope dacc new_arg1 min_name_mode
      in
      let* arg2_ty_opt :=
        S.simplify_simple_if_in_scope dacc new_arg2 min_name_mode
      in
      match arg1_ty_opt, arg2_ty_opt with
      | Some new_arg1_ty, Some new_arg2_ty =>
        ret
          (T6 new_original_prim new_prim new_arg1 new_arg1_ty new_arg2
             new_arg2_ty)
      | None, _ | _, None =>
        ret (T6 original_prim prim arg1 arg1_ty arg2 arg2_ty)
      end
    | Some other_prim =>
      fatal_errorf2 "Recovered primitive %a is not a comparison"
        Flambda_primitive.print other_prim
    end
  in
  simplify_binary_primitive0 dacc original_prim prim arg1 arg1_ty arg2 arg2_ty
    dbg result_var.
