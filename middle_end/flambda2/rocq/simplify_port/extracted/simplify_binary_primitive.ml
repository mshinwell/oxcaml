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
   middle_end/flambda2/rocq/simplify_port/Simplify_binary_primitive.v, which
   follows middle_end/flambda2/simplify/simplify_binary_primitive.ml function by
   function. Its OCaml text also copies
   middle_end/flambda2/simplify/number_adjuncts.mli, lines 91-125. Do not edit
   this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import

module Container_types = struct
  include Container_types

  module type S = sig
    include S

    module Set_ = Set
  end
end

module Target_ocaml_int = struct
  include Target_ocaml_int
  module Set_ = Set
end

module Numeric_types = struct
  include Numeric_types

  module type Float_by_bit_pattern_ = sig
    type t

    module Pair : Container_types.S with type t = t * t

    include Float_by_bit_pattern with type t := t and module Pair := Pair

    module Set_ = Set
  end

  module Float_by_bit_pattern = struct
    include Float_by_bit_pattern
    module Set_ = Set

    module Pair = struct
      include Pair
      module Set_ = Set
    end
  end

  module Float32_by_bit_pattern = struct
    include Float32_by_bit_pattern
    module Set_ = Set

    module Pair = struct
      include Pair
      module Set_ = Set
    end
  end
end

module Number_adjuncts = struct
  include Number_adjuncts

  module type Num_common = sig
    type t

    module Pair : sig
      type nonrec t = t * t

      include Container_types.S with type t := t
    end

    include Num_common with type t := t and module Pair := Pair

    module Set_ = Set
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

      (* [shift_right] is arithmetic shift right, matching [Int32], [Int64],
         etc. *)
      val shift_right : t -> Target_ocaml_int.t -> t

      val shift_right_logical : t -> Target_ocaml_int.t -> t

      val swap_byte_endianness : t -> t

      val neg : t -> t

      val compare_unsigned : t -> t -> int
    end

    include Number_kind_common with module Num := Num

    val standard_int_kind : Flambda_kind.Standard_int.t
  end

  module For_tagged_immediates = struct
    include For_tagged_immediates

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_naked_immediates = struct
    include For_naked_immediates

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_int8s = struct
    include For_int8s

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_int16s = struct
    include For_int16s

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_int32s = struct
    include For_int32s

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_int64s = struct
    include For_int64s

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_nativeints = struct
    include For_nativeints

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end
end

open Port_monad
module A = Number_adjuncts

type 'a binary_arith_outcome_for_one_side_only =
  | Exactly of 'a
  | The_other_side
  | Negation_of_the_other_side
  | Bitwise_not_of_the_other_side of K.Standard_int.t
  | Float_negation_of_the_other_side of Flambda_primitive.float_bitwidth
  | Cannot_simplify
  | Invalid

module type Pair_S = sig
  type t

  module Set_ : sig
    type elt = t

    type t

    val fold : (elt -> 'a1 -> 'a1 coq_M) -> t -> 'a1 -> 'a1 coq_M
  end
end

module As_container_types_S = functor (X : Container_types.S) -> X

module type Binary_arith_like_sig = sig
  module Lhs : Container_types.S

  module Rhs : Container_types.S

  module Pair : Pair_S with type t = Lhs.t * Rhs.t

  module Result : Container_types.S

  val ok_to_evaluate : DE.t -> bool coq_M

  val cross_product : Lhs.Set_.t -> Rhs.Set_.t -> Pair.Set_.t coq_M

  val arg_kind : K.Standard_int_or_float.t

  val result_kind : K.t

  val term : Result.t -> Named.t coq_M

  val prover_lhs : T.Typing_env.t -> T.t -> Lhs.Set_.t T.meet_shortcut coq_M

  val prover_rhs : T.Typing_env.t -> T.t -> Rhs.Set_.t T.meet_shortcut coq_M

  type op_

  val unknown : Target_system.Machine_width.t -> op_ -> T.t coq_M

  val these : Result.Set_.t -> (T.t * Simple.t option) coq_M

  val op :
    Target_system.Machine_width.t ->
    op_ ->
    Lhs.t ->
    Rhs.t ->
    Result.t option coq_M

  val op_lhs_unknown :
    Target_system.Machine_width.t ->
    op_ ->
    Rhs.t ->
    Result.t binary_arith_outcome_for_one_side_only coq_M

  val op_rhs_unknown :
    Target_system.Machine_width.t ->
    op_ ->
    Lhs.t ->
    Result.t binary_arith_outcome_for_one_side_only coq_M
end

module Binary_arith_like =
functor
  (N : Binary_arith_like_sig)
  ->
  struct
    module Possible_result = struct
      type t =
        | Simple of Simple.t
        | Prim of P.t
        | Exactly of N.Result.t

      (** val compare : t -> t -> int coq_M **)

      let compare t1 t2 =
        match t1 with
        | Simple simple1 -> (
          match t2 with
          | Simple simple2 -> Simple.compare simple1 simple2
          | Prim _ -> -1
          | Exactly _ -> -1)
        | Prim prim1 -> (
          match t2 with
          | Simple _ -> 1
          | Prim prim2 -> P.compare prim1 prim2
          | Exactly _ -> -1)
        | Exactly i1 -> (
          match t2 with
          | Simple _ -> 1
          | Prim _ -> 1
          | Exactly i2 -> N.Result.compare i1 i2)

      (** val print : Format.formatter -> t -> unit coq_M **)

      let print _ _ = Misc.fatal_error "Not implemented"

      module Set_ = struct
        type elt = t

        type t = elt list

        (** val empty : t **)

        let empty = []

        (** val add : elt -> t -> t coq_M **)

        let rec add elt0 s =
          match s with
          | [] -> elt0 :: []
          | elt' :: rest ->
            let c = compare elt0 elt' in
            if c < 0
            then elt0 :: s
            else if c = 0
            then s
            else
              let rest0 = add elt0 rest in
              elt' :: rest0

        (** val is_empty : t -> bool coq_M **)

        let is_empty = function [] -> true | _ :: _ -> false

        (** val cardinal : t -> int coq_M **)

        let cardinal = List.length

        (** val get_singleton : t -> elt option coq_M **)

        let get_singleton = function
          | [] -> None
          | elt0 :: l -> ( match l with [] -> Some elt0 | _ :: _ -> None)

        (** val elements : t -> elt list coq_M **)

        let elements s = s
      end
    end

    (** val max_num_possible_results : int **)

    let max_num_possible_results = 10

    (** val simplify : N.op_ -> DA.t -> Named.t -> Debuginfo.t -> Simple.t ->
        T.t -> Simple.t -> T.t -> Bound_var.t -> SPR.t coq_M **)

    let simplify op0 dacc original_term dbg arg1 arg1_ty arg2 arg2_ty result_var
        =
      let denv = DA.denv dacc in
      let typing_env = DE.typing_env denv in
      let proof1 = N.prover_lhs typing_env arg1_ty in
      let proof2 = N.prover_rhs typing_env arg2_ty in
      let kind = N.result_kind in
      let result_unknown =
       fun _ ->
        let machine_width = DE.machine_width denv in
        let dacc0 =
          DA.add_variable dacc result_var (N.unknown machine_width op0)
        in
        SPR.create original_term false dacc0
      in
      let result_invalid =
       fun _ ->
        let dacc0 = DA.add_variable dacc result_var (T.bottom kind) in
        SPR.create_invalid dacc0
      in
      let check_possible_results =
       fun possible_results ->
        if Possible_result.Set_.is_empty possible_results
        then result_invalid ()
        else
          let named =
            match Possible_result.Set_.get_singleton possible_results with
            | Some e -> (
              match e with
              | Possible_result.Simple simple -> Named.create_simple simple
              | Possible_result.Prim prim -> Named.create_prim prim dbg
              | Possible_result.Exactly i -> N.term i)
            | None -> original_term
          in
          let ty, simple_opt =
            let is_ =
              List.filter_map
                (fun possible_result ->
                  match possible_result with
                  | Possible_result.Simple _ -> None
                  | Possible_result.Prim _ -> None
                  | Possible_result.Exactly i -> Some i)
                (Possible_result.Set_.elements possible_results)
            in
            if List.length is_ = Possible_result.Set_.cardinal possible_results
            then N.these (N.Result.Set_.of_list is_)
            else
              match Possible_result.Set_.get_singleton possible_results with
              | Some e -> (
                match e with
                | Possible_result.Simple simple ->
                  T.alias_type_of kind simple, Some simple
                | Possible_result.Prim _ ->
                  let machine_width = DE.machine_width denv in
                  N.unknown machine_width op0, None
                | Possible_result.Exactly _ ->
                  let machine_width = DE.machine_width denv in
                  N.unknown machine_width op0, None)
              | None ->
                let machine_width = DE.machine_width denv in
                N.unknown machine_width op0, None
          in
          let dacc0 = DA.add_variable dacc result_var ty in
          match simple_opt with
          | Some simple ->
            let named0 = Named.create_simple simple in
            SPR.create named0 false dacc0
          | None -> SPR.create named false dacc0
      in
      (fun f__1 f__2 f__3 x__0 ->
        match (x__0 : _ T.meet_shortcut) with
        | T.Known_result x__1 -> f__1 x__1
        | T.Need_meet -> f__2 ()
        | T.Invalid -> f__3 ())
        (fun nums1 ->
          (fun f__1 f__2 f__3 x__0 ->
            match (x__0 : _ T.meet_shortcut) with
            | T.Known_result x__1 -> f__1 x__1
            | T.Need_meet -> f__2 ()
            | T.Invalid -> f__3 ())
            (fun nums2 ->
              if N.ok_to_evaluate denv
              then
                let () = assert (not (N.Lhs.Set_.is_empty nums1)) in
                let () = assert (not (N.Rhs.Set_.is_empty nums2)) in
                if
                  N.Lhs.Set_.cardinal nums1 > max_num_possible_results
                  || N.Rhs.Set_.cardinal nums2 > max_num_possible_results
                then result_unknown ()
                else
                  let all_pairs = N.cross_product nums1 nums2 in
                  let possible_results =
                    N.Pair.Set_.fold
                      (fun pat ->
                        let i1, i2 = pat in
                        fun possible_results ->
                          let machine_width = DE.machine_width denv in
                          match N.op machine_width op0 i1 i2 with
                          | Some result ->
                            Possible_result.Set_.add
                              (Possible_result.Exactly result) possible_results
                          | None -> possible_results)
                      all_pairs Possible_result.Set_.empty
                  in
                  check_possible_results possible_results
              else result_unknown ())
            (fun _ ->
              if N.ok_to_evaluate denv
              then
                let () = assert (not (N.Lhs.Set_.is_empty nums1)) in
                let machine_width = DE.machine_width denv in
                let possible_results =
                  N.Lhs.Set_.fold
                    (fun i possible_results ->
                      match possible_results with
                      | Some possible_results0 -> (
                        match N.op_rhs_unknown machine_width op0 i with
                        | Exactly result ->
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Exactly result)
                               possible_results0)
                        | The_other_side ->
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Simple arg2) possible_results0)
                        | Negation_of_the_other_side ->
                          let standard_int_kind0 =
                            match N.arg_kind with
                            | K.Standard_int_or_float.Tagged_immediate ->
                              K.Standard_int.Tagged_immediate
                            | K.Standard_int_or_float.Naked_immediate ->
                              K.Standard_int.Naked_immediate
                            | K.Standard_int_or_float.Naked_float32 ->
                              Misc.fatal_error
                                "Cannot use [Negation_of_the_other_side] with \
                                 floats; use the float version instead"
                            | K.Standard_int_or_float.Naked_float ->
                              Misc.fatal_error
                                "Cannot use [Negation_of_the_other_side] with \
                                 floats; use the float version instead"
                            | K.Standard_int_or_float.Naked_int8 ->
                              K.Standard_int.Naked_int8
                            | K.Standard_int_or_float.Naked_int16 ->
                              K.Standard_int.Naked_int16
                            | K.Standard_int_or_float.Naked_int32 ->
                              K.Standard_int.Naked_int32
                            | K.Standard_int_or_float.Naked_int64 ->
                              K.Standard_int.Naked_int64
                            | K.Standard_int_or_float.Naked_nativeint ->
                              K.Standard_int.Naked_nativeint
                          in
                          let machine_width0 = DE.machine_width denv in
                          let zero0 =
                            Simple.const_int_of_kind machine_width0
                              (K.Standard_int.to_kind standard_int_kind0)
                              0
                          in
                          let prim =
                            P.Binary
                              ( P.Int_arith
                                  ( standard_int_kind0,
                                    (P.Sub : P.binary_int_arith_op) ),
                                zero0,
                                arg2 )
                          in
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Prim prim) possible_results0)
                        | Bitwise_not_of_the_other_side kind0 ->
                          let prim =
                            P.Unary
                              ( (fun (x__1, x__2) ->
                                  (P.Int_arith (x__1, x__2) : P.unary_primitive))
                                  (kind0, P.Not),
                                arg2 )
                          in
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Prim prim) possible_results0)
                        | Float_negation_of_the_other_side width0 ->
                          let prim =
                            P.Unary
                              ( (fun (x__1, x__2) ->
                                  (P.Float_arith (x__1, x__2)
                                    : P.unary_primitive))
                                  (width0, P.Neg),
                                arg2 )
                          in
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Prim prim) possible_results0)
                        | Cannot_simplify -> None
                        | Invalid -> Some possible_results0)
                      | None -> None)
                    nums1 (Some Possible_result.Set_.empty)
                in
                match possible_results with
                | Some results -> check_possible_results results
                | None -> result_unknown ()
              else result_unknown ())
            (fun _ -> result_invalid ())
            proof2)
        (fun _ ->
          (fun f__1 f__2 f__3 x__0 ->
            match (x__0 : _ T.meet_shortcut) with
            | T.Known_result x__1 -> f__1 x__1
            | T.Need_meet -> f__2 ()
            | T.Invalid -> f__3 ())
            (fun nums2 ->
              if N.ok_to_evaluate denv
              then
                let () = assert (not (N.Rhs.Set_.is_empty nums2)) in
                let machine_width = DE.machine_width denv in
                let possible_results =
                  N.Rhs.Set_.fold
                    (fun i possible_results ->
                      match possible_results with
                      | Some possible_results0 -> (
                        match N.op_lhs_unknown machine_width op0 i with
                        | Exactly result ->
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Exactly result)
                               possible_results0)
                        | The_other_side ->
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Simple arg1) possible_results0)
                        | Negation_of_the_other_side ->
                          let standard_int_kind0 =
                            match N.arg_kind with
                            | K.Standard_int_or_float.Tagged_immediate ->
                              K.Standard_int.Tagged_immediate
                            | K.Standard_int_or_float.Naked_immediate ->
                              K.Standard_int.Naked_immediate
                            | K.Standard_int_or_float.Naked_float32 ->
                              Misc.fatal_error
                                "Cannot use [Negation_of_the_other_side] with \
                                 floats; use the float version instead"
                            | K.Standard_int_or_float.Naked_float ->
                              Misc.fatal_error
                                "Cannot use [Negation_of_the_other_side] with \
                                 floats; use the float version instead"
                            | K.Standard_int_or_float.Naked_int8 ->
                              K.Standard_int.Naked_int8
                            | K.Standard_int_or_float.Naked_int16 ->
                              K.Standard_int.Naked_int16
                            | K.Standard_int_or_float.Naked_int32 ->
                              K.Standard_int.Naked_int32
                            | K.Standard_int_or_float.Naked_int64 ->
                              K.Standard_int.Naked_int64
                            | K.Standard_int_or_float.Naked_nativeint ->
                              K.Standard_int.Naked_nativeint
                          in
                          let machine_width0 = DE.machine_width denv in
                          let zero0 =
                            Simple.const_int_of_kind machine_width0
                              (K.Standard_int.to_kind standard_int_kind0)
                              0
                          in
                          let prim =
                            P.Binary
                              ( P.Int_arith
                                  ( standard_int_kind0,
                                    (P.Sub : P.binary_int_arith_op) ),
                                zero0,
                                arg1 )
                          in
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Prim prim) possible_results0)
                        | Bitwise_not_of_the_other_side kind0 ->
                          let prim =
                            P.Unary
                              ( (fun (x__1, x__2) ->
                                  (P.Int_arith (x__1, x__2) : P.unary_primitive))
                                  (kind0, P.Not),
                                arg1 )
                          in
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Prim prim) possible_results0)
                        | Float_negation_of_the_other_side width0 ->
                          let prim =
                            P.Unary
                              ( (fun (x__1, x__2) ->
                                  (P.Float_arith (x__1, x__2)
                                    : P.unary_primitive))
                                  (width0, P.Neg),
                                arg1 )
                          in
                          Some
                            (Possible_result.Set_.add
                               (Possible_result.Prim prim) possible_results0)
                        | Cannot_simplify -> None
                        | Invalid -> Some possible_results0)
                      | None -> None)
                    nums2 (Some Possible_result.Set_.empty)
                in
                match possible_results with
                | Some results -> check_possible_results results
                | None -> result_unknown ()
              else result_unknown ())
            (fun _ -> result_unknown ())
            (fun _ -> result_invalid ())
            proof2)
        (fun _ -> result_invalid ())
        proof1
  end

module Int_ops_for_binary_arith =
functor
  (I : A.Int_number_kind)
  ->
  struct
    module Lhs = I.Num
    module Rhs = I.Num
    module Result = I.Num

    type op_ = P.binary_int_arith_op

    (** val ok_to_evaluate : DE.t -> bool coq_M **)

    let ok_to_evaluate _ = true

    (** val arg_kind : K.Standard_int_or_float.t **)

    let arg_kind = I.standard_int_or_float_kind

    (** val result_kind : K.t **)

    let result_kind = Flambda_kind.Standard_int_or_float.to_kind arg_kind

    (** val prover_lhs : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
        I.Num.Set_.t Flambda2_types.meet_shortcut coq_M **)

    let prover_lhs = I.unboxed_prover

    (** val prover_rhs : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
        I.Num.Set_.t Flambda2_types.meet_shortcut coq_M **)

    let prover_rhs = I.unboxed_prover

    (** val unknown : Target_system.Machine_width.t -> op_ -> T.t coq_M **)

    let unknown _ _ =
      match arg_kind with
      | K.Standard_int_or_float.Tagged_immediate -> T.any_tagged_immediate
      | K.Standard_int_or_float.Naked_immediate -> T.any_naked_immediate
      | K.Standard_int_or_float.Naked_float32 -> T.any_naked_float32
      | K.Standard_int_or_float.Naked_float -> T.any_naked_float
      | K.Standard_int_or_float.Naked_int8 -> T.any_naked_int8
      | K.Standard_int_or_float.Naked_int16 -> T.any_naked_int16
      | K.Standard_int_or_float.Naked_int32 -> T.any_naked_int32
      | K.Standard_int_or_float.Naked_int64 -> T.any_naked_int64
      | K.Standard_int_or_float.Naked_nativeint -> T.any_naked_nativeint

    (** val these : I.Num.Set_.t -> (T.t * Simple.t option) coq_M **)

    let these s =
      let ty = I.these_unboxed s in
      let simple_opt =
        match I.Num.Set_.get_singleton s with
        | Some i -> Some (Simple.const (I.Num.to_const i))
        | None -> None
      in
      ty, simple_opt

    (** val term : I.Num.t -> Flambda.Named.t coq_M **)

    let term = I.term_unboxed

    module Pair = I.Num.Pair

    (** val cross_product : I.Num.Set_.t -> I.Num.Set_.t -> I.Num.Pair.Set_.t
        coq_M **)

    let cross_product = I.Num.cross_product

    (** val op : Target_system.Machine_width.t -> P.binary_int_arith_op ->
        I.Num.t -> I.Num.t -> I.Num.t option coq_M **)

    let op _ op0 n1 n2 =
      let always_some = fun f -> Some (f n1 n2) in
      (fun f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 x__0 ->
        match (x__0 : P.binary_int_arith_op) with
        | P.Add -> f__1 ()
        | P.Sub -> f__2 ()
        | P.Mul -> f__3 ()
        | P.Div x__1 -> f__4 x__1
        | P.Mod x__1 -> f__5 x__1
        | P.And -> f__6 ()
        | P.Or -> f__7 ()
        | P.Xor -> f__8 ())
        (fun _ -> always_some I.Num.add)
        (fun _ -> always_some I.Num.sub)
        (fun _ -> always_some I.Num.mul)
        (fun t0 ->
          match t0 with
          | Scalar.Signedness.Signed -> I.Num.div n1 n2
          | Scalar.Signedness.Unsigned -> I.Num.unsigned_div n1 n2)
        (fun t0 ->
          match t0 with
          | Scalar.Signedness.Signed -> I.Num.mod_ n1 n2
          | Scalar.Signedness.Unsigned -> I.Num.unsigned_mod n1 n2)
        (fun _ -> always_some I.Num.and_)
        (fun _ -> always_some I.Num.or_)
        (fun _ -> always_some I.Num.xor)
        op0

    type symmetric_op =
      | Add
      | Mul
      | And
      | Or
      | Xor

    module Num = I.Num

    (** val symmetric_op_one_side_unknown : Target_system.Machine_width.t ->
        symmetric_op -> Num.t -> Num.t binary_arith_outcome_for_one_side_only
        coq_M **)

    let symmetric_op_one_side_unknown machine_width op0 this_side =
      match op0 with
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

    (** val op_lhs_unknown : Target_system.Machine_width.t ->
        P.binary_int_arith_op -> Num.t -> Num.t
        binary_arith_outcome_for_one_side_only coq_M **)

    let op_lhs_unknown machine_width op0 rhs =
      (fun f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 x__0 ->
        match (x__0 : P.binary_int_arith_op) with
        | P.Add -> f__1 ()
        | P.Sub -> f__2 ()
        | P.Mul -> f__3 ()
        | P.Div x__1 -> f__4 x__1
        | P.Mod x__1 -> f__5 x__1
        | P.And -> f__6 ()
        | P.Or -> f__7 ()
        | P.Xor -> f__8 ())
        (fun _ -> symmetric_op_one_side_unknown machine_width Add rhs)
        (fun _ ->
          if Num.equal rhs (Num.zero machine_width)
          then The_other_side
          else Cannot_simplify)
        (fun _ -> symmetric_op_one_side_unknown machine_width Mul rhs)
        (fun signedness ->
          if Num.equal rhs (Num.zero machine_width)
          then Invalid
          else if Num.equal rhs (Num.one machine_width)
          then The_other_side
          else if
            Num.equal rhs (Num.minus_one machine_width)
            &&
            match signedness with
            | Scalar.Signedness.Signed -> true
            | Scalar.Signedness.Unsigned -> false
          then Negation_of_the_other_side
          else Cannot_simplify)
        (fun signedness ->
          if Num.equal rhs (Num.zero machine_width)
          then Invalid
          else if Num.equal rhs (Num.one machine_width)
          then Exactly (Num.zero machine_width)
          else if
            Num.equal rhs (Num.minus_one machine_width)
            &&
            match signedness with
            | Scalar.Signedness.Signed -> true
            | Scalar.Signedness.Unsigned -> false
          then Exactly (Num.zero machine_width)
          else Cannot_simplify)
        (fun _ -> symmetric_op_one_side_unknown machine_width And rhs)
        (fun _ -> symmetric_op_one_side_unknown machine_width Or rhs)
        (fun _ -> symmetric_op_one_side_unknown machine_width Xor rhs)
        op0

    (** val op_rhs_unknown : Target_system.Machine_width.t ->
        P.binary_int_arith_op -> Num.t -> Num.t
        binary_arith_outcome_for_one_side_only coq_M **)

    let op_rhs_unknown machine_width op0 lhs =
      (fun f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 x__0 ->
        match (x__0 : P.binary_int_arith_op) with
        | P.Add -> f__1 ()
        | P.Sub -> f__2 ()
        | P.Mul -> f__3 ()
        | P.Div x__1 -> f__4 x__1
        | P.Mod x__1 -> f__5 x__1
        | P.And -> f__6 ()
        | P.Or -> f__7 ()
        | P.Xor -> f__8 ())
        (fun _ -> symmetric_op_one_side_unknown machine_width Add lhs)
        (fun _ ->
          if Num.equal lhs (Num.zero machine_width)
          then Negation_of_the_other_side
          else Cannot_simplify)
        (fun _ -> symmetric_op_one_side_unknown machine_width Mul lhs)
        (fun t0 ->
          match t0 with
          | Scalar.Signedness.Signed -> Cannot_simplify
          | Scalar.Signedness.Unsigned -> Cannot_simplify)
        (fun t0 ->
          match t0 with
          | Scalar.Signedness.Signed -> Cannot_simplify
          | Scalar.Signedness.Unsigned -> Cannot_simplify)
        (fun _ -> symmetric_op_one_side_unknown machine_width And lhs)
        (fun _ -> symmetric_op_one_side_unknown machine_width Or lhs)
        (fun _ -> symmetric_op_one_side_unknown machine_width Xor lhs)
        op0
  end

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

module Int_ops_for_binary_shift =
functor
  (I : A.Int_number_kind)
  ->
  struct
    module Lhs = I.Num
    module Rhs = As_container_types_S (Target_ocaml_int)
    module Result = I.Num

    type op_ = P.int_shift_op

    (** val arg_kind : K.Standard_int_or_float.t **)

    let arg_kind = I.standard_int_or_float_kind

    (** val result_kind : K.t **)

    let result_kind = Flambda_kind.Standard_int_or_float.to_kind arg_kind

    (** val ok_to_evaluate : DE.t -> bool coq_M **)

    let ok_to_evaluate _ = true

    (** val prover_lhs : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
        I.Num.Set_.t Flambda2_types.meet_shortcut coq_M **)

    let prover_lhs = I.unboxed_prover

    (** val prover_rhs : T.Typing_env.t -> T.t -> Target_ocaml_int.Set.t
        T.meet_shortcut coq_M **)

    let prover_rhs = T.meet_naked_immediates

    (** val unknown : Target_system.Machine_width.t -> op_ -> T.t coq_M **)

    let unknown _ _ =
      match arg_kind with
      | K.Standard_int_or_float.Tagged_immediate -> T.any_tagged_immediate
      | K.Standard_int_or_float.Naked_immediate -> T.any_naked_immediate
      | K.Standard_int_or_float.Naked_float32 -> T.any_naked_float32
      | K.Standard_int_or_float.Naked_float -> T.any_naked_float
      | K.Standard_int_or_float.Naked_int8 -> T.any_naked_int8
      | K.Standard_int_or_float.Naked_int16 -> T.any_naked_int16
      | K.Standard_int_or_float.Naked_int32 -> T.any_naked_int32
      | K.Standard_int_or_float.Naked_int64 -> T.any_naked_int64
      | K.Standard_int_or_float.Naked_nativeint -> T.any_naked_nativeint

    (** val these : I.Num.Set_.t -> (T.t * Simple.t option) coq_M **)

    let these s =
      let ty = I.these_unboxed s in
      let simple_opt =
        match I.Num.Set_.get_singleton s with
        | Some i -> Some (Simple.const (I.Num.to_const i))
        | None -> None
      in
      ty, simple_opt

    (** val term : I.Num.t -> Flambda.Named.t coq_M **)

    let term = I.term_unboxed

    module Pair = struct
      type t = Lhs.t * Rhs.t

      module Set_ = struct
        type elt = t

        type t = elt list

        (** val empty : t **)

        let empty = []

        (** val add : elt -> t -> t coq_M **)

        let add elt0 s = elt0 :: s

        (** val fold : (elt -> 'a1 -> 'a1 coq_M) -> t -> 'a1 -> 'a1 coq_M **)

        let rec fold f s acc =
          match s with
          | [] -> acc
          | elt0 :: rest ->
            let acc0 = fold f rest acc in
            f elt0 acc0
      end
    end

    (** val cross_product : Lhs.Set_.t -> Rhs.Set_.t -> Pair.Set_.t coq_M **)

    let cross_product set1 set2 =
      Lhs.Set_.fold
        (fun elt1 result ->
          Rhs.Set_.fold
            (fun elt2 result0 -> Pair.Set_.add (elt1, elt2) result0)
            set2 result)
        set1 Pair.Set_.empty

    module Num = I.Num

    (** val op : Target_system.Machine_width.t -> P.int_shift_op -> Num.t ->
        Target_ocaml_int.t -> Num.t option coq_M **)

    let op _ op0 n1 n2 =
      let always_some = fun f -> Some (f n1 n2) in
      match op0 with
      | P.Lsl -> always_some Num.shift_left
      | P.Lsr -> always_some Num.shift_right_logical
      | P.Asr -> always_some Num.shift_right

    (** val op_lhs_unknown : Target_system.Machine_width.t -> P.int_shift_op ->
        Target_ocaml_int.t -> Num.t binary_arith_outcome_for_one_side_only coq_M
        **)

    let op_lhs_unknown machine_width op0 rhs =
      let rhs0 = rhs in
      match op0 with
      | P.Lsl ->
        if Target_ocaml_int.equal rhs0 (Target_ocaml_int.zero machine_width)
        then The_other_side
        else Cannot_simplify
      | P.Lsr ->
        if Target_ocaml_int.equal rhs0 (Target_ocaml_int.zero machine_width)
        then The_other_side
        else Cannot_simplify
      | P.Asr ->
        if Target_ocaml_int.equal rhs0 (Target_ocaml_int.zero machine_width)
        then The_other_side
        else Cannot_simplify

    (** val op_rhs_unknown : Target_system.Machine_width.t -> P.int_shift_op ->
        Num.t -> Num.t binary_arith_outcome_for_one_side_only coq_M **)

    let op_rhs_unknown machine_width op0 lhs =
      match op0 with
      | P.Lsl ->
        if Num.equal lhs (Num.zero machine_width)
        then Exactly (Num.zero machine_width)
        else Cannot_simplify
      | P.Lsr ->
        if Num.equal lhs (Num.zero machine_width)
        then Exactly (Num.zero machine_width)
        else Cannot_simplify
      | P.Asr ->
        if Num.equal lhs (Num.zero machine_width)
        then Exactly (Num.zero machine_width)
        else if Num.equal lhs (Num.minus_one machine_width)
        then Exactly (Num.minus_one machine_width)
        else Cannot_simplify
  end

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

module Int_ops_for_binary_comp =
functor
  (I : A.Int_number_kind)
  ->
  struct
    module Lhs = I.Num
    module Rhs = I.Num
    module Result = As_container_types_S (Target_ocaml_int)

    type op_ = P.signed_or_unsigned P.comparison_behaviour

    (** val arg_kind : K.Standard_int_or_float.t **)

    let arg_kind = I.standard_int_or_float_kind

    (** val result_kind : K.t **)

    let result_kind = K.naked_immediate

    (** val ok_to_evaluate : DE.t -> bool coq_M **)

    let ok_to_evaluate _ = true

    (** val prover_lhs : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
        I.Num.Set_.t Flambda2_types.meet_shortcut coq_M **)

    let prover_lhs = I.unboxed_prover

    (** val prover_rhs : Flambda2_types.Typing_env.t -> Flambda2_types.t ->
        I.Num.Set_.t Flambda2_types.meet_shortcut coq_M **)

    let prover_rhs = I.unboxed_prover

    (** val unknown : Target_system.Machine_width.t -> op_ -> T.t coq_M **)

    let unknown machine_width = function
      | P.Yielding_bool _ ->
        T.these_naked_immediates (Target_ocaml_int.all_bools machine_width)
      | P.Yielding_int_like_compare_functions _ ->
        T.these_naked_immediates
          (Target_ocaml_int.zero_one_and_minus_one machine_width)

    (** val these : Target_ocaml_int.Set.t -> (T.t * Simple.t option) coq_M **)

    let these s =
      let ty = T.these_naked_immediates s in
      let simple_opt =
        match Target_ocaml_int.Set.get_singleton s with
        | Some i -> Some (Simple.const (Reg_width_const.naked_immediate i))
        | None -> None
      in
      ty, simple_opt

    (** val term : Target_ocaml_int.t -> Named.t coq_M **)

    let term imm =
      Named.create_simple (Simple.const (Reg_width_const.naked_immediate imm))

    module Pair = I.Num.Pair

    (** val cross_product : I.Num.Set_.t -> I.Num.Set_.t -> I.Num.Pair.Set_.t
        coq_M **)

    let cross_product = I.Num.cross_product

    module Num = I.Num

    (** val op : Target_system.Machine_width.t -> P.signed_or_unsigned
        P.comparison_behaviour -> Num.t -> Num.t -> Target_ocaml_int.t option
        coq_M **)

    let op machine_width op0 n1 n2 =
      match op0 with
      | P.Yielding_bool op1 ->
        let bool = fun b -> Target_ocaml_int.bool machine_width b in
        (fun f__1 f__2 f__3 f__4 f__5 f__6 x__0 ->
          match (x__0 : _ P.comparison) with
          | P.Eq -> f__1 ()
          | P.Neq -> f__2 ()
          | P.Lt x__1 -> f__3 x__1
          | P.Gt x__1 -> f__4 x__1
          | P.Le x__1 -> f__5 x__1
          | P.Ge x__1 -> f__6 x__1)
          (fun _ -> Some (bool (Num.compare n1 n2 = 0)))
          (fun _ -> Some (bool (Num.compare n1 n2 <> 0)))
          (fun s ->
            match s with
            | P.Signed -> Some (bool (Num.compare n1 n2 < 0))
            | P.Unsigned -> Some (bool (Num.compare_unsigned n1 n2 < 0)))
          (fun s ->
            match s with
            | P.Signed -> Some (bool (Num.compare n1 n2 > 0))
            | P.Unsigned -> Some (bool (Num.compare_unsigned n1 n2 > 0)))
          (fun s ->
            match s with
            | P.Signed -> Some (bool (Num.compare n1 n2 <= 0))
            | P.Unsigned -> Some (bool (Num.compare_unsigned n1 n2 <= 0)))
          (fun s ->
            match s with
            | P.Signed -> Some (bool (Num.compare n1 n2 >= 0))
            | P.Unsigned -> Some (bool (Num.compare_unsigned n1 n2 >= 0)))
          op1
      | P.Yielding_int_like_compare_functions signed_or_unsigned -> (
        match signed_or_unsigned with
        | P.Signed ->
          let int = fun i -> Target_ocaml_int.of_int machine_width i in
          let c = Num.compare n1 n2 in
          if c < 0
          then Some (int (-1))
          else if c = 0
          then Some (int 0)
          else Some (int 1)
        | P.Unsigned ->
          let int = fun i -> Target_ocaml_int.of_int machine_width i in
          let c = Num.compare_unsigned n1 n2 in
          if c < 0
          then Some (int (-1))
          else if c = 0
          then Some (int 0)
          else Some (int 1))

    (** val op_lhs_unknown : Target_system.Machine_width.t -> op_ -> Num.t ->
        Target_ocaml_int.t binary_arith_outcome_for_one_side_only coq_M **)

    let op_lhs_unknown _ _ _ = Cannot_simplify

    (** val op_rhs_unknown : Target_system.Machine_width.t -> op_ -> Num.t ->
        Target_ocaml_int.t binary_arith_outcome_for_one_side_only coq_M **)

    let op_rhs_unknown _ _ _ = Cannot_simplify
  end

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

module type Float_ops_for_binary_arith_gen_FP = sig
  module F : Numeric_types.Float_by_bit_pattern_

  val width : Flambda_primitive.float_bitwidth

  val arg_kind : K.Standard_int_or_float.t

  val result_kind : Flambda_kind.t

  val prover : T.Typing_env.t -> T.t -> F.Set_.t T.meet_shortcut coq_M

  val unknown : T.t

  val these : F.Set_.t -> T.t coq_M

  val const : F.t -> Const.t coq_M
end

module Float_ops_for_binary_arith_gen =
functor
  (FP : Float_ops_for_binary_arith_gen_FP)
  ->
  struct
    module F = FP.F
    module Lhs = F
    module Rhs = F
    module Result = F

    type op_ = P.binary_float_arith_op

    (** val arg_kind : K.Standard_int_or_float.t **)

    let arg_kind = FP.arg_kind

    (** val result_kind : K.t **)

    let result_kind = FP.result_kind

    (** val ok_to_evaluate : DE.t -> bool coq_M **)

    let ok_to_evaluate = DE.propagating_float_consts

    (** val prover_lhs : T.Typing_env.t -> T.t -> FP.F.Set_.t T.meet_shortcut
        coq_M **)

    let prover_lhs = FP.prover

    (** val prover_rhs : T.Typing_env.t -> T.t -> FP.F.Set_.t T.meet_shortcut
        coq_M **)

    let prover_rhs = FP.prover

    (** val unknown : Target_system.Machine_width.t -> op_ -> T.t coq_M **)

    let unknown _ _ = FP.unknown

    (** val these : F.Set_.t -> (T.t * Simple.t option) coq_M **)

    let these s =
      let ty = FP.these s in
      let simple_opt =
        match F.Set_.get_singleton s with
        | Some f -> Some (Simple.const (FP.const f))
        | None -> None
      in
      ty, simple_opt

    (** val term : F.t -> Named.t coq_M **)

    let term f = Named.create_simple (Simple.const (FP.const f))

    module Pair = F.Pair

    (** val cross_product : F.Set_.t -> F.Set_.t -> F.Pair.Set_.t coq_M **)

    let cross_product = F.cross_product

    (** val op : Target_system.Machine_width.t -> op_ -> F.t -> F.t -> F.t
        option coq_M **)

    let op _ op0 n1 n2 =
      let always_some = fun f -> Some (f n1 n2) in
      (fun f__1 f__2 f__3 f__4 x__0 ->
        match (x__0 : P.binary_float_arith_op) with
        | P.Add -> f__1 ()
        | P.Sub -> f__2 ()
        | P.Mul -> f__3 ()
        | P.Div -> f__4 ())
        (fun _ -> always_some F.IEEE_semantics.add)
        (fun _ -> always_some F.IEEE_semantics.sub)
        (fun _ -> always_some F.IEEE_semantics.mul)
        (fun _ -> always_some F.IEEE_semantics.div)
        op0

    type symmetric_op =
      | Add
      | Mul

    (** val symmetric_op_one_side_unknown : symmetric_op -> F.t -> F.t
        binary_arith_outcome_for_one_side_only coq_M **)

    let symmetric_op_one_side_unknown op0 this_side =
      match op0 with
      | Add -> Cannot_simplify
      | Mul ->
        if F.equal this_side F.one
        then The_other_side
        else if F.equal this_side F.minus_one
        then Float_negation_of_the_other_side FP.width
        else Cannot_simplify

    (** val op_lhs_unknown : Target_system.Machine_width.t -> op_ -> F.t -> F.t
        binary_arith_outcome_for_one_side_only coq_M **)

    let op_lhs_unknown _ op0 rhs =
      (fun f__1 f__2 f__3 f__4 x__0 ->
        match (x__0 : P.binary_float_arith_op) with
        | P.Add -> f__1 ()
        | P.Sub -> f__2 ()
        | P.Mul -> f__3 ()
        | P.Div -> f__4 ())
        (fun _ -> symmetric_op_one_side_unknown Add rhs)
        (fun _ -> Cannot_simplify)
        (fun _ -> symmetric_op_one_side_unknown Mul rhs)
        (fun _ ->
          if F.equal rhs F.one
          then The_other_side
          else if F.equal rhs F.minus_one
          then Float_negation_of_the_other_side FP.width
          else Cannot_simplify)
        op0

    (** val op_rhs_unknown : Target_system.Machine_width.t -> op_ -> F.t -> F.t
        binary_arith_outcome_for_one_side_only coq_M **)

    let op_rhs_unknown _ op0 lhs =
      (fun f__1 f__2 f__3 f__4 x__0 ->
        match (x__0 : P.binary_float_arith_op) with
        | P.Add -> f__1 ()
        | P.Sub -> f__2 ()
        | P.Mul -> f__3 ()
        | P.Div -> f__4 ())
        (fun _ -> symmetric_op_one_side_unknown Add lhs)
        (fun _ -> Cannot_simplify)
        (fun _ -> symmetric_op_one_side_unknown Mul lhs)
        (fun _ -> Cannot_simplify)
        op0
  end

module Float_ops_for_binary_arith_FP = struct
  module F = Numeric_types.Float_by_bit_pattern

  (** val width : Flambda_primitive.float_bitwidth **)

  let width = Flambda_primitive.Float64

  (** val arg_kind : K.Standard_int_or_float.t **)

  let arg_kind = K.Standard_int_or_float.Naked_float

  (** val result_kind : Flambda_kind.t **)

  let result_kind = K.naked_float

  (** val prover : T.Typing_env.t -> T.t ->
      Numeric_types.Float_by_bit_pattern.Set.t T.meet_shortcut coq_M **)

  let prover = T.meet_naked_floats

  (** val unknown : T.t **)

  let unknown = T.any_naked_float

  (** val these : Numeric_types.Float_by_bit_pattern.Set.t -> T.t coq_M **)

  let these = T.these_naked_floats

  (** val const : Numeric_types.Float_by_bit_pattern.t -> Reg_width_const.t
      coq_M **)

  let const = Reg_width_const.naked_float
end

module Float_ops_for_binary_arith =
  Float_ops_for_binary_arith_gen (Float_ops_for_binary_arith_FP)

module Float32_ops_for_binary_arith_FP = struct
  module F = Numeric_types.Float32_by_bit_pattern

  (** val width : Flambda_primitive.float_bitwidth **)

  let width = Flambda_primitive.Float32

  (** val arg_kind : K.Standard_int_or_float.t **)

  let arg_kind = K.Standard_int_or_float.Naked_float32

  (** val result_kind : Flambda_kind.t **)

  let result_kind = K.naked_float32

  (** val prover : T.Typing_env.t -> T.t ->
      Numeric_types.Float32_by_bit_pattern.Set.t T.meet_shortcut coq_M **)

  let prover = T.meet_naked_float32s

  (** val unknown : T.t **)

  let unknown = T.any_naked_float32

  (** val these : Numeric_types.Float32_by_bit_pattern.Set.t -> T.t coq_M **)

  let these = T.these_naked_float32s

  (** val const : Numeric_types.Float32_by_bit_pattern.t -> Reg_width_const.t
      coq_M **)

  let const = Reg_width_const.naked_float32
end

module Float32_ops_for_binary_arith =
  Float_ops_for_binary_arith_gen (Float32_ops_for_binary_arith_FP)
module Binary_float_arith = Binary_arith_like (Float_ops_for_binary_arith)
module Binary_float32_arith = Binary_arith_like (Float32_ops_for_binary_arith)

module type Float_ops_for_binary_comp_gen_FP = sig
  module F : Numeric_types.Float_by_bit_pattern_

  val arg_kind : K.Standard_int_or_float.t

  val prover : T.Typing_env.t -> T.t -> F.Set_.t T.meet_shortcut coq_M
end

module Float_ops_for_binary_comp_gen =
functor
  (FP : Float_ops_for_binary_comp_gen_FP)
  ->
  struct
    module F = FP.F
    module Lhs = F
    module Rhs = F
    module Result = As_container_types_S (Target_ocaml_int)

    type op_ = unit P.comparison_behaviour

    (** val arg_kind : K.Standard_int_or_float.t **)

    let arg_kind = FP.arg_kind

    (** val result_kind : K.t **)

    let result_kind = K.naked_immediate

    (** val ok_to_evaluate : DE.t -> bool coq_M **)

    let ok_to_evaluate = DE.propagating_float_consts

    (** val prover_lhs : T.Typing_env.t -> T.t -> FP.F.Set_.t T.meet_shortcut
        coq_M **)

    let prover_lhs = FP.prover

    (** val prover_rhs : T.Typing_env.t -> T.t -> FP.F.Set_.t T.meet_shortcut
        coq_M **)

    let prover_rhs = FP.prover

    (** val unknown : Target_system.Machine_width.t -> op_ -> T.t coq_M **)

    let unknown machine_width = function
      | P.Yielding_bool _ ->
        T.these_naked_immediates (Target_ocaml_int.all_bools machine_width)
      | P.Yielding_int_like_compare_functions u ->
        let () = u in
        T.these_naked_immediates
          (Target_ocaml_int.zero_one_and_minus_one machine_width)

    (** val these : Target_ocaml_int.Set.t -> (T.t * Simple.t option) coq_M **)

    let these s =
      let ty = T.these_naked_immediates s in
      let simple_opt =
        match Target_ocaml_int.Set.get_singleton s with
        | Some i -> Some (Simple.const (Reg_width_const.naked_immediate i))
        | None -> None
      in
      ty, simple_opt

    (** val term : Target_ocaml_int.t -> Named.t coq_M **)

    let term imm =
      Named.create_simple (Simple.const (Reg_width_const.naked_immediate imm))

    module Pair = F.Pair

    (** val cross_product : F.Set_.t -> F.Set_.t -> F.Pair.Set_.t coq_M **)

    let cross_product = F.cross_product

    (** val op : Target_system.Machine_width.t -> op_ -> F.t -> F.t ->
        Target_ocaml_int.t option coq_M **)

    let op machine_width op0 n1 n2 =
      match op0 with
      | P.Yielding_bool op1 ->
        let has_nan = F.is_any_nan n1 || F.is_any_nan n2 in
        let bool = fun b -> Target_ocaml_int.bool machine_width b in
        (fun f__1 f__2 f__3 f__4 f__5 f__6 x__0 ->
          match (x__0 : _ P.comparison) with
          | P.Eq -> f__1 ()
          | P.Neq -> f__2 ()
          | P.Lt x__1 -> f__3 x__1
          | P.Gt x__1 -> f__4 x__1
          | P.Le x__1 -> f__5 x__1
          | P.Ge x__1 -> f__6 x__1)
          (fun _ -> Some (bool (F.IEEE_semantics.equal n1 n2)))
          (fun _ -> Some (bool (not (F.IEEE_semantics.equal n1 n2))))
          (fun u ->
            let () = u in
            if has_nan
            then Some (bool false)
            else Some (bool (F.IEEE_semantics.compare n1 n2 < 0)))
          (fun u ->
            let () = u in
            if has_nan
            then Some (bool false)
            else Some (bool (F.IEEE_semantics.compare n1 n2 > 0)))
          (fun u ->
            let () = u in
            if has_nan
            then Some (bool false)
            else Some (bool (F.IEEE_semantics.compare n1 n2 <= 0)))
          (fun u ->
            let () = u in
            if has_nan
            then Some (bool false)
            else Some (bool (F.IEEE_semantics.compare n1 n2 >= 0)))
          op1
      | P.Yielding_int_like_compare_functions u ->
        let () = u in
        let int = fun i -> Target_ocaml_int.of_int machine_width i in
        let c = F.IEEE_semantics.compare n1 n2 in
        if c < 0
        then Some (int (-1))
        else if c = 0
        then Some (int 0)
        else Some (int 1)

    (** val result_of_comparison_with_nan : Target_system.Machine_width.t ->
        unit P.comparison -> Target_ocaml_int.t
        binary_arith_outcome_for_one_side_only coq_M **)

    let result_of_comparison_with_nan machine_width op0 =
      (fun f__1 f__2 f__3 f__4 f__5 f__6 x__0 ->
        match (x__0 : _ P.comparison) with
        | P.Eq -> f__1 ()
        | P.Neq -> f__2 ()
        | P.Lt x__1 -> f__3 x__1
        | P.Gt x__1 -> f__4 x__1
        | P.Le x__1 -> f__5 x__1
        | P.Ge x__1 -> f__6 x__1)
        (fun _ -> Exactly (Target_ocaml_int.bool_false machine_width))
        (fun _ -> Exactly (Target_ocaml_int.bool_true machine_width))
        (fun u ->
          let () = u in
          Exactly (Target_ocaml_int.bool_false machine_width))
        (fun u ->
          let () = u in
          Exactly (Target_ocaml_int.bool_false machine_width))
        (fun u ->
          let () = u in
          Exactly (Target_ocaml_int.bool_false machine_width))
        (fun u ->
          let () = u in
          Exactly (Target_ocaml_int.bool_false machine_width))
        op0

    (** val op_lhs_unknown : Target_system.Machine_width.t -> op_ -> F.t ->
        Target_ocaml_int.t binary_arith_outcome_for_one_side_only coq_M **)

    let op_lhs_unknown machine_width op0 rhs =
      match op0 with
      | P.Yielding_bool op1 ->
        if F.is_any_nan rhs
        then result_of_comparison_with_nan machine_width op1
        else Cannot_simplify
      | P.Yielding_int_like_compare_functions u ->
        let () = u in
        Cannot_simplify

    (** val op_rhs_unknown : Target_system.Machine_width.t -> op_ -> F.t ->
        Target_ocaml_int.t binary_arith_outcome_for_one_side_only coq_M **)

    let op_rhs_unknown machine_width op0 lhs =
      match op0 with
      | P.Yielding_bool op1 ->
        if F.is_any_nan lhs
        then result_of_comparison_with_nan machine_width op1
        else Cannot_simplify
      | P.Yielding_int_like_compare_functions u ->
        let () = u in
        Cannot_simplify
  end

module Float_ops_for_binary_comp_FP = struct
  module F = Numeric_types.Float_by_bit_pattern

  (** val arg_kind : K.Standard_int_or_float.t **)

  let arg_kind = K.Standard_int_or_float.Naked_float

  (** val prover : T.Typing_env.t -> T.t ->
      Numeric_types.Float_by_bit_pattern.Set.t T.meet_shortcut coq_M **)

  let prover = T.meet_naked_floats
end

module Float_ops_for_binary_comp =
  Float_ops_for_binary_comp_gen (Float_ops_for_binary_comp_FP)

module Float32_ops_for_binary_comp_FP = struct
  module F = Numeric_types.Float32_by_bit_pattern

  (** val arg_kind : K.Standard_int_or_float.t **)

  let arg_kind = K.Standard_int_or_float.Naked_float32

  (** val prover : T.Typing_env.t -> T.t ->
      Numeric_types.Float32_by_bit_pattern.Set.t T.meet_shortcut coq_M **)

  let prover = T.meet_naked_float32s
end

module Float32_ops_for_binary_comp =
  Float_ops_for_binary_comp_gen (Float32_ops_for_binary_comp_FP)
module Binary_float_comp = Binary_arith_like (Float_ops_for_binary_comp)
module Binary_float32_comp = Binary_arith_like (Float32_ops_for_binary_comp)

(** val simplify_phys_equal : P.equality_comparison -> DA.t -> Named.t ->
    Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t -> Bound_var.t -> SPR.t
    coq_M **)

let simplify_phys_equal op0 dacc original_term _ _ arg1_ty _ arg2_ty result_var
    =
  let typing_env = DA.typing_env dacc in
  let machine_width = DE.machine_width (DA.denv dacc) in
  match T.prove_physical_equality typing_env arg1_ty arg2_ty with
  | T.Proved bool ->
    let result = match op0 with P.Eq -> bool | P.Neq -> not bool in
    let dacc0 =
      DA.add_variable dacc result_var
        (T.this_naked_immediate (Target_ocaml_int.bool machine_width result))
    in
    SPR.create
      (Named.create_simple (Simple.untagged_const_bool machine_width result))
      false dacc0
  | T.Unknown ->
    let dacc0 =
      DA.add_variable dacc result_var
        (T.these_naked_immediates (Target_ocaml_int.all_bools machine_width))
    in
    SPR.create original_term false dacc0

(** val simplify_array_load : P.Array_kind.t -> P.Array_load_kind.t ->
    Mutability.t -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t ->
    Simple.t -> T.t -> Bound_var.t -> SPR.t coq_M **)

let simplify_array_load array_kind array_load_kind mutability dacc _ dbg array
    array_ty index index_ty result_var =
  let result_kind0 =
    match array_load_kind with
    | P.Array_load_kind.Immediates -> K.value
    | P.Array_load_kind.Gc_ignorable_values -> K.value
    | P.Array_load_kind.Values -> K.value
    | P.Array_load_kind.Naked_floats -> K.naked_float
    | P.Array_load_kind.Naked_float32s -> K.naked_float32
    | P.Array_load_kind.Naked_ints -> K.naked_immediate
    | P.Array_load_kind.Naked_int8s -> K.naked_int8
    | P.Array_load_kind.Naked_int16s -> K.naked_int16
    | P.Array_load_kind.Naked_int32s -> K.naked_int32
    | P.Array_load_kind.Naked_int64s -> K.naked_int64
    | P.Array_load_kind.Naked_nativeints -> K.naked_nativeint
    | P.Array_load_kind.Naked_vec128s -> K.naked_vec128
    | P.Array_load_kind.Naked_vec256s -> K.naked_vec256
    | P.Array_load_kind.Naked_vec512s -> K.naked_vec512
    | P.Array_load_kind.Naked_masks -> K.naked_mask
  in
  let array_kind0 =
    Simplify_common.specialise_array_kind dacc array_kind array_ty
  in
  match array_kind0 with
  | Or_bottom.Ok array_kind1 -> (
    let prim =
      P.Binary
        (P.Array_load (array_kind1, array_load_kind, mutability), array, index)
    in
    let return_given_type =
     fun ty try_reify ->
      let named = Named.create_prim prim dbg in
      let dacc0 = DA.add_variable dacc result_var ty in
      SPR.create named try_reify dacc0
    in
    let contents_unknown =
     fun _ -> return_given_type (T.unknown (P.result_kind' prim)) false
    in
    match T.prove_is_immutable_array (DA.typing_env dacc) array_ty with
    | T.Proved t0 -> (
      let elt_kind, fields, _ = t0 in
      match elt_kind with
      | Or_unknown_or_bottom.Unknown -> contents_unknown ()
      | Or_unknown_or_bottom.Ok elt_kind0 -> (
        if not (K.equal (K.With_subkind.kind elt_kind0) result_kind0)
        then contents_unknown ()
        else
          match
            T.prove_equals_tagged_immediates (DA.typing_env dacc) index_ty
          with
          | T.Proved imms -> (
            match Target_ocaml_int.Set.get_singleton imms with
            | Some imm ->
              let machine_width = DE.machine_width (DA.denv dacc) in
              if
                Target_ocaml_int.( < ) imm (Target_ocaml_int.zero machine_width)
                || Target_ocaml_int.( >= ) imm
                     (Target_ocaml_int.of_int machine_width
                        (Array.length fields))
              then SPR.create_invalid dacc
              else
                return_given_type
                  (Array.get fields (Target_ocaml_int.to_int imm))
                  true
            | None -> contents_unknown ())
          | T.Unknown -> contents_unknown ())
      | Or_unknown_or_bottom.Bottom -> contents_unknown ())
    | T.Unknown -> contents_unknown ())
  | Or_bottom.Bottom ->
    let ty = T.bottom result_kind0 in
    let dacc0 = DA.add_variable dacc result_var ty in
    SPR.create_invalid dacc0

(** val simplify_string_or_bigstring_load : P.string_like_value ->
    P.string_accessor_width -> P.t -> DA.t -> Named.t -> Debuginfo.t -> Simple.t
    -> T.t -> Simple.t -> T.t -> Bound_var.t -> SPR.t coq_M **)

let simplify_string_or_bigstring_load _ _ original_prim dacc original_term _ _ _
    _ _ result_var =
  SPR.create_unknown dacc result_var
    (P.result_kind' original_prim)
    original_term

(** val simplify_bigarray_load : P.num_dimensions -> P.Bigarray_kind.t ->
    P.Bigarray_layout.t -> P.t -> DA.t -> Named.t -> Debuginfo.t -> Simple.t ->
    T.t -> Simple.t -> T.t -> Bound_var.t -> SPR.t coq_M **)

let simplify_bigarray_load _ _ _ original_prim dacc original_term _ _ _ _ _
    result_var =
  SPR.create_unknown dacc result_var
    (P.result_kind' original_prim)
    original_term

(** val simplify_bigarray_get_alignment : int -> P.t -> DA.t -> Named.t ->
    Debuginfo.t -> Simple.t -> T.t -> Simple.t -> T.t -> Bound_var.t -> SPR.t
    coq_M **)

let simplify_bigarray_get_alignment _ original_prim dacc original_term _ _ _ _ _
    result_var =
  SPR.create_unknown dacc result_var
    (P.result_kind' original_prim)
    original_term

(** val simplify_atomic_load : P.t -> DA.t -> Named.t -> Debuginfo.t -> Simple.t
    -> T.t -> Simple.t -> T.t -> Bound_var.t -> SPR.t coq_M **)

let simplify_atomic_load original_prim dacc original_term _ _ _ _ _ result_var =
  SPR.create_unknown dacc result_var
    (P.result_kind' original_prim)
    original_term

(** val simplify_block_set : P.Block_access_kind.t -> P.Init_or_assign.t ->
    Target_ocaml_int.t -> DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t ->
    Simple.t -> T.t -> Bound_var.t -> SPR.t coq_M **)

let simplify_block_set _ _ _ dacc original_term _ _ _ _ _ result_var =
  SPR.create_unit dacc result_var original_term

(** val simplify_poke : DA.t -> Named.t -> Debuginfo.t -> Simple.t -> T.t ->
    Simple.t -> T.t -> Bound_var.t -> SPR.t coq_M **)

let simplify_poke dacc original_term _ _ _ _ _ result_var =
  SPR.create_unit dacc result_var original_term

(** val simplify_read_offset : P.t -> DA.t -> Named.t -> Debuginfo.t -> Simple.t
    -> T.t -> Simple.t -> T.t -> Bound_var.t -> SPR.t coq_M **)

let simplify_read_offset original_prim dacc original_term _ _ _ _ _ result_var =
  SPR.create_unknown dacc result_var
    (P.result_kind' original_prim)
    original_term

(** val simplify_binary_primitive0 : DA.t -> P.t -> P.binary_primitive ->
    Simple.t -> T.t -> Simple.t -> T.t -> Debuginfo.t -> Bound_var.t -> SPR.t
    coq_M **)

let simplify_binary_primitive0 dacc original_prim prim arg1 arg1_ty arg2 arg2_ty
    dbg result_var =
  let original_term = Named.create_prim original_prim dbg in
  let simplifier =
    (fun f__1
      f__2
      f__3
      f__4
      f__5
      f__6
      f__7
      f__8
      f__9
      f__10
      f__11
      f__12
      f__13
      f__14
      x__0
    ->
      match (x__0 : P.binary_primitive) with
      | P.Block_set { kind = x__1; init = x__2; field = x__3 } ->
        f__1 x__1 x__2 x__3
      | P.Array_load (x__1, x__2, x__3) -> f__2 x__1 x__2 x__3
      | P.String_or_bigstring_load (x__1, x__2) -> f__3 x__1 x__2
      | P.Bigarray_load (x__1, x__2, x__3) -> f__4 x__1 x__2 x__3
      | P.Phys_equal x__1 -> f__5 x__1
      | P.Int_arith (x__1, x__2) -> f__6 x__1 x__2
      | P.Int_shift (x__1, x__2) -> f__7 x__1 x__2
      | P.Int_comp (x__1, x__2) -> f__8 x__1 x__2
      | P.Float_arith (x__1, x__2) -> f__9 x__1 x__2
      | P.Float_comp (x__1, x__2) -> f__10 x__1 x__2
      | P.Bigarray_get_alignment x__1 -> f__11 x__1
      | P.Atomic_load (x__1, x__2) -> f__12 x__1 x__2
      | P.Poke x__1 -> f__13 x__1
      | P.Read_offset (x__1, x__2) -> f__14 x__1 x__2)
      (fun kind init field -> simplify_block_set kind init field)
      (fun array_kind width0 mutability ->
        simplify_array_load array_kind width0 mutability)
      (fun string_like_value string_accessor_width ->
        simplify_string_or_bigstring_load string_like_value
          string_accessor_width original_prim)
      (fun num_dimensions bigarray_kind bigarray_layout ->
        simplify_bigarray_load num_dimensions bigarray_kind bigarray_layout
          original_prim)
      (fun op0 -> simplify_phys_equal op0)
      (fun kind op0 ->
        match kind with
        | Flambda_kind.Standard_int.Tagged_immediate ->
          Binary_int_arith_tagged_immediate.simplify op0
        | Flambda_kind.Standard_int.Naked_immediate ->
          Binary_int_arith_naked_immediate.simplify op0
        | Flambda_kind.Standard_int.Naked_int8 ->
          Binary_int_arith_int8.simplify op0
        | Flambda_kind.Standard_int.Naked_int16 ->
          Binary_int_arith_int16.simplify op0
        | Flambda_kind.Standard_int.Naked_int32 ->
          Binary_int_arith_int32.simplify op0
        | Flambda_kind.Standard_int.Naked_int64 ->
          Binary_int_arith_int64.simplify op0
        | Flambda_kind.Standard_int.Naked_nativeint ->
          Binary_int_arith_nativeint.simplify op0)
      (fun kind op0 ->
        match kind with
        | Flambda_kind.Standard_int.Tagged_immediate ->
          Binary_int_shift_tagged_immediate.simplify op0
        | Flambda_kind.Standard_int.Naked_immediate ->
          Binary_int_shift_naked_immediate.simplify op0
        | Flambda_kind.Standard_int.Naked_int8 ->
          Binary_int_shift_int8.simplify op0
        | Flambda_kind.Standard_int.Naked_int16 ->
          Binary_int_shift_int16.simplify op0
        | Flambda_kind.Standard_int.Naked_int32 ->
          Binary_int_shift_int32.simplify op0
        | Flambda_kind.Standard_int.Naked_int64 ->
          Binary_int_shift_int64.simplify op0
        | Flambda_kind.Standard_int.Naked_nativeint ->
          Binary_int_shift_nativeint.simplify op0)
      (fun kind op0 ->
        match kind with
        | Flambda_kind.Standard_int.Tagged_immediate ->
          Binary_int_comp_tagged_immediate.simplify op0
        | Flambda_kind.Standard_int.Naked_immediate ->
          Binary_int_comp_naked_immediate.simplify op0
        | Flambda_kind.Standard_int.Naked_int8 ->
          Binary_int_comp_int8.simplify op0
        | Flambda_kind.Standard_int.Naked_int16 ->
          Binary_int_comp_int16.simplify op0
        | Flambda_kind.Standard_int.Naked_int32 ->
          Binary_int_comp_int32.simplify op0
        | Flambda_kind.Standard_int.Naked_int64 ->
          Binary_int_comp_int64.simplify op0
        | Flambda_kind.Standard_int.Naked_nativeint ->
          Binary_int_comp_nativeint.simplify op0)
      (fun f op0 ->
        match f with
        | P.Float32 -> Binary_float32_arith.simplify op0
        | P.Float64 -> Binary_float_arith.simplify op0)
      (fun f op0 ->
        match f with
        | P.Float32 -> Binary_float32_comp.simplify op0
        | P.Float64 -> Binary_float_comp.simplify op0)
      (fun align -> simplify_bigarray_get_alignment align original_prim)
      (fun _ _ -> simplify_atomic_load original_prim)
      (fun _ -> simplify_poke)
      (fun _ _ -> simplify_read_offset original_prim)
      prim
  in
  simplifier dacc original_term dbg arg1 arg1_ty arg2 arg2_ty result_var

(** val recover_comparison_primitive : DA.t -> P.binary_primitive -> Simple.t ->
    Simple.t -> P.t option coq_M **)

let recover_comparison_primitive dacc prim arg1 arg2 =
  let try_one_direction =
   fun left right op0 ->
    Simple.pattern_match right
      (fun _ _ -> None)
      (fun const0 ->
        match Const.descr const0 with
        | Int_ids.Const.Descr.Naked_immediate _ -> None
        | Int_ids.Const.Descr.Tagged_immediate i ->
          if
            Target_ocaml_int.equal i
              (Target_ocaml_int.zero (DE.machine_width (DA.denv dacc)))
          then
            Simple.pattern_match' left
              (fun var _ ->
                match DE.find_comparison_result (DA.denv dacc) var with
                | Some comp ->
                  Comparison_result.convert_result_compared_to_tagged_zero comp
                    op0
                | None -> None)
              (fun _ _ -> None)
              (fun _ -> None)
          else None
        | Int_ids.Const.Descr.Naked_float32 _ -> None
        | Int_ids.Const.Descr.Naked_float _ -> None
        | Int_ids.Const.Descr.Naked_int8 _ -> None
        | Int_ids.Const.Descr.Naked_int16 _ -> None
        | Int_ids.Const.Descr.Naked_int32 _ -> None
        | Int_ids.Const.Descr.Naked_int64 _ -> None
        | Int_ids.Const.Descr.Naked_nativeint _ -> None
        | Int_ids.Const.Descr.Naked_vec128 _ -> None
        | Int_ids.Const.Descr.Naked_vec256 _ -> None
        | Int_ids.Const.Descr.Naked_vec512 _ -> None
        | Int_ids.Const.Descr.Naked_mask _ -> None
        | Int_ids.Const.Descr.Null -> None
        | Int_ids.Const.Descr.Poison (_, _) -> None)
  in
  let try_both_directions =
   fun op0 swapped_op ->
    match try_one_direction arg1 arg2 op0 with
    | Some p -> Some p
    | None -> try_one_direction arg2 arg1 swapped_op
  in
  (fun f__1
    f__2
    f__3
    f__4
    f__5
    f__6
    f__7
    f__8
    f__9
    f__10
    f__11
    f__12
    f__13
    f__14
    x__0
  ->
    match (x__0 : P.binary_primitive) with
    | P.Block_set { kind = x__1; init = x__2; field = x__3 } ->
      f__1 x__1 x__2 x__3
    | P.Array_load (x__1, x__2, x__3) -> f__2 x__1 x__2 x__3
    | P.String_or_bigstring_load (x__1, x__2) -> f__3 x__1 x__2
    | P.Bigarray_load (x__1, x__2, x__3) -> f__4 x__1 x__2 x__3
    | P.Phys_equal x__1 -> f__5 x__1
    | P.Int_arith (x__1, x__2) -> f__6 x__1 x__2
    | P.Int_shift (x__1, x__2) -> f__7 x__1 x__2
    | P.Int_comp (x__1, x__2) -> f__8 x__1 x__2
    | P.Float_arith (x__1, x__2) -> f__9 x__1 x__2
    | P.Float_comp (x__1, x__2) -> f__10 x__1 x__2
    | P.Bigarray_get_alignment x__1 -> f__11 x__1
    | P.Atomic_load (x__1, x__2) -> f__12 x__1 x__2
    | P.Poke x__1 -> f__13 x__1
    | P.Read_offset (x__1, x__2) -> f__14 x__1 x__2)
    (fun _ _ _ -> None)
    (fun _ _ _ -> None)
    (fun _ _ -> None)
    (fun _ _ _ -> None)
    (fun op0 ->
      let op1 =
        match op0 with
        | P.Eq -> (P.Eq : _ P.comparison)
        | P.Neq -> (P.Neq : _ P.comparison)
      in
      try_both_directions op1 op1)
    (fun _ _ -> None)
    (fun _ _ -> None)
    (fun kind c ->
      match c with
      | P.Yielding_bool op0 -> (
        match kind with
        | Flambda_kind.Standard_int.Tagged_immediate ->
          let swapped_op =
            (fun f__1 f__2 f__3 f__4 f__5 f__6 x__0 ->
              match (x__0 : _ P.comparison) with
              | P.Eq -> f__1 ()
              | P.Neq -> f__2 ()
              | P.Lt x__1 -> f__3 x__1
              | P.Gt x__1 -> f__4 x__1
              | P.Le x__1 -> f__5 x__1
              | P.Ge x__1 -> f__6 x__1)
              (fun _ -> (P.Eq : _ P.comparison))
              (fun _ -> (P.Neq : _ P.comparison))
              (fun s -> P.Gt s)
              (fun s -> P.Lt s)
              (fun s -> P.Ge s)
              (fun s -> P.Le s)
              op0
          in
          try_both_directions op0 swapped_op
        | Flambda_kind.Standard_int.Naked_immediate -> None
        | Flambda_kind.Standard_int.Naked_int8 -> None
        | Flambda_kind.Standard_int.Naked_int16 -> None
        | Flambda_kind.Standard_int.Naked_int32 -> None
        | Flambda_kind.Standard_int.Naked_int64 -> None
        | Flambda_kind.Standard_int.Naked_nativeint -> None)
      | P.Yielding_int_like_compare_functions _ -> None)
    (fun _ _ -> None)
    (fun _ _ -> None)
    (fun _ -> None)
    (fun _ _ -> None)
    (fun _ -> None)
    (fun _ _ -> None)
    prim

(** val simplify_binary_primitive : DA.t -> P.t -> P.binary_primitive ->
    Simple.t -> T.t -> Simple.t -> T.t -> Debuginfo.t -> Bound_var.t -> SPR.t
    coq_M **)

let simplify_binary_primitive dacc original_prim prim arg1 arg1_ty arg2 arg2_ty
    dbg result_var =
  let original_prim0, prim0, arg3, arg1_ty0, arg4, arg2_ty0 =
    match recover_comparison_primitive dacc prim arg1 arg2 with
    | Some other_prim -> (
      match other_prim with
      | P.Nullary _ ->
        Misc.fatal_errorf "Recovered primitive %a is not a comparison"
          Flambda_primitive.print other_prim
      | P.Unary (_, _) ->
        Misc.fatal_errorf "Recovered primitive %a is not a comparison"
          Flambda_primitive.print other_prim
      | P.Binary (new_prim, new_arg1, new_arg2) -> (
        let min_name_mode = Bound_var.name_mode result_var in
        let arg1_ty_opt =
          Simplify_simple.simplify_simple_if_in_scope dacc new_arg1
            min_name_mode
        in
        let arg2_ty_opt =
          Simplify_simple.simplify_simple_if_in_scope dacc new_arg2
            min_name_mode
        in
        match arg1_ty_opt with
        | Some new_arg1_ty -> (
          match arg2_ty_opt with
          | Some new_arg2_ty ->
            other_prim, new_prim, new_arg1, new_arg1_ty, new_arg2, new_arg2_ty
          | None -> original_prim, prim, arg1, arg1_ty, arg2, arg2_ty)
        | None -> original_prim, prim, arg1, arg1_ty, arg2, arg2_ty)
      | P.Ternary (_, _, _, _) ->
        Misc.fatal_errorf "Recovered primitive %a is not a comparison"
          Flambda_primitive.print other_prim
      | P.Quaternary (_, _, _, _, _) ->
        Misc.fatal_errorf "Recovered primitive %a is not a comparison"
          Flambda_primitive.print other_prim
      | P.Variadic (_, _) ->
        Misc.fatal_errorf "Recovered primitive %a is not a comparison"
          Flambda_primitive.print other_prim)
    | None -> original_prim, prim, arg1, arg1_ty, arg2, arg2_ty
  in
  simplify_binary_primitive0 dacc original_prim0 prim0 arg3 arg1_ty0 arg4
    arg2_ty0 dbg result_var
