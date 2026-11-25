(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Vincent Laviron, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023 OCamlPro SAS                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Comparison_result.v, which follows
   middle_end/flambda2/simplify/comparison_result.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

module P = Flambda_primitive
open Port_monad

type tagged_or_untagged_ =
  | Tagged
  | Untagged

type t =
  { lhs : Simple.t;
    rhs : Simple.t;
    kind : Flambda_kind.Standard_int.t;
    signed : P.signed_or_unsigned;
    tagged_or_untagged : tagged_or_untagged_
  }

(** val lhs : t -> Simple.t **)

let lhs t0 = t0.lhs

(** val rhs : t -> Simple.t **)

let rhs t0 = t0.rhs

(** val kind : t -> Flambda_kind.Standard_int.t **)

let kind t0 = t0.kind

(** val signed : t -> P.signed_or_unsigned **)

let signed t0 = t0.signed

(** val tagged_or_untagged : t -> tagged_or_untagged_ **)

let tagged_or_untagged t0 = t0.tagged_or_untagged

(** val create : P.t -> t Variable_.Map.t -> t option coq_M **)

let create prim comparison_results =
  match prim with
  | P.Nullary _ -> None
  | P.Unary (u, arg) ->
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
      f__15
      f__16
      f__17
      f__18
      f__19
      f__20
      f__21
      f__22
      f__23
      f__24
      f__25
      f__26
      f__27
      f__28
      f__29
      f__30
      f__31
      x__0
    ->
      match (x__0 : P.unary_primitive) with
      | P.Block_load { kind = x__1; mut = x__2; field = x__3 } ->
        f__1 x__1 x__2 x__3
      | P.Duplicate_block { kind = x__1; alloc_region = x__2 } -> f__2 x__1 x__2
      | P.Duplicate_array
          { kind = x__1;
            source_mutability = x__2;
            destination_mutability = x__3;
            alloc_region = x__4
          } ->
        f__3 x__1 x__2 x__3 x__4
      | P.Is_int { variant_only = x__1 } -> f__4 x__1
      | P.Is_null -> f__5 ()
      | P.Get_tag -> f__6 ()
      | P.Array_length x__1 -> f__7 x__1
      | P.Bigarray_length { dimension = x__1 } -> f__8 x__1
      | P.String_length x__1 -> f__9 x__1
      | P.Int_as_pointer x__1 -> f__10 x__1
      | P.Opaque_identity { middle_end_only = x__1; kind = x__2 } ->
        f__11 x__1 x__2
      | P.Int_arith (x__1, x__2) -> f__12 x__1 x__2
      | P.Float_arith (x__1, x__2) -> f__13 x__1 x__2
      | P.Num_conv { src = x__1; dst = x__2 } -> f__14 x__1 x__2
      | P.Boolean_not -> f__15 ()
      | P.Reinterpret_64_bit_word x__1 -> f__16 x__1
      | P.Reinterpret_boxed_vector -> f__17 ()
      | P.Unbox_number x__1 -> f__18 x__1
      | P.Box_number (x__1, x__2) -> f__19 x__1 x__2
      | P.Untag_immediate -> f__20 ()
      | P.Tag_immediate -> f__21 ()
      | P.Project_function_slot { move_from = x__1; move_to = x__2 } ->
        f__22 x__1 x__2
      | P.Project_value_slot { project_from = x__1; value_slot = x__2 } ->
        f__23 x__1 x__2
      | P.Is_boxed_float -> f__24 ()
      | P.Is_flat_float_array -> f__25 ()
      | P.End_region { ghost = x__1 } -> f__26 x__1
      | P.End_try_region { ghost = x__1 } -> f__27 x__1
      | P.Obj_dup { alloc_region = x__1 } -> f__28 x__1
      | P.Get_header -> f__29 ()
      | P.Peek x__1 -> f__30 x__1
      | P.Make_lazy { lazy_tag = x__1; alloc_region = x__2 } -> f__31 x__1 x__2)
      (fun _ _ _ -> None)
      (fun _ _ -> None)
      (fun _ _ _ _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ _ -> None)
      (fun _ _ -> None)
      (fun _ _ -> None)
      (fun _ _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ _ -> None)
      (fun _ -> None)
      (fun _ ->
        match Simple.must_be_var arg with
        | Some p -> (
          let var, _ = p in
          match Variable.Map.find_opt var comparison_results with
          | Some t0 -> (
            let { lhs = lhs0;
                  rhs = rhs0;
                  kind = kind0;
                  signed = signed0;
                  tagged_or_untagged = tagged_or_untagged0
                } =
              t0
            in
            match tagged_or_untagged0 with
            | Tagged ->
              Misc.fatal_errorf "Tagging of an already tagged result %a"
                Variable.print var
            | Untagged ->
              Some
                { lhs = lhs0;
                  rhs = rhs0;
                  kind = kind0;
                  signed = signed0;
                  tagged_or_untagged = Tagged
                })
          | None -> None)
        | None -> None)
      (fun _ _ -> None)
      (fun _ _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ -> None)
      (fun _ _ -> None)
      u
  | P.Binary (b, lhs0, rhs0) ->
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
      (fun _ -> None)
      (fun _ _ -> None)
      (fun _ _ -> None)
      (fun kind0 c ->
        match c with
        | Yielding_bool _ -> None
        | Yielding_int_like_compare_functions signed0 ->
          Some
            { lhs = lhs0;
              rhs = rhs0;
              kind = kind0;
              signed = signed0;
              tagged_or_untagged = Untagged
            })
      (fun _ _ -> None)
      (fun _ _ -> None)
      (fun _ -> None)
      (fun _ _ -> None)
      (fun _ -> None)
      (fun _ _ -> None)
      b
  | P.Ternary (_, _, _, _) -> None
  | P.Quaternary (_, _, _, _, _) -> None
  | P.Variadic (_, _) -> None

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf pat =
  let { lhs = lhs0;
        rhs = rhs0;
        kind = kind0;
        signed = signed0;
        tagged_or_untagged = tagged_or_untagged0
      } =
    pat
  in
  let prefix = match signed0 with P.Signed -> "" | P.Unsigned -> "u" in
  let result =
    match tagged_or_untagged0 with Tagged -> "tagged" | Untagged -> "untagged"
  in
  Format.fprintf ppf
    "@[<hov 1>(@[<hov 1>(lhs@ %a)@]@ @[<hov 1>(rhs@ %a)@]@ @[<hov 1>(kind@ \
     %s%a -> %s)@]@ )@]"
    Simple.print lhs0 Simple.print rhs0 prefix
    Flambda_kind.Standard_int.print_lowercase kind0 result

(** val convert_result_compared_to_tagged_zero : t -> P.signed_or_unsigned
    P.comparison -> P.t option coq_M **)

let convert_result_compared_to_tagged_zero t0 =
  let { lhs = lhs0;
        rhs = rhs0;
        kind = kind0;
        signed = signed0;
        tagged_or_untagged = tagged_or_untagged0
      } =
    t0
  in
  fun op ->
    let () =
      match tagged_or_untagged0 with
      | Tagged -> ()
      | Untagged ->
        Misc.fatal_errorf "Comparing untagged result with tagged zero: %a" print
          t0
    in
    let make_result =
     fun new_op ->
      let prim = P.Int_comp (kind0, Yielding_bool new_op) in
      Some (P.Binary (prim, lhs0, rhs0))
    in
    (fun f__1 f__2 f__3 f__4 f__5 f__6 x__0 ->
      match (x__0 : _ P.comparison) with
      | P.Eq -> f__1 ()
      | P.Neq -> f__2 ()
      | P.Lt x__1 -> f__3 x__1
      | P.Gt x__1 -> f__4 x__1
      | P.Le x__1 -> f__5 x__1
      | P.Ge x__1 -> f__6 x__1)
      (fun _ -> make_result (P.Eq : _ P.comparison))
      (fun _ -> make_result (P.Neq : _ P.comparison))
      (fun s ->
        match s with P.Signed -> make_result (Lt signed0) | P.Unsigned -> None)
      (fun s ->
        match s with
        | P.Signed -> make_result (Gt signed0)
        | P.Unsigned -> make_result (P.Neq : _ P.comparison))
      (fun s ->
        match s with
        | P.Signed -> make_result (Le signed0)
        | P.Unsigned -> make_result (P.Eq : _ P.comparison))
      (fun s ->
        match s with P.Signed -> make_result (Ge signed0) | P.Unsigned -> None)
      op
