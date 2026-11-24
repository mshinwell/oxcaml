(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*   Copyright 2021--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Simplify_extcall.v, which follows
   middle_end/flambda2/simplify/simplify_extcall.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import
module RO = Removed_operations
open Port_monad

type t =
  | Unchanged of { return_types : Flambda2_types.t list Or_unknown.t }
  | Specialised of DA.t * Expr.t * Removed_operations.t
  | Invalid

(** val fun_symbol : Simple.t -> Symbol.t coq_M **)

let fun_symbol simple =
  let fail =
   fun simple0 ->
    Misc.fatal_errorf "Expected a function symbol, instead of@ %a" Simple.print
      simple0
  in
  Simple.pattern_match simple
    (fun name coercion ->
      let of_coercion =
        Name.pattern_match name (fun _ _ -> fail simple) (fun sym _ -> sym)
      in
      of_coercion coercion)
    (fun _ -> fail simple)

(** val apply_cont : Continuation.t -> Variable.t -> Debuginfo.t -> (NO.t *
    Expr.t) coq_M **)

let apply_cont cont v dbg =
  let args = Simple.name (Name.var v) :: [] in
  let apply_cont0 =
    (fun x__1 x__2 x__3 x__4 ->
      Apply_cont.create ?trap_action:x__1 x__2 x__3 x__4)
      None cont args dbg
  in
  let free_names = Apply_cont.free_names apply_cont0 in
  let expr = Expr.create_apply_cont apply_cont0 in
  free_names, expr

(** val let_prim : Debuginfo.t -> Variable.t -> Flambda_debug_uid.t -> P.t ->
    (NO.t * Expr.t) -> (NO.t * Expr.t) coq_M **)

let let_prim dbg v v_duid prim = function
  | free_names, body ->
    let v' = Bound_var.create v v_duid Name_mode.normal in
    let bindable = Bound_pattern.singleton v' in
    let named = Named.create_prim prim dbg in
    let free_names_of_body = Or_unknown.Known free_names in
    let let_expr = Let.create bindable named body free_names_of_body in
    let free_names0 = NO.remove_var free_names v in
    let expr = Expr.create_let let_expr in
    free_names0, expr

(** val simplify_comparison_of_tagged_immediates : Debuginfo.t -> DA.t ->
    P.binary_primitive -> Continuation.t -> Simple.t -> Simple.t -> t coq_M **)

let simplify_comparison_of_tagged_immediates dbg dacc cmp_prim cont a b =
  let v_comp =
    (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
      None "comp" K.naked_immediate
  in
  let v_comp_duid = Flambda_debug_uid.none in
  let tagged =
    (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
      None "tagged" K.value
  in
  let tagged_duid = Flambda_debug_uid.none in
  let _, res =
    let_prim dbg v_comp v_comp_duid
      (P.Binary (cmp_prim, a, b))
      (let_prim dbg tagged tagged_duid
         (P.Unary (Tag_immediate, Simple.var v_comp))
         (apply_cont cont tagged dbg))
  in
  Specialised (dacc, res, RO.specialized_poly_compare)

(** val simplify_comparison_of_boxed_numbers : Debuginfo.t -> DA.t ->
    K.Boxable_number.t -> P.binary_primitive -> Continuation.t -> Simple.t ->
    Simple.t -> t coq_M **)

let simplify_comparison_of_boxed_numbers dbg dacc kind cmp_prim cont a b =
  let a_naked =
    (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
      None "unboxed"
      (K.Boxable_number.unboxed_kind kind)
  in
  let a_naked_duid = Flambda_debug_uid.none in
  let b_naked =
    (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
      None "unboxed"
      (K.Boxable_number.unboxed_kind kind)
  in
  let b_naked_duid = Flambda_debug_uid.none in
  let v_comp =
    (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
      None "comp" K.naked_immediate
  in
  let v_comp_duid = Flambda_debug_uid.none in
  let tagged =
    (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
      None "tagged" K.value
  in
  let tagged_duid = Flambda_debug_uid.none in
  let _, res =
    let_prim dbg a_naked a_naked_duid
      (P.Unary (Unbox_number kind, a))
      (let_prim dbg b_naked b_naked_duid
         (P.Unary (Unbox_number kind, b))
         (let_prim dbg v_comp v_comp_duid
            (P.Binary (cmp_prim, Simple.var a_naked, Simple.var b_naked))
            (let_prim dbg tagged tagged_duid
               (P.Unary (Tag_immediate, Simple.var v_comp))
               (apply_cont cont tagged dbg))))
  in
  Specialised (dacc, res, RO.specialized_poly_compare)

(** val simplify_comparison : Debuginfo.t -> DA.t -> Continuation.t ->
    P.binary_primitive -> (P.float_bitwidth -> P.binary_primitive coq_M) ->
    (K.Standard_int.t -> P.binary_primitive coq_M) -> Simple.t -> Simple.t ->
    T.t -> T.t -> t coq_M **)

let simplify_comparison dbg dacc cont tagged_prim float_prim boxed_int_prim a b
    a_ty b_ty =
  let tenv = DA.typing_env dacc in
  let m, m0 =
    ( T.prove_is_a_boxed_or_tagged_number tenv a_ty,
      T.prove_is_a_boxed_or_tagged_number tenv b_ty )
  in
  match m with
  | T.Proved b0 -> (
    match b0 with
    | Boxed (_, t0, _) -> (
      match t0 with
      | Naked_float32 -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, t3, _) -> (
            match t3 with
            | Naked_float32 ->
              simplify_comparison_of_boxed_numbers dbg dacc Naked_float32
                (float_prim Flambda_primitive.Float32)
                cont a b
            | Naked_float ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_int32 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_int64 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_nativeint ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec128 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec256 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec512 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_mask ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            )
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
      | Naked_float -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, t3, _) -> (
            match t3 with
            | Naked_float32 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_float ->
              simplify_comparison_of_boxed_numbers dbg dacc Naked_float
                (float_prim Flambda_primitive.Float64)
                cont a b
            | Naked_int32 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_int64 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_nativeint ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec128 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec256 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec512 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_mask ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            )
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
      | Naked_int32 -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, t3, _) -> (
            match t3 with
            | Naked_float32 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_float ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_int32 ->
              simplify_comparison_of_boxed_numbers dbg dacc Naked_int32
                (boxed_int_prim K.Standard_int.Naked_int32)
                cont a b
            | Naked_int64 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_nativeint ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec128 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec256 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec512 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_mask ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            )
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
      | Naked_int64 -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, t3, _) -> (
            match t3 with
            | Naked_float32 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_float ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_int32 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_int64 ->
              simplify_comparison_of_boxed_numbers dbg dacc Naked_int64
                (boxed_int_prim K.Standard_int.Naked_int64)
                cont a b
            | Naked_nativeint ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec128 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec256 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec512 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_mask ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            )
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
      | Naked_nativeint -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, t3, _) -> (
            match t3 with
            | Naked_float32 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_float ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_int32 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_int64 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_nativeint ->
              simplify_comparison_of_boxed_numbers dbg dacc Naked_nativeint
                (boxed_int_prim K.Standard_int.Naked_nativeint)
                cont a b
            | Naked_vec128 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec256 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_vec512 ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            | Naked_mask ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            )
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
      | Naked_vec128 -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, _, _) ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
      | Naked_vec256 -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, _, _) ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
      | Naked_vec512 -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, _, _) ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
      | Naked_mask -> (
        match m0 with
        | T.Proved b1 -> (
          match b1 with
          | Boxed (_, _, _) ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
          | Tagged_immediate ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
        | T.Unknown ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown))
    | Tagged_immediate -> (
      match m0 with
      | T.Proved b1 -> (
        match b1 with
        | Boxed (_, _, _) ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
        | Tagged_immediate ->
          simplify_comparison_of_tagged_immediates dbg dacc tagged_prim cont a b
        )
      | T.Unknown ->
        (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown))
  | T.Unknown -> (
    match m0 with
    | T.Proved b0 -> (
      match b0 with
      | Boxed (_, _, _) ->
        (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
      | Tagged_immediate ->
        (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)
    | T.Unknown ->
      (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown)

(** val simplify_caml_array_make : DA.t -> T.t -> T.t -> t coq_M **)

let simplify_caml_array_make dacc len_ty init_value_ty =
  let typing_env = DA.typing_env dacc in
  let element_kind =
    if not (Flambda_features.flat_float_array ())
    then
      Or_unknown_or_bottom.Ok
        (Flambda_kind.With_subkind.anything (T.kind init_value_ty))
    else
      match T.prove_is_or_is_not_a_boxed_float typing_env init_value_ty with
      | T.Proved b ->
        if b
        then Or_unknown_or_bottom.Ok Flambda_kind.With_subkind.naked_float
        else Or_unknown_or_bottom.Unknown
      | T.Unknown -> Or_unknown_or_bottom.Unknown
  in
  let type_of_returned_array =
    T.mutable_array element_kind len_ty Alloc_mode.For_types.heap
  in
  (fun x__1 -> Unchanged { return_types = x__1 })
    (Or_unknown.Known (type_of_returned_array :: []))

(** val simplify_returning_extcall : Debuginfo.t -> Continuation.t ->
    Exn_continuation.t -> DA.t -> string -> Simple.t list -> T.t list -> t coq_M
    **)

let simplify_returning_extcall dbg cont _ dacc fun_name args arg_types =
  match args with
  | [] -> (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
  | a :: l -> (
    match l with
    | [] -> (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
    | b :: l0 -> (
      match l0 with
      | [] -> (
        match arg_types with
        | [] ->
          (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
        | a_ty :: l1 -> (
          match l1 with
          | [] ->
            (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
          | b_ty :: l2 -> (
            match l2 with
            | [] ->
              if String.equal fun_name "caml_compare"
              then
                simplify_comparison dbg dacc cont
                  (Int_comp
                     ( K.Standard_int.Tagged_immediate,
                       Yielding_int_like_compare_functions Signed ))
                  (fun width ->
                    Float_comp (width, Yielding_int_like_compare_functions ()))
                  (fun kind ->
                    Int_comp (kind, Yielding_int_like_compare_functions Signed))
                  a b a_ty b_ty
              else if String.equal fun_name "caml_equal"
              then
                simplify_comparison dbg dacc cont (Phys_equal Eq)
                  (fun width ->
                    Float_comp (width, Yielding_bool (P.Eq : _ P.comparison)))
                  (fun kind ->
                    Int_comp (kind, Yielding_bool (P.Eq : _ P.comparison)))
                  a b a_ty b_ty
              else if String.equal fun_name "caml_notequal"
              then
                simplify_comparison dbg dacc cont (Phys_equal Neq)
                  (fun width ->
                    Float_comp (width, Yielding_bool (P.Neq : _ P.comparison)))
                  (fun kind ->
                    Int_comp (kind, Yielding_bool (P.Neq : _ P.comparison)))
                  a b a_ty b_ty
              else if String.equal fun_name "caml_lessequal"
              then
                simplify_comparison dbg dacc cont
                  (Int_comp
                     (K.Standard_int.Tagged_immediate, Yielding_bool (Le Signed)))
                  (fun width -> Float_comp (width, Yielding_bool (Le ())))
                  (fun kind -> Int_comp (kind, Yielding_bool (Le Signed)))
                  a b a_ty b_ty
              else if String.equal fun_name "caml_lessthan"
              then
                simplify_comparison dbg dacc cont
                  (Int_comp
                     (K.Standard_int.Tagged_immediate, Yielding_bool (Lt Signed)))
                  (fun width -> Float_comp (width, Yielding_bool (Lt ())))
                  (fun kind -> Int_comp (kind, Yielding_bool (Lt Signed)))
                  a b a_ty b_ty
              else if String.equal fun_name "caml_greaterequal"
              then
                simplify_comparison dbg dacc cont
                  (Int_comp
                     (K.Standard_int.Tagged_immediate, Yielding_bool (Ge Signed)))
                  (fun width -> Float_comp (width, Yielding_bool (Ge ())))
                  (fun kind -> Int_comp (kind, Yielding_bool (Ge Signed)))
                  a b a_ty b_ty
              else if String.equal fun_name "caml_greaterthan"
              then
                simplify_comparison dbg dacc cont
                  (Int_comp
                     (K.Standard_int.Tagged_immediate, Yielding_bool (Gt Signed)))
                  (fun width -> Float_comp (width, Yielding_bool (Gt ())))
                  (fun kind -> Int_comp (kind, Yielding_bool (Gt Signed)))
                  a b a_ty b_ty
              else if String.equal fun_name "caml_array_make"
              then simplify_caml_array_make dacc a_ty b_ty
              else
                (fun x__1 -> Unchanged { return_types = x__1 })
                  Or_unknown.Unknown
            | _ :: _ ->
              (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
            )))
      | _ :: _ ->
        (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown))

(** val simplify_extcall : DA.t -> Apply.t -> T.t -> T.t list -> t coq_M **)

let simplify_extcall dacc apply _ arg_types =
  let dbg = Apply.dbg apply in
  let args = Apply.args apply in
  let exn_cont = Apply.exn_continuation apply in
  let fun_name =
    let callee =
      match Apply.callee apply with
      | Some callee -> callee
      | None ->
        Misc.fatal_errorf
          "Application expression did not provide callee for C call:@ %a"
          Apply.print apply
    in
    Linkage_name.to_string (Symbol.linkage_name (fun_symbol callee))
  in
  match Apply.continuation apply with
  | Return cont ->
    simplify_returning_extcall dbg cont exn_cont dacc fun_name args arg_types
  | Never_returns ->
    (fun x__1 -> Unchanged { return_types = x__1 }) Or_unknown.Unknown
