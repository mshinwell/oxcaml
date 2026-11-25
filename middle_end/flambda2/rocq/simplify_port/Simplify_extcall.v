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

(* This file follows middle_end/flambda2/simplify/simplify_extcall.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Bound_pattern Bound_var Continuation
  Debuginfo Exn_continuation Flambda_debug_uid Flambda_features Int_ids
  Linkage_name Name Name_mode Or_unknown Or_unknown_or_bottom
  Removed_operations Simple Symbol Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Apply_expr.Result_continuation.t
   Flambda2_types.boxed_or_tagged_number Flambda2_types.proof_of_property
   Flambda_kind.Boxable_number.t Flambda_primitive.binary_primitive
   Flambda_primitive.comparison Flambda_primitive.comparison_behaviour
   Flambda_primitive.equality_comparison
   Flambda_primitive.signed_or_unsigned Flambda_primitive.unary_primitive *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 17 *)
From SimplifyPort.abbrev.simplify_extcall Require Import Port_abbreviations.
(*OCAML
module RO = Removed_operations
OCAML*)

(* 19-22 *)
(* The type has an inline record. In Rocq it is the inductive type [t_], in
   the form of decl/Simplify_extcall.v (the field by place); the OCaml
   definition is the compiler's text, which the directive of [t] puts at this
   place of the extracted file. *)
Inductive t_ : Type :=
| Unchanged : Or_unknown.t (list Flambda2_types.t) -> t_
| Specialised : DA.t -> Expr.t -> Removed_operations.t -> t_
| Invalid : t_.
Extract Inductive t_ => "t"
  [ "(fun x__1 -> Unchanged { return_types = x__1 })" "Specialised" "Invalid" ]
  "(fun f__1 f__2 f__3 x__0 -> match x__0 with Unchanged { return_types = x__1 } -> f__1 x__1 | Specialised (x__1, x__2, x__3) -> f__2 x__1 x__2 x__3 | Invalid -> f__3 ())".
Definition t : Type := t_.
Extract Constant t =>
  "| Unchanged of { return_types : Flambda2_types.t list Or_unknown.t } | Specialised of DA.t * Expr.t * Removed_operations.t | Invalid".

(* Helpers *)
(* ******* *)

(* 27-37 *)
Definition fun_symbol (simple : Simple.t) : M Symbol.t :=
  let& fail :=
    fun (simple : Simple.t) =>
    (fatal_errorf2 "Expected a function symbol, instead of@ %a" Simple.print
       simple
      : M Symbol.t)
  in
  (* PORT-GAP(loose): 33-36, the compiler's [~name] is [fun name ->
     Name.pattern_match name ~var:(fun _ ~coercion:_ -> ..) ~symbol:(fun sym
     ~coercion:_ -> ..)]: [Name.pattern_match] answers the function of the
     coercion. Here that function is named and applied to the coercion. *)
  Simple.pattern_match simple
    (fun name coercion =>
      let* of_coercion :=
        Name.pattern_match name
          (fun _ => ret (fun (_ : Int_ids.Coercion.t) => fail simple))
          (fun sym => ret (fun (_ : Int_ids.Coercion.t) => ret sym))
      in
      of_coercion coercion)
    (fun _ => fail simple).

(* 39-44. In the compiler: [cont v ~dbg]. *)
Definition apply_cont (cont : Continuation.t) (v : Variable_.t)
    (dbg : Debuginfo.t) : M (NO.t * Expr.t) :=
  let* args :=
    let! tmp1 := Name.var v in
    let! tmp2 := Simple.name tmp1 in
    ret [tmp2]
  in
  let* apply_cont := Apply_cont.create None cont args dbg in
  let* free_names := Apply_cont.free_names apply_cont in
  let* expr := Expr.create_apply_cont apply_cont in
  ret (free_names, expr).

(* 46-54. In the compiler: [~dbg v v_duid prim (free_names, body)]. *)
Definition let_prim (dbg : Debuginfo.t) (v : Variable_.t)
    (v_duid : Flambda_debug_uid.t) (prim : P.t)
    '((free_names, body) : NO.t * Expr.t) : M (NO.t * Expr.t) :=
  let* v' := Bound_var.create v v_duid Name_mode.normal in
  let* bindable := Bound_pattern.singleton v' in
  let* named := Named.create_prim prim dbg in
  let& free_names_of_body := Or_unknown.Known free_names in
  let* let_expr := Let.create bindable named body free_names_of_body in
  let* free_names := NO.remove_var free_names v in
  let* expr := Expr.create_let let_expr in
  ret (free_names, expr).

(* Exported simplification function *)
(* ******************************** *)

(* 58-70. In the compiler: [~dbg dacc ~cmp_prim cont a b]. *)
Definition simplify_comparison_of_tagged_immediates (dbg : Debuginfo.t)
    (dacc : DA.t) (cmp_prim : P.binary_primitive) (cont : Continuation.t)
    (a b : Simple.t) : M t :=
  let* v_comp := Variable_.create None "comp" K.naked_immediate in
  let& v_comp_duid := Flambda_debug_uid.none in
  let* tagged := Variable_.create None "tagged" K.value in
  let& tagged_duid := Flambda_debug_uid.none in
  (* 64-69: [f x @@ g y @@ e] is [f x (g y e)]. *)
  let* '(_free_names, res) :=
    let! tmp1 := apply_cont cont tagged dbg in
    let! tmp2 := Simple.var v_comp in
    let! tmp3 :=
      let_prim dbg tagged tagged_duid (P.Unary P.Tag_immediate tmp2) tmp1
    in
    let_prim dbg v_comp v_comp_duid (P.Binary cmp_prim a b) tmp3
  in
  ret (Specialised dacc res RO.specialized_poly_compare).

(* 72-95. In the compiler: [~dbg dacc ~kind ~cmp_prim cont a b]. *)
Definition simplify_comparison_of_boxed_numbers (dbg : Debuginfo.t)
    (dacc : DA.t) (kind : K.Boxable_number.t) (cmp_prim : P.binary_primitive)
    (cont : Continuation.t) (a b : Simple.t) : M t :=
  let* a_naked :=
    let! tmp1 := K.Boxable_number.unboxed_kind kind in
    Variable_.create None "unboxed" tmp1
  in
  let& a_naked_duid := Flambda_debug_uid.none in
  let* b_naked :=
    let! tmp1 := K.Boxable_number.unboxed_kind kind in
    Variable_.create None "unboxed" tmp1
  in
  let& b_naked_duid := Flambda_debug_uid.none in
  let* v_comp := Variable_.create None "comp" K.naked_immediate in
  let& v_comp_duid := Flambda_debug_uid.none in
  let* tagged := Variable_.create None "tagged" K.value in
  let& tagged_duid := Flambda_debug_uid.none in
  (* 85-94: [f x @@ g y @@ e] is [f x (g y e)]. *)
  let* '(_free_names, res) :=
    (* XXX try to remove @@ *)
    let! tmp1 := apply_cont cont tagged dbg in
    let! tmp2 := Simple.var v_comp in
    let! tmp3 :=
      let_prim dbg tagged tagged_duid (P.Unary P.Tag_immediate tmp2) tmp1
    in
    let! tmp4 := Simple.var b_naked in
    let! tmp5 := Simple.var a_naked in
    let! tmp6 :=
      let_prim dbg v_comp v_comp_duid (P.Binary cmp_prim tmp5 tmp4) tmp3
    in
    let! tmp7 :=
      let_prim dbg b_naked b_naked_duid (P.Unary (P.Unbox_number kind) b) tmp6
    in
    let_prim dbg a_naked a_naked_duid (P.Unary (P.Unbox_number kind) a) tmp7
  in
  ret (Specialised dacc res RO.specialized_poly_compare).

(* 97-140. In the compiler: [~dbg ~dacc ~cont ~tagged_prim ~float_prim
   ~boxed_int_prim a b a_ty b_ty]. *)
Definition simplify_comparison (dbg : Debuginfo.t) (dacc : DA.t)
    (cont : Continuation.t) (tagged_prim : P.binary_primitive)
    (float_prim : P.float_bitwidth -> M P.binary_primitive)
    (boxed_int_prim : K.Standard_int.t -> M P.binary_primitive)
    (a b : Simple.t) (a_ty b_ty : T.t) : M t :=
  let* tenv := DA.typing_env dacc in
  let! tmp1 := T.prove_is_a_boxed_or_tagged_number tenv b_ty in
  let! tmp2 := T.prove_is_a_boxed_or_tagged_number tenv a_ty in
  match (tmp2, tmp1) with
  | (T.Proved T.Tagged_immediate, T.Proved T.Tagged_immediate) =>
    simplify_comparison_of_tagged_immediates dbg dacc tagged_prim cont a b
  | (T.Proved (T.Boxed _ K.Boxable_number.Naked_float _),
     T.Proved (T.Boxed _ K.Boxable_number.Naked_float _)) =>
    let! tmp3 := float_prim Flambda_primitive.Float64 in
    simplify_comparison_of_boxed_numbers dbg dacc K.Boxable_number.Naked_float
      tmp3 cont a b
  | (T.Proved (T.Boxed _ K.Boxable_number.Naked_float32 _),
     T.Proved (T.Boxed _ K.Boxable_number.Naked_float32 _)) =>
    let! tmp3 := float_prim Flambda_primitive.Float32 in
    simplify_comparison_of_boxed_numbers dbg dacc
      K.Boxable_number.Naked_float32 tmp3 cont a b
  | (T.Proved (T.Boxed _ K.Boxable_number.Naked_int32 _),
     T.Proved (T.Boxed _ K.Boxable_number.Naked_int32 _)) =>
    let! tmp3 := boxed_int_prim K.Standard_int.Naked_int32 in
    simplify_comparison_of_boxed_numbers dbg dacc K.Boxable_number.Naked_int32
      tmp3 cont a b
  | (T.Proved (T.Boxed _ K.Boxable_number.Naked_int64 _),
     T.Proved (T.Boxed _ K.Boxable_number.Naked_int64 _)) =>
    let! tmp3 := boxed_int_prim K.Standard_int.Naked_int64 in
    simplify_comparison_of_boxed_numbers dbg dacc K.Boxable_number.Naked_int64
      tmp3 cont a b
  | (T.Proved (T.Boxed _ K.Boxable_number.Naked_nativeint _),
     T.Proved (T.Boxed _ K.Boxable_number.Naked_nativeint _)) =>
    let! tmp3 := boxed_int_prim K.Standard_int.Naked_nativeint in
    simplify_comparison_of_boxed_numbers dbg dacc
      K.Boxable_number.Naked_nativeint tmp3 cont a b
  (* Mismatches between varieties of numbers *)
  | (T.Proved T.Tagged_immediate, T.Proved (T.Boxed _ _ _))
  | (T.Proved (T.Boxed _ _ _), T.Proved T.Tagged_immediate)
  | (T.Proved
       (T.Boxed _
          (K.Boxable_number.Naked_float | K.Boxable_number.Naked_float32
          | K.Boxable_number.Naked_int32 | K.Boxable_number.Naked_int64
          | K.Boxable_number.Naked_nativeint | K.Boxable_number.Naked_vec128
          | K.Boxable_number.Naked_vec256 | K.Boxable_number.Naked_vec512
          | K.Boxable_number.Naked_mask)
          _),
     T.Proved (T.Boxed _ _ _))
  (* One or two of the arguments is not known *)
  | (T.Unknown, T.Unknown)
  | (T.Unknown, T.Proved (T.Tagged_immediate | T.Boxed _ _ _))
  | (T.Proved (T.Tagged_immediate | T.Boxed _ _ _), T.Unknown) =>
    ret (Unchanged Or_unknown.Unknown)
  end.

(* 142-169. In the compiler: [dacc ~len_ty ~init_value_ty]. *)
Definition simplify_caml_array_make (dacc : DA.t) (len_ty init_value_ty : T.t)
    : M t :=
  let* typing_env := DA.typing_env dacc in
  let* element_kind :=
    (* We can't deduce subkind information, e.g. an array is all-immediates
       rather than arbitrary values, but we can deduce kind information. *)
    let! tmp1 := Flambda_features.flat_float_array tt in
    if negb tmp1
    then
      let! tmp2 := T.kind init_value_ty in
      let! tmp3 := Flambda_kind.With_subkind.anything tmp2 in
      ret (Or_unknown_or_bottom.Ok tmp3)
    else
      let! tmp4 :=
        T.prove_is_or_is_not_a_boxed_float typing_env init_value_ty
      in
      match tmp4 with
      | T.Proved true =>
        (* A boxed float provided to [caml_array_make] with the float array
           optimisation on will always yield a flat array of naked floats. *)
        ret (Or_unknown_or_bottom.Ok Flambda_kind.With_subkind.naked_float)
      | T.Proved false | T.Unknown => ret Or_unknown_or_bottom.Unknown
      end
  in
  let* type_of_returned_array :=
    T.mutable_array element_kind len_ty Alloc_mode.For_types.heap
  in
  ret (Unchanged (Or_unknown.Known [type_of_returned_array])).

(* 171-215. In the compiler: [~dbg ~cont ~exn_cont:_ dacc fun_name args
   ~arg_types]. *)
(* PORT-GAP(loose): 173-215, the compiler matches the triple [fun_name,
   args, arg_types], the name against string constants. Here the two lists
   are matched first, and then the name is compared with each constant, in
   the compiler's order; the last case [_] is the two answers [Unchanged]. *)
Definition simplify_returning_extcall (dbg : Debuginfo.t)
    (cont : Continuation.t) (_ : Exn_continuation.t) (dacc : DA.t)
    (fun_name : string) (args : list Simple.t) (arg_types : list T.t)
    : M t :=
  match args, arg_types with
  | [a; b], [a_ty; b_ty] =>
    (* Polymorphic comparisons *)
    if (fun_name =? "caml_compare")%string
    then
      simplify_comparison dbg dacc cont
        (P.Int_comp K.Standard_int.Tagged_immediate
           (P.Yielding_int_like_compare_functions P.Signed))
        (fun width =>
          ret (P.Float_comp width (P.Yielding_int_like_compare_functions tt)))
        (fun kind =>
          ret (P.Int_comp kind (P.Yielding_int_like_compare_functions P.Signed)))
        a b a_ty b_ty
    else if (fun_name =? "caml_equal")%string
    then
      simplify_comparison dbg dacc cont (P.Phys_equal P.Eq_)
        (fun width => ret (P.Float_comp width (P.Yielding_bool P.Eq)))
        (fun kind => ret (P.Int_comp kind (P.Yielding_bool P.Eq)))
        a b a_ty b_ty
    else if (fun_name =? "caml_notequal")%string
    then
      simplify_comparison dbg dacc cont (P.Phys_equal P.Neq_)
        (fun width => ret (P.Float_comp width (P.Yielding_bool P.Neq)))
        (fun kind => ret (P.Int_comp kind (P.Yielding_bool P.Neq)))
        a b a_ty b_ty
    else if (fun_name =? "caml_lessequal")%string
    then
      simplify_comparison dbg dacc cont
        (P.Int_comp K.Standard_int.Tagged_immediate
           (P.Yielding_bool (P.Le P.Signed)))
        (fun width => ret (P.Float_comp width (P.Yielding_bool (P.Le tt))))
        (fun kind => ret (P.Int_comp kind (P.Yielding_bool (P.Le P.Signed))))
        a b a_ty b_ty
    else if (fun_name =? "caml_lessthan")%string
    then
      simplify_comparison dbg dacc cont
        (P.Int_comp K.Standard_int.Tagged_immediate
           (P.Yielding_bool (P.Lt P.Signed)))
        (fun width => ret (P.Float_comp width (P.Yielding_bool (P.Lt tt))))
        (fun kind => ret (P.Int_comp kind (P.Yielding_bool (P.Lt P.Signed))))
        a b a_ty b_ty
    else if (fun_name =? "caml_greaterequal")%string
    then
      simplify_comparison dbg dacc cont
        (P.Int_comp K.Standard_int.Tagged_immediate
           (P.Yielding_bool (P.Ge P.Signed)))
        (fun width => ret (P.Float_comp width (P.Yielding_bool (P.Ge tt))))
        (fun kind => ret (P.Int_comp kind (P.Yielding_bool (P.Ge P.Signed))))
        a b a_ty b_ty
    else if (fun_name =? "caml_greaterthan")%string
    then
      simplify_comparison dbg dacc cont
        (P.Int_comp K.Standard_int.Tagged_immediate
           (P.Yielding_bool (P.Gt P.Signed)))
        (fun width => ret (P.Float_comp width (P.Yielding_bool (P.Gt tt))))
        (fun kind => ret (P.Int_comp kind (P.Yielding_bool (P.Gt P.Signed))))
        a b a_ty b_ty
    else if (fun_name =? "caml_array_make")%string
    then
      (* 213-214: [[_; _], [len_ty; init_value_ty]] *)
      simplify_caml_array_make dacc a_ty b_ty
    else ret (Unchanged Or_unknown.Unknown)
  | _, _ => ret (Unchanged Or_unknown.Unknown)
  end.

(* Exported simplification function *)
(* ******************************** *)

(* 217-239. In the compiler: [dacc apply ~callee_ty:_ ~arg_types]. *)
Definition simplify_extcall (dacc : DA.t) (apply : Apply.t) (_ : T.t)
    (arg_types : list T.t) : M t :=
  let* dbg := Apply.dbg apply in
  let* args := Apply.args apply in
  let* exn_cont := Apply.exn_continuation apply in
  let* fun_name :=
    let* callee :=
      let! tmp1 := Apply.callee apply in
      match tmp1 with
      | Some callee => ret callee
      | None =>
        fatal_errorf2
          "Application expression did not provide callee for C call:@ %a"
          Apply.print apply
      end
    in
    (* 233: [a |> f |> g |> h] is [h (g (f a))]. *)
    let! tmp1 := fun_symbol callee in
    let! tmp2 := Symbol.linkage_name tmp1 in
    Linkage_name.to_string tmp2
  in
  let! tmp1 := Apply.continuation apply in
  match tmp1 with
  | Apply_expr.Result_continuation.Never_returns =>
    ret (Unchanged Or_unknown.Unknown)
  | Apply_expr.Result_continuation.Return cont =>
    simplify_returning_extcall dbg cont exn_cont dacc fun_name args arg_types
  end.
