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
   middle_end/flambda2/simplify/simplify_variadic_primitive.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Bound_var Debuginfo List Mutability
  Or_bottom Or_unknown_or_bottom Simple Stdlib_ Target_ocaml_int.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 19-73. In the compiler: [~original_prim ~block_kind ~mutable_or_immutable
   alloc_mode dacc ~original_term _dbg ~args_with_tys ~result_var]. *)
Definition simplify_make_block (original_prim : P.t)
    (block_kind : P.Block_kind.t) (mutable_or_immutable : Mutability.t)
    (alloc_mode : Alloc_mode.For_allocations.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t)
    (args_with_tys : list (Simple.t * T.t)) (result_var : Bound_var.t)
    : M SPR.t :=
  let* typing_env := DA.typing_env dacc in
  (* 23-49 *)
  let* typing_env :=
    match block_kind with
    | P.Block_kind.Naked_floats | P.Block_kind.Mixed _ _ =>
      (* No useful subkind information *)
      ret (Or_bottom.Ok typing_env)
    | P.Block_kind.Values _tag field_kinds =>
      (let! tmp1 := List.compare_lengths args_with_tys field_kinds in
       if tmp1 <>? 0
       then
         fatal_errorf2
           "Shape in [Make_block] of different length from argument list:@ %a"
           Named.print original_term
       else ret tt) ;;
      (* PORT-GAP(loose): 34-49, the binding operators of
         [Or_bottom.Let_syntax] (36-37 [let<*], 40 [let<+]) are written as
         the application of the operator to the function of the rest. 38-48,
         [Simple.pattern_match' arg ~var ~const ~symbol]: the arguments are
         in the order of the interface. *)
      List.fold_left2
        (fun (typing_env : Or_bottom.t TE.t) (arg_kind : K.With_subkind.t)
             '((arg, _arg_ty) : Simple.t * T.t) =>
          Or_bottom.Let_syntax.let_op_lt_star typing_env
            (fun typing_env =>
              Simple.pattern_match' arg
                (fun _ _ =>
                  let! tmp1 := DA.denv dacc in
                  let! tmp2 := DE.machine_width tmp1 in
                  let! tmp3 := T.unknown_with_subkind None tmp2 arg_kind in
                  let! tmp4 := K.With_subkind.kind arg_kind in
                  let! tmp5 := T.alias_type_of tmp4 arg in
                  let! tmp6 := T.meet typing_env tmp5 tmp3 in
                  Or_bottom.Let_syntax.let_op_lt_plus tmp6
                    (fun '(_ty, typing_env) => ret typing_env))
                (fun _ _ => ret (Or_bottom.Ok typing_env))
                (fun _ => ret (Or_bottom.Ok typing_env))))
        (Or_bottom.Ok typing_env) field_kinds args_with_tys
    end
  in
  (* 50-73 *)
  match typing_env with
  | Or_bottom.Bottom => SPR.create_invalid dacc
  | Or_bottom.Ok typing_env =>
    let* dacc :=
      DA.map_denv dacc (fun denv => DE.with_typing_env denv typing_env)
    in
    let* ty :=
      let* fields := List.map Stdlib_.snd args_with_tys in
      let* alloc_mode := Alloc_mode.For_allocations.as_type alloc_mode in
      let* '(tag, shape) := P.Block_kind.to_shape block_kind in
      (* 61-67, [T.immutable_block ~is_unique tag ~shape alloc_mode ~fields
         ~machine_width]: the arguments are in the order of the
         interface. *)
      match mutable_or_immutable with
      | Mutability.Immutable =>
        let! tmp1 := DA.denv dacc in
        let! tmp2 := DE.machine_width tmp1 in
        T.immutable_block tmp2 false tag shape alloc_mode fields
      | Mutability.Immutable_unique =>
        let! tmp1 := DA.denv dacc in
        let! tmp2 := DE.machine_width tmp1 in
        T.immutable_block tmp2 true tag shape alloc_mode fields
      | Mutability.Mutable => T.mutable_block alloc_mode
      end
    in
    let* dacc := DA.add_variable dacc result_var ty in
    let* dacc :=
      match mutable_or_immutable with
      | Mutability.Immutable_unique | Mutability.Mutable => ret dacc
      | Mutability.Immutable =>
        let! tmp1 := P.Eligible_for_cse.create original_prim in
        match tmp1 with
        | None => ret dacc
        | Some prim =>
          DA.map_denv dacc
            (fun denv =>
              let! tmp1 := Bound_var.name_mode result_var in
              let! tmp2 := Bound_var.var result_var in
              let! tmp3 := Simple.var tmp2 in
              DE.add_cse denv prim tmp3 tmp1)
        end
      end
    in
    SPR.create original_term true dacc
  end.

(* 75-151. In the compiler: [array_kind ~mutable_or_immutable alloc_mode
   dacc ~original_term dbg ~args_with_tys ~result_var]. *)
Definition simplify_make_array (array_kind : P.Array_kind.t)
    (mutable_or_immutable : Mutability.t)
    (alloc_mode : Alloc_mode.For_allocations.t) (dacc : DA.t)
    (original_term : Named.t) (dbg : Debuginfo.t)
    (args_with_tys : list (Simple.t * T.t)) (result_var : Bound_var.t)
    : M SPR.t :=
  let* '(args, tys) := List.split args_with_tys in
  (* 79-84 *)
  let* length :=
    let* machine_width :=
      let! tmp1 := DA.denv dacc in
      DE.machine_width tmp1
    in
    let! tmp1 := List.length args in
    let! tmp2 := Target_ocaml_int.of_int_option machine_width tmp1 in
    match tmp2 with
    | Some ti => T.this_tagged_immediate ti
    | None => T.unknown K.value
    end
  in
  let* element_kinds := P.Array_kind.element_kinds array_kind in
  (* 86-98 *)
  let* element_kind :=
    (* Remember that the element subkinds cannot in general be deduced from the
       types of the array members, it must be obtained from the array kind
       annotations that came via [Lambda]. *)
    let! tmp1 := P.Array_kind.element_kinds array_kind in
    match tmp1 with
    | [kind] => ret (Some kind)
    | _ :: _ => ret None
    | [] =>
      fatal_errorf4 "Empty list of element kinds given for array kind:@ %a@ %a"
        P.Array_kind.print array_kind Debuginfo.print_compact dbg
    end
  in
  let* num_element_kinds := List.length element_kinds in
  (* 100-105 *)
  (let! tmp1 := List.length args in
   let! tmp2 := int_mod tmp1 num_element_kinds in
   if tmp2 <>? 0
   then
     let! tmp3 := List.length args in
     fatal_errorf5
       "Array length not a multiple of the length of the unboxed product kind list:@ array_kind=%a@ num args=%d@ %a"
       P.Array_kind.print array_kind tmp3 Named.print original_term
   else ret tt) ;;
  (* 106-124 *)
  let* env_extension :=
    let* typing_env := DA.typing_env dacc in
    match element_kind with
    | None => ret (Or_bottom.Ok typing_env)
    | Some element_kind =>
      let* initial_element_type :=
        let! tmp1 := DA.denv dacc in
        let! tmp2 := DE.machine_width tmp1 in
        T.unknown_with_subkind None tmp2 element_kind
      in
      (* PORT-GAP(loose): 115-123, as at 34-49: the binding operators of
         [Or_bottom.Let_syntax] are written as applications. *)
      List.fold_left
        (fun (typing_env : Or_bottom.t TE.t) (element_type : T.t) =>
          Or_bottom.Let_syntax.let_op_lt_star typing_env
            (fun typing_env =>
              let! tmp1 := T.meet typing_env initial_element_type element_type in
              Or_bottom.Let_syntax.let_op_lt_plus tmp1
                (fun '(_, typing_env) => ret typing_env)))
        (Or_bottom.Ok typing_env) tys
    end
  in
  (* 125-151 *)
  match env_extension with
  | Or_bottom.Bottom => SPR.create_invalid dacc
  | Or_bottom.Ok typing_env =>
    let* ty :=
      let* alloc_mode := Alloc_mode.For_allocations.as_type alloc_mode in
      let& element_kind :=
        match element_kind with
        | None => (* Array of unboxed products *) Or_unknown_or_bottom.Unknown
        | Some element_kind => Or_unknown_or_bottom.Ok element_kind
        end
      in
      match mutable_or_immutable with
      | Mutability.Mutable => T.mutable_array element_kind length alloc_mode
      | Mutability.Immutable =>
        let! tmp1 := DA.denv dacc in
        let! tmp2 := DE.machine_width tmp1 in
        T.immutable_array element_kind tys alloc_mode tmp2
      | Mutability.Immutable_unique =>
        fatal_errorf2 "Immutable_unique is not expected for arrays:@ %a"
          Named.print original_term
      end
    in
    let* named :=
      Named.create_prim
        (P.Variadic
           (P.Make_array array_kind mutable_or_immutable alloc_mode) args)
        dbg
    in
    let* dacc :=
      DA.map_denv dacc
        (fun denv =>
          let* denv := DE.with_typing_env denv typing_env in
          DE.add_variable denv result_var ty)
    in
    SPR.create named true dacc
  end.

(* 153-157. In the compiler: [dacc ~original_term _dbg ~args_with_tys:_
   ~result_var]. *)
Definition simplify_begin_region (dacc : DA.t) (original_term : Named.t)
    (_dbg : Debuginfo.t) (_ : list (Simple.t * T.t)) (result_var : Bound_var.t)
    : M SPR.t :=
  let& ty := T.any_region in
  let* dacc := DA.add_variable dacc result_var ty in
  Simplify_primitive_result.create original_term false dacc.

(* 159-173. In the compiler: [dacc original_prim prim ~args_with_tys dbg
   ~result_var]. *)
Definition simplify_variadic_primitive (dacc : DA.t) (original_prim : P.t)
    (prim : P.variadic_primitive) (args_with_tys : list (Simple.t * T.t))
    (dbg : Debuginfo.t) (result_var : Bound_var.t) : M SPR.t :=
  let* original_term := Named.create_prim original_prim dbg in
  (* 162-171: each case is a ported function, or one given its first
     arguments: a value. *)
  let& simplifier :=
    match prim with
    | P.Begin_region _ | P.Begin_try_region _ => simplify_begin_region
    | P.Make_block block_kind mutable_or_immutable alloc_mode =>
      simplify_make_block original_prim block_kind mutable_or_immutable
        alloc_mode
    | P.Make_array array_kind mutable_or_immutable alloc_mode =>
      simplify_make_array array_kind mutable_or_immutable alloc_mode
    end
  in
  simplifier dacc original_term dbg args_with_tys result_var.
