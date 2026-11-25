(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows
   middle_end/flambda2/simplify/inlining/inlining_transforms.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Bound_parameter Bound_parameters
  Bound_pattern Bound_var Call_kind Code Code_id Code_or_metadata Coercion
  Continuation Debuginfo Downwards_acc Downwards_env Exn_continuation
  Flambda Flambda2_types Flambda_arity Flambda_debug_uid Flambda_kind
  Inlining_helpers Lambda List ListLabels Name_mode Or_unknown Rec_info_expr
  Renaming Simple Trap_action Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Call_kind.t Flambda2_types.meet_shortcut
   Flambda2_types.reification_result Lambda.return_mode Or_unknown.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 18-21 *)
From SimplifyPort.abbrev.inlining_transforms Require Import Port_abbreviations.
(*OCAML
module DA = Downwards_acc
module DE = Downwards_env
module FT = Flambda2_types.Function_type
module VB = Bound_var
OCAML*)

(* 23-84 *)
(* PORT-GAP(loose): 81-84, the compiler does not give
   [Inlining_helpers.make_inlined_body] its argument [~region_inlined_into],
   so that the compiler's [make_inlined_body] returns a function of that
   label; here [region_inlined_into] is the last parameter (the place that
   the type of the definition gives it without labels). *)
Definition make_inlined_body (callee : option Simple.t)
    (called_code_id : Code_id.t) (unroll_to : option int)
    (params : list Bound_parameter.t) (args : Simple.List.t)
    (my_closure : Variable_.t) (my_alloc_mode : Alloc_mode.For_applications.t)
    (my_depth : Variable_.t) (rec_info : Rec_info_expr.t) (body : Expr.t)
    (exn_continuation return_continuation apply_exn_continuation
       : Continuation.t)
    (apply_return_continuation : Apply.Result_continuation.t)
    (region_inlined_into : Alloc_mode.For_applications.t) : M Expr.t :=
  (* 26-45 *)
  let* '(callee, rec_info) :=
    match callee with
    | None => ret (None, Rec_info_expr.do_not_inline)
    | Some callee =>
      match unroll_to with
      | None => ret (Some callee, rec_info)
      | Some unroll_depth =>
        let* unrolled_rec_info :=
          Rec_info_expr.unroll_to unroll_depth rec_info
        in
        let* coercion_from_callee_to_unrolled_callee :=
          let! tmp1 := Rec_info_expr.var my_depth in
          Coercion.change_depth rec_info tmp1
        in
        let* callee :=
          Simple.apply_coercion_exn callee
            coercion_from_callee_to_unrolled_callee
        in
        ret (Some callee, unrolled_rec_info)
      end
    end
  in
  (* 46 *)
  let& my_closure_duid := Flambda_debug_uid.none in
  (* 50-53 *)
  let* my_closure :=
    Bound_parameter.create my_closure Flambda_kind.With_subkind.any_value
      my_closure_duid
  in
  (* 54-69 *)
  let& bind_params :=
    fun (params : list Bound_parameter.t) (args : Simple.List.t)
        (body : Expr.t) =>
    (let! tmp1 := List.compare_lengths params args in
     if tmp1 <>? 0
     then
       let! tmp2 := Bound_parameters.create params in
       fatal_errorf4 "Mismatching parameters and arguments: %a and %a"
         Bound_parameters.print tmp2 Simple.List.print args
     else ret tt) ;;
    (* 61-68: [ListLabels.fold_left2 l1 l2 ~init ~f]: the arguments are in
       the order of the interface. [a |> f] is [f a]. *)
    let! tmp4 := List.rev args in
    let! tmp5 := List.rev params in
    ListLabels.fold_left2
      (fun (expr : Expr.t) (param : Bound_parameter.t) (arg : Simple.t) =>
        let* '(param_var, param_uid) := BP.var_and_uid param in
        let* var := Bound_var.create param_var param_uid Name_mode.normal in
        let! tmp1 := Named.create_simple arg in
        let! tmp2 := Bound_pattern.singleton var in
        let! tmp3 := Let.create tmp2 tmp1 expr Or_unknown.Unknown in
        Expr.create_let tmp3)
      body tmp5 tmp4
  in
  (* 70-80 *)
  let& bind_depth :=
    fun (my_depth : Variable_.t) (rec_info : Rec_info_expr.t)
        (body : Expr.t) =>
    let& my_depth_duid := Flambda_debug_uid.none in
    let* bound :=
      let! tmp1 := VB.create my_depth my_depth_duid Name_mode.normal in
      Bound_pattern.singleton tmp1
    in
    let! tmp1 := Named.create_rec_info rec_info in
    let! tmp2 := Let.create bound tmp1 body Or_unknown.Unknown in
    Expr.create_let tmp2
  in
  (* 81-84 *)
  Inlining_helpers.make_inlined_body callee called_code_id region_inlined_into
    params args my_closure my_alloc_mode my_depth rec_info body
    exn_continuation return_continuation apply_exn_continuation
    apply_return_continuation bind_params bind_depth Expr.apply_renaming.

(* 86-102 *)
Definition wrap_inlined_body_for_exn_extra_args
    (extra_args : list (Simple.t * Flambda_kind.With_subkind.t))
    (apply_exn_continuation : Exn_continuation.t)
    (apply_return_continuation : Apply.Result_continuation.t)
    (result_arity : Flambda_arity.t)
    (make_inlined_body :
      unit -> Continuation.t -> Apply.Result_continuation.t -> M Expr.t)
    : M Expr.t :=
  (* 88-90: [~trap_action] is given to the optional argument of
     [Apply_cont.create]. *)
  let& apply_cont_create :=
    fun (_ : unit) (trap_action : Trap_action.t) (cont : Continuation.t)
        (args : Simple.List.t) (dbg : Debuginfo.t) =>
    let! tmp1 := Apply_cont.create (Some trap_action) cont args dbg in
    Expr.create_apply_cont tmp1
  in
  (* 91-99 *)
  let& let_cont_create :=
    fun (_ : unit) (cont : Continuation.t)
        (handler_params : Bound_parameters.t) (handler body : unit -> M Expr.t)
        (is_exn_handler is_cold : bool) =>
    let* handler :=
      let! tmp1 := handler tt in
      Continuation_handler.create handler_params tmp1 Or_unknown.Unknown
        is_exn_handler is_cold
    in
    let! tmp1 := body tt in
    Let_cont.create_non_recursive cont handler tmp1 Or_unknown.Unknown
  in
  (* 100-102 *)
  Inlining_helpers.wrap_inlined_body_for_exn_extra_args tt extra_args
    apply_exn_continuation apply_return_continuation result_arity
    make_inlined_body apply_cont_create let_cont_create.

(* 103-181 *)
Definition inline (dacc : DA.t) (apply : Apply.t) (unroll_to : option int)
    (was_inline_always : bool) (function_decl : FT.t) : M (DA.t * Expr.t) :=
  let* callee := Apply.callee apply in
  (* 106-113 *)
  (let! tmp1 := Apply.call_kind apply in
   match tmp1 with
   | Call_kind.Function _ => ret tt
   | Call_kind.Method _ _ | Call_kind.C_call _ _ _ _ | Call_kind.Effect _ =>
     fatal_error
       "Trying to call [Inlining_transforms.inline] on something other than an OCaml function call."
   end) ;;
  let* region_inlined_into := Apply.return_mode apply in
  let* args := Apply.args apply in
  let* apply_return_continuation := Apply.continuation apply in
  let* apply_exn_continuation := Apply.exn_continuation apply in
  let* denv := DA.denv dacc in
  (* 120-126 *)
  let* code_or_metadata :=
    try_with
      (fun _ =>
        let! tmp1 := FT.code_id function_decl in
        DE.find_code_exn denv tmp1)
      Not_found
      (fun _ =>
        let! tmp1 := FT.code_id function_decl in
        fatal_errorf2
          "Trying to inline %a but could not find its code or metadata"
          Code_id.print tmp1)
  in
  let* code := Code_or_metadata.get_code code_or_metadata in
  (* 128-133 *)
  let* rec_info :=
    let! tmp1 := FT.rec_info function_decl in
    let! tmp2 := DE.typing_env denv in
    let! tmp3 := T.meet_rec_info tmp2 tmp1 in
    match tmp3 with
    | T.Known_result rec_info => ret rec_info
    | T.Need_meet => ret Rec_info_expr.unknown
    | T.Invalid => ret Rec_info_expr.do_not_inline
    end
  in
  (* 134-181. The call is one of the two values of the match: it is bound
     first, under a name that is not the compiler's. *)
  let* result_mode := Code.result_mode code in
  match region_inlined_into, result_mode with
  | Alloc_mode.For_applications.Not_alloc_stack _, Lambda.Maybe_alloc_stack =>
    (* The alloc_mode of the application and of the code are incompatible.
       This should have been prevented by the typer; therefore we are in
       GADT-caused unreachable code; we replace the inlined body by
       [Invalid]. *)
    let! tmp1 :=
      Expr.create_invalid
        (Flambda.Invalid.Calling_local_returning_closure_with_normal_apply
           apply)
    in
    ret (dacc, tmp1)
  | Alloc_mode.For_applications.Maybe_alloc_stack _ _ _, Lambda.Not_alloc_stack
    (* This is allowed by subtyping *)
  | Alloc_mode.For_applications.Maybe_alloc_stack _ _ _,
    Lambda.Maybe_alloc_stack
  | Alloc_mode.For_applications.Not_alloc_stack _, Lambda.Not_alloc_stack =>
    (* 146-148 *)
    let* denv := DE.enter_inlined_apply code apply was_inline_always denv in
    let* params_and_body := Code.params_and_body code in
    (* 150-181 *)
    Function_params_and_body.pattern_match params_and_body
      (fun return_continuation exn_continuation params body my_closure _
           my_alloc_mode my_depth _ =>
        (* 162-168 *)
        (* PORT-GAP(loose): the compiler gives its
           [make_inlined_body] all its arguments but
           [~apply_exn_continuation] and [~apply_return_continuation], and
           its local [make_inlined_body ()] returns a function of these
           two; here the local function takes them. *)
        let& make_inlined_body :=
          fun (_ : unit) (apply_exn_continuation : Continuation.t)
              (apply_return_continuation : Apply.Result_continuation.t) =>
          let! tmp1 := Bound_parameters.to_list params in
          let! tmp2 := Code.code_id code in
          make_inlined_body callee tmp2 unroll_to tmp1 args my_closure
            my_alloc_mode my_depth rec_info body exn_continuation
            return_continuation apply_exn_continuation
            apply_return_continuation region_inlined_into
        in
        (* 169-180 *)
        (* PORT-GAP(loose): the compiler's second case is the
           variable [extra_args], which names the scrutinee; here the
           scrutinee is bound to that name before the match. *)
        let* expr :=
          let* extra_args :=
            Exn_continuation.extra_args apply_exn_continuation
          in
          match extra_args with
          | [] =>
            let! tmp1 := Exn_continuation.exn_handler apply_exn_continuation in
            make_inlined_body tt tmp1 apply_return_continuation
          | _ :: _ =>
            let! tmp1 := Code.result_arity code in
            wrap_inlined_body_for_exn_extra_args extra_args
              apply_exn_continuation apply_return_continuation tmp1
              make_inlined_body
          end
        in
        let! tmp1 := DA.with_denv dacc denv in
        ret (tmp1, expr))
  end.
