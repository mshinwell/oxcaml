(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Guillaume Bury, Pierre Chambart and Nathanaëlle Courant, OCamlPro    *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2024 OCamlPro SAS                                    *)
(*   Copyright 2014--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplify_let_cont_expr.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the recursive functions)
   is that of GUIDE.md; the Rocq names of the fields whose names are taken
   (one or two [_] after), and of the first of the two functions
   [rebuild_let_cont] ([rebuild_let_cont_]); the three setters [update_...]
   that stand for the compiler's [{ data with ... }]. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Import Simplify_let_cont_expr__local.
From SimplifyPort.decl Require Apply_cont_rewrite Apply_cont_rewrite_id
  Are_lifting_conts Array Bound_parameter Bound_parameters Bound_pattern
  Bound_var Continuation Continuation_use_kind Continuation_uses
  Continuation_uses_env Cost_metrics Debuginfo Flambda Flambda_debug_uid
  Flambda_kind Flambda_primitive Flow Flow_types Int Join_points
  Lifted_cont_params List ListLabels Misc Name Name_mode Name_occurrences
  Non_recursive_handler Num_occurrences One_continuation_use
  One_recursive_handler Option Or_invalid Or_null Or_unknown
  Original_handlers Replay_history Simple Simplified_named Simplify_common
  Specialization_cost Unbox_continuation_params Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Are_lifting_conts.reason Are_lifting_conts.t
   Continuation.Sort.t Continuation_use_kind.t Flambda.let_cont_expr
   Flambda_primitive.nullary_primitive Num_occurrences.t Or_null.t
   Or_unknown.t Original_handlers.t Replay_history.replay_result
   Unbox_continuation_params.continuation_arg_types *)
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 1048. The module [SCC] is made by a functor of the compiler; it is at the
   head of the extracted file, not at its place. *)
(*OCAML
module SCC = Strongly_connected_components.Make (Continuation)
OCAML*)

(* High-level view of the workflow for simplification of let cont:
 *
 * +--------------------+           +--------------------+
 * | simplify_let_cont  |           | rebuild_let_cont   |
 * +--------------------+           +--------------------+
 *           |                                 ^
 *           | DOWN(body)             UP(body) |
 *           v                                 |
 * +--------------------+           +--------------------+
 * | after_downwards_   |           | prepare_to_        |
 * | traversal_of_body  |           | rebuild_body       |
 * +--------------------+           +--------------------+
 *           |                                 ^
 *           | DOWN(handlers)     UP(handlers) |
 *           v                                 |
 * +--------------------+           +--------------------+
 * | after_downwards_   |           | prepare_to_        |
 * | traversal_of_body_ |           | rebuild_handlers   |
 * | and_handlers       |           |                    |
 * +--------------------+           +--------------------+
 *           |                                 ^
 *           |       DOWN_TO_UP(global)        |
 *           +---------------------------------+
 *)

(* For each stage, the information received by this stage is of type
   stage_data. *)

(* 47-49 *)
Inductive one_original_handler : Type :=
| Rec : One_recursive_handler.t -> one_original_handler
| Non_rec : Non_recursive_handler.t -> one_original_handler.

(* 51-54 *)
(* Two later records of the file have a field [handlers] too. Rocq has one
   name space, and the plain name is that of the field of the last of the
   three (the record that the file updates): this Rocq record has [handlers_],
   and Rocq prints the compiler's definition and reads each field with the
   type written. *)
Record simplify_let_cont_data_ : Type := {
  body : Expr.t;
  handlers_ : Original_handlers.t
}.
Extract Inductive simplify_let_cont_data_ => "simplify_let_cont_data"
  [ "(fun (x__1, x__2) -> ({ body = x__1; handlers = x__2 } : simplify_let_cont_data))" ]
  "(fun f__1 x__0 -> let ({ body = x__1; handlers = x__2 } : simplify_let_cont_data) = x__0 in f__1 x__1 x__2)".
Extract Inlined Constant body =>
  "(fun (x__0 : simplify_let_cont_data) -> x__0.body)".
Extract Inlined Constant handlers_ =>
  "(fun (x__0 : simplify_let_cont_data) -> x__0.handlers)".
Definition simplify_let_cont_data : Type := simplify_let_cont_data_.
Extract Constant simplify_let_cont_data =>
  "{ body : Expr.t; handlers : Original_handlers.t }".

(* 56-60 *)
(* The name of the field [handlers] is taken in Rocq (see
   [simplify_let_cont_data]): the Rocq record has [handlers__], and Rocq
   prints the compiler's definition and the compiler's fields. *)
Record after_downwards_traversal_of_body_data_ : Type := {
  denv_for_join : DE.t;
  prior_lifted_constants : LCS.t;
  handlers__ : Original_handlers.t
}.
Extract Inductive after_downwards_traversal_of_body_data_ => "after_downwards_traversal_of_body_data"
  [ "(fun (x__1, x__2, x__3) -> ({ denv_for_join = x__1; prior_lifted_constants = x__2; handlers = x__3 } : after_downwards_traversal_of_body_data))" ]
  "(fun f__1 x__0 -> let ({ denv_for_join = x__1; prior_lifted_constants = x__2; handlers = x__3 } : after_downwards_traversal_of_body_data) = x__0 in f__1 x__1 x__2 x__3)".
Extract Inlined Constant denv_for_join =>
  "(fun (x__0 : after_downwards_traversal_of_body_data) -> x__0.denv_for_join)".
Extract Inlined Constant prior_lifted_constants =>
  "(fun (x__0 : after_downwards_traversal_of_body_data) -> x__0.prior_lifted_constants)".
Extract Inlined Constant handlers__ =>
  "(fun (x__0 : after_downwards_traversal_of_body_data) -> x__0.handlers)".
Definition after_downwards_traversal_of_body_data : Type := after_downwards_traversal_of_body_data_.
Extract Constant after_downwards_traversal_of_body_data =>
  "{ denv_for_join : DE.t; prior_lifted_constants : LCS.t; handlers : Original_handlers.t }".

(* 62-75 *)
Record handler_after_downwards_traversal : Type := {
  original : one_original_handler;
  params : Bound_parameters.t;
  simplified_handler : Simplified_expr.t;
  is_exn_handler : bool;
  is_cold : bool;
  (* continuations_used is the set of which continuations from this block of
     mutually recursive continuations is used inside the handler *)
  continuations_used : Continuation.Set_.t;
  unbox_decisions : Unbox_continuation_params.Decisions.t;
  extra_params_and_args : EPA.t
      (* These extra params and args are generated by the CSE and the
         continuation lifting process. *)
}.

(* 77-100 *)
(* The name of the field [after_downwards_traversal_of_body] is taken in Rocq
   (a function of the file): the Rocq record has
   [after_downwards_traversal_of_body_]; its field [handlers] has the plain
   name (see [simplify_let_cont_data]). Rocq prints the compiler's definition
   (without its comments, which are here) and the compiler's fields. *)
Record after_downwards_traversal_of_body_and_handlers_data_ : Type := {
  after_downwards_traversal_of_body_ : after_downwards_traversal_of_body_data;
  cont_uses_env_after_body : CUE.t;
  (* used for specialization *)
  dacc_after_body : DA.t;
  simplified_body : Simplified_expr.t;
  cont_uses_env : CUE.t;
  (* total cont uses env in body + handlers, including the uses of the
     continuations currently being bound *)
  at_unit_toplevel : bool;
  consts_lifted_during_body : Lifted_constant_state.t;
  consts_lifted_after_fork : Lifted_constant_state.t;
  (* We need to keep a copy of the constants lifted during the body, separate
     from the constants lifted after the fork (i.e. those from the body
     **and** the handlers (there may be multiple handlers, e.g. during
     specialization, or for recursive continuations)), because when
     specializing a continuation, the consts lifted from the first downwards
     pass on the handler must be dropped (but those from the body must be
     kept), since we forget everything that happened during that pass. *)
  lifted_params : Lifted_cont_params.t;
  invariant_params : Bound_parameters.t;
  invariant_extra_params_and_args : EPA.t;
  handlers : Continuation.Map.t handler_after_downwards_traversal
}.
Extract Inductive after_downwards_traversal_of_body_and_handlers_data_ => "after_downwards_traversal_of_body_and_handlers_data"
  [ "(fun (x__1, x__2, x__3, x__4, x__5, x__6, x__7, x__8, x__9, x__10, x__11, x__12) -> ({ after_downwards_traversal_of_body = x__1; cont_uses_env_after_body = x__2; dacc_after_body = x__3; simplified_body = x__4; cont_uses_env = x__5; at_unit_toplevel = x__6; consts_lifted_during_body = x__7; consts_lifted_after_fork = x__8; lifted_params = x__9; invariant_params = x__10; invariant_extra_params_and_args = x__11; handlers = x__12 } : after_downwards_traversal_of_body_and_handlers_data))" ]
  "(fun f__1 x__0 -> let ({ after_downwards_traversal_of_body = x__1; cont_uses_env_after_body = x__2; dacc_after_body = x__3; simplified_body = x__4; cont_uses_env = x__5; at_unit_toplevel = x__6; consts_lifted_during_body = x__7; consts_lifted_after_fork = x__8; lifted_params = x__9; invariant_params = x__10; invariant_extra_params_and_args = x__11; handlers = x__12 } : after_downwards_traversal_of_body_and_handlers_data) = x__0 in f__1 x__1 x__2 x__3 x__4 x__5 x__6 x__7 x__8 x__9 x__10 x__11 x__12)".
Extract Inlined Constant after_downwards_traversal_of_body_ =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.after_downwards_traversal_of_body)".
Extract Inlined Constant cont_uses_env_after_body =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.cont_uses_env_after_body)".
Extract Inlined Constant dacc_after_body =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.dacc_after_body)".
Extract Inlined Constant simplified_body =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.simplified_body)".
Extract Inlined Constant cont_uses_env =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.cont_uses_env)".
Extract Inlined Constant at_unit_toplevel =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.at_unit_toplevel)".
Extract Inlined Constant consts_lifted_during_body =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.consts_lifted_during_body)".
Extract Inlined Constant consts_lifted_after_fork =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.consts_lifted_after_fork)".
Extract Inlined Constant lifted_params =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.lifted_params)".
Extract Inlined Constant invariant_params =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.invariant_params)".
Extract Inlined Constant invariant_extra_params_and_args =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.invariant_extra_params_and_args)".
Extract Inlined Constant handlers =>
  "(fun (x__0 : after_downwards_traversal_of_body_and_handlers_data) -> x__0.handlers)".
Definition after_downwards_traversal_of_body_and_handlers_data : Type := after_downwards_traversal_of_body_and_handlers_data_.
Extract Constant after_downwards_traversal_of_body_and_handlers_data =>
  "{ after_downwards_traversal_of_body : after_downwards_traversal_of_body_data; cont_uses_env_after_body : CUE.t; dacc_after_body : DA.t; simplified_body : Simplified_expr.t; cont_uses_env : CUE.t; at_unit_toplevel : bool; consts_lifted_during_body : Lifted_constant_state.t; consts_lifted_after_fork : Lifted_constant_state.t; lifted_params : Lifted_cont_params.t; invariant_params : Bound_parameters.t; invariant_extra_params_and_args : EPA.t; handlers : handler_after_downwards_traversal Continuation.Map.t }".

(* 102-107 *)
Record rebuilt_handler : Type := {
  handler : Rebuilt_expr.Continuation_handler.t;
  handler_expr : Rebuilt_expr.t;
  name_occurrences_of_handler : Name_occurrences.t;
  cost_metrics_of_handler : Cost_metrics.t
}.

(* 109-117 *)
(* The type has two inline records; the fields are by place, as in decl/, and
   Rocq prints the compiler's definition. *)
Inductive rebuilt_handlers_group_ : Type :=
| Recursive :
    Continuation.Lmap.t rebuilt_handler -> Bound_parameters.t ->
    rebuilt_handlers_group_
| Non_recursive : Continuation.t -> rebuilt_handler -> rebuilt_handlers_group_.
Extract Inductive rebuilt_handlers_group_ => "rebuilt_handlers_group"
  [ "(fun (x__1, x__2) -> (Recursive { continuation_handlers = x__1; invariant_params = x__2 } : rebuilt_handlers_group))"
    "(fun (x__1, x__2) -> (Non_recursive { cont = x__1; handler = x__2 } : rebuilt_handlers_group))" ]
  "(fun f__1 f__2 x__0 -> match (x__0 : rebuilt_handlers_group) with Recursive { continuation_handlers = x__1; invariant_params = x__2 } -> f__1 x__1 x__2 | Non_recursive { cont = x__1; handler = x__2 } -> f__2 x__1 x__2)".
Definition rebuilt_handlers_group : Type := rebuilt_handlers_group_.
Extract Constant rebuilt_handlers_group =>
  "| Recursive of { continuation_handlers : rebuilt_handler Continuation.Lmap.t; invariant_params : Bound_parameters.t } | Non_recursive of { cont : Continuation.t; handler : rebuilt_handler }".

(* 119-125 *)
(* The name of the field [simplified_body] is taken in Rocq: the Rocq record
   has [simplified_body_], and Rocq prints the compiler's definition and the
   compiler's fields. *)
Record prepare_to_rebuild_body_data_ (A : Type) : Type := {
  simplified_body_ : A;
  handlers_from_the_inside_to_the_outside : list rebuilt_handlers_group;
  name_occurrences_of_subsequent_exprs : Name_occurrences.t;
  cost_metrics_of_subsequent_exprs : Cost_metrics.t;
  uenv_of_subsequent_exprs : UE.t
}.
Arguments simplified_body_ {A}.
Arguments handlers_from_the_inside_to_the_outside {A}.
Arguments name_occurrences_of_subsequent_exprs {A}.
Arguments cost_metrics_of_subsequent_exprs {A}.
Arguments uenv_of_subsequent_exprs {A}.
Extract Inductive prepare_to_rebuild_body_data_ => "prepare_to_rebuild_body_data"
  [ "(fun (x__1, x__2, x__3, x__4, x__5) -> ({ simplified_body = x__1; handlers_from_the_inside_to_the_outside = x__2; name_occurrences_of_subsequent_exprs = x__3; cost_metrics_of_subsequent_exprs = x__4; uenv_of_subsequent_exprs = x__5 } : _ prepare_to_rebuild_body_data))" ]
  "(fun f__1 x__0 -> let ({ simplified_body = x__1; handlers_from_the_inside_to_the_outside = x__2; name_occurrences_of_subsequent_exprs = x__3; cost_metrics_of_subsequent_exprs = x__4; uenv_of_subsequent_exprs = x__5 } : _ prepare_to_rebuild_body_data) = x__0 in f__1 x__1 x__2 x__3 x__4 x__5)".
Extract Inlined Constant simplified_body_ =>
  "(fun (x__0 : _ prepare_to_rebuild_body_data) -> x__0.simplified_body)".
Extract Inlined Constant handlers_from_the_inside_to_the_outside =>
  "(fun (x__0 : _ prepare_to_rebuild_body_data) -> x__0.handlers_from_the_inside_to_the_outside)".
Extract Inlined Constant name_occurrences_of_subsequent_exprs =>
  "(fun (x__0 : _ prepare_to_rebuild_body_data) -> x__0.name_occurrences_of_subsequent_exprs)".
Extract Inlined Constant cost_metrics_of_subsequent_exprs =>
  "(fun (x__0 : _ prepare_to_rebuild_body_data) -> x__0.cost_metrics_of_subsequent_exprs)".
Extract Inlined Constant uenv_of_subsequent_exprs =>
  "(fun (x__0 : _ prepare_to_rebuild_body_data) -> x__0.uenv_of_subsequent_exprs)".
Definition prepare_to_rebuild_body_data (A : Type) : Type := prepare_to_rebuild_body_data_ A.
Extract Constant prepare_to_rebuild_body_data "'a" =>
  "{ simplified_body : 'a; handlers_from_the_inside_to_the_outside : rebuilt_handlers_group list; name_occurrences_of_subsequent_exprs : Name_occurrences.t; cost_metrics_of_subsequent_exprs : Cost_metrics.t; uenv_of_subsequent_exprs : UE.t }".

(* 127-132 *)
(* The names of the four fields are taken in Rocq (by the fields of
   [prepare_to_rebuild_body_data]): the Rocq record has them with one [_]
   after, and Rocq prints the compiler's definition and the compiler's
   fields. *)
Record rebuild_let_cont_data_ : Type := {
  handlers_from_the_inside_to_the_outside_ : list rebuilt_handlers_group;
  name_occurrences_of_subsequent_exprs_ : Name_occurrences.t;
  cost_metrics_of_subsequent_exprs_ : Cost_metrics.t;
  uenv_of_subsequent_exprs_ : UE.t
}.
Extract Inductive rebuild_let_cont_data_ => "rebuild_let_cont_data"
  [ "(fun (x__1, x__2, x__3, x__4) -> ({ handlers_from_the_inside_to_the_outside = x__1; name_occurrences_of_subsequent_exprs = x__2; cost_metrics_of_subsequent_exprs = x__3; uenv_of_subsequent_exprs = x__4 } : rebuild_let_cont_data))" ]
  "(fun f__1 x__0 -> let ({ handlers_from_the_inside_to_the_outside = x__1; name_occurrences_of_subsequent_exprs = x__2; cost_metrics_of_subsequent_exprs = x__3; uenv_of_subsequent_exprs = x__4 } : rebuild_let_cont_data) = x__0 in f__1 x__1 x__2 x__3 x__4)".
Extract Inlined Constant handlers_from_the_inside_to_the_outside_ =>
  "(fun (x__0 : rebuild_let_cont_data) -> x__0.handlers_from_the_inside_to_the_outside)".
Extract Inlined Constant name_occurrences_of_subsequent_exprs_ =>
  "(fun (x__0 : rebuild_let_cont_data) -> x__0.name_occurrences_of_subsequent_exprs)".
Extract Inlined Constant cost_metrics_of_subsequent_exprs_ =>
  "(fun (x__0 : rebuild_let_cont_data) -> x__0.cost_metrics_of_subsequent_exprs)".
Extract Inlined Constant uenv_of_subsequent_exprs_ =>
  "(fun (x__0 : rebuild_let_cont_data) -> x__0.uenv_of_subsequent_exprs)".
Definition rebuild_let_cont_data : Type := rebuild_let_cont_data_.
Extract Constant rebuild_let_cont_data =>
  "{ handlers_from_the_inside_to_the_outside : rebuilt_handlers_group list; name_occurrences_of_subsequent_exprs : Name_occurrences.t; cost_metrics_of_subsequent_exprs : Cost_metrics.t; uenv_of_subsequent_exprs : UE.t }".

(* Helpers *)

(* 136-150 *)
Definition split_non_recursive_let_cont (can_be_lifted : bool)
    (handler : Non_recursive_let_cont_handler.t)
    : M (Expr.t * Non_recursive_handler.t) :=
  let* '(cont, body) :=
    Non_recursive_let_cont_handler.pattern_match handler
      (fun cont body => ret (cont, body))
  in
  let* cont_handler := Non_recursive_let_cont_handler.handler handler in
  let* is_exn_handler := CH.is_exn_handler cont_handler in
  let* is_cold := CH.is_cold cont_handler in
  let* '(params, handler) :=
    CH.pattern_match cont_handler (fun params handler => ret (params, handler))
  in
  let! tmp1 :=
    Non_recursive_handler.create cont params Lifted_cont_params.empty handler
      is_exn_handler can_be_lifted is_cold
  in
  ret (body, tmp1).

(* 152-168 *)
Definition split_recursive_let_cont (handlers : Recursive_let_cont_handlers.t)
    : M (tuple3 Expr.t Bound_parameters.t
           (Continuation.Lmap.t One_recursive_handler.t)) :=
  let* '(T3 invariant_params body rec_handlers) :=
    Recursive_let_cont_handlers.pattern_match handlers
      (fun invariant_params body rec_handlers =>
        ret (T3 invariant_params body rec_handlers))
  in
  (let! tmp1 := Continuation_handlers.contains_exn_handler rec_handlers in
   assert_ (negb tmp1)) ;;
  let* handlers := Continuation_handlers.to_map rec_handlers in
  let* continuation_handlers :=
    Continuation.Lmap.map
      (fun handler =>
        let* is_cold := CH.is_cold handler in
        CH.pattern_match handler
          (fun params handler =>
            One_recursive_handler.create params handler is_cold))
      handlers
  in
  ret (T3 body invariant_params continuation_handlers).

(* 170-190 *)
Definition extra_params_and_args_for_lifting
    (callee_lifted_params : Lifted_cont_params.t)
    (uses : list One_continuation_use.t) : M EPA.t :=
  let* epa :=
    let! tmp1 := Lifted_cont_params.bound_parameters callee_lifted_params in
    EPA.init_with_params_only tmp1
  in
  List.fold_left
    (fun epa one_use =>
      let* id := One_continuation_use.id one_use in
      let* env_at_use := One_continuation_use.env_at_use one_use in
      let* caller_stack_lifted_params :=
        DE.defined_variables_by_scope env_at_use
      in
      let* args :=
        Lifted_cont_params.args callee_lifted_params
          caller_stack_lifted_params
      in
      let* extra_args :=
        List.map (fun arg => ret (EPA.Extra_arg.Already_in_scope arg)) args
      in
      EPA.add_args_for_all_params epa id extra_args)
    epa uses.

(* 192-225 *)
Definition arg_types_by_use_id_for_lifting
    (callee_lifted_params : Lifted_cont_params.t)
    (uses : list One_continuation_use.t)
    : M Continuation_uses.arg_types_by_use_id :=
  let* bound_callee_params :=
    let! tmp1 := Lifted_cont_params.bound_parameters callee_lifted_params in
    Bound_parameters.to_list tmp1
  in
  let! tmp1 :=
    List.map
      (fun _ =>
        ret
          (Apply_cont_rewrite_id.Map.empty
            : Apply_cont_rewrite_id.Map.t Continuation_uses.arg_at_use))
      bound_callee_params
  in
  List.fold_left
    (fun arg_types_by_use_id one_use =>
      let* id := One_continuation_use.id one_use in
      let* env_at_use := One_continuation_use.env_at_use one_use in
      let* caller_stack_lifted_params :=
        DE.defined_variables_by_scope env_at_use
      in
      let* args :=
        Lifted_cont_params.args callee_lifted_params
          caller_stack_lifted_params
      in
      let* lifted_arg_types :=
        List.map2
          (fun arg param =>
            (* PORT-GAP(record-order): 211-217, a record with a call in
               each of its two fields, which the compiler writes
               [typing_env] first; here in the order of the type
               ([arg_type], [typing_env]), the last field first. *)
            let* typing_env := DE.typing_env env_at_use in
            let* arg_type :=
              let! tmp2 := Bound_parameter.kind param in
              let! tmp3 := KS.kind tmp2 in
              Flambda2_types.alias_type_of tmp3 arg
            in
            ret
              {| Continuation_uses.arg_type := arg_type;
                 Continuation_uses.typing_env := typing_env |})
          args bound_callee_params
      in
      List.map2
        (fun arg_type_by_use_id arg_type =>
          Apply_cont_rewrite_id.Map.add id arg_type arg_type_by_use_id)
        arg_types_by_use_id lifted_arg_types)
    tmp1 uses.

(* 227-259 *)
Definition decide_param_usage_non_recursive (free_names : NO.t)
    (required_names : Name.Set_.t) (removed_aliased : Variable_.Set_.t)
    (exn_bucket : option Variable_.t) (param : BP.t)
    : M Apply_cont_rewrite.used :=
  (* The free_names computation is the reference here, because it records
     precisely what is actually used in the term being rebuilt. The required
     variables computed by the data_flow analysis can only be an over
     approximation of it here (given that some simplification/dead code
     elimination may have removed some uses on the way up). To make sure the
     data_flow analysis is correct (or rather than the pre-condition for its
     correctness are verified, i.e. that on the way down, the use constraints
     accumulated are an over-approximation of the actual use constraints), we
     check here that all actually-used variables were also marked as used by the
     data_flow analysis. *)
  let* param_var := BP.var param in
  let* is_used :=
    let! tmp1 := NO.count_variable_normal_mode free_names param_var in
    match tmp1 with
    | Num_occurrences.Zero =>
      Option.equal Variable_.equal exn_bucket (Some param_var)
    | Num_occurrences.One | Num_occurrences.More_than_one => ret true
    end
  in
  (* 245-251 *)
  (let! tmp1 :=
     and_then is_used
       (let! tmp2 := Name.var param_var in
        let! tmp3 := Name.Set_.mem tmp2 required_names in
        ret (negb tmp3))
   in
   if tmp1
   then
     fatal_errorf4
       "The data_flow analysis marked the param %a@ as not required, but the free_names indicate it is actually used:@ 
free_names = %a"
       BP.print param NO.print free_names
   else ret tt) ;;
  (* 252-258 *)
  (let! tmp1 :=
     and_then is_used (Variable_.Set_.mem param_var removed_aliased)
   in
   if tmp1
   then
     fatal_errorf4
       "The alias analysis marked the param %a@ as removed, but the free_names indicate it is actually used:@ 
free_names = %a"
       BP.print param NO.print free_names
   else ret tt) ;;
  if is_used then ret Apply_cont_rewrite.Used else ret Apply_cont_rewrite.Unused.

(* 261-270 *)
Definition decide_param_usage_recursive (required_names : Name.Set_.t)
    (invariant_set : Bound_parameter.Set_.t)
    (removed_aliased : Variable_.Set_.t) (param : BP.t)
    : M Apply_cont_rewrite.used :=
  let! tmp1 := BP.name param in
  let! tmp2 := Name.Set_.mem tmp1 required_names in
  let! tmp3 :=
    and_then tmp2
      (let! tmp4 := BP.var param in
       let! tmp5 := Variable_.Set_.mem tmp4 removed_aliased in
       ret (negb tmp5))
  in
  if tmp3
  then
    let! tmp1 := Bound_parameter.Set_.mem param invariant_set in
    if tmp1
    then ret Apply_cont_rewrite.Used_as_invariant
    else ret Apply_cont_rewrite.Used
  else ret Apply_cont_rewrite.Unused.

(* 272-312 *)
Definition extra_params_for_continuation_param_aliases (cont : Continuation.t)
    (uacc : UA.t) (rewrite_ids : Apply_cont_rewrite_id.Set_.t) : M EPA.t :=
  let* '{| Flow_types.Alias_result.aliases_kind := aliases_kind;
           Flow_types.Alias_result.continuation_parameters :=
             continuation_parameters |} :=
    UA.continuation_param_aliases uacc
  in
  let* required_extra_args :=
    Continuation.Map.find cont continuation_parameters
  in
  (* We don't want to add the extra params and args according to the order of
     the Int_ids hash, because that is unstable and produces noise in fexpr
     dumps.

     Ideally, we'd want to create the parameters according to the binding times
     of the original variables, but currently binding times are not comparable
     across scopes, so we instead sort the extra args according to their name
     stamp, which should be a good enough approximation for now. *)
  (* 287-292: [a |> f b] is [f b a]; the comparison takes two pairs
     apart. *)
  let* extra_args_for_aliases_sorted_by_stamp :=
    let! tmp1 :=
      Variable_.Set_.fold
        (fun var acc =>
          let! tmp2 := Variable_.name_stamp var in
          ret ((tmp2, var) :: acc))
        required_extra_args.(Flow_types.Continuation_param_aliases.extra_args_for_aliases)
        []
    in
    List.sort
      (fun pat1 pat2 =>
        let* '(stamp1, _) := ret pat1 in
        let* '(stamp2, _) := ret pat2 in
        Int.compare stamp2 stamp1)
      tmp1
  in
  List.fold_left
    (fun epa '(_stamp, var) =>
      let* extra_args :=
        Apply_cont_rewrite_id.Map.of_set
          (fun _id =>
            let! tmp1 := Simple.var var in
            ret (EPA.Extra_arg.Already_in_scope tmp1))
          rewrite_ids
      in
      let& var_duid := Flambda_debug_uid.none in
      let* var_kind :=
        let! tmp1 := Variable_.Map.find var aliases_kind in
        Flambda_kind.With_subkind.anything tmp1
      in
      let! tmp1 := Bound_parameter.create var var_kind var_duid in
      EPA.add epa Apply_cont_rewrite_id.Set_.empty tmp1 extra_args)
    EPA.empty extra_args_for_aliases_sorted_by_stamp.

(* 314-321 *)
Definition add_extra_params_for_mutable_unboxing (cont : Continuation.t)
    (uacc : UA.t) (extra_params_and_args : EPA.t) : M EPA.t :=
  let* '{| Flow_types.Mutable_unboxing_result.did_unbox_a_mutable_block := _;
           Flow_types.Mutable_unboxing_result.additional_epa := additional_epa;
           Flow_types.Mutable_unboxing_result.let_rewrites := _ |} :=
    UA.mutable_unboxing_result uacc
  in
  let! tmp1 := Continuation.Map.find_or_null cont additional_epa in
  match tmp1 with
  | Or_null.Null => ret extra_params_and_args
  | Or_null.This additional_epa =>
    EPA.concat additional_epa extra_params_and_args
  end.

(* 323-326 *)
Inductive behaviour : Type :=
| Invalid : behaviour
| Shortcut_to : Continuation.t -> list Simple.t -> behaviour
| Unknown : behaviour.

(* 328-333 *)
Definition get_removed_aliased_params (uacc : UA.t) (cont : Continuation.t)
    : M Variable_.Set_.t :=
  let* param_aliases := UA.continuation_param_aliases uacc in
  let* cont_params :=
    Continuation.Map.find cont
      param_aliases.(Flow_types.Alias_result.continuation_parameters)
  in
  ret
    cont_params.(Flow_types.Continuation_param_aliases.removed_aliased_params_and_extra_params).

(* 335-381 *)
Definition make_rewrite_for_recursive_continuation (uacc : UA.t)
    (cont : Continuation.t) (is_cold : bool)
    (original_invariant_params : Bound_parameters.t)
    (invariant_extra_params_and_args : EPA.t)
    (original_variant_params : Bound_parameters.t)
    (variant_extra_params_and_args : EPA.t)
    (rewrite_ids : Apply_cont_rewrite_id.Set_.t) : M UA.t :=
  (* Note: extra_params_and_args come from CSE & immutable unboxing *)
  let* alias_epa :=
    extra_params_for_continuation_param_aliases cont uacc rewrite_ids
  in
  let* invariant_extra_params_and_args :=
    EPA.concat alias_epa invariant_extra_params_and_args
  in
  let* variant_extra_params_and_args :=
    add_extra_params_for_mutable_unboxing cont uacc
      variant_extra_params_and_args
  in
  let* required_names := UA.required_names uacc in
  let* removed_aliased := get_removed_aliased_params uacc cont in
  (* 351-356 *)
  let* invariant_set :=
    let! tmp1 := EPA.extra_params invariant_extra_params_and_args in
    let! tmp2 := Bound_parameters.to_set tmp1 in
    let! tmp3 := Bound_parameters.to_set original_invariant_params in
    BP.Set_.union tmp3 tmp2
  in
  (* 357-359: a function of this file, given its first arguments. *)
  let& decide_param_usage :=
    decide_param_usage_recursive required_names invariant_set removed_aliased
  in
  (* 360-369 *)
  let* rewrite :=
    let! tmp1 :=
      EPA.concat invariant_extra_params_and_args variant_extra_params_and_args
    in
    let! tmp2 :=
      Bound_parameters.append original_invariant_params
        original_variant_params
    in
    Apply_cont_rewrite.create tmp2 tmp1 decide_param_usage
  in
  let* '(invariant_params, variant_params) :=
    Apply_cont_rewrite.get_used_params rewrite
  in
  let* params := Bound_parameters.append invariant_params variant_params in
  (* 374-380 *)
  let* uacc :=
    UA.map_uenv uacc
      (fun uenv =>
        let* uenv := UE.add_apply_cont_rewrite uenv cont rewrite in
        let! tmp1 := UA.are_rebuilding_terms uacc in
        UE.add_non_inlinable_continuation tmp1 uenv cont is_cold params
          Or_unknown.Unknown)
  in
  ret uacc.

(* 383-522 *)
(* PORT-GAP(loose): 383, the compiler defines [rebuild_let_cont] twice (here
   and at 961, which hides this one); Rocq has one name space, and this
   first one has one [_] after its name. *)
Definition rebuild_let_cont_ (data : rebuild_let_cont_data)
    (after_rebuild : Simplify_common.after_rebuild) (body : RE.t)
    (uacc : UA.t) : M (RE.t * UA.t) :=
  (* Here both the body and the handlers have been rebuilt. We only need to
     restore the cost metrics and name occurrences accumulators, rebuild all the
     let cont expressions, and call after_rebuild with the result and the new
     upwards accumulator. *)
  let* name_occurrences_body := UA.name_occurrences uacc in
  let* cost_metrics_of_body := UA.cost_metrics uacc in
  (* 390-520: a local [let rec], on the list [groups]. *)
  let rebuild_groups :=
    fix rebuild_groups (body : RE.t) (name_occurrences_body : NO.t)
        (cost_metrics_of_body : Cost_metrics.t) (uacc : UA.t)
        (groups : list rebuilt_handlers_group) {struct groups}
        : M (RE.t * UA.t) :=
      match groups with
      | [] =>
        (* Everything has now been rebuilt.

           We correctly set the name occurrences and the cost metrics, and we
           restore the upwards environment of [uacc] so that out-of-scope
           continuation bindings do not end up in the accumulator. *)
        let* uacc :=
          let! tmp1 :=
            Name_occurrences.union name_occurrences_body
              data.(name_occurrences_of_subsequent_exprs_)
          in
          UA.with_name_occurrences uacc tmp1
        in
        let* uacc :=
          let! tmp1 :=
            Cost_metrics.op_plus cost_metrics_of_body
              data.(cost_metrics_of_subsequent_exprs_)
          in
          UA.with_cost_metrics tmp1 uacc
        in
        let* uacc := UA.with_uenv uacc data.(uenv_of_subsequent_exprs_) in
        after_rebuild body uacc
      | Non_recursive cont handler :: groups =>
        let* num_free_occurrences_of_cont_in_body :=
          (* Note that this does not count uses in trap actions. If there are uses
             in trap actions, but [remove_let_cont_leaving_body] is [true] below,
             then this must be a case where the exception handler can be demoted
             to a normal handler. This will cause the trap actions to be
             erased. *)
          NO.count_continuation name_occurrences_body cont
        in
        let* is_applied_with_traps :=
          NO.continuation_is_applied_with_traps name_occurrences_body cont
        in
        let* remove_let_cont_leaving_body :=
          match num_free_occurrences_of_cont_in_body with
          | Num_occurrences.Zero => ret true
          | Num_occurrences.One | Num_occurrences.More_than_one => ret false
          end
        in
        (* We are passing back over a binder, so remove the bound continuation
           from the free name information. Then compute the free names of the
           whole [Let_cont]. *)
        let* name_occurrences_body :=
          NO.remove_continuation name_occurrences_body cont
        in
        (* Having rebuilt both the body and handler, the [Let_cont] expression
           itself is rebuilt -- unless either the continuation had zero uses, in
           which case we're left with the body; or if the body is just an
           [Apply_cont] (with no trap action) of [cont], in which case we're left
           with the handler. *)
        (* 442-482 *)
        let* '(T3 expr name_occurrences cost_metrics) :=
          if remove_let_cont_leaving_body
          then ret (T3 body name_occurrences_body cost_metrics_of_body)
          else
            let* remove_let_cont_leaving_handler :=
              let! tmp1 := RE.to_apply_cont body in
              match tmp1 with
              | Some apply_cont =>
                let! tmp1 := Apply_cont.continuation apply_cont in
                let! tmp2 := Continuation.equal cont tmp1 in
                if negb tmp2
                then ret false
                else
                  let! tmp1 := Apply_cont.args apply_cont in
                  match tmp1 with
                  | [] =>
                    let! tmp1 := Apply_cont.trap_action apply_cont in
                    Option.is_none tmp1
                  | _ :: _ => ret false
                  end
              | None => ret false
              end
            in
            if remove_let_cont_leaving_handler
            then
              let! tmp1 := Cost_metrics.removed cost_metrics_of_body in
              let! tmp2 :=
                Cost_metrics.notify_removed tmp1
                  handler.(cost_metrics_of_handler)
              in
              ret
                (T3 handler.(handler_expr)
                   handler.(name_occurrences_of_handler) tmp2)
            else
              let* name_occurrences :=
                NO.union name_occurrences_body
                  handler.(name_occurrences_of_handler)
              in
              let* cost_metrics :=
                let! tmp1 :=
                  Cost_metrics.increase_due_to_let_cont_non_recursive
                    handler.(cost_metrics_of_handler)
                in
                Cost_metrics.op_plus cost_metrics_of_body tmp1
              in
              let* expr :=
                let! tmp1 := UA.are_rebuilding_terms uacc in
                RE.create_non_recursive_let_cont' tmp1 cont
                  handler.(Simplify_let_cont_expr.handler) body
                  num_free_occurrences_of_cont_in_body is_applied_with_traps
              in
              ret (T3 expr name_occurrences cost_metrics)
        in
        rebuild_groups expr name_occurrences cost_metrics uacc groups
      | Recursive continuation_handlers invariant_params :: groups =>
        let* rec_handlers :=
          Continuation.Lmap.map
            (fun handler => ret handler.(Simplify_let_cont_expr.handler))
            continuation_handlers
        in
        let* expr :=
          let! tmp1 := UA.are_rebuilding_terms uacc in
          RE.create_recursive_let_cont tmp1 invariant_params rec_handlers body
        in
        let* name_occurrences :=
          Continuation.Lmap.fold
            (fun _ handler name_occurrences =>
              let! tmp1 :=
                NO.increase_counts handler.(name_occurrences_of_handler)
              in
              NO.union name_occurrences tmp1)
            continuation_handlers name_occurrences_body
        in
        let* name_occurrences :=
          Continuation.Lmap.fold
            (fun cont _ name_occurrences =>
              NO.remove_continuation name_occurrences cont)
            continuation_handlers name_occurrences
        in
        let* cost_metrics_of_handlers :=
          Continuation.Lmap.fold
            (fun _ handler cost_metrics =>
              Cost_metrics.op_plus cost_metrics
                handler.(cost_metrics_of_handler))
            continuation_handlers Cost_metrics.zero
        in
        let* cost_metrics :=
          Cost_metrics.increase_due_to_let_cont_recursive
            cost_metrics_of_handlers
        in
        let* cost_metrics :=
          Cost_metrics.op_plus cost_metrics cost_metrics_of_body
        in
        rebuild_groups expr name_occurrences cost_metrics uacc groups
      end
  in
  rebuild_groups body name_occurrences_body cost_metrics_of_body uacc
    data.(handlers_from_the_inside_to_the_outside_).

(* 524-544 *)
Definition prepare_to_rebuild_body {A : Type}
    (rebuild_body : Simplify_common.rebuild A)
    (data : prepare_to_rebuild_body_data A) (uacc : UA.t)
    (after_rebuild : Simplify_common.after_rebuild) : M (RE.t * UA.t) :=
  (* At this point all handlers have been rebuild and added to the upwards
     environment. All that we still need to do is to rebuild the body, and then
     rebuild the chain of let cont expressions once this is done. We reinit the
     name occurrences and cost metrics one last time to get precise information
     for those two in the body, we rebuild the body, and we pass on to the final
     stage for the reconstruction of the let cont expressions. *)
  let* uacc :=
    let! tmp1 := UA.clear_name_occurrences uacc in
    UA.clear_cost_metrics tmp1
  in
  let& simplified_body := data.(simplified_body_) in
  (* 534-542: the fields in the order of the type. *)
  let& data :=
    ({| handlers_from_the_inside_to_the_outside_ :=
          data.(handlers_from_the_inside_to_the_outside);
        name_occurrences_of_subsequent_exprs_ :=
          data.(name_occurrences_of_subsequent_exprs);
        cost_metrics_of_subsequent_exprs_ :=
          data.(cost_metrics_of_subsequent_exprs);
        uenv_of_subsequent_exprs_ := data.(uenv_of_subsequent_exprs) |}
      : rebuild_let_cont_data)
  in
  rebuild_body simplified_body uacc
    (fun body uacc => rebuild_let_cont_ data after_rebuild body uacc).

(* 546-603 *)
Definition add_lets_around_handler (cont : Continuation.t)
    (at_unit_toplevel : bool) (uacc : UA.t) (handler : RE.t)
    : M (tuple4 RE.t UA.t NO.t Cost_metrics.t) :=
  let* '{| Flow_types.Alias_result.aliases_kind := _;
           Flow_types.Alias_result.continuation_parameters :=
             continuation_parameters |} :=
    UA.continuation_param_aliases uacc
  in
  let* continuation_parameters :=
    try_with
      (fun _ => Continuation.Map.find cont continuation_parameters)
      Not_found
      (fun _ =>
        fatal_errorf2
          "Continuation %a not found in the continuation param aliases map from the Flow Analysis results."
          Continuation.print cont)
  in
  (* 558-573 *)
  let* '(handler, uacc) :=
    (* We might need to place lifted constants now, as they could depend on
       continuation parameters. As such we must also compute the unused
       parameters after placing any constants! *)
    if negb at_unit_toplevel
    then ret (handler, uacc)
    else
      let* '(uacc, lifted_constants_from_body) :=
        UA.get_and_clear_lifted_constants uacc
      in
      EB.place_lifted_constants uacc LCS.empty lifted_constants_from_body
        (fun uacc body => ret (body, uacc))
        handler
  in
  (* The [lets_to_introduce] rebind parameters that the alias analysis has
     removed from the continuation. These lets must be placed outside any lifted
     constants placed above, since such constants can reference the removed
     parameters, which are not bound anywhere else. Conversely, each let's
     defining expression is the parameter's canonical dominator, which must be
     in scope at the continuation's use sites, so it cannot be bound by the
     lifted constants placed inside. *)
  (* 581-600 *)
  let* '(handler, uacc) :=
    Variable_.Lmap.fold
      (fun var bound_to '(handler, uacc) =>
        let& var_duid := Flambda_debug_uid.none in
        let* bound_pattern :=
          let! tmp1 := Bound_var.create var var_duid Name_mode.normal in
          Bound_pattern.singleton tmp1
        in
        let* named := Named.create_simple bound_to in
        let* '(handler, uacc) :=
          let! tmp1 := Simple.free_names bound_to in
          Expr_builder.create_let_binding uacc bound_pattern named tmp1
            handler Cost_metrics.zero
        in
        ret (handler, uacc))
      continuation_parameters.(Flow_types.Continuation_param_aliases.lets_to_introduce)
      (handler, uacc)
  in
  let* free_names := UA.name_occurrences uacc in
  let* cost_metrics := UA.cost_metrics uacc in
  ret (T4 handler uacc free_names cost_metrics).

(* 605-627 *)
Definition add_phantom_params_bindings (uacc : UA.t) (handler : RE.t)
    (new_phantom_params : Bound_parameters.t) : M (RE.t * UA.t) :=
  let* machine_width :=
    let! tmp1 := UA.uenv uacc in
    UE.machine_width tmp1
  in
  let* new_phantom_param_bindings_outermost_first :=
    let! tmp1 := Bound_parameters.to_list new_phantom_params in
    List.map
      (fun param =>
        let* '(param_var, param_uid) := BP.var_and_uid param in
        let* kind :=
          let! tmp2 := BP.kind param in
          K.With_subkind.kind tmp2
        in
        let* var := Bound_var.create param_var param_uid Name_mode.phantom in
        let* let_bound := Bound_pattern.singleton var in
        let& prim :=
          Flambda_primitive.Nullary (Flambda_primitive.Optimised_out kind)
        in
        let* named := Named.create_prim prim Debuginfo.none in
        let* simplified_defining_expr :=
          Simplified_named.create machine_width named
        in
        ret
          (Simplified_named.Keep_binding let_bound simplified_defining_expr
             (Some named)))
      tmp1
  in
  EB.make_new_let_bindings uacc new_phantom_param_bindings_outermost_first
    handler.

(* 629-631 *)
Definition remove_params (params : Bound_parameters.t) (free_names : NO.t)
    : M NO.t :=
  let! tmp1 := Bound_parameters.to_list params in
  ListLabels.fold_left
    (fun free_names param =>
      let! tmp2 := BP.var param in
      NO.remove_var free_names tmp2)
    free_names tmp1.

(* 633-786 *)
Definition rebuild_single_non_recursive_handler
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (at_unit_toplevel : bool) (is_single_inlinable_use : bool)
    (original_invariant_params : Bound_parameters.t) (cont : Continuation.t)
    (handler_to_rebuild : Simplified_expr.simplified_handler_) (uacc : UA.t)
    (k : rebuilt_handler -> UA.t -> M (RE.t * UA.t)) : M (RE.t * UA.t) :=
  (* Clear existing name occurrences & cost metrics *)
  let* uacc :=
    let! tmp1 := UA.clear_cost_metrics uacc in
    UA.clear_name_occurrences tmp1
  in
  (* PORT-GAP(type): 638-647, [Simplified_expr.simplified_handler] is
     abstract in decl/: its eliminator stands for the compiler's record
     pattern. *)
  Simplified_expr.match_simplified_handler_ handler_to_rebuild
    (fun params simplified_handler is_exn_handler is_cold
         extra_params_and_args invariant_extra_params_and_args rewrite_ids =>
      (* In case the continuation was previously recursive, we make sure not to
         forget the invariant original and extra params. *)
      (* 650-654 *)
      let* params := Bound_parameters.append original_invariant_params params in
      let* extra_params_and_args :=
        EPA.concat extra_params_and_args invariant_extra_params_and_args
      in
      rebuild_expr simplified_handler uacc
        (fun handler uacc =>
          let* '(T4 handler uacc free_names cost_metrics) :=
            add_lets_around_handler cont at_unit_toplevel uacc handler
          in
          (* 659-664: [a |> f b] is [f b a] *)
          let* extra_params_and_args :=
            let! tmp1 :=
              extra_params_for_continuation_param_aliases cont uacc
                rewrite_ids
            in
            let! tmp2 := EPA.concat tmp1 extra_params_and_args in
            add_extra_params_for_mutable_unboxing cont uacc tmp2
          in
          let* exn_bucket :=
            if is_exn_handler
            then
              let! tmp1 := Bound_parameters.to_list params in
              let! tmp2 := List.hd tmp1 in
              let! tmp3 := Bound_parameter.var tmp2 in
              ret (Some tmp3)
            else ret None
          in
          let* removed_aliased := get_removed_aliased_params uacc cont in
          (* 672-675: a function of this file, given its first arguments. *)
          let* decide_param_usage :=
            let! tmp1 := UA.required_names uacc in
            ret
              (decide_param_usage_non_recursive free_names tmp1
                 removed_aliased exn_bucket)
          in
          let* rewrite :=
            Apply_cont_rewrite.create params extra_params_and_args
              decide_param_usage
          in
          let* '(invariant_params, params) :=
            Apply_cont_rewrite.get_used_params rewrite
          in
          (let! tmp1 := Bound_parameters.is_empty invariant_params in
           if negb tmp1
           then
             fatal_errorf2
               "Non-recursive continuation has invariant params: %a"
               Apply_cont_rewrite.print rewrite
           else ret tt) ;;
          let* new_phantom_params :=
            let! tmp1 := Apply_cont_rewrite.get_unused_params rewrite in
            Bound_parameters.filter
              (fun param =>
                let! tmp2 := BP.var param in
                NO.mem_var free_names tmp2)
              tmp1
          in
          let* '(handler, uacc) :=
            add_phantom_params_bindings uacc handler new_phantom_params
          in
          let* free_names_of_handler :=
            remove_params new_phantom_params free_names
          in
          (* Update the cold marker on the rebuilt handler according to the marker
             on the [let cont], so that it gets properly propagated if the
             continuation gets inlined. *)
          (* 699-705 *)
          let* handler :=
            if is_cold then RE.mark_as_cold handler else ret handler
          in
          let* is_cold := RE.is_cold handler in
          let* cont_handler :=
            let! tmp1 := UA.are_rebuilding_terms uacc in
            RE.Continuation_handler.create tmp1 params handler
              free_names_of_handler is_exn_handler is_cold
          in
          (* The parameters are removed from the free name information as they are
             no longer in scope. *)
          let* free_names := remove_params params free_names_of_handler in
          let* uacc :=
            UA.map_uenv uacc
              (fun uenv => UE.add_apply_cont_rewrite uenv cont rewrite)
          in
          let* uenv := UA.uenv uacc in
          (* TODO move to its own function *)
          (* 715-777 *)
          let* uenv :=
            (* We must make the final decision now as to whether to inline this
               continuation or not; we can't wait until
               [Simplify_apply_cont.rebuild_apply_cont] because we need to decide
               sooner than that whether to keep the [Let_cont] (in order to keep
               free name sets correct). *)
            if is_single_inlinable_use
            then
              (* Note that [Continuation_uses] won't set [is_single_inlinable_use]
                 if [cont] is an exception handler. *)
              assert_ (negb is_exn_handler) ;;
              (* We pass the parameters and the handler expression, rather than the
                 [CH.t], to avoid re-opening the name abstraction. *)
              UE.add_linearly_used_inlinable_continuation uenv cont params
                handler free_names_of_handler cost_metrics
            else
              let* behaviour :=
                if is_exn_handler
                then ret Unknown
                else
                  let! tmp1 := RE.to_apply_cont handler in
                  match tmp1 with
                  | Some apply_cont =>
                    let! tmp1 := Apply_cont.trap_action apply_cont in
                    match tmp1 with
                    | Some _ => ret Unknown
                    | None =>
                      let* args := Apply_cont.args apply_cont in
                      let! tmp1 := Apply_cont.continuation apply_cont in
                      ret (Shortcut_to tmp1 args)
                    end
                  | None =>
                    let! tmp1 := UA.are_rebuilding_terms uacc in
                    let! tmp2 := RE.can_be_removed_as_invalid handler tmp1 in
                    if tmp2
                    then ret Invalid
                    else
                      let! tmp1 := UA.are_rebuilding_terms uacc in
                      let! tmp2 :=
                        UE.find_unique_continuation_handler tmp1 uenv params
                          handler is_exn_handler free_names
                      in
                      match tmp2 with
                      | Some (cont, args) => ret (Shortcut_to cont args)
                      | None => ret Unknown
                      end
                  end
              in
              match behaviour with
              | Invalid =>
                let* arity := Bound_parameters.arity params in
                UE.add_invalid_continuation uenv cont arity
              | Shortcut_to shortcut_to args =>
                UE.add_continuation_shortcut uenv cont params shortcut_to args
              | Unknown =>
                let! tmp1 := UA.are_rebuilding_terms uacc in
                UE.add_non_inlinable_continuation tmp1 uenv cont is_cold
                  params
                  (* 772-776: the tuple with labels [(handler,
                     ~is_exn_handler,
                     ~free_names_without_params:free_names)] is the type
                     [UE.handler_tuple] of decl/. *)
                  (Or_unknown.Known
                     (UE.Handler_tuple handler is_exn_handler free_names))
              end
          in
          let* uacc := UA.with_uenv uacc uenv in
          let& rebuilt_handler :=
            ({| handler := cont_handler;
                handler_expr := handler;
                name_occurrences_of_handler := free_names;
                cost_metrics_of_handler := cost_metrics |}
              : rebuilt_handler)
          in
          k rebuilt_handler uacc)).

(* 788-834 *)
Definition rebuild_single_recursive_handler
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (cont : Continuation.t)
    (handler_to_rebuild : Simplified_expr.simplified_handler_) (uacc : UA.t)
    (k : Bound_parameters.t -> rebuilt_handler -> UA.t -> M (RE.t * UA.t))
    : M (RE.t * UA.t) :=
  (* Clear existing name occurrences & cost metrics *)
  let* uacc :=
    let! tmp1 := UA.clear_cost_metrics uacc in
    UA.clear_name_occurrences tmp1
  in
  (* PORT-GAP(type): 792 and 822, [Simplified_expr.simplified_handler] is
     abstract in decl/: its eliminator stands for the two places where the
     compiler reads a field ([handler_to_rebuild.simplified_handler],
     [handler_to_rebuild.is_cold]). *)
  Simplified_expr.match_simplified_handler_ handler_to_rebuild
    (fun _ simplified_handler _ is_cold _ _ _ =>
      rebuild_expr simplified_handler uacc
        (fun handler uacc =>
          let* '(T4 handler uacc free_names cost_metrics) :=
            add_lets_around_handler cont false uacc handler
          in
          let* rewrite :=
            let! tmp1 := UA.uenv uacc in
            let! tmp2 := UE.find_apply_cont_rewrite tmp1 cont in
            match tmp2 with
            | None =>
              fatal_errorf2
                "An [Apply_cont_rewrite] for the recursive continuation %a should have already been added"
                Continuation.print cont
            | Some rewrite => ret rewrite
            end
          in
          let* new_phantom_params :=
            let! tmp1 := Apply_cont_rewrite.get_unused_params rewrite in
            Bound_parameters.filter
              (fun param =>
                let! tmp2 := BP.var param in
                NO.mem_var free_names tmp2)
              tmp1
          in
          let* '(handler, uacc) :=
            add_phantom_params_bindings uacc handler new_phantom_params
          in
          let* free_names := remove_params new_phantom_params free_names in
          let* '(invariant_params, variant_params) :=
            Apply_cont_rewrite.get_used_params rewrite
          in
          let* cont_handler :=
            let! tmp1 := UA.are_rebuilding_terms uacc in
            RE.Continuation_handler.create tmp1 variant_params handler
              free_names false is_cold
          in
          let* free_names :=
            let! tmp1 := remove_params variant_params free_names in
            remove_params invariant_params tmp1
          in
          let& rebuilt_handler :=
            ({| handler := cont_handler;
                handler_expr := handler;
                name_occurrences_of_handler := free_names;
                cost_metrics_of_handler := cost_metrics |}
              : rebuilt_handler)
          in
          k invariant_params rebuilt_handler uacc)).

(* 836-920: a [let rec] on the list [groups_to_rebuild]. *)
Fixpoint rebuild_continuation_handlers_loop {A : Type}
    (rebuild_body : Simplify_common.rebuild A)
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (simplified_body : A) (name_occurrences_of_subsequent_exprs : NO.t)
    (cost_metrics_of_subsequent_exprs : Cost_metrics.t)
    (uenv_of_subsequent_exprs : UE.t) (at_unit_toplevel : bool)
    (original_invariant_params : Bound_parameters.t)
    (invariant_extra_params : Bound_parameters.t) (uacc : UA.t)
    (after_rebuild : Simplify_common.after_rebuild)
    (groups_to_rebuild : list Simplified_expr.simplified_handlers_group)
    (rebuilt_groups : list rebuilt_handlers_group) {struct groups_to_rebuild}
    : M (RE.t * UA.t) :=
  match groups_to_rebuild with
  | [] =>
    (* 845-852: the fields in the order of the type. *)
    let& data :=
      ({| simplified_body_ := simplified_body;
          handlers_from_the_inside_to_the_outside := rebuilt_groups;
          name_occurrences_of_subsequent_exprs :=
            name_occurrences_of_subsequent_exprs;
          cost_metrics_of_subsequent_exprs := cost_metrics_of_subsequent_exprs;
          uenv_of_subsequent_exprs := uenv_of_subsequent_exprs |}
        : prepare_to_rebuild_body_data A)
    in
    prepare_to_rebuild_body rebuild_body data uacc after_rebuild
  | Simplified_expr.Non_recursive cont handler is_single_inlinable_use
    :: groups_to_rebuild =>
    rebuild_single_non_recursive_handler rebuild_expr at_unit_toplevel
      is_single_inlinable_use original_invariant_params cont handler uacc
      (fun rebuilt_handler uacc =>
        rebuild_continuation_handlers_loop rebuild_body rebuild_expr
          simplified_body name_occurrences_of_subsequent_exprs
          cost_metrics_of_subsequent_exprs uenv_of_subsequent_exprs
          at_unit_toplevel original_invariant_params invariant_extra_params
          uacc after_rebuild groups_to_rebuild
          (Non_recursive cont rebuilt_handler :: rebuilt_groups))
  | Simplified_expr.Recursive simplified_continuation_handlers
    :: groups_to_rebuild =>
    (* Common setup for recursive handlers: add rewrites; for now: always add
       params (ignore alias analysis) *)
    let* uacc :=
      Continuation.Map.fold
        (fun cont (handler : Simplified_expr.simplified_handler_) uacc =>
          (* PORT-GAP(type): 871-877, the eliminator of
             [Simplified_expr.simplified_handler] stands for the five
             places where the compiler reads a field of [handler]. *)
          Simplified_expr.match_simplified_handler_ handler
            (fun params _ _ is_cold extra_params_and_args
                 invariant_extra_params_and_args rewrite_ids =>
              make_rewrite_for_recursive_continuation uacc cont is_cold
                original_invariant_params invariant_extra_params_and_args
                params extra_params_and_args rewrite_ids))
        simplified_continuation_handlers uacc
    in
    (* Rebuild all the handlers *)
    (* 881-909: a local [let rec]. *)
    let loop :=
      fix loop (fuel : Port_monad.fuel) (uacc : UA.t)
          (invariant_params : option Bound_parameters.t)
          (remaining_handlers :
            Continuation.Map.t Simplified_expr.simplified_handler_)
          (rebuilt_handlers : Continuation.Lmap.t rebuilt_handler)
          (k :
            Bound_parameters.t -> Continuation.Lmap.t rebuilt_handler ->
            UA.t -> M (RE.t * UA.t))
          {struct fuel} : M (RE.t * UA.t) :=
        recursive! fuel in
        let! tmp1 := Continuation.Map.min_binding_opt remaining_handlers in
        match tmp1 with
        | None =>
          let! tmp1 := Option.get invariant_params in
          k tmp1 rebuilt_handlers uacc
        | Some (cont, handler) =>
          let* remaining_handlers :=
            Continuation.Map.remove cont remaining_handlers
          in
          rebuild_single_recursive_handler rebuild_expr cont handler uacc
            (fun cont_invariant_params rebuilt_handler uacc =>
              let* invariant_params :=
                match invariant_params with
                | None => ret (Some cont_invariant_params)
                | Some invariant_params =>
                  let! tmp1 :=
                    Bound_parameters.equal invariant_params
                      cont_invariant_params
                  in
                  if negb tmp1
                  then
                    fatal_errorf4
                      "Inconsistent invariant params: invariant_params=%a@ cont_invariant_params=%a"
                      Bound_parameters.print invariant_params
                      Bound_parameters.print cont_invariant_params
                  else ret (Some invariant_params)
                end
              in
              let! tmp1 :=
                Continuation.Lmap.add cont rebuilt_handler rebuilt_handlers
              in
              loop fuel uacc invariant_params remaining_handlers tmp1 k)
        end
    in
    let_fuel! fuel in
    loop fuel uacc None simplified_continuation_handlers Continuation.Lmap.empty
      (fun invariant_params rebuilt_handlers uacc =>
        (* Add all rewrites and continue rebuilding *)
        rebuild_continuation_handlers_loop rebuild_body rebuild_expr
          simplified_body name_occurrences_of_subsequent_exprs
          cost_metrics_of_subsequent_exprs uenv_of_subsequent_exprs
          at_unit_toplevel original_invariant_params invariant_extra_params
          uacc after_rebuild groups_to_rebuild
          (Recursive rebuilt_handlers invariant_params :: rebuilt_groups))
  end.

(* 922-959 *)
Definition prepare_to_rebuild_handlers {A : Type}
    (rebuild_body : Simplify_common.rebuild A)
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (data : Simplified_expr.simplified_let_cont_handlers)
    (simplified_body : A) (uacc : UA.t)
    (after_rebuild : Simplify_common.after_rebuild) : M (RE.t * UA.t) :=
  (* Here we just returned from the global [down_to_up], which is asking us to
     rebuild the let cont. The flow analyses have been done, and we start to
     rebuild the expressions. As with the downward pass, we loop over each
     defined handler to rebuild it. As the handlers have been sorted by
     strongly-connected components, we must process the handlers group-by-group,
     and rebuild the groups from the outside to the inside. For each of these
     groups, we need to perform different steps depending on whether it is a
     mutually-recursive group or a single non-recursive handler.

     For mutually-recursive groups, we need to add the rewrites to the
     environment, and then rebuild the handlers, as the handlers might use
     themselves, so the rewrites need to be ready at that point. We can only use
     the dataflow information to compute which parameters are used and which are
     not, since we won't be able to remove parameters after the handlers have
     been rebuilt, since we can't rewrite them inside themselves.

     For a single non-recursive handler, we first rebuild the handler. This
     allows us to get precise information on the parameters which are used,
     which are then used to add the rewrites to the environment.

     In both cases, we add the handlers to the environment after rebuilding
     them, so that the environment is ready when rebuilding the remaining
     handlers. We also reset the name occurrences and the cost metrics before
     rebuilding each handler, so that we know the name occurrences and cost
     metrics corresponding to each handler when rebuilding later. *)
  let* name_occurrences_of_subsequent_exprs := UA.name_occurrences uacc in
  let* cost_metrics_of_subsequent_exprs := UA.cost_metrics uacc in
  let* uenv_of_subsequent_exprs := UA.uenv uacc in
  (* PORT-GAP(type): 954-959, [Simplified_expr.simplified_let_cont_handlers]
     is abstract in decl/: its eliminator stands for the four places where
     the compiler reads a field of [data]. *)
  Simplified_expr.match_simplified_let_cont_handlers data
    (fun at_unit_toplevel handlers_from_the_outside_to_the_inside
         original_invariant_params invariant_extra_params =>
      rebuild_continuation_handlers_loop rebuild_body rebuild_expr
        simplified_body name_occurrences_of_subsequent_exprs
        cost_metrics_of_subsequent_exprs uenv_of_subsequent_exprs
        at_unit_toplevel original_invariant_params invariant_extra_params uacc
        after_rebuild handlers_from_the_outside_to_the_inside []).

(* 961-964: the third parameter is the pattern [(simplified_let_cont,
   simplified_body)]. *)
Definition rebuild_let_cont {A : Type}
    (rebuild_body : Simplify_common.rebuild A)
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (pat : Simplified_expr.simplified_let_cont_handlers * A) (uacc : UA.t)
    (after_rebuild : Simplify_common.after_rebuild) : M (RE.t * UA.t) :=
  let* '(simplified_let_cont, simplified_body) := ret pat in
  prepare_to_rebuild_handlers rebuild_body rebuild_expr simplified_let_cont
    simplified_body uacc after_rebuild.

(* 966-973 *)
Definition get_uses
    (data : after_downwards_traversal_of_body_and_handlers_data)
    (cont : Continuation.t) : M Continuation_uses.t :=
  let! tmp1 := CUE.get_continuation_uses data.(cont_uses_env) cont in
  match tmp1 with
  | None =>
    fatal_errorf2
      "Uses of %a not found in [after_downwards_traversal_of_body_and_handlers_data]@."
      Continuation.print cont
  | Some cont => ret cont
  end.

(* 975-1046 *)
Definition create_handler_to_rebuild
    (data : after_downwards_traversal_of_body_and_handlers_data)
    (cont : Continuation.t) (handler : handler_after_downwards_traversal)
    : M Simplified_expr.simplified_handler_ :=
  (* See comment at the top of
     [after_downwards_travsersal_of_body_and_handlers]. *)
  let* uses := get_uses data cont in
  let* use_ids := Continuation_uses.get_use_ids uses in
  let* invariant_extra_args :=
    Apply_cont_rewrite_id.Map.of_set
      (fun rewrite_id =>
        let! tmp1 := EPA.extra_args data.(invariant_extra_params_and_args) in
        let! tmp2 := Apply_cont_rewrite_id.Map.find_or_null rewrite_id tmp1 in
        match tmp2 with
        | Or_null.This extra_args => ret extra_args
        | Or_null.Null =>
          let! tmp1 :=
            EPA.extra_params data.(invariant_extra_params_and_args)
          in
          let! tmp2 := Bound_parameters.to_list tmp1 in
          let! tmp3 :=
            List.map
              (fun param =>
                let! tmp4 := Bound_parameter.var param in
                let! tmp5 := Simple.var tmp4 in
                ret (EPA.Extra_arg.Already_in_scope tmp5))
              tmp2
          in
          ret (Or_invalid.Ok tmp3)
        end)
      use_ids
  in
  (* This completes the extra args for recursive uses of all invariant extra
     params. Note that these extra params come from unboxing of already
     invariant params, as well as continuation lifting (and CSE if/when it
     generates extra params for recursive continuations). *)
  let* invariant_epa :=
    EPA.replace_extra_args data.(invariant_extra_params_and_args)
      invariant_extra_args
  in
  let* extra_params_and_args :=
    let* machine_width :=
      let! tmp1 := DA.denv data.(dacc_after_body) in
      DE.machine_width tmp1
    in
    let* arg_types_by_use_id := Continuation_uses.get_arg_types_by_use_id uses in
    let* '(_, arg_types_by_use_id) :=
      let! tmp1 := Bound_parameters.to_list data.(invariant_params) in
      let! tmp2 := List.length tmp1 in
      Misc.Stdlib.List.split_at tmp2 arg_types_by_use_id
    in
    match handler.(original) with
    | Non_rec _ =>
      (* For non-rec continuations, we need to add the lifted params, since the
         unboxing decision was made while taking those into account *)
      let* arg_types_by_use_id :=
        let! tmp1 := Continuation_uses.get_uses uses in
        let! tmp2 := arg_types_by_use_id_for_lifting data.(lifted_params) tmp1 in
        ret (arg_types_by_use_id ++ tmp2)
      in
      Unbox_continuation_params.compute_extra_params_and_args machine_width
        handler.(unbox_decisions) arg_types_by_use_id
        handler.(Simplify_let_cont_expr.extra_params_and_args)
    | Rec _ =>
      (* In the recursive case, we must *not* add the lifted params, since they
         ahve already been added when making the unboxing decisions on the
         invariant params, and this decision as well as the extra args required
         have all been put into the EPA for invariant params (this is why the
         unboxing decision for invariant params is not propagated up to here) *)
      Unbox_continuation_params.compute_extra_params_and_args machine_width
        handler.(unbox_decisions) arg_types_by_use_id
        handler.(Simplify_let_cont_expr.extra_params_and_args)
    end
  in
  (* 1039-1046: the record of [Simplified_expr.simplified_handler], which is
     abstract in decl/, is made by its maker (the fields by place, in the
     order of the type); one field has a call. *)
  let! tmp1 := Continuation_uses.get_use_ids uses in
  ret
    (Simplified_expr.mk_simplified_handler_ handler.(params)
       handler.(simplified_handler) handler.(is_exn_handler) handler.(is_cold)
       extra_params_and_args invariant_epa tmp1).

(* 1050-1088 *)
Definition sort_handlers
    (data : after_downwards_traversal_of_body_and_handlers_data)
    (handlers : Continuation.Map.t Simplified_expr.simplified_handler_)
    : M (list Simplified_expr.simplified_handlers_group) :=
  let* handlers_graph :=
    Continuation.Map.map
      (fun handler => ret handler.(continuations_used))
      data.(Simplify_let_cont_expr.handlers)
  in
  let* sorted_handlers_from_the_inside_to_the_outside :=
    SCC.connected_components_sorted_from_roots_to_leaf handlers_graph
  in
  Array.fold_left
    (fun inner group =>
      let* group :=
        match (group : SCC.component) with
        | SCC.Has_loop conts =>
          let* simplified_continuation_handlers :=
            List.fold_left
              (fun group cont =>
                let! tmp1 := Continuation.Map.find cont handlers in
                Continuation.Map.add cont tmp1 group)
              Continuation.Map.empty conts
          in
          ret (Simplified_expr.Recursive simplified_continuation_handlers)
        | SCC.No_loop cont =>
          let* handler := Continuation.Map.find cont handlers in
          let* is_single_inlinable_use :=
            let! tmp1 := get_uses data cont in
            let! tmp2 := Continuation_uses.get_uses tmp1 in
            match tmp2 with
            | [] | _ :: _ :: _ => ret false
            | [use] =>
              let! tmp1 := One_continuation_use.use_kind use in
              match tmp1 with
              | Continuation_use_kind.Inlinable => ret true
              | Continuation_use_kind.Non_inlinable _ => ret false
              end
            end
          in
          ret
            (Simplified_expr.Non_recursive cont handler is_single_inlinable_use)
        end
      in
      ret (group :: inner))
    ([] : list Simplified_expr.simplified_handlers_group)
    sorted_handlers_from_the_inside_to_the_outside.

(* 1166-1175. [{ data with consts_lifted_after_fork; handlers; cont_uses_env
   }]. *)
Definition update_consts_lifted_after_fork_handlers_cont_uses_env
    (t : after_downwards_traversal_of_body_and_handlers_data)
    (consts_lifted_after_fork : LCS.t)
    (handlers : Continuation.Map.t handler_after_downwards_traversal)
    (cont_uses_env : CUE.t)
    : after_downwards_traversal_of_body_and_handlers_data :=
  {| after_downwards_traversal_of_body_ :=
       t.(after_downwards_traversal_of_body_);
     cont_uses_env_after_body := t.(cont_uses_env_after_body);
     dacc_after_body := t.(dacc_after_body);
     simplified_body := t.(simplified_body);
     cont_uses_env := cont_uses_env;
     at_unit_toplevel := t.(at_unit_toplevel);
     consts_lifted_during_body := t.(consts_lifted_during_body);
     consts_lifted_after_fork := consts_lifted_after_fork;
     lifted_params := t.(lifted_params);
     invariant_params := t.(invariant_params);
     invariant_extra_params_and_args := t.(invariant_extra_params_and_args);
     handlers := handlers |}.
Extract Inlined Constant update_consts_lifted_after_fork_handlers_cont_uses_env =>
  "(fun t consts_lifted_after_fork handlers cont_uses_env -> { t with
   consts_lifted_after_fork = consts_lifted_after_fork; handlers = handlers;
   cont_uses_env = cont_uses_env })".

(* 1238-1243. [{ data with handlers; cont_uses_env; cont_uses_env_after_body;
   consts_lifted_after_fork }]. *)
Definition update_handlers_cont_uses_env_cont_uses_env_after_body_consts_lifted_after_fork
    (t : after_downwards_traversal_of_body_and_handlers_data)
    (handlers : Continuation.Map.t handler_after_downwards_traversal)
    (cont_uses_env : CUE.t)
    (cont_uses_env_after_body : CUE.t)
    (consts_lifted_after_fork : LCS.t)
    : after_downwards_traversal_of_body_and_handlers_data :=
  {| after_downwards_traversal_of_body_ :=
       t.(after_downwards_traversal_of_body_);
     cont_uses_env_after_body := cont_uses_env_after_body;
     dacc_after_body := t.(dacc_after_body);
     simplified_body := t.(simplified_body);
     cont_uses_env := cont_uses_env;
     at_unit_toplevel := t.(at_unit_toplevel);
     consts_lifted_during_body := t.(consts_lifted_during_body);
     consts_lifted_after_fork := consts_lifted_after_fork;
     lifted_params := t.(lifted_params);
     invariant_params := t.(invariant_params);
     invariant_extra_params_and_args := t.(invariant_extra_params_and_args);
     handlers := handlers |}.
Extract Inlined Constant update_handlers_cont_uses_env_cont_uses_env_after_body_consts_lifted_after_fork =>
  "(fun t handlers cont_uses_env cont_uses_env_after_body
   consts_lifted_after_fork -> { t with handlers = handlers; cont_uses_env =
   cont_uses_env; cont_uses_env_after_body = cont_uses_env_after_body;
   consts_lifted_after_fork = consts_lifted_after_fork })".

(* 1268. [{ data with cont_uses_env_after_body }]. *)
Definition update_cont_uses_env_after_body
    (t : after_downwards_traversal_of_body_and_handlers_data)
    (cont_uses_env_after_body : CUE.t)
    : after_downwards_traversal_of_body_and_handlers_data :=
  {| after_downwards_traversal_of_body_ :=
       t.(after_downwards_traversal_of_body_);
     cont_uses_env_after_body := cont_uses_env_after_body;
     dacc_after_body := t.(dacc_after_body);
     simplified_body := t.(simplified_body);
     cont_uses_env := t.(cont_uses_env);
     at_unit_toplevel := t.(at_unit_toplevel);
     consts_lifted_during_body := t.(consts_lifted_during_body);
     consts_lifted_after_fork := t.(consts_lifted_after_fork);
     lifted_params := t.(lifted_params);
     invariant_params := t.(invariant_params);
     invariant_extra_params_and_args := t.(invariant_extra_params_and_args);
     handlers := t.(handlers) |}.
Extract Inlined Constant update_cont_uses_env_after_body =>
  "(fun t cont_uses_env_after_body -> { t with cont_uses_env_after_body =
   cont_uses_env_after_body })".

(* 1092-1177 *)
Fixpoint compute_specialized_continuation (fuel : fuel)
    (replay : option (Replay_history.t * bool))
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (original_cont : Continuation.t)
    (handler : handler_after_downwards_traversal) (dacc : DA.t)
    (data : after_downwards_traversal_of_body_and_handlers_data)
    (use : One_continuation_use.t)
    (k :
      DA.t -> after_downwards_traversal_of_body_and_handlers_data ->
      M (SE.t * DA.t))
    {struct fuel} : M (SE.t * DA.t) :=
  recursive! fuel in
  let* cont := Continuation.rename original_cont in
  (* Compute the specialized handler *)
  match handler.(original) with
  | Rec one_rec_handler =>
    fatal_errorf2 "Cannot specialize recursive continuation: %a"
      One_recursive_handler.print one_rec_handler
  | Non_rec original =>
    let* original := Non_recursive_handler.rename_params original in
    let& is_recursive := false in
    let& params := original.(Non_recursive_handler.params) in
    let& lifted_params := original.(Non_recursive_handler.lifted_params) in
    let& is_exn_handler := original.(Non_recursive_handler.is_exn_handler) in
    let& denv :=
      data.(after_downwards_traversal_of_body_).(denv_for_join)
    in
    let* arg_types_by_use_id :=
      let* uses :=
        let! tmp1 := Bound_parameters.arity params in
        Continuation_uses.create cont tmp1
      in
      let* uses := Continuation_uses.add_use uses use in
      Continuation_uses.get_arg_types_by_use_id uses
    in
    (* 1114-1120 *)
    let* '(T4 dacc unbox_decisions is_exn_handler extra_params_and_args) :=
      let! tmp1 := Continuation.sort cont in
      prepare_dacc_for_handlers fuel dacc replay denv params is_recursive
        data.(consts_lifted_after_fork) tmp1
        (if is_exn_handler then Some cont else None)
        [use] lifted_params arg_types_by_use_id
    in
    (* Set the adequate state for lifting. Note that this must be done **after**
       the call to {prepare_dacc_for_handlers} as that function can sometimes
       set some of these values for the generic case. *)
    let* dacc :=
      let! tmp1 :=
        Are_lifting_conts.no_lifting
          Are_lifting_conts.In_continuation_specialization
      in
      DA.with_are_lifting_conts dacc tmp1
    in
    simplify_handler fuel simplify_expr is_recursive is_exn_handler
      Bound_parameters.empty params cont dacc
      original.(Non_recursive_handler.handler)
      (fun dacc simplified_handler cont_uses_env_in_handler =>
        let* '(dacc, consts_lifted_in_handler) :=
          DA.get_and_clear_lifted_constants dacc
        in
        let* consts_lifted_after_fork :=
          LCS.union data.(consts_lifted_after_fork) consts_lifted_in_handler
        in
        let* cont_uses_env :=
          CUE.union data.(cont_uses_env) cont_uses_env_in_handler
        in
        (* create the new handler *)
        let& rebuild :=
          ({| original := Non_rec original;
              params := params;
              simplified_handler := simplified_handler;
              is_exn_handler := is_exn_handler;
              is_cold := handler.(is_cold);
              continuations_used := Continuation.Set_.empty;
              (* this is only used for sorting mutually recursive continuation, so
                 this does not matter for non-recursive continuations *)
              unbox_decisions := unbox_decisions;
              extra_params_and_args := extra_params_and_args |}
            : handler_after_downwards_traversal)
        in
        (* set things up so that the specialized continuations are rewritten on
           the way up *)
        let* dacc :=
          let! tmp1 := One_continuation_use.id use in
          DA.add_specialization dacc tmp1 original_cont cont
        in
        let* cont_uses_env :=
          let! tmp1 := Bound_parameters.arity params in
          CUE.record_continuation cont_uses_env cont tmp1
        in
        (* PORT-GAP(record-order): 1165-1176, a record with a call in two
           of the fields that it changes ([handlers], [cont_uses_env]),
           which the compiler writes [handlers] first; here in the order of
           the type, the last field ([handlers]) first. *)
        let* data :=
          let* handlers := Continuation.Map.add cont rebuild data.(handlers) in
          let* cont_uses_env :=
            let! tmp1 := One_continuation_use.arg_types use in
            let! tmp2 := One_continuation_use.env_at_use use in
            let! tmp3 := One_continuation_use.id use in
            let! tmp4 := One_continuation_use.use_kind use in
            CUE.add_continuation_use cont_uses_env cont tmp4 tmp3 tmp2 tmp1
          in
          ret
            (update_consts_lifted_after_fork_handlers_cont_uses_env data
               consts_lifted_after_fork handlers cont_uses_env)
        in
        k dacc data)
  end

(* 1179-1187 *)
with compute_specialized_continuation_handlers (fuel : fuel)
    (replay : option (Replay_history.t * bool))
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (original_cont : Continuation.t)
    (handler : handler_after_downwards_traversal) (dacc : DA.t)
    (data : after_downwards_traversal_of_body_and_handlers_data)
    (uses : list One_continuation_use.t)
    (k :
      DA.t -> after_downwards_traversal_of_body_and_handlers_data ->
      M (SE.t * DA.t))
    {struct fuel} : M (SE.t * DA.t) :=
  recursive! fuel in
  match uses with
  | [] => k dacc data
  | use :: other_uses =>
    compute_specialized_continuation fuel replay simplify_expr original_cont
      handler dacc data use
      (fun dacc data =>
        compute_specialized_continuation_handlers fuel replay simplify_expr
          original_cont handler dacc data other_uses k)
  end

(* 1189-1247 *)
with specialize_continuation_if_needed (fuel : fuel)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t) (dacc : DA.t)
    (data : after_downwards_traversal_of_body_and_handlers_data)
    (k :
      DA.t -> after_downwards_traversal_of_body_and_handlers_data ->
      M (SE.t * DA.t))
    {struct fuel} : M (SE.t * DA.t) :=
  recursive! fuel in
  let! tmp1 := Continuation.Map.get_singleton data.(handlers) in
  match tmp1 with
  | Some (cont, handler) =>
    (* 1193: the guard. *)
    let! tmp1 := DA.continuations_to_specialize dacc in
    let! tmp2 := Continuation.Set_.mem cont tmp1 in
    if tmp2
    then
      let! tmp1 := CUE.get_continuation_uses data.(cont_uses_env) cont in
      match tmp1 with
      | None =>
        fatal_errorf2 "No uses for continuation %a to be specialized"
          Continuation.print cont
      | Some uses =>
        (* 1199-1206: the last case of the compiler's match names the whole
           list [uses]. *)
        let* uses := Continuation_uses.get_uses uses in
        match uses with
        | [] =>
          fatal_errorf2 "Empty uses for continuation %a to be specialized"
            Continuation.print cont
        | [_] =>
          (* only a single use, the continuation is already specialized *)
          k dacc data
        | _ :: _ :: _ =>
          (* We need to save a few values from the dacc, because the
             specialization can reset the dacc to the one after the traversal of
             the body. For most values in the dacc, this is not a problem since
             they relate to the simplified handler that we throw away (and replace
             by the specialized handlers). However, some values in the dacc
             instead keep track of some budgets/amount of work done/to do, and
             these values should be kept so that these budgets are accurately
             respected. *)
          let* lifting_budget := DA.get_continuation_lifting_budget dacc in
          (* Save the replay history from the handler, using the dacc after
             traversal of the handler *)
          let* replay :=
            let& always_inline := true in
            let* denv := DA.denv dacc in
            let* replay_history := DE.replay_history denv in
            ret (Some (replay_history, always_inline))
          in
          (* Remove the (generic) continuation uses from the CUE, since we will
             then add uses for each of the specialized continuation. *)
          let* cont_uses_env :=
            CUE.remove data.(cont_uses_env_after_body) cont
          in
          (* Use the dacc after the body to ignore any lifted constants or other
             information coming from the first traversal of the handler. We still
             reset a few values that come from the dacc after simplification of
             the handler, see comment above. *)
          let& dacc := data.(dacc_after_body) in
          let* dacc := DA.with_continuation_lifting_budget dacc lifting_budget in
          let* dacc := DA.with_continuation_uses_env dacc cont_uses_env in
          (* We need to drop the constants lifted during the first downwards
             traversal of the handler. *)
          let& consts_lifted_after_fork := data.(consts_lifted_during_body) in
          let& data :=
            update_handlers_cont_uses_env_cont_uses_env_after_body_consts_lifted_after_fork
              data Continuation.Map.empty cont_uses_env cont_uses_env
              consts_lifted_after_fork
          in
          compute_specialized_continuation_handlers fuel replay simplify_expr
            cont handler dacc data uses k
        end
      end
    else k dacc data
  | None => k dacc data
  end

(* 1249-1339 *)
with after_downwards_traversal_of_body_and_handlers (fuel : fuel)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (denv_for_join : DE.t)
    (data : after_downwards_traversal_of_body_and_handlers_data)
    (down_to_up : Simplify_common.down_to_up SE.t) (dacc : DA.t)
    {struct fuel} : M (SE.t * DA.t) :=
  recursive! fuel in
  (* At this point we have done a downwards traversal on the body and all the
     handlers. *)
  let* '(dacc, lifted_conts) := DA.get_and_clear_lifted_continuations dacc in
  (* We need to record the arity of the lifted continuations now, because they
     will be used in the specialized handler, even though we haven't really seen
     their let-cont. *)
  let* data :=
    match lifted_conts with
    | [] => ret data
    | _ :: _ =>
      let* cont_uses_env_after_body :=
        List.fold_left
          (fun cont_uses_env_after_body '(_denv, lifted_cont) =>
            CUE.record_continuation_arity cont_uses_env_after_body lifted_cont)
          data.(cont_uses_env_after_body) lifted_conts
      in
      ret (update_cont_uses_env_after_body data cont_uses_env_after_body)
    end
  in
  let* down_to_up :=
    down_to_up_for_lifted_continuations fuel simplify_expr denv_for_join
      lifted_conts down_to_up
  in
  specialize_continuation_if_needed fuel simplify_expr dacc data
    (fun dacc (data : after_downwards_traversal_of_body_and_handlers_data) =>
      (* Here, we want to actually rebuild the let-cont, so we need to call the
         global [down_to_up] function. First however, we have to take care of
         several things:

         - We need to compute the extra params and args related to unboxed
         parameters. This could not be done earlier, as we might not have seen
         every use of the continuations (particularly in the recursive case)
         (done in the [create_handler_to_rebuild] function).

         - Now that we were able to compute the extra params and args, we add
         this information to the flow analysis, so that it can correctly compute
         all the information we need when going up.

         - We perform a strongly-connected components analysis of the
         continuations to be able to turn mutually-recursive continuations into
         several independant blocks of recursive or non-recursive continuations.
         In case one of those is non-recursive, we can check whether the
         continuation is inlinable if it is used a single time. *)
      (* We need to restore the lifted constant state so that the lifted
         constants can be placed as needed when rebuilding. *)
      let* dacc :=
        DA.add_to_lifted_constant_accumulator None dacc
          data.(consts_lifted_after_fork)
      in
      let* dacc :=
        DA.add_to_lifted_constant_accumulator None dacc
          data.(after_downwards_traversal_of_body_).(prior_lifted_constants)
      in
      (* We need to reset the [dacc.cont_uses_env] for the rest of the
         traversal. Here, [data.cont_uses_env] contains the total CUE for the
         body + handler, so we only need to remove the continuations that we
         bind from it to reset the [cont_uses_env] correctly. *)
      let* cont_uses_env :=
        Continuation.Map.fold
          (fun cont _ cont_uses_env => CUE.remove cont_uses_env cont)
          data.(handlers) data.(cont_uses_env)
      in
      let* dacc := DA.with_continuation_uses_env dacc cont_uses_env in
      (* 1313-1315: a function of this file, given its first argument. *)
      let* handlers :=
        Continuation.Map.mapi (create_handler_to_rebuild data) data.(handlers)
      in
      let* dacc :=
        DA.map_flow_acc dacc
          (fun flow_acc =>
            Continuation.Map.fold
              (fun cont (handler : Simplified_expr.simplified_handler_)
                   flow_acc =>
                (* PORT-GAP(type): 1322-1323, the eliminator of
                   [Simplified_expr.simplified_handler] stands for the two
                   places where the compiler reads a field of [handler]. *)
                Simplified_expr.match_simplified_handler_ handler
                  (fun _ _ _ _ extra_params_and_args
                       invariant_extra_params_and_args _ =>
                    let! tmp1 :=
                      EPA.concat extra_params_and_args
                        invariant_extra_params_and_args
                    in
                    Flow.Acc.add_extra_params_and_args cont tmp1 flow_acc))
              handlers flow_acc)
      in
      let* handlers_from_the_outside_to_the_inside :=
        sort_handlers data handlers
      in
      let& simplified_body := data.(simplified_body) in
      (* 1331-1338: the record of
         [Simplified_expr.simplified_let_cont_handlers], which is abstract
         in decl/, is made by its maker (the fields by place, in the order
         of the type); one field has a call. *)
      let* data :=
        let! tmp1 := EPA.extra_params data.(invariant_extra_params_and_args) in
        ret
          (Simplified_expr.mk_simplified_let_cont_handlers
             data.(at_unit_toplevel) handlers_from_the_outside_to_the_inside
             data.(invariant_params) tmp1)
      in
      let! tmp1 := SE.simplified_let_cont data simplified_body in
      down_to_up dacc tmp1)

(* 1341-1437 *)
with prepare_dacc_for_handlers (fuel : fuel) (dacc : DA.t)
    (replay : option (Replay_history.t * bool)) (env_at_fork : DE.t)
    (params : Bound_parameters.t) (is_recursive : bool)
    (consts_lifted_after_fork : LCS.t)
    (continuation_sort : Continuation.Sort.t)
    (is_exn_handler_cont : option Continuation.t)
    (uses : list One_continuation_use.t)
    (lifted_params : Lifted_cont_params.t)
    (arg_types_by_use_id : Continuation_uses.arg_types_by_use_id)
    {struct fuel}
    : M (tuple4 DA.t Unbox_continuation_params.Decisions.t bool EPA.t) :=
  recursive! fuel in
  (* In the recursive case, [params] are actually the invariant params, as we
     prepare a common dacc for all handlers. *)
  let* env_at_fork := DE.enter_continuation_handler lifted_params env_at_fork in
  let* lifted_cont_extra_params_and_args :=
    extra_params_and_args_for_lifting lifted_params uses
  in
  let* params_including_lifted_params :=
    let! tmp1 := Lifted_cont_params.bound_parameters lifted_params in
    Bound_parameters.append params tmp1
  in
  let* join_result :=
    (* We add to the continuation uses (and therefore to the handler env) the
       params added by the eventual lifting of continuations. *)
    Join_points.compute_handler_env replay None uses is_recursive env_at_fork
      consts_lifted_after_fork params lifted_cont_extra_params_and_args
  in
  let* code_age_relation :=
    let! tmp1 := DA.typing_env dacc in
    TE.code_age_relation tmp1
  in
  (* 1368-1371: [a |> f] is [f a] *)
  let* handler_env :=
    let! tmp1 :=
      DE.with_code_age_relation code_age_relation
        join_result.(Join_points.handler_env)
    in
    DE.bump_current_level_scope tmp1
  in
  let& do_not_unbox :=
    fun (_ : unit) =>
    Unbox_continuation_params.make_do_not_unbox_decisions
      params_including_lifted_params
  in
  (* PORT-GAP(loose): 1377-1378, the guard [when
     join_result.is_single_inlinable_use], which reads a field of a value,
     is the second value of the match. *)
  let* '(T4 handler_env unbox_decisions is_exn_handler dacc) :=
    match
      continuation_sort, join_result.(Join_points.is_single_inlinable_use)
    with
    | Continuation.Sort.Normal_or_exn, true =>
      match is_exn_handler_cont with
      | Some cont =>
        (* This should be prevented by [Simplify_apply_cont_expr]. *)
        fatal_errorf2
          "Exception handlers should never be marked as [Inlinable]:@ %a"
          Continuation.print cont
      (* Don't try to unbox parameters of inlinable continuations, since the
         typing env still contains enough information to avoid re-reading the
         fields. *)
      | None =>
        let* dacc :=
          let! tmp1 :=
            Are_lifting_conts.no_lifting
              Are_lifting_conts.In_inlinable_continuation
          in
          DA.with_are_lifting_conts dacc tmp1
        in
        let! tmp1 := do_not_unbox tt in
        ret (T4 handler_env tmp1 false dacc)
      end
    | Continuation.Sort.Normal_or_exn, false
    | Continuation.Sort.Define_root_symbol, _ =>
      let* '(dacc, is_exn_handler) :=
        match is_exn_handler_cont with
        | None => ret (dacc, false)
        | Some cont =>
          if join_result.(Join_points.escapes)
          then ret (dacc, true)
          else
            let! tmp1 := DA.demote_exn_handler dacc cont in
            ret (tmp1, false)
        end
      in
      if is_exn_handler
      then
        let! tmp1 := do_not_unbox tt in
        ret (T4 handler_env tmp1 true dacc)
      else
        (* Unbox the parameters of the continuation if possible. Any such
           unboxing will induce a rewrite (or wrapper) on the application sites
           of the continuation. *)
        let* arg_types_by_use_id :=
          let! tmp1 := arg_types_by_use_id_for_lifting lifted_params uses in
          ret (arg_types_by_use_id ++ tmp1)
        in
        let* param_types_including_lifted :=
          let! tmp1 := DE.typing_env handler_env in
          TE.find_params tmp1 params_including_lifted_params
        in
        let* '(handler_env, decisions) :=
          Unbox_continuation_params.make_decisions
            (Unbox_continuation_params.Non_recursive arg_types_by_use_id)
            handler_env params_including_lifted_params
            param_types_including_lifted
        in
        ret (T4 handler_env decisions false dacc)
    | Continuation.Sort.Return, _ | Continuation.Sort.Toplevel_return, _ =>
      match is_exn_handler_cont with
      | Some cont =>
        (* This should be prevented by [Simplify_apply_cont_expr]. *)
        fatal_errorf2
          "Exception handlers should never be marked as [Return] or [Toplevel_return]:@ %a"
          Continuation.print cont
      | None =>
        let! tmp1 := do_not_unbox tt in
        ret (T4 handler_env tmp1 false dacc)
      end
    end
  in
  let! tmp1 := DA.with_denv dacc handler_env in
  ret
    (T4 tmp1 unbox_decisions is_exn_handler
       join_result.(Join_points.extra_params_and_args))

(* 1439-1462 *)
with simplify_handler (fuel : fuel)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (is_recursive is_exn_handler : bool)
    (invariant_params params : Bound_parameters.t) (cont : Continuation.t)
    (dacc : DA.t) (handler : Expr.t)
    (k : DA.t -> SE.t -> CUE.t -> M (SE.t * DA.t)) {struct fuel}
    : M (SE.t * DA.t) :=
  recursive! fuel in
  (let! tmp1 := DA.typing_env dacc in
   TE.notify_test_observer tmp1 cont) ;;
  let* dacc :=
    let! tmp1 := DA.continuation_uses_env dacc in
    let! tmp2 := CUE.reset_uses tmp1 in
    DA.with_continuation_uses_env dacc tmp2
  in
  let* dacc :=
    let! tmp1 := Bound_parameters.append invariant_params params in
    (* 1449-1451 *)
    let! tmp2 :=
      papp4 Flow.Acc.enter_continuation cont is_recursive is_exn_handler tmp1
    in
    DA.map_flow_acc dacc tmp2
  in
  simplify_expr dacc handler
    (fun dacc simplified_handler =>
      let* dacc :=
        (* 1455 *)
        let! tmp1 := papp1 Flow.Acc.exit_continuation cont in
        DA.map_flow_acc dacc tmp1
      in
      let* cont_uses_env_in_handler := DA.continuation_uses_env dacc in
      let* cont_uses_env_in_handler :=
        if is_recursive
        then CUE.mark_non_inlinable cont_uses_env_in_handler
        else ret cont_uses_env_in_handler
      in
      k dacc simplified_handler cont_uses_env_in_handler)

(* 1464-1520: the last parameter but one is the pattern [({ params; handler;
   is_cold } as original : One_recursive_handler.t)]. *)
with simplify_single_recursive_handler (fuel : fuel)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (cont_uses_env_so_far : CUE.t) (invariant_params : Bound_parameters.t)
    (consts_lifted_after_fork : LCS.t)
    (all_handlers_set : Continuation.Set_.t) (denv_to_reset : DE.t)
    (dacc : DA.t) (cont : Continuation.t)
    (original : One_recursive_handler.t)
    (k :
      DA.t -> handler_after_downwards_traversal -> CUE.t -> M (SE.t * DA.t))
    {struct fuel} : M (SE.t * DA.t) :=
  recursive! fuel in
  let* '{| One_recursive_handler.params := params;
           One_recursive_handler.handler := handler;
           One_recursive_handler.is_cold := is_cold |} :=
    ret original
  in
  (* Here we perform the downwards traversal on a single handler.

     We also make unboxing decisions at this step, which are necessary to
     correctly simplify the handler using the unboxed parameters, but we delay
     the unboxing extra_params_and_args to later, when we will have seen all
     uses (needed for the recursive continuation handlers). *)
  let* handler_env :=
    (let! tmp1 := DE.at_unit_toplevel denv_to_reset in
     assert_ (negb tmp1)) ;;
    DE.add_parameters_with_unknown_types false None None denv_to_reset params
  in
  let* handler_env :=
    if is_cold then DE.mark_as_cold handler_env else ret handler_env
  in
  let* is_cold := DE.is_cold handler_env in
  let* handler_env :=
    DE.add_lifted_constant_state None handler_env consts_lifted_after_fork
  in
  let* code_age_relation :=
    let! tmp1 := DA.typing_env dacc in
    TE.code_age_relation tmp1
  in
  let* handler_env := DE.with_code_age_relation code_age_relation handler_env in
  let* '(T3 handler_env unbox_decisions dacc) :=
    (* Unbox the parameters of the continuation if possible. Any such unboxing
       will induce a rewrite (or wrapper) on the application sites of the
       continuation; that rewrite will be comptued later, when we compute all
       the extra args and params. *)
    let* param_types :=
      let! tmp1 := DE.typing_env handler_env in
      TE.find_params tmp1 params
    in
    let* '(handler_env, decisions) :=
      Unbox_continuation_params.make_decisions
        Unbox_continuation_params.Recursive handler_env params param_types
    in
    ret (T3 handler_env decisions dacc)
  in
  let* dacc := DA.with_denv dacc handler_env in
  simplify_handler fuel simplify_expr true false invariant_params params cont
    dacc handler
    (fun dacc simplified_handler cont_uses_env_in_handler =>
      let* cont_uses_env_so_far :=
        CUE.union cont_uses_env_so_far cont_uses_env_in_handler
      in
      let* continuations_used :=
        let! tmp1 := CUE.all_continuations_used cont_uses_env_in_handler in
        Continuation.Set_.inter all_handlers_set tmp1
      in
      k dacc
        {| original := Rec original;
           params := params;
           simplified_handler := simplified_handler;
           is_exn_handler := false;
           is_cold := is_cold;
           continuations_used := continuations_used;
           unbox_decisions := unbox_decisions;
           extra_params_and_args := EPA.empty |}
        cont_uses_env_so_far)

(* 1522-1588: the function returns its local function [loop], given its
   first argument. *)
with simplify_recursive_handlers (fuel : fuel)
    (down_to_up : Simplify_common.down_to_up SE.t)
    (data : after_downwards_traversal_of_body_data) (simplified_body : SE.t)
    (dacc_after_body : DA.t) (denv_for_join : DE.t)
    (previous_are_lifting_conts : Are_lifting_conts.t)
    (cont_uses_env_after_body : CUE.t)
    (lifted_params : Lifted_cont_params.t)
    (invariant_params : Bound_parameters.t) (invariant_epa : EPA.t)
    (continuation_handlers : Continuation.Lmap.t One_recursive_handler.t)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (consts_lifted_during_body : LCS.t)
    (all_conts_set : Continuation.Set_.t) (common_denv : DE.t)
    {struct fuel}
    : M (CUE.t -> Continuation.Set_.t -> Continuation.Set_.t ->
         Continuation.Map.t handler_after_downwards_traversal -> DA.t ->
         M (SE.t * DA.t)) :=
  recursive! fuel in
  (* 1527-1586: a local [let rec]. *)
  let loop :=
    fix loop (fuel : Port_monad.fuel) (consts_lifted_after_fork : LCS.t)
        (cont_uses_env_so_far : CUE.t)
        (reachable_handlers_to_simplify : Continuation.Set_.t)
        (simplified_handlers_set : Continuation.Set_.t)
        (simplified_handlers :
          Continuation.Map.t handler_after_downwards_traversal)
        (dacc : DA.t) {struct fuel} : M (SE.t * DA.t) :=
      recursive! fuel in
      (* This is the core loop to simplify all handlers defined by a recursive let
         cont. We loop over all handlers, each time taking the first handler that
         we have not yet processed and that has at least one use, until we have
         seen every handler that is reachable. *)
      let! tmp1 := Continuation.Set_.min_elt_opt reachable_handlers_to_simplify in
      match tmp1 with
      | None =>
        (* all remaining_handlers are unreachable *)
        (* 1541-1555: the fields in the order of the type. *)
        let& data :=
          ({| after_downwards_traversal_of_body_ := data;
              cont_uses_env_after_body := cont_uses_env_after_body;
              dacc_after_body := dacc_after_body;
              simplified_body := simplified_body;
              cont_uses_env := cont_uses_env_so_far;
              at_unit_toplevel := false;
              consts_lifted_during_body := consts_lifted_during_body;
              consts_lifted_after_fork := consts_lifted_after_fork;
              lifted_params := lifted_params;
              invariant_params := invariant_params;
              invariant_extra_params_and_args := invariant_epa;
              handlers := simplified_handlers |}
            : after_downwards_traversal_of_body_and_handlers_data)
        in
        let* dacc := DA.with_are_lifting_conts dacc previous_are_lifting_conts in
        after_downwards_traversal_of_body_and_handlers fuel simplify_expr
          denv_for_join data down_to_up dacc
      | Some cont =>
        let* reachable_handlers_to_simplify :=
          Continuation.Set_.remove cont reachable_handlers_to_simplify
        in
        let* handler := Continuation.Lmap.find cont continuation_handlers in
        simplify_single_recursive_handler fuel simplify_expr
          cont_uses_env_so_far invariant_params consts_lifted_after_fork
          all_conts_set common_denv dacc cont handler
          (fun dacc rebuild cont_uses_env_so_far =>
            let* '(dacc, consts_lifted_in_handler) :=
              DA.get_and_clear_lifted_constants dacc
            in
            let* consts_lifted_after_fork :=
              LCS.union consts_lifted_after_fork consts_lifted_in_handler
            in
            let* simplified_handlers_set :=
              Continuation.Set_.add cont simplified_handlers_set
            in
            let* reachable_handlers_to_simplify :=
              let! tmp1 :=
                Continuation.Set_.diff rebuild.(continuations_used)
                  simplified_handlers_set
              in
              Continuation.Set_.union reachable_handlers_to_simplify tmp1
            in
            let* simplified_handlers :=
              Continuation.Map.add cont rebuild simplified_handlers
            in
            loop fuel consts_lifted_after_fork cont_uses_env_so_far
              reachable_handlers_to_simplify simplified_handlers_set
              simplified_handlers dacc)
      end
  in
  ret (loop fuel consts_lifted_during_body)

(* 1590-1777 *)
with simplify_handlers (fuel : fuel)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (down_to_up : Simplify_common.down_to_up SE.t) (denv_for_join : DE.t)
    (simplified_body : SE.t) (data : after_downwards_traversal_of_body_data)
    (dacc : DA.t) {struct fuel} : M (SE.t * DA.t) :=
  recursive! fuel in
  (* In this case we have decided not to lift the continuation being let-bound
     outside of its context. So the remaining thing to do is setup the dacc, and
     later decide whether to lift the continuations defined inside the
     continuation being currently let-bound. *)
  let* '(dacc, consts_lifted_during_body) :=
    DA.get_and_clear_lifted_constants dacc
  in
  let& dacc_after_body := dacc in
  let* body_continuation_uses_env := DA.continuation_uses_env dacc in
  let& denv := data.(Simplify_let_cont_expr.denv_for_join) in
  let* previous_are_lifting_conts := DA.are_lifting_conts dacc in
  match data.(handlers__) with
  | Original_handlers.Non_recursive original =>
    (* 1604-1612: the record pattern [({ cont; params; lifted_params;
       handler; is_exn_handler; is_cold; can_be_lifted = _ } as
       original)]. *)
    let* '{| Non_recursive_handler.cont := cont;
             Non_recursive_handler.params := params;
             Non_recursive_handler.lifted_params := lifted_params;
             Non_recursive_handler.handler := handler;
             Non_recursive_handler.is_exn_handler := is_exn_handler;
             Non_recursive_handler.can_be_lifted := _;
             Non_recursive_handler.is_cold := is_cold |} :=
      ret original
    in
    let! tmp1 :=
      Continuation_uses_env.get_continuation_uses body_continuation_uses_env
        cont
    in
    match tmp1 with
    | None =>
      (* Continuation unused, no need to traverse its handler *)
      (* 1619-1633: the fields in the order of the type. *)
      let& data :=
        ({| after_downwards_traversal_of_body_ := data;
            cont_uses_env_after_body := body_continuation_uses_env;
            dacc_after_body := dacc_after_body;
            simplified_body := simplified_body;
            cont_uses_env := body_continuation_uses_env;
            at_unit_toplevel := false;
            consts_lifted_during_body := consts_lifted_during_body;
            consts_lifted_after_fork := consts_lifted_during_body;
            lifted_params := Lifted_cont_params.empty;
            invariant_params := Bound_parameters.empty;
            invariant_extra_params_and_args := EPA.empty;
            handlers := Continuation.Map.empty |}
          : after_downwards_traversal_of_body_and_handlers_data)
      in
      after_downwards_traversal_of_body_and_handlers fuel simplify_expr
        denv_for_join data down_to_up dacc
    | Some uses =>
      let* dacc :=
        let! tmp1 :=
          Are_lifting_conts.think_about_lifting_out_of is_exn_handler cont uses
        in
        DA.with_are_lifting_conts dacc tmp1
      in
      let* at_unit_toplevel :=
        (* We try to show that [handler] postdominates [body] (which is done by
           showing that [body] can only return through [cont]) and that if
           [body] raises any exceptions then it only does so to toplevel. If
           this can be shown and we are currently at the toplevel of a
           compilation unit, the handler for the environment can remain marked
           as toplevel (and suitable for "let symbol" bindings); otherwise, it
           cannot. *)
        let! tmp1 := DE.at_unit_toplevel denv in
        and_then tmp1
          (and_then (negb is_exn_handler)
             (let! tmp2 := DE.unit_toplevel_exn_continuation denv in
              let! tmp3 := Continuation.Set_.of_list [cont; tmp2] in
              let! tmp4 :=
                CUE.all_continuations_used body_continuation_uses_env
              in
              Continuation.Set_.subset tmp4 tmp3))
      in
      let* denv := DE.set_at_unit_toplevel_state denv at_unit_toplevel in
      let* denv := if is_cold then DE.mark_as_cold denv else ret denv in
      let* is_cold := DE.is_cold denv in
      (* 1659-1666 *)
      let* '(T4 dacc unbox_decisions is_exn_handler extra_params_and_args) :=
        let! tmp1 := Continuation_uses.get_arg_types_by_use_id uses in
        let! tmp2 := Continuation_uses.get_uses uses in
        let! tmp3 := Continuation.sort cont in
        prepare_dacc_for_handlers fuel dacc None denv params false
          consts_lifted_during_body tmp3
          (if is_exn_handler then Some cont else None)
          tmp2 lifted_params tmp1
      in
      simplify_handler fuel simplify_expr false is_exn_handler
        Bound_parameters.empty params cont dacc handler
        (fun dacc simplified_handler cont_uses_env_in_handler =>
          let* '(dacc, consts_lifted_in_handler) :=
            DA.get_and_clear_lifted_constants dacc
          in
          let* consts_lifted_after_fork :=
            LCS.union consts_lifted_during_body consts_lifted_in_handler
          in
          let* cont_uses_env_so_far :=
            CUE.union body_continuation_uses_env cont_uses_env_in_handler
          in
          let& continuations_used := Continuation.Set_.empty in
          let& rebuild :=
            ({| original := Non_rec original;
                params := params;
                simplified_handler := simplified_handler;
                is_exn_handler := is_exn_handler;
                is_cold := is_cold;
                continuations_used := continuations_used;
                unbox_decisions := unbox_decisions;
                extra_params_and_args := extra_params_and_args |}
              : handler_after_downwards_traversal)
          in
          let* dacc :=
            DA.with_are_lifting_conts dacc previous_are_lifting_conts
          in
          (* 1694-1708: the fields in the order of the type; one field has
             a call. *)
          let* data :=
            let! tmp1 := Continuation.Map.singleton cont rebuild in
            ret
              ({| after_downwards_traversal_of_body_ := data;
                  cont_uses_env_after_body := body_continuation_uses_env;
                  dacc_after_body := dacc_after_body;
                  simplified_body := simplified_body;
                  cont_uses_env := cont_uses_env_so_far;
                  at_unit_toplevel := at_unit_toplevel;
                  consts_lifted_during_body := consts_lifted_during_body;
                  consts_lifted_after_fork := consts_lifted_after_fork;
                  lifted_params := lifted_params;
                  invariant_params := Bound_parameters.empty;
                  invariant_extra_params_and_args := EPA.empty;
                  handlers := tmp1 |}
                : after_downwards_traversal_of_body_and_handlers_data)
          in
          after_downwards_traversal_of_body_and_handlers fuel simplify_expr
            denv_for_join data down_to_up dacc)
    end
  | Original_handlers.Recursive invariant_params lifted_params
      continuation_handlers _ =>
    let* dacc :=
      let! tmp1 :=
        Are_lifting_conts.no_lifting Are_lifting_conts.In_recursive_continuation
      in
      DA.with_are_lifting_conts dacc tmp1
    in
    let* denv := DE.set_at_unit_toplevel_state denv false in
    (* 1735-1737: [f @@ a] is [f a] *)
    let* all_conts_set :=
      let! tmp1 := Continuation.Lmap.keys continuation_handlers in
      Continuation.Set_.of_list tmp1
    in
    let* used_handlers_in_body :=
      let! tmp1 := CUE.all_continuations_used body_continuation_uses_env in
      Continuation.Set_.inter all_conts_set tmp1
    in
    let* all_uses :=
      let! tmp1 := Continuation.Set_.elements all_conts_set in
      (* 1744 *)
      let! tmp2 := papp1 CUE.get_continuation_uses body_continuation_uses_env in
      List.filter_map tmp2 tmp1
    in
    let* arity := Bound_parameters.arity invariant_params in
    let* arg_types_by_use_id :=
      Continuation_uses.get_arg_types_by_use_id_for_invariant_params arity
        all_uses
    in
    let* uses := List.concat_map Continuation_uses.get_uses all_uses in
    let* '(T4 dacc unbox_decisions is_exn_handler extra_params_and_args) :=
      prepare_dacc_for_handlers fuel dacc None denv invariant_params true
        consts_lifted_during_body Continuation.Sort.Normal_or_exn None uses
        lifted_params arg_types_by_use_id
    in
    let* arg_types_by_use_id_including_lifted :=
      let! tmp1 := arg_types_by_use_id_for_lifting lifted_params uses in
      ret (arg_types_by_use_id ++ tmp1)
    in
    let* machine_width := DE.machine_width denv in
    let* invariant_epa :=
      Unbox_continuation_params.compute_extra_params_and_args machine_width
        unbox_decisions arg_types_by_use_id_including_lifted
        extra_params_and_args
    in
    let* common_denv := DA.denv dacc in
    assert_ (negb is_exn_handler) ;;
    (* 1771-1777: [simplify_recursive_handlers] returns a function, which
       takes the last five arguments. *)
    let! tmp1 :=
      simplify_recursive_handlers fuel down_to_up data simplified_body
        dacc_after_body denv_for_join previous_are_lifting_conts
        body_continuation_uses_env lifted_params invariant_params
        invariant_epa continuation_handlers simplify_expr
        consts_lifted_during_body all_conts_set common_denv
    in
    tmp1 body_continuation_uses_env used_handlers_in_body
      Continuation.Set_.empty Continuation.Map.empty dacc
  end

(* 1779-1811 *)
with after_downwards_traversal_of_body (fuel : fuel)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (down_to_up : Simplify_common.down_to_up SE.t)
    (data : after_downwards_traversal_of_body_data) (dacc : DA.t)
    (simplified_body : SE.t) {struct fuel} : M (SE.t * DA.t) :=
  recursive! fuel in
  (* At this point, we have done the downwards traversal of the body, and we
     have two situations wrt to continuation lifting. *)
  let& denv_for_join := data.(denv_for_join) in
  let! tmp1 := DA.are_lifting_conts dacc in
  match tmp1 with
  | Are_lifting_conts.Lifting_out_of _ =>
    let! tmp1 := Original_handlers.can_be_lifted data.(handlers__) in
    if negb tmp1
    then
      (* wrapper continuations are not lifted, and will be duplicated and
         re-simplified for each specialized continuation, so we can just not
         simplify their handler *)
      down_to_up dacc simplified_body
    else
      (* In this case, we have decided to lift the continuation being bound out
         of its defining handler. Therefore we save the non-simplified version
         of the continuation in the dacc, so that we can simplify during the
         `down_to_up` later. *)
      let* params_to_lift :=
        DE.variables_defined_in_current_continuation denv_for_join
      in
      let* handlers :=
        Original_handlers.add_params_to_lift data.(handlers__) params_to_lift
      in
      let* dacc :=
        DA.add_lifted_continuation
          data.(Simplify_let_cont_expr.denv_for_join) handlers dacc
      in
      (* Restore lifted constants in dacc *)
      let* dacc :=
        DA.add_to_lifted_constant_accumulator None dacc
          data.(prior_lifted_constants)
      in
      down_to_up dacc simplified_body
  | Are_lifting_conts.Not_lifting _ | Are_lifting_conts.Analyzing _ _ _ =>
    simplify_handlers fuel simplify_expr down_to_up denv_for_join
      simplified_body data dacc
  end

(* 1813-1838 *)
with down_to_up_for_lifted_continuations (fuel : fuel)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (denv_for_join : DE.t)
    (lifted_conts : list (DE.t * Original_handlers.t))
    (down_to_up : Simplify_common.down_to_up SE.t) {struct fuel}
    : M (Simplify_common.down_to_up SE.t) :=
  recursive! fuel in
  match lifted_conts with
  | [] => ret down_to_up
  | (denv, handlers) :: other_lifted_handlers =>
    (* At this point, we are lifting a continuation k' with handler [handlers],
       out of a continuation k, and:

       - [denv_for_join] is the denv just before the letk for k

       - [denv] is the denv just before the letk for k'

       And we need to decide which parts of denv to use to simplify the handlers
       of k' after there are lifted out from the handler of k. *)
    let* actual_denv := DE.denv_for_lifted_continuation denv_for_join denv in
    let& data :=
      ({| denv_for_join := actual_denv;
          prior_lifted_constants := LCS.empty;
          handlers__ := handlers |}
        : after_downwards_traversal_of_body_data)
    in
    (* 1834-1836: a function of this file, given its first arguments. *)
    let& down_to_up :=
      after_downwards_traversal_of_body fuel simplify_expr down_to_up data
    in
    down_to_up_for_lifted_continuations fuel simplify_expr denv_for_join
      other_lifted_handlers down_to_up
  end.

(* 1840-1987 *)
Definition simplify_let_cont0
    (simplify_expr : Simplify_common.expr_simplifier Expr.t) (dacc : DA.t)
    (data : simplify_let_cont_data)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  (* We begin to simplify a let cont by simplifying its body, so that we can see
     all external calls to the handler in the non-recursive case, and so that we
     can know the values of all invariant arguments in the recursive case. We
     reset the [continuation_uses_env] so we can have precise information on
     continuations called by the body, and we reset the lifted constants because
     we need to add them to the handler's denv. *)
  let* '(dacc, prior_lifted_constants) :=
    DA.get_and_clear_lifted_constants dacc
  in
  let* denv_before_body := DA.denv dacc in
  let* can_be_lifted :=
    let! tmp1 := Original_handlers.can_be_lifted data.(handlers_) in
    and_then tmp1
      (let! tmp2 :=
         DE.has_seen_a_non_liftable_continuation denv_before_body
       in
       ret (negb tmp2))
  in
  (* About scopes: supposing we are at scope 'n' before the let-cont, we will:

     - use scope 'n + 2' to inspect the body

     - use scope 'n + 1' to perform the join of continuation uses

     - bump the scope of the env after join to get an env at scope 'n + 2'

     - we repeat this process for each lifted continuation, whose join will take
     place at level 'n + 1' (which is the level for denv_for_join), after which
     the scope will be bumped to `n + 2`, so that further lifted continuations
     can also perform their join at level `n + 1`. *)
  let* denv_for_join := DE.increment_continuation_scope denv_before_body in
  let* denv_for_body := DE.increment_continuation_scope denv_for_join in
  let* denv_for_body :=
    let* lifting_cost :=
      let! tmp1 := DE.variables_defined_in_current_continuation denv_for_body in
      Lifted_cont_params.length tmp1
    in
    let* bound_continuations :=
      Original_handlers.bound_continuations data.(handlers_)
    in
    (* 1876-1882 *)
    let! tmp1 :=
      DE.define_continuations can_be_lifted denv_for_body bound_continuations
    in
    let! tmp2 := DE.add_lifting_cost lifting_cost tmp1 in
    let! tmp3 := Original_handlers.can_be_lifted data.(handlers_) in
    (* 1878-1879 *)
    let! tmp4 :=
      papp2 Specialization_cost.add_continuations tmp3 data.(handlers_)
    in
    DE.map_specialization_cost tmp4 tmp2
  in
  (* During specialization, we must take care of correctly handling let-bound
     continuations that have been lifted during the first downwards pass, and
     whose handlers must be replaced on subsequent passes, so that they can
     refer to the lifted ones.

     Note that the `can_be_lifted` of the `handlers` bound by this let-binding
     does not matter: instead we use the `can_be_lifted` from the original
     handlers and the denv to decide what we will simplify: either the original
     handlers, or new handlers that are apply_conts toward the lifted ones. *)
  let* handlers :=
    let! tmp1 := DE.replay_history denv_for_body in
    let! tmp2 := Replay_history.replay_continuation_mapping tmp1 in
    match tmp2 with
    | Replay_history.Still_recording => ret data.(handlers_)
    | Replay_history.Replayed continuation_mapping =>
      match data.(handlers_) with
      | Original_handlers.Non_recursive non_rec_handler =>
        if negb can_be_lifted
        then
          (* wrapper continuations (such as the ones introduced for
             over-applications), are not lifted, and are duplicated.

             CR gbury: this might end up duplicating a fair bit of code, e.g. if
             an application in a wrapper continuation (such as the ones
             introduced for over-application wrapper continuations) is inlined.
             The "correct" way to solve this is to either better handle symbols
             introduced while simplifying downwards, or partially rebuild the
             generic handler to use as base for the specialized handlers. *)
          ret data.(handlers_)
        else
          let* lifted_cont :=
            Continuation.Map.find
              non_rec_handler.(Non_recursive_handler.cont) continuation_mapping
          in
          let* new_handler :=
            let* args :=
              let! tmp1 :=
                Bound_parameters.to_list
                  non_rec_handler.(Non_recursive_handler.params)
              in
              List.map
                (fun bp =>
                  let! tmp2 := Bound_parameter.var bp in
                  Simple.var tmp2)
                tmp1
            in
            let* apply_cont :=
              Apply_cont.create None lifted_cont args Debuginfo.none
            in
            Flambda.Expr.create_apply_cont apply_cont
          in
          let* new_non_rec_handler :=
            Non_recursive_handler.with_handler new_handler non_rec_handler
          in
          Original_handlers.create_non_recursive new_non_rec_handler
      | Original_handlers.Recursive invariant_params lifted_params
          continuation_handlers _ =>
        (let! tmp1 := Lifted_cont_params.is_empty lifted_params in
         assert_ tmp1) ;;
        if negb can_be_lifted
        then ret data.(handlers_)
        else
          let* continuation_handlers :=
            Continuation.Lmap.mapi
              (fun cont (one_recursive_handler : One_recursive_handler.t) =>
                let* lifted_cont :=
                  Continuation.Map.find cont continuation_mapping
                in
                let* new_handler :=
                  let* args :=
                    let! tmp1 :=
                      Bound_parameters.to_list
                        one_recursive_handler.(One_recursive_handler.params)
                    in
                    let! tmp2 := Bound_parameters.to_list invariant_params in
                    List.map
                      (fun bp =>
                        let! tmp3 := Bound_parameter.var bp in
                        Simple.var tmp3)
                      (tmp2 ++ tmp1)
                  in
                  let* apply_cont :=
                    Apply_cont.create None lifted_cont args Debuginfo.none
                  in
                  Flambda.Expr.create_apply_cont apply_cont
                in
                One_recursive_handler.with_handler new_handler
                  one_recursive_handler)
              continuation_handlers
          in
          (* 1965-1969: the compiler's variable is [ret], which is a name of
             the kit. *)
          let* ret_ :=
            Original_handlers.create_recursive invariant_params lifted_params
              continuation_handlers can_be_lifted
          in
          ret ret_
      end
    end
  in
  let* dacc := DA.with_denv dacc denv_for_body in
  let* dacc :=
    if can_be_lifted
    then ret dacc
    else DA.map_denv dacc DE.set_has_seen_a_non_liftable_continuation
  in
  let* cont_uses_env :=
    let! tmp1 := DA.continuation_uses_env dacc in
    CUE.record_continuation_arity tmp1 handlers
  in
  let* dacc := DA.with_continuation_uses_env dacc cont_uses_env in
  let& body := data.(body) in
  let& data :=
    ({| denv_for_join := denv_for_join;
        prior_lifted_constants := prior_lifted_constants;
        handlers__ := handlers |}
      : after_downwards_traversal_of_body_data)
  in
  (* 1985-1987: a function of this file, given its first arguments. *)
  let_fuel! fuel in
  simplify_expr dacc body
    (after_downwards_traversal_of_body fuel simplify_expr down_to_up data).

(* 1989-2014 *)
Definition simplify_let_cont
    (simplify_expr : Simplify_common.expr_simplifier Expr.t) (dacc : DA.t)
    (let_cont : Let_cont.t) (down_to_up : Simplify_common.down_to_up SE.t)
    : M (SE.t * DA.t) :=
  (* This is the entry point to simplify a let cont expression. The only thing
     it does is to match all handlers to break the name abstraction, and then
     call [simplify_let_cont_stage1]. *)
  let* '(body, handlers) :=
    match (let_cont : Let_cont.t) with
    | Flambda.Non_recursive handler _ _ can_be_lifted =>
      let* '(body, non_rec_handler) :=
        split_non_recursive_let_cont can_be_lifted handler
      in
      let* original_handlers :=
        Original_handlers.create_non_recursive non_rec_handler
      in
      ret (body, original_handlers)
    | Flambda.Recursive handlers =>
      let& lifted_params := Lifted_cont_params.empty in
      let* '(T3 body invariant_params continuation_handlers) :=
        split_recursive_let_cont handlers
      in
      let* original_handlers :=
        Original_handlers.create_recursive invariant_params lifted_params
          continuation_handlers true
      in
      ret (body, original_handlers)
    end
  in
  simplify_let_cont0 simplify_expr dacc
    {| body := body; handlers_ := handlers |}
    down_to_up.

(* 2016-2039: the third parameter is the pattern [(body, handlers)]. *)
Definition simplify_as_recursive_let_cont
    (simplify_expr : Simplify_common.expr_simplifier Expr.t) (dacc : DA.t)
    (pat : Expr.t * Continuation.Lmap.t Continuation_handler.t)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  let* '(body, handlers) := ret pat in
  (* Loopify needs to simplify a recursive continuation, but knowing the unique
     id of the continuation and parameters being simplified, so this function
     allows to simplify a recursive let cont with the name abstraction already
     opened. *)
  let* continuation_handlers :=
    Continuation.Lmap.map
      (fun handler =>
        let* is_cold := CH.is_cold handler in
        CH.pattern_match handler
          (fun params handler =>
            One_recursive_handler.create params handler is_cold))
      handlers
  in
  let* data :=
    let! tmp1 :=
      Original_handlers.create_recursive Bound_parameters.empty
        Lifted_cont_params.empty continuation_handlers true
    in
    ret ({| body := body; handlers_ := tmp1 |} : simplify_let_cont_data)
  in
  simplify_let_cont0 simplify_expr dacc data down_to_up.
