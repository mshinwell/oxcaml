(******************************************************************************
 *                                  OxCaml                                    *
 *                        Basile Clément, OCamlPro                            *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2024 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplified_expr.ml
   (Git blob a5940b9805c3198ce95701601fa8fc7773f17284), function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN], the arguments by place) is that of GUIDE.md; the Rocq
   form of the types (which are abstract, which take their fields by place,
   the names [mk_C] and the names with [_]) is that of
   decl/Simplified_expr.v. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Apply_cont_rewrite_id
  Apply_expr Bound_parameters Branch_annotations Closure_info
  Common_subexpression_elimination Continuation
  Continuation_extra_params_and_args Debuginfo Flambda Flambda2_types
  Flambda_arity Lifted_constant_state Named_rewrite_id Removed_operations
  Simple Simplified_named Symbol Target_ocaml_int.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 29 *)
(*OCAML
open! Flambda.Import
OCAML*)
Import Flambda.Import_.
(* 30-34 *)
From SimplifyPort.abbrev.simplified_expr Require Import Port_abbreviations.
(*OCAML
module CSE = Common_subexpression_elimination
module EPA = Continuation_extra_params_and_args
module T = Flambda2_types
module TE = T.Typing_env
module LCS = Lifted_constant_state
OCAML*)

(* 36-121 *)
(* The ten types are defined together in the compiler, with records whose
   fields have the same names, inline records, a labelled tuple and indices
   that are polymorphic variants. In Rocq, the form of decl/Simplified_expr.v:
   a record is a type of one constructor [mk_T] that takes the fields by
   place, a constructor with an inline record takes its fields by place,
   [simplified_handler_] is abstract (it holds [t] and is held in the abstract
   [Continuation.Map.t]), with its maker and its eliminator, and a type that
   has the name of a function or of a field has one [_] after it. The OCaml
   definition is the compiler's text, whole: the directive of [t] below puts
   it at this place of the extracted file. *)
Inductive simplified_defining_expr : Type :=
| mk_simplified_defining_expr :
    list Simplified_named.binding_to_place -> Removed_operations.t ->
    LCS.t -> bool -> Closure_info.t -> Named_rewrite_id.t ->
    simplified_defining_expr.
Extract Inductive simplified_defining_expr => "simplified_defining_expr"
  [ "(fun (x__1, x__2, x__3, x__4, x__5, x__6) -> ({ bindings_to_place = x__1; removed_operations = x__2; lifted_constants_from_defining_expr = x__3; at_unit_toplevel = x__4; closure_info = x__5; rewrite_id = x__6 } : simplified_defining_expr))" ]
  "(fun f__1 x__0 -> let ({ bindings_to_place = x__1; removed_operations = x__2; lifted_constants_from_defining_expr = x__3; at_unit_toplevel = x__4; closure_info = x__5; rewrite_id = x__6 } : simplified_defining_expr) = x__0 in f__1 x__1 x__2 x__3 x__4 x__5 x__6)".

Parameter simplified_handler_ : Type.
Extract Inlined Constant simplified_handler_ => "simplified_handler".

Inductive simplified_handlers_group : Type :=
| Recursive : Continuation.Map.t simplified_handler_ -> simplified_handlers_group
| Non_recursive :
    Continuation.t -> simplified_handler_ -> bool -> simplified_handlers_group.
Extract Inductive simplified_handlers_group => "simplified_handlers_group"
  [ "(fun x__1 -> (Recursive { simplified_continuation_handlers = x__1 } : simplified_handlers_group))"
    "(fun (x__1, x__2, x__3) -> (Non_recursive { cont = x__1; handler = x__2; is_single_inlinable_use = x__3 } : simplified_handlers_group))" ]
  "(fun f__1 f__2 x__0 -> match (x__0 : simplified_handlers_group) with Recursive { simplified_continuation_handlers = x__1 } -> f__1 x__1 | Non_recursive { cont = x__1; handler = x__2; is_single_inlinable_use = x__3 } -> f__2 x__1 x__2 x__3)".

Inductive simplified_let_cont_handlers : Type :=
| mk_simplified_let_cont_handlers :
    bool -> list simplified_handlers_group -> Bound_parameters.t ->
    Bound_parameters.t -> simplified_let_cont_handlers.
Extract Inductive simplified_let_cont_handlers =>
  "simplified_let_cont_handlers"
  [ "(fun (x__1, x__2, x__3, x__4) -> ({ at_unit_toplevel = x__1; handlers_from_the_outside_to_the_inside = x__2; original_invariant_params = x__3; invariant_extra_params = x__4 } : simplified_let_cont_handlers))" ]
  "(fun f__1 x__0 -> let ({ at_unit_toplevel = x__1; handlers_from_the_outside_to_the_inside = x__2; original_invariant_params = x__3; invariant_extra_params = x__4 } : simplified_let_cont_handlers) = x__0 in f__1 x__1 x__2 x__3 x__4)".

Inductive simplified_lets_and_let_conts_ : Type :=
| Simplified_terminator : simplified_lets_and_let_conts_
| Simplified_let :
    simplified_defining_expr -> simplified_lets_and_let_conts_ ->
    simplified_lets_and_let_conts_
| Simplified_let_cont :
    simplified_let_cont_handlers -> simplified_lets_and_let_conts_ ->
    simplified_lets_and_let_conts_.
Extract Inductive simplified_lets_and_let_conts_ =>
  "simplified_lets_and_let_conts"
  [ "Simplified_terminator" "Simplified_let" "Simplified_let_cont" ].

Inductive simplified_apply_ : Type :=
| mk_simplified_apply_ :
    Apply.t -> option Apply_cont_rewrite_id.t -> Apply_cont_rewrite_id.t ->
    Flambda_arity.t -> bool -> simplified_apply_.
Extract Inductive simplified_apply_ => "simplified_apply"
  [ "(fun (x__1, x__2, x__3, x__4, x__5) -> ({ apply = x__1; use_id = x__2; exn_cont_use_id = x__3; result_arity = x__4; is_cold = x__5 } : simplified_apply))" ]
  "(fun f__1 x__0 -> let ({ apply = x__1; use_id = x__2; exn_cont_use_id = x__3; result_arity = x__4; is_cold = x__5 } : simplified_apply) = x__0 in f__1 x__1 x__2 x__3 x__4 x__5)".

Inductive simplified_apply_cont_ : Type :=
| mk_simplified_apply_cont_ :
    Apply_cont.t -> list Simple.t -> Apply_cont_rewrite_id.t ->
    simplified_apply_cont_.
Extract Inductive simplified_apply_cont_ => "simplified_apply_cont"
  [ "(fun (x__1, x__2, x__3) -> ({ apply_cont = x__1; args = x__2; rewrite_id = x__3 } : simplified_apply_cont))" ]
  "(fun f__1 x__0 -> let ({ apply_cont = x__1; args = x__2; rewrite_id = x__3 } : simplified_apply_cont) = x__0 in f__1 x__1 x__2 x__3)".

Inductive simplified_switch_ : Type :=
| mk_simplified_switch_ :
    Target_ocaml_int.Map.t
      (tuple5 Apply_cont_expr.t Branch_annotations.t Apply_cont_rewrite_id.t
         Flambda_arity.t TE.t) ->
    Debuginfo.t -> Simple.t -> T.t -> Static_const.Map.t Symbol.t -> TE.t ->
    CSE.t -> simplified_switch_.
Extract Inductive simplified_switch_ => "simplified_switch"
  [ "(fun (x__1, x__2, x__3, x__4, x__5, x__6, x__7) -> ({ arms = x__1; condition_dbg = x__2; scrutinee = x__3; scrutinee_ty = x__4; shareable_constants = x__5; typing_env_before_switch = x__6; cse_before_switch = x__7 } : simplified_switch))" ]
  "(fun f__1 x__0 -> let ({ arms = x__1; condition_dbg = x__2; scrutinee = x__3; scrutinee_ty = x__4; shareable_constants = x__5; typing_env_before_switch = x__6; cse_before_switch = x__7 } : simplified_switch) = x__0 in f__1 x__1 x__2 x__3 x__4 x__5 x__6 x__7)".

Inductive simplified_terminator_ : Type :=
| Simplified_apply : simplified_apply_ -> simplified_terminator_
| Simplified_apply_cont : simplified_apply_cont_ -> simplified_terminator_
| Simplified_switch : simplified_switch_ -> simplified_terminator_
| Simplified_invalid : Flambda.Invalid.t -> simplified_terminator_.
Extract Inductive simplified_terminator_ => "simplified_terminator"
  [ "Simplified_apply" "Simplified_apply_cont" "Simplified_switch"
    "Simplified_invalid" ].

Inductive t_ : Type :=
| mk_t :
    simplified_lets_and_let_conts_ -> simplified_terminator_ ->
    Removed_operations.t -> bool -> t_.
Extract Inductive t_ => "t"
  [ "(fun (x__1, x__2, x__3, x__4) -> ({ simplified_lets_and_let_conts = x__1; simplified_terminator = x__2; removed_operations = x__3; is_cold = x__4 } : t))" ]
  "(fun f__1 x__0 -> let ({ simplified_lets_and_let_conts = x__1; simplified_terminator = x__2; removed_operations = x__3; is_cold = x__4 } : t) = x__0 in f__1 x__1 x__2 x__3 x__4)".
Definition t : Type := t_.
Extract Constant t => "
  { simplified_lets_and_let_conts : simplified_lets_and_let_conts;
    simplified_terminator : simplified_terminator;
    removed_operations : Removed_operations.t;
    is_cold : bool
  }

and simplified_lets_and_let_conts =
  | Simplified_terminator
  | Simplified_let of simplified_defining_expr * simplified_lets_and_let_conts
  | Simplified_let_cont of
      simplified_let_cont_handlers * simplified_lets_and_let_conts

and simplified_defining_expr =
  { bindings_to_place : Simplified_named.binding_to_place list;
    removed_operations : Removed_operations.t;
    lifted_constants_from_defining_expr : LCS.t;
    at_unit_toplevel : bool;
    closure_info : Closure_info.t;
    rewrite_id : Named_rewrite_id.t
  }

and simplified_handler =
  { params : Bound_parameters.t;
    simplified_handler : t;
    is_exn_handler : bool;
    is_cold : bool;
    extra_params_and_args : EPA.t;
    (* Note: EPA.extra_params invariant_extra_params_and_args should always be
       equal to invariant_extra_params in stage4 *)
    invariant_extra_params_and_args : EPA.t;
    rewrite_ids : Apply_cont_rewrite_id.Set.t
  }

and simplified_handlers_group =
  | Recursive of
      { simplified_continuation_handlers : simplified_handler Continuation.Map.t
      }
  | Non_recursive of
      { cont : Continuation.t;
        handler : simplified_handler;
        is_single_inlinable_use : bool
      }

and simplified_let_cont_handlers =
  { at_unit_toplevel : bool;
    handlers_from_the_outside_to_the_inside : simplified_handlers_group list;
    original_invariant_params : Bound_parameters.t;
    invariant_extra_params : Bound_parameters.t
  }

and simplified_apply =
  { apply : Apply.t;
    use_id : Apply_cont_rewrite_id.t option;
    exn_cont_use_id : Apply_cont_rewrite_id.t;
    result_arity : [`Complex] Flambda_arity.t;
    is_cold : bool
  }

and simplified_terminator =
  | Simplified_apply of simplified_apply
  | Simplified_apply_cont of simplified_apply_cont
  | Simplified_switch of simplified_switch
  | Simplified_invalid of Flambda.Invalid.t

and simplified_apply_cont =
  { apply_cont : Apply_cont.t;
    args : Simple.t list;
    rewrite_id : Apply_cont_rewrite_id.t
  }

and simplified_switch =
  { arms :
      (Apply_cont_expr.t
      * annotations:Branch_annotations.t
      * Apply_cont_rewrite_id.t
      * [`Unarized] Flambda_arity.t
      * TE.t)
      Target_ocaml_int.Map.t;
    condition_dbg : Debuginfo.t;
    scrutinee : Simple.t;
    scrutinee_ty : T.t;
    shareable_constants : Symbol.t Static_const.Map.t;
    typing_env_before_switch : TE.t;
    cse_before_switch : CSE.t
  }
".

(* The maker and the eliminator of the abstract [simplified_handler_], as in
   decl/Simplified_expr.v. *)
Parameter mk_simplified_handler_ :
  Bound_parameters.t -> t -> bool -> bool -> EPA.t -> EPA.t ->
  Apply_cont_rewrite_id.Set_.t -> simplified_handler_.
Extract Inlined Constant mk_simplified_handler_ =>
  "(fun x__1 x__2 x__3 x__4 x__5 x__6 x__7 -> ({ params = x__1; simplified_handler = x__2; is_exn_handler = x__3; is_cold = x__4; extra_params_and_args = x__5; invariant_extra_params_and_args = x__6; rewrite_ids = x__7 } : simplified_handler))".
Parameter match_simplified_handler_ :
  forall {Res : Type},
  simplified_handler_ ->
  (Bound_parameters.t -> t -> bool -> bool -> EPA.t -> EPA.t ->
   Apply_cont_rewrite_id.Set_.t -> M Res) ->
  M Res.
Extract Inlined Constant match_simplified_handler_ =>
  "(fun x__0 f__1 -> let ({ params = x__1; simplified_handler = x__2; is_exn_handler = x__3; is_cold = x__4; extra_params_and_args = x__5; invariant_extra_params_and_args = x__6; rewrite_ids = x__7 } : simplified_handler) = x__0 in f__1 x__1 x__2 x__3 x__4 x__5 x__6 x__7)".

(* 123-126 *)
Definition notify_removed (operation : Removed_operations.t)
    (t : Simplified_expr.t) : M Simplified_expr.t :=
  (* [{ t with removed_operations = ... }]: all the fields, by place. *)
  let 'mk_t simplified_lets_and_let_conts simplified_terminator
        removed_operations is_cold := t in
  let! tmp1 := Removed_operations.op_plus operation removed_operations in
  ret (mk_t simplified_lets_and_let_conts simplified_terminator tmp1 is_cold).

(* 128 *)
Definition mark_as_cold (t : Simplified_expr.t) : M Simplified_expr.t :=
  let 'mk_t simplified_lets_and_let_conts simplified_terminator
        removed_operations is_cold := t in
  if is_cold
  then ret t
  else
    ret
      (mk_t simplified_lets_and_let_conts simplified_terminator
         removed_operations true).

(* 130-144 *)
Definition simplified_let
    (bindings_to_place : list Simplified_named.binding_to_place)
    (removed_operations : Removed_operations.t)
    (lifted_constants_from_defining_expr : LCS.t) (at_unit_toplevel : bool)
    (closure_info : Closure_info.t) (rewrite_id : Named_rewrite_id.t)
    (t : Simplified_expr.t) : M Simplified_expr.t :=
  (* [t_removed_operations]: the field of [t], which the compiler does not
     name here ([{ t with ... }]). *)
  let 'mk_t simplified_lets_and_let_conts simplified_terminator
        t_removed_operations is_cold := t in
  ret
    (mk_t
       (Simplified_let
          (mk_simplified_defining_expr bindings_to_place removed_operations
             lifted_constants_from_defining_expr at_unit_toplevel
             closure_info rewrite_id)
          simplified_lets_and_let_conts)
       simplified_terminator t_removed_operations is_cold).

(* 146-150 *)
Definition simplified_let_cont
    (simplified_handlers : simplified_let_cont_handlers)
    (t : Simplified_expr.t) : M Simplified_expr.t :=
  let 'mk_t simplified_lets_and_let_conts simplified_terminator
        removed_operations is_cold := t in
  ret
    (mk_t
       (Simplified_let_cont simplified_handlers simplified_lets_and_let_conts)
       simplified_terminator removed_operations is_cold).

(* 152-157 *)
Definition simplified_terminator
    (simplified_terminator : simplified_terminator_) : M t :=
  ret
    (mk_t Simplified_terminator simplified_terminator Removed_operations.zero
       false).

(* 159-166 *)
Definition simplified_apply (result_arity : option Flambda_arity.t)
    (apply : Apply.t) (use_id : option Apply_cont_rewrite_id.t)
    (exn_cont_use_id : Apply_cont_rewrite_id.t) (is_cold : bool) : M t :=
  let* result_arity :=
    match result_arity with
    | None => Apply_expr.return_arity apply
    | Some result_arity => ret result_arity
    end
  in
  simplified_terminator
    (Simplified_apply
       (mk_simplified_apply_ apply use_id exn_cont_use_id result_arity
          is_cold)).
(* PORT-GAP(verbatim): the wrapper that gives [simplified_apply] its
   optional argument [?result_arity]. *)
(*OCAML-END
let simplified_apply ?result_arity apply use_id exn_cont_use_id is_cold =
  simplified_apply result_arity apply use_id exn_cont_use_id is_cold
OCAML-END*)

(* 168-169 *)
Definition simplified_apply_cont (apply_cont : Apply_cont.t)
    (args : list Simple.t) (rewrite_id : Apply_cont_rewrite_id.t) : M t :=
  simplified_terminator
    (Simplified_apply_cont (mk_simplified_apply_cont_ apply_cont args rewrite_id)).

(* 171-182 *)
Definition simplified_switch
    (arms :
      Target_ocaml_int.Map.t
        (tuple5 Apply_cont_expr.t Branch_annotations.t Apply_cont_rewrite_id.t
           Flambda_arity.t TE.t))
    (condition_dbg : Debuginfo.t) (scrutinee : Simple.t) (scrutinee_ty : T.t)
    (shareable_constants : Static_const.Map.t Symbol.t)
    (typing_env_before_switch : TE.t) (cse_before_switch : CSE.t) : M t :=
  simplified_terminator
    (Simplified_switch
       (mk_simplified_switch_ arms condition_dbg scrutinee scrutinee_ty
          shareable_constants typing_env_before_switch cse_before_switch)).

(* 184-185 *)
Definition simplified_invalid (invalid : Flambda.Invalid.t) : M t :=
  simplified_terminator (Simplified_invalid invalid).
