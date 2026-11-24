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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Simplified_expr.v, which follows
   middle_end/flambda2/simplify/simplified_expr.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Flambda.Import
open Common_subexpression_elimination
open Continuation_extra_params_and_args
open Flambda
open Flambda2_types
open Lifted_constant_state
open Port_monad
open Tag
open Target_ocaml_int
module CSE = Common_subexpression_elimination
module EPA = Continuation_extra_params_and_args
module T = Flambda2_types
module TE = T.Typing_env
module LCS = Lifted_constant_state

type t =
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

(** val notify_removed : Removed_operations.t -> t -> t coq_M **)

let notify_removed operation t0 =
  (fun f__1 x__0 ->
    let ({ simplified_lets_and_let_conts = x__1;
           simplified_terminator = x__2;
           removed_operations = x__3;
           is_cold = x__4
         }
          : t) =
      x__0
    in
    f__1 x__1 x__2 x__3 x__4)
    (fun simplified_lets_and_let_conts simplified_terminator0 removed_operations
         is_cold ->
      (fun (x__1, x__2, x__3, x__4) ->
        ({ simplified_lets_and_let_conts = x__1;
           simplified_terminator = x__2;
           removed_operations = x__3;
           is_cold = x__4
         }
          : t))
        ( simplified_lets_and_let_conts,
          simplified_terminator0,
          Removed_operations.( + ) operation removed_operations,
          is_cold ))
    t0

(** val mark_as_cold : t -> t coq_M **)

let mark_as_cold t0 =
  (fun f__1 x__0 ->
    let ({ simplified_lets_and_let_conts = x__1;
           simplified_terminator = x__2;
           removed_operations = x__3;
           is_cold = x__4
         }
          : t) =
      x__0
    in
    f__1 x__1 x__2 x__3 x__4)
    (fun simplified_lets_and_let_conts simplified_terminator0 removed_operations
         is_cold ->
      if is_cold
      then t0
      else
        (fun (x__1, x__2, x__3, x__4) ->
          ({ simplified_lets_and_let_conts = x__1;
             simplified_terminator = x__2;
             removed_operations = x__3;
             is_cold = x__4
           }
            : t))
          ( simplified_lets_and_let_conts,
            simplified_terminator0,
            removed_operations,
            true ))
    t0

(** val simplified_let : Simplified_named.binding_to_place list ->
    Removed_operations.t -> Lifted_constant_state.t -> bool -> Closure_info.t ->
    Named_rewrite_id.t -> t -> t coq_M **)

let simplified_let bindings_to_place removed_operations
    lifted_constants_from_defining_expr at_unit_toplevel closure_info rewrite_id
    t0 =
  (fun f__1 x__0 ->
    let ({ simplified_lets_and_let_conts = x__1;
           simplified_terminator = x__2;
           removed_operations = x__3;
           is_cold = x__4
         }
          : t) =
      x__0
    in
    f__1 x__1 x__2 x__3 x__4)
    (fun simplified_lets_and_let_conts simplified_terminator0
         t_removed_operations is_cold ->
      (fun (x__1, x__2, x__3, x__4) ->
        ({ simplified_lets_and_let_conts = x__1;
           simplified_terminator = x__2;
           removed_operations = x__3;
           is_cold = x__4
         }
          : t))
        ( Simplified_let
            ( (fun (x__1, x__2, x__3, x__4, x__5, x__6) ->
                ({ bindings_to_place = x__1;
                   removed_operations = x__2;
                   lifted_constants_from_defining_expr = x__3;
                   at_unit_toplevel = x__4;
                   closure_info = x__5;
                   rewrite_id = x__6
                 }
                  : simplified_defining_expr))
                ( bindings_to_place,
                  removed_operations,
                  lifted_constants_from_defining_expr,
                  at_unit_toplevel,
                  closure_info,
                  rewrite_id ),
              simplified_lets_and_let_conts ),
          simplified_terminator0,
          t_removed_operations,
          is_cold ))
    t0

(** val simplified_let_cont : simplified_let_cont_handlers -> t -> t coq_M **)

let simplified_let_cont simplified_handlers t0 =
  (fun f__1 x__0 ->
    let ({ simplified_lets_and_let_conts = x__1;
           simplified_terminator = x__2;
           removed_operations = x__3;
           is_cold = x__4
         }
          : t) =
      x__0
    in
    f__1 x__1 x__2 x__3 x__4)
    (fun simplified_lets_and_let_conts simplified_terminator0 removed_operations
         is_cold ->
      (fun (x__1, x__2, x__3, x__4) ->
        ({ simplified_lets_and_let_conts = x__1;
           simplified_terminator = x__2;
           removed_operations = x__3;
           is_cold = x__4
         }
          : t))
        ( Simplified_let_cont
            (simplified_handlers, simplified_lets_and_let_conts),
          simplified_terminator0,
          removed_operations,
          is_cold ))
    t0

(** val simplified_terminator : simplified_terminator -> t coq_M **)

let simplified_terminator simplified_terminator0 =
  (fun (x__1, x__2, x__3, x__4) ->
    ({ simplified_lets_and_let_conts = x__1;
       simplified_terminator = x__2;
       removed_operations = x__3;
       is_cold = x__4
     }
      : t))
    ( Simplified_terminator,
      simplified_terminator0,
      Removed_operations.zero,
      false )

(** val simplified_apply : (_) Flambda_arity.t option -> Flambda.Import.Apply.t
    -> Apply_cont_rewrite_id.t option -> Apply_cont_rewrite_id.t -> bool -> t
    coq_M **)

let simplified_apply result_arity apply use_id exn_cont_use_id is_cold =
  let result_arity0 =
    match result_arity with
    | Some result_arity0 -> result_arity0
    | None -> Apply_expr.return_arity apply
  in
  simplified_terminator
    (Simplified_apply
       ((fun (x__1, x__2, x__3, x__4, x__5) ->
          ({ apply = x__1;
             use_id = x__2;
             exn_cont_use_id = x__3;
             result_arity = x__4;
             is_cold = x__5
           }
            : simplified_apply))
          (apply, use_id, exn_cont_use_id, result_arity0, is_cold)))

(** val simplified_apply_cont : Flambda.Import.Apply_cont.t -> Simple.t list ->
    Apply_cont_rewrite_id.t -> t coq_M **)

let simplified_apply_cont apply_cont args rewrite_id =
  simplified_terminator
    (Simplified_apply_cont
       ((fun (x__1, x__2, x__3) ->
          ({ apply_cont = x__1; args = x__2; rewrite_id = x__3 }
            : simplified_apply_cont))
          (apply_cont, args, rewrite_id)))

(** val simplified_switch : (Apply_cont_expr.t, Branch_annotations.t,
    Apply_cont_rewrite_id.t, (_) Flambda_arity.t, Flambda2_types.Typing_env.t)
    Port_monad.tuple5 Map.t -> Debuginfo.t -> Simple.t -> Flambda2_types.t ->
    Symbol.t Import_.Static_const.Map.t -> Flambda2_types.Typing_env.t ->
    Common_subexpression_elimination.t -> t coq_M **)

let simplified_switch arms condition_dbg scrutinee scrutinee_ty
    shareable_constants typing_env_before_switch cse_before_switch =
  simplified_terminator
    (Simplified_switch
       ((fun (x__1, x__2, x__3, x__4, x__5, x__6, x__7) ->
          ({ arms = x__1;
             condition_dbg = x__2;
             scrutinee = x__3;
             scrutinee_ty = x__4;
             shareable_constants = x__5;
             typing_env_before_switch = x__6;
             cse_before_switch = x__7
           }
            : simplified_switch))
          ( arms,
            condition_dbg,
            scrutinee,
            scrutinee_ty,
            shareable_constants,
            typing_env_before_switch,
            cse_before_switch )))

(** val simplified_invalid : Flambda.Invalid.t -> t coq_M **)

let simplified_invalid invalid =
  simplified_terminator (Simplified_invalid invalid)

let simplified_apply ?result_arity apply use_id exn_cont_use_id is_cold =
  simplified_apply result_arity apply use_id exn_cont_use_id is_cold
