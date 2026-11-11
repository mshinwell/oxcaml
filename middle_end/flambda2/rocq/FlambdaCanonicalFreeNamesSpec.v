(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
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

(* The statements about binders, written with the one function for the
   free names.

   This file is to be reviewed: the statements, each against the
   statement of FlambdaNominalSpec.v or the rule of
   FlambdaAlphaSpec.alpha_equivalent that it restates.

   The statements of FlambdaNominalSpec.v and the rules of
   [alpha_equivalent] are written with the older relations
   [var_free_in_expr] and [cont_free_in_expr], which do not look into
   code. The free names of a term are now given by one function for
   each sort (FlambdaBindersSpec.v), which does. Here each of those
   statements is written with the functions: where the older statement
   asks that a renaming fixes every name that is free by the relation,
   this one asks that it fixes the list ([fixes_names]); where the older
   asks that a name is not free by the relation, this one asks that it
   is not among the list.

   Each is proved from the statement it restates and from
   FlambdaFreeNamesSpec.var_free_among_statement and
   cont_free_among_statement (free by the relation is among the list,
   whatever the code). So the premise about names here asks at least as
   much as the older one, and the two are the same where code is closed
   (FlambdaFreeNamesSpec.var_free_agrees_statement). The premises that
   code is closed are kept as they are.

   These are the forms that the statements of FlambdaNominalSpec.v and
   the rules of [alpha_equivalent] are to take when the older relations
   are deleted; until then both are there, and this file adds nothing
   that a well-formed term can tell from the older ones.

   Nothing is trusted here. The proofs are in
   FlambdaCanonicalFreeNamesProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaBindersSpec FlambdaSemanticsSpec FlambdaNominalSpec
  FlambdaAlphaSpec FlambdaNameAbstractionSpec.
Import ListNotations.

(* The renaming moves none of the variables [vs] and none of the
   continuations [ks]. *)
Definition fixes_names (r : renaming) (vs : list variable)
    (ks : list continuation) : Prop :=
  fixes (variable_permutation r) vs
  ∧ fixes (continuation_permutation r) ks.

(* ======================================================================== *)
(* The statements of FlambdaNominalSpec.v                                   *)
(* ======================================================================== *)

(* [rename_let_statement]. *)
Definition rename_let_canonical_statement : Prop :=
  ∀ (r : renaming) (x : variable) (kind : flambda_kind)
    (defining_expr : named) (body : expr),
    code_closed body = true ->
    fixes_names r (without [x] (free_variables_of_expr body))
      (free_continuations_of_expr body) ->
    expr_equivalent (Let x kind defining_expr body)
      (Let (rename_variable r x) kind defining_expr (rename_expr r body)).

(* [freshen_let_statement]. *)
Definition freshen_let_canonical_statement : Prop :=
  ∀ (x fresh : variable) (kind : flambda_kind) (defining_expr : named)
    (body : expr),
    code_closed body = true ->
    among fresh (free_variables_of_expr body) = false ->
    expr_equivalent (Let x kind defining_expr body)
      (Let fresh kind defining_expr
         (rename_expr (Renaming [(x, fresh)] []) body)).

(* [rename_let_cont_statement]. *)
Definition rename_let_cont_canonical_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (handler : continuation_handler)
    (body : expr),
    code_closed body = true ->
    fixes_names r (free_variables_of_expr body)
      (without [k] (free_continuations_of_expr body)) ->
    expr_equivalent (Let_cont_non_recursive k handler body)
      (Let_cont_non_recursive (rename_continuation r k) handler
         (rename_expr r body)).

(* [rename_handler_params_statement]. The free variables of a handler
   are those of its body that are not its parameters. *)
Definition rename_handler_params_canonical_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler body : expr),
    code_closed handler = true ->
    fixes_names r
      (free_variables_of_handler (Handler params metadata handler))
      (free_continuations_of_expr handler) ->
    expr_equivalent
      (Let_cont_non_recursive k (Handler params metadata handler) body)
      (Let_cont_non_recursive k
         (rename_handler r (Handler params metadata handler)) body).

(* [rename_recursive_handler_params_statement]. *)
Definition rename_recursive_handler_params_canonical_statement : Prop :=
  ∀ (r : renaming) (before : list (continuation * continuation_handler))
    (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler : expr)
    (after : list (continuation * continuation_handler)) (body : expr),
    code_closed handler = true ->
    fixes_names r
      (free_variables_of_handler (Handler params metadata handler))
      (free_continuations_of_expr handler) ->
    expr_equivalent
      (Let_cont_recursive
         (before ++ (k, Handler params metadata handler) :: after) body)
      (Let_cont_recursive
         (before
          ++ (k, rename_handler r (Handler params metadata handler)) :: after)
         body).

(* [rename_let_cont_recursive_statement]. *)
Definition rename_let_cont_recursive_canonical_statement : Prop :=
  ∀ (r : renaming) (handlers : list (continuation * continuation_handler))
    (body : expr),
    code_closed (Let_cont_recursive handlers body) = true ->
    fixes_names r
      (free_variables_of_expr (Let_cont_recursive handlers body))
      (free_continuations_of_expr (Let_cont_recursive handlers body)) ->
    expr_equivalent (Let_cont_recursive handlers body)
      (rename_expr r (Let_cont_recursive handlers body)).

(* [unused_let_statement]. No condition on code, there or here; here
   the premise asks more where code is not closed. *)
Definition unused_let_canonical_statement : Prop :=
  ∀ (x : variable) (kind : flambda_kind) (defining_expr : named)
    (body : expr),
    among x (free_variables_of_expr body) = false ->
    expr_refines (Let x kind defining_expr body) body.

(* [unused_let_cont_statement]. *)
Definition unused_let_cont_canonical_statement : Prop :=
  ∀ (k : continuation) (handler : continuation_handler) (body : expr),
    among k (free_continuations_of_expr body) = false ->
    expr_equivalent (Let_cont_non_recursive k handler body) body.

(* [unused_let_cont_recursive_statement]. *)
Definition unused_let_cont_recursive_canonical_statement : Prop :=
  ∀ (handlers : list (continuation * continuation_handler)) (body : expr),
    handlers_bind_statics handlers = false ->
    (∀ k : continuation,
      among k (free_continuations_of_expr body) = true ->
      lookup k handlers = None) ->
    expr_equivalent (Let_cont_recursive handlers body) body.

(* ======================================================================== *)
(* The rules of alpha-equivalence                                           *)
(* ======================================================================== *)

(* [Alpha_rename]. *)
Definition alpha_rename_canonical_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    code_closed e = true ->
    fixes_names r (free_variables_of_expr e)
      (free_continuations_of_expr e) ->
    alpha_equivalent e (rename_expr r e).

(* [Alpha_let]. *)
Definition alpha_let_canonical_statement : Prop :=
  ∀ (r : renaming) (x : variable) (kind : flambda_kind)
    (defining_expr : named) (body : expr),
    code_closed body = true ->
    fixes_names r (without [x] (free_variables_of_expr body))
      (free_continuations_of_expr body) ->
    alpha_equivalent (Let x kind defining_expr body)
      (Let (rename_variable r x) kind defining_expr (rename_expr r body)).

(* [Alpha_let_cont]. *)
Definition alpha_let_cont_canonical_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (handler : continuation_handler)
    (body : expr),
    code_closed body = true ->
    fixes_names r (free_variables_of_expr body)
      (without [k] (free_continuations_of_expr body)) ->
    alpha_equivalent (Let_cont_non_recursive k handler body)
      (Let_cont_non_recursive (rename_continuation r k) handler
         (rename_expr r body)).

(* [Alpha_handler]. *)
Definition alpha_handler_canonical_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler body : expr),
    code_closed handler = true ->
    fixes_names r
      (free_variables_of_handler (Handler params metadata handler))
      (free_continuations_of_expr handler) ->
    alpha_equivalent
      (Let_cont_non_recursive k (Handler params metadata handler) body)
      (Let_cont_non_recursive k
         (rename_handler r (Handler params metadata handler)) body).

(* [Alpha_recursive_handler]. *)
Definition alpha_recursive_handler_canonical_statement : Prop :=
  ∀ (r : renaming) (before : list (continuation * continuation_handler))
    (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler : expr)
    (after : list (continuation * continuation_handler)) (body : expr),
    code_closed handler = true ->
    fixes_names r
      (free_variables_of_handler (Handler params metadata handler))
      (free_continuations_of_expr handler) ->
    alpha_equivalent
      (Let_cont_recursive
         (before ++ (k, Handler params metadata handler) :: after) body)
      (Let_cont_recursive
         (before
          ++ (k, rename_handler r (Handler params metadata handler)) :: after)
         body).

(* [rename_variables_equivalent_statement]. *)
Definition rename_variables_equivalent_canonical_statement : Prop :=
  ∀ (r : renaming) (e : expr) (vars : env) (conts : cont_env)
    (statics : static_env),
    code_closed e = true ->
    fixes (continuation_permutation r) (free_continuations_of_expr e) ->
    equivalent (State e vars conts statics)
      (State (rename_expr r e) (rename_env r vars) conts statics).
