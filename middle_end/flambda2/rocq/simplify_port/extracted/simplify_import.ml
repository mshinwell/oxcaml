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
   middle_end/flambda2/rocq/simplify_port/Simplify_import.v, which follows
   middle_end/flambda2/simplify/simplify_import.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Apply_cont_rewrite_id
open Bound_parameter
open Bound_pattern
open Bound_var
open Code
open Code_id_or_symbol
open Continuation_extra_params_and_args
open Continuation_uses_env
open Downwards_acc
open Downwards_env
open Expr_builder
open Flambda
open Flambda2_types
open Flambda_kind
open Flambda_primitive
open Flambda_unit
open Lifted_constant
open Lifted_constant_state
open Name_mode
open Name_occurrences
open Port_monad
open Rebuilt_expr
open Rebuilt_static_const
open Reg_width_const
open Simplified_expr
open Simplified_named
open Simplify_primitive_result
open Simplify_simple
open Static_const
open Tag
open Target_ocaml_int
open Upwards_acc
open Upwards_env

(** val debug : unit -> bool coq_M **)

let debug = Flambda_features.debug_flambda2

module Apply = Apply
module Apply_cont = Apply_cont
module Code = Code
module Const = Reg_width_const
module Continuation_handler = Flambda.Continuation_handler
module Continuation_handlers = Continuation_handlers
module Expr = Expr
module Function_declarations = Function_declarations
module Function_params_and_body = Flambda.Function_params_and_body
module Let_cont = Let_cont
module Let = Let
module Named = Named
module Non_recursive_let_cont_handler = Non_recursive_let_cont_handler
module Recursive_let_cont_handlers = Recursive_let_cont_handlers
module Set_of_closures = Set_of_closures
module Switch = Switch
module AC = Apply_cont
module BP = Bound_parameter
module BPt = Bound_pattern
module BV = Bound_var
module CH = Continuation_handler
module CIS = Code_id_or_symbol
module CUE = Continuation_uses_env
module DA = Downwards_acc
module DE = Downwards_env
module EA = Extra_arg
module EB = Expr_builder
module EPA = Continuation_extra_params_and_args
module FU = Flambda_unit
module K = Flambda_kind
module KS = With_subkind
module LC = Lifted_constant
module LCS = Lifted_constant_state
module NM = Name_mode
module NO = Name_occurrences
module P = Flambda_primitive
module RE = Rebuilt_expr
module RSC = Rebuilt_static_const
module RI = Apply_cont_rewrite_id
module S = Simplify_simple
module SC = Static_const
module SE = Simplified_expr
module SPR = Simplify_primitive_result
module T = Flambda2_types
module TE = Typing_env
module TEE = Typing_env_extension
module UA = Upwards_acc
module UE = Upwards_env
module VB = Bound_var
