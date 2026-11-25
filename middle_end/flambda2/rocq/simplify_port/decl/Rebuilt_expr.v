(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2021 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Rebuilt_expr], after its interface
   middle_end/flambda2/simplify/rebuilt_expr.mli
   (Git blob 6fc2563231d433c86a86e30948c7e26779efd4ac). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Are_rebuilding_terms Bound_parameters Bound_pattern Bound_var Code_size Continuation Cost_metrics Flambda Format Name_occurrences Num_occurrences Recursive Simple Switch_expr Variable_.

(* rebuilt_expr.mli:28  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Rebuilt_expr.t".
(* rebuilt_expr.mli:30  type rebuilt_expr = t *)
Definition rebuilt_expr : Type := t.
Extract Inlined Constant rebuilt_expr => "Rebuilt_expr.rebuilt_expr".
(* rebuilt_expr.mli:32  val print : Are_rebuilding_terms.t -> Format.formatter -> t -> unit *)
Parameter print : Are_rebuilding_terms.t -> Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Rebuilt_expr.print".
(* rebuilt_expr.mli:35  val to_expr : t -> Are_rebuilding_terms.t -> Expr.t *)
Parameter to_expr : t -> Are_rebuilding_terms.t -> M Flambda.Expr.t.
Extract Inlined Constant to_expr => "Rebuilt_expr.to_expr".
(* rebuilt_expr.mli:37  val to_apply_cont : t -> Apply_cont.t option *)
Parameter to_apply_cont : t -> M (option Flambda.Apply_cont.t).
Extract Inlined Constant to_apply_cont => "Rebuilt_expr.to_apply_cont".
(* rebuilt_expr.mli:39  val is_cold : t -> bool *)
Parameter is_cold : t -> M bool.
Extract Inlined Constant is_cold => "Rebuilt_expr.is_cold".
(* rebuilt_expr.mli:41  val mark_as_cold : t -> t *)
Parameter mark_as_cold : t -> M t.
Extract Inlined Constant mark_as_cold => "Rebuilt_expr.mark_as_cold".
(* rebuilt_expr.mli:43  val can_be_removed_as_invalid : t -> Are_rebuilding_terms.t -> bool *)
Parameter can_be_removed_as_invalid : t -> Are_rebuilding_terms.t -> M bool.
Extract Inlined Constant can_be_removed_as_invalid => "Rebuilt_expr.can_be_removed_as_invalid".
(* rebuilt_expr.mli:45  val term_not_rebuilt : t *)
Parameter term_not_rebuilt : t.
Extract Inlined Constant term_not_rebuilt => "Rebuilt_expr.term_not_rebuilt".
(* rebuilt_expr.mli:49  val create_let : Are_rebuilding_terms.t -> Bound_pattern.t -> Named.t -> body:t -> free_names_of_body:Name_occurrences.t -> t *)
Parameter create_let : Are_rebuilding_terms.t -> Bound_pattern.t -> Flambda.Named.t -> t -> Name_occurrences.t -> M t.
Extract Inlined Constant create_let => "Rebuilt_expr.create_let".
(* rebuilt_expr.mli:57  val create_apply : Are_rebuilding_terms.t -> is_cold:bool -> Apply.t -> t *)
Parameter create_apply : Are_rebuilding_terms.t -> bool -> Flambda.Apply.t -> M t.
Extract Inlined Constant create_apply => "Rebuilt_expr.create_apply".
(* rebuilt_expr.mli:61  val create_apply_cont : is_cold:bool -> Apply_cont.t -> t *)
Parameter create_apply_cont : bool -> Flambda.Apply_cont.t -> M t.
Extract Inlined Constant create_apply_cont => "Rebuilt_expr.create_apply_cont".
Module Function_params_and_body.
  (* rebuilt_expr.mli:64  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Rebuilt_expr.Function_params_and_body.t".
  (* rebuilt_expr.mli:66  val create : return_continuation:Continuation.t -> exn_continuation:Continuation.t -> Bound_parameters.t -> body:rebuilt_expr -> free_names_of_body:Name_occurrences.t -> my_closure:Variable.t -> my_alloc_mode:Alloc_mode.For_applications.t -> my_depth:Variable.t -> t *)
  Parameter create : Continuation.t -> Continuation.t -> Bound_parameters.t -> Rebuilt_expr.rebuilt_expr -> Name_occurrences.t -> Variable_.t -> Alloc_mode.For_applications.t -> Variable_.t -> M t.
  Extract Inlined Constant create => "Rebuilt_expr.Function_params_and_body.create".
  (* rebuilt_expr.mli:78  val to_function_params_and_body : t -> Are_rebuilding_terms.t -> Function_params_and_body.t *)
  Parameter to_function_params_and_body : t -> Are_rebuilding_terms.t -> M Flambda.Function_params_and_body.t.
  Extract Inlined Constant to_function_params_and_body => "Rebuilt_expr.Function_params_and_body.to_function_params_and_body".
  (* rebuilt_expr.mli:81  val is_my_closure_used : t -> bool *)
  Parameter is_my_closure_used : t -> M bool.
  Extract Inlined Constant is_my_closure_used => "Rebuilt_expr.Function_params_and_body.is_my_closure_used".
End Function_params_and_body.
Module Continuation_handler.
  (* rebuilt_expr.mli:85  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Rebuilt_expr.Continuation_handler.t".
  (* rebuilt_expr.mli:87  val print : cont:Continuation.t -> recursive:Recursive.t -> Format.formatter -> t -> unit *)
  Parameter print : Continuation.t -> Recursive.t -> Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Rebuilt_expr.Continuation_handler.print".
  (* rebuilt_expr.mli:94  val create : Are_rebuilding_terms.t -> Bound_parameters.t -> handler:rebuilt_expr -> free_names_of_handler:Name_occurrences.t -> is_exn_handler:bool -> is_cold:bool -> t *)
  Parameter create : Are_rebuilding_terms.t -> Bound_parameters.t -> Rebuilt_expr.rebuilt_expr -> Name_occurrences.t -> bool -> bool -> M t.
  Extract Inlined Constant create => "Rebuilt_expr.Continuation_handler.create".
End Continuation_handler.
(* rebuilt_expr.mli:104  val create_non_recursive_let_cont : Are_rebuilding_terms.t -> Continuation.t -> Continuation_handler.t -> body:t -> free_names_of_body:Name_occurrences.t -> t *)
Parameter create_non_recursive_let_cont : Are_rebuilding_terms.t -> Continuation.t -> Rebuilt_expr.Continuation_handler.t -> t -> Name_occurrences.t -> M t.
Extract Inlined Constant create_non_recursive_let_cont => "Rebuilt_expr.create_non_recursive_let_cont".
(* rebuilt_expr.mli:112  val create_non_recursive_let_cont' : Are_rebuilding_terms.t -> Continuation.t -> Continuation_handler.t -> body:t -> num_free_occurrences_of_cont_in_body:Num_occurrences.t -> is_applied_with_traps:bool -> t *)
Parameter create_non_recursive_let_cont' : Are_rebuilding_terms.t -> Continuation.t -> Rebuilt_expr.Continuation_handler.t -> t -> Num_occurrences.t -> bool -> M t.
Extract Inlined Constant create_non_recursive_let_cont' => "Rebuilt_expr.create_non_recursive_let_cont'".
(* rebuilt_expr.mli:121  val create_non_recursive_let_cont_without_free_names : Are_rebuilding_terms.t -> Continuation.t -> Continuation_handler.t -> body:t -> t *)
Parameter create_non_recursive_let_cont_without_free_names : Are_rebuilding_terms.t -> Continuation.t -> Rebuilt_expr.Continuation_handler.t -> t -> M t.
Extract Inlined Constant create_non_recursive_let_cont_without_free_names => "Rebuilt_expr.create_non_recursive_let_cont_without_free_names".
(* rebuilt_expr.mli:128  val create_recursive_let_cont : Are_rebuilding_terms.t -> invariant_params:Bound_parameters.t -> Continuation_handler.t Continuation.Lmap.t -> body:t -> t *)
Parameter create_recursive_let_cont : Are_rebuilding_terms.t -> Bound_parameters.t -> Continuation.Lmap.t Rebuilt_expr.Continuation_handler.t -> t -> M t.
Extract Inlined Constant create_recursive_let_cont => "Rebuilt_expr.create_recursive_let_cont".
(* rebuilt_expr.mli:135  val create_switch : Are_rebuilding_terms.t -> is_cold:bool -> Switch_expr.t -> t *)
Parameter create_switch : Are_rebuilding_terms.t -> bool -> Switch_expr.t -> M t.
Extract Inlined Constant create_switch => "Rebuilt_expr.create_switch".
(* rebuilt_expr.mli:137  val create_invalid : Invalid.t -> t *)
Parameter create_invalid : Flambda.Invalid.t -> M t.
Extract Inlined Constant create_invalid => "Rebuilt_expr.create_invalid".
(* rebuilt_expr.mli:139  val bind_no_simplification : Are_rebuilding_terms.t -> bindings:(Bound_var.t * Code_size.t * Named.t) list -> body:t -> cost_metrics_of_body:Cost_metrics.t -> free_names_of_body:Name_occurrences.t -> t * Cost_metrics.t * Name_occurrences.t *)
Parameter bind_no_simplification : Are_rebuilding_terms.t -> list (tuple3 Bound_var.t Code_size.t Flambda.Named.t) -> t -> Cost_metrics.t -> Name_occurrences.t -> M (tuple3 t Cost_metrics.t Name_occurrences.t).
Extract Inlined Constant bind_no_simplification => "Rebuilt_expr.bind_no_simplification".
Module Unique_continuation_handlers.
  (* rebuilt_expr.mli:151  type 'a t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Rebuilt_expr.Unique_continuation_handlers.t".
  (* rebuilt_expr.mli:153  val empty : 'a t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Rebuilt_expr.Unique_continuation_handlers.empty".
  (* rebuilt_expr.mli:155  val add : Are_rebuilding_terms.t -> Bound_parameters.t -> rebuilt_expr -> is_exn_handler:bool -> free_names_without_params:Name_occurrences.t -> 'a -> 'a t -> 'a t *)
  Parameter add : forall {A : Type}, Are_rebuilding_terms.t -> Bound_parameters.t -> Rebuilt_expr.rebuilt_expr -> bool -> Name_occurrences.t -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Rebuilt_expr.Unique_continuation_handlers.add".
  (* rebuilt_expr.mli:165  val find_opt : Are_rebuilding_terms.t -> Bound_parameters.t -> rebuilt_expr -> is_exn_handler:bool -> free_names_without_params:Name_occurrences.t -> 'a t -> ('a * Simple.t list) option *)
  Parameter find_opt : forall {A : Type}, Are_rebuilding_terms.t -> Bound_parameters.t -> Rebuilt_expr.rebuilt_expr -> bool -> Name_occurrences.t -> t A -> M (option (A * list Simple.t)).
  Extract Inlined Constant find_opt => "Rebuilt_expr.Unique_continuation_handlers.find_opt".
End Unique_continuation_handlers.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Rebuilt_expr. End Rebuilt_expr.
