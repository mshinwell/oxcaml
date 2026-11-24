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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flambda], after its interface
   middle_end/flambda2/terms/flambda.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Apply_expr Bound_parameters Bound_pattern Code_metadata Continuation Debuginfo Flambda_arity Format Name_occurrences Or_unknown Set_of_closures Simple Static_const Switch_expr Trap_action.

(* flambda.mli:41  type expr *)
Parameter expr : Type.
Extract Inlined Constant expr => "Flambda.expr".
(* flambda.mli:43  type let_expr *)
Parameter let_expr : Type.
Extract Inlined Constant let_expr => "Flambda.let_expr".
(* flambda.mli:49  type function_params_and_body *)
Parameter function_params_and_body : Type.
Extract Inlined Constant function_params_and_body => "Flambda.function_params_and_body".
(* flambda.mli:70  and named = private | Simple of Simple.t ( ** Things that fit in a register (variables, symbols, constants). These do not have to be [Let]-bound but are allowed here for convenience. * ) | Prim of Flambda_primitive.t * Debuginfo.t ( ** Primitive operations (arithmetic, memory access, allocation, etc). * ) | Set_of_closures of Set_of_closures.t * Alloc_mode.For_allocations.t ( ** Definition of a... *)
Parameter named : Type.
Extract Inlined Constant named => "Flambda.named".
(* flambda.mli:85  and let_cont_expr = private | Non_recursive of { handler : non_recursive_let_cont_handler; num_free_occurrences : Num_occurrences.t Or_unknown.t; ( ** [num_free_occurrences] can be used, for example, to decide whether to inline out a linearly-used continuation. It will always be strictly greater than zero. * ) is_applied_with_traps : bool; ( ** [is_applied_with_traps] is used to prevent inlinin... *)
Parameter let_cont_expr : Type.
Extract Inlined Constant let_cont_expr => "Flambda.let_cont_expr".
(* flambda.mli:101  and static_const_or_code = private | Code of function_params_and_body Code0.t | Deleted_code | Static_const of Static_const.t *)
Parameter static_const_or_code : Type.
Extract Inlined Constant static_const_or_code => "Flambda.static_const_or_code".
(* flambda.mli:53  type expr_descr = private | Let of let_expr ( ** Bind variable(s), symbol(s) and/or code ID(s). The defining expression (the part after the '=', as in 'let x = defining_expr in body') never has any effect on control flow. * ) | Let_cont of let_cont_expr ( ** Define one or more continuations. * ) | Apply of Apply_expr.t ( ** Call an OCaml function, external function or method. * ) | Apply_cont o... *)
Record invalid_payload_ : Type := { message : string }.
Inductive expr_descr : Type :=
| Let : let_expr -> expr_descr
| Let_cont : let_cont_expr -> expr_descr
| Apply : Apply_expr.t -> expr_descr
| Apply_cont : Apply_cont_expr.t -> expr_descr
| Switch : Switch_expr.t -> expr_descr
| Invalid : invalid_payload_ -> expr_descr.
Module Invalid.
  (* flambda.mli:110  type t = | Body_of_unreachable_continuation of Continuation.t | Apply_cont_of_unreachable_continuation of Continuation.t | Defining_expr_of_let of Bound_pattern.t * named | Closure_type_was_invalid of Apply_expr.t | Direct_application_parameter_kind_mismatch of { params_arity : [`Complex] Flambda_arity.t; args_arity : [`Complex] Flambda_arity.t; apply : Apply_expr.t } | Application_argument_kin... *)
  Record direct_application_parameter_kind_mismatch_payload_ : Type := { params_arity : Flambda_arity.t; args_arity : Flambda_arity.t; apply : Apply_expr.t }.
  Inductive t : Type :=
  | Body_of_unreachable_continuation : Continuation.t -> t
  | Apply_cont_of_unreachable_continuation : Continuation.t -> t
  | Defining_expr_of_let : Bound_pattern.t -> Flambda.named -> t
  | Closure_type_was_invalid : Apply_expr.t -> t
  | Direct_application_parameter_kind_mismatch : direct_application_parameter_kind_mismatch_payload_ -> t
  | Application_argument_kind_mismatch : Flambda_arity.t -> Apply_expr.t -> t
  | Application_result_kind_mismatch : Flambda_arity.t -> Apply_expr.t -> t
  | Application_result_kind_mismatch_in_lambda : Debuginfo.t -> t
  | Partial_application_mode_mismatch : Apply_expr.t -> Code_metadata.t -> t
  | Partial_application_mode_mismatch_in_lambda : Debuginfo.t -> t
  | Calling_local_returning_closure_with_normal_apply : Apply_expr.t -> t
  | Zero_switch_arms : t
  | Code_not_rebuilt : t
  | To_cmm_dummy_body : t
  | Application_never_returns : Apply_expr.t -> t
  | Over_application_never_returns : Apply_expr.t -> t
  | Message : string -> t.
End Invalid.
Module Expr.
  (* flambda.mli:139  type t = expr *)
  Definition t : Type := Flambda.expr.
  Extract Inlined Constant t => "Flambda.Expr.t".
  (* flambda.mli:148  val descr : t -> expr_descr *)
  Parameter descr : t -> M Flambda.expr_descr.
  Extract Inlined Constant descr => "Flambda.Expr.descr".
  (* flambda.mli:156  val create_apply_cont : Apply_cont_expr.t -> t *)
  Parameter create_apply_cont : Apply_cont_expr.t -> M t.
  Extract Inlined Constant create_apply_cont => "Flambda.Expr.create_apply_cont".
End Expr.
Module Named.
  (* flambda.mli:165  type t = named *)
  Definition t : Type := Flambda.named.
  Extract Inlined Constant t => "Flambda.Named.t".
  (* flambda.mli:172  val create_simple : Simple.t -> t *)
  Parameter create_simple : Simple.t -> M t.
  Extract Inlined Constant create_simple => "Flambda.Named.create_simple".
End Named.
Module Let_expr.
  (* flambda.mli:233  type t = let_expr *)
  Definition t : Type := Flambda.let_expr.
  Extract Inlined Constant t => "Flambda.Let_expr.t".
End Let_expr.
Module Continuation_handler.
  (* flambda.mli:307  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda.Continuation_handler.t".
  (* flambda.mli:319  val create : Bound_parameters.t -> handler:expr -> free_names_of_handler:Name_occurrences.t Or_unknown.t -> is_exn_handler:bool -> is_cold:bool -> t *)
  Parameter create : Bound_parameters.t -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> bool -> bool -> M t.
  Extract Inlined Constant create => "Flambda.Continuation_handler.create".
End Continuation_handler.
Module Let_cont_expr.
  (* flambda.mli:422  type t = let_cont_expr *)
  Definition t : Type := Flambda.let_cont_expr.
  Extract Inlined Constant t => "Flambda.Let_cont_expr.t".
End Let_cont_expr.
Module Function_params_and_body.
  (* flambda.mli:548  type t = function_params_and_body *)
  Definition t : Type := Flambda.function_params_and_body.
  Extract Inlined Constant t => "Flambda.Function_params_and_body.t".
End Function_params_and_body.
Module Static_const_or_code.
  (* flambda.mli:638  type t = static_const_or_code *)
  Definition t : Type := Flambda.static_const_or_code.
  Extract Inlined Constant t => "Flambda.Static_const_or_code.t".
End Static_const_or_code.
(* module Apply = Apply_expr: declared again here under this name. *)
Module Apply.
  (* apply_expr.mli:20  type t *)
  Definition t : Type := Apply_expr.t.
  Extract Inlined Constant t => "Flambda.Apply.t".
End Apply.
(* module Apply_cont = Apply_cont_expr: declared again here under this name. *)
Module Apply_cont.
  (* apply_cont_expr.mli:20  type t *)
  Definition t : Type := Apply_cont_expr.t.
  Extract Inlined Constant t => "Flambda.Apply_cont.t".
  (* apply_cont_expr.mli:22  include Expr_std.S with type t := t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Flambda.Apply_cont.free_names".
  (* apply_cont_expr.mli:35  val continuation : t -> Continuation.t *)
  Parameter continuation : t -> M Continuation.t.
  Extract Inlined Constant continuation => "Flambda.Apply_cont.continuation".
  (* apply_cont_expr.mli:37  val args : t -> Simple.t list *)
  Parameter args : t -> M (list Simple.t).
  Extract Inlined Constant args => "Flambda.Apply_cont.args".
  (* apply_cont_expr.mli:39  val trap_action : t -> Trap_action.t option *)
  Parameter trap_action : t -> M (option Trap_action.t).
  Extract Inlined Constant trap_action => "Flambda.Apply_cont.trap_action".
  (* apply_cont_expr.mli:41  val debuginfo : t -> Debuginfo.t *)
  Parameter debuginfo : t -> M Debuginfo.t.
  Extract Inlined Constant debuginfo => "Flambda.Apply_cont.debuginfo".
  (* apply_cont_expr.mli:43  val with_continuation : t -> Continuation.t -> t *)
  Parameter with_continuation : t -> Continuation.t -> M t.
  Extract Inlined Constant with_continuation => "Flambda.Apply_cont.with_continuation".
  (* apply_cont_expr.mli:47  val update_args : t -> args:Simple.t list -> t *)
  Parameter update_args : t -> list Simple.t -> M t.
  Extract Inlined Constant update_args => "Flambda.Apply_cont.update_args".
  (* apply_cont_expr.mli:49  val with_debuginfo : t -> dbg:Debuginfo.t -> t *)
  Parameter with_debuginfo : t -> Debuginfo.t -> M t.
  Extract Inlined Constant with_debuginfo => "Flambda.Apply_cont.with_debuginfo".
  (* module T = Apply_cont_expr.T: declared again here under this name. *)
  Module T.
    (* apply_cont_expr.mli:60  include Container_types.S with type t := t *)
    Definition t : Type := Apply_cont_expr.T.t.
    Extract Inlined Constant t => "Flambda.Apply_cont.T.t".
  End T.
  (* apply_cont_expr.mli:60  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> Flambda.Apply_cont.T.t -> M unit.
  Extract Inlined Constant print => "Flambda.Apply_cont.print".
End Apply_cont.
(* module Let = Flambda.Let_expr: declared again here under this name. *)
Module Let.
  (* flambda.mli:233  type t = let_expr *)
  Definition t : Type := Flambda.Let_expr.t.
  Extract Inlined Constant t => "Flambda.Let.t".
End Let.
(* module Let_cont = Flambda.Let_cont_expr: declared again here under this name. *)
Module Let_cont.
  (* flambda.mli:422  type t = let_cont_expr *)
  Definition t : Type := Flambda.Let_cont_expr.t.
  Extract Inlined Constant t => "Flambda.Let_cont.t".
End Let_cont.
(* module Set_of_closures = Set_of_closures: declared again here under this name. *)
Module Set_of_closures.
  (* set_of_closures.mli:17  type t *)
  Definition t : Type := decl.Set_of_closures.t.
  Extract Inlined Constant t => "Flambda.Set_of_closures.t".
End Set_of_closures.
(* module Switch = Switch_expr: declared again here under this name. *)
Module Switch.
  (* switch_expr.mli:26  type t *)
  Definition t : Type := Switch_expr.t.
  Extract Inlined Constant t => "Flambda.Switch.t".
End Switch.
Module Import_.
  (* module Apply = Apply_expr: declared again here under this name. *)
  Module Apply.
    (* apply_expr.mli:20  type t *)
    Definition t : Type := Apply_expr.t.
    Extract Inlined Constant t => "Flambda.Import.Apply.t".
  End Apply.
  (* module Apply_cont = Apply_cont_expr: declared again here under this name. *)
  Module Apply_cont.
    (* apply_cont_expr.mli:20  type t *)
    Definition t : Type := Apply_cont_expr.t.
    Extract Inlined Constant t => "Flambda.Import.Apply_cont.t".
  End Apply_cont.
  (* module Named = Flambda.Named: declared again here under this name. *)
  Module Named.
    (* flambda.mli:165  type t = named *)
    Definition t : Type := Flambda.Named.t.
    Extract Inlined Constant t => "Flambda.Import.Named.t".
  End Named.
  (* module Static_const = Static_const: declared again here under this name. *)
  Module Static_const.
    (* module Map = Static_const.Map: declared again here under this name. *)
    Module Map.
      (* static_const.mli:71  include Container_types.S with type t := t *)
      Definition t (A : Type) : Type := decl.Static_const.Map.t A.
      Extract Constant t "'a1" => "('a1) Flambda.Import.Static_const.Map.t".
    End Map.
  End Static_const.
End Import_.
