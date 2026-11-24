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
From SimplifyPort.decl Require Alloc_mode Apply_cont_expr Apply_expr Bound_parameters Bound_pattern Bound_static Call_kind Code0 Code_id Code_metadata Continuation Debuginfo Exn_continuation Flambda_arity Flambda_primitive Format Function_declarations Function_slot Inlined_attribute Inlining_arguments Inlining_history Inlining_state Name_occurrences Num_occurrences Or_unknown Probe Rec_info_expr Recursive Renaming Set_of_closures Simple Static_const Switch_arm Switch_expr Symbol Target_ocaml_int Trap_action Value_slot Variable_.

(* flambda.mli:41  type expr *)
Parameter expr : Type.
Extract Inlined Constant expr => "Flambda.expr".
(* flambda.mli:43  type let_expr *)
Parameter let_expr : Type.
Extract Inlined Constant let_expr => "Flambda.let_expr".
(* flambda.mli:45  type non_recursive_let_cont_handler *)
Parameter non_recursive_let_cont_handler : Type.
Extract Inlined Constant non_recursive_let_cont_handler => "Flambda.non_recursive_let_cont_handler".
(* flambda.mli:47  type recursive_let_cont_handlers *)
Parameter recursive_let_cont_handlers : Type.
Extract Inlined Constant recursive_let_cont_handlers => "Flambda.recursive_let_cont_handlers".
(* flambda.mli:49  type function_params_and_body *)
Parameter function_params_and_body : Type.
Extract Inlined Constant function_params_and_body => "Flambda.function_params_and_body".
(* flambda.mli:51  type static_const_group *)
Parameter static_const_group : Type.
Extract Inlined Constant static_const_group => "Flambda.static_const_group".
(* flambda.mli:53  type expr_descr = private | Let of let_expr ( ** Bind variable(s), symbol(s) and/or code ID(s). The defining expression (the part after the '=', as in 'let x = defining_expr in body') never has any effect on control flow. * ) | Let_cont of let_cont_expr ( ** Define one or more continuations. * ) | Apply of Apply_expr.t ( ** Call an OCaml function, external function or method. * ) | Apply_cont o... *)
(* PORT-GAP(type): it is recursive with a type that is declared after it: abstract, with a maker for each constructor and one eliminator. *)
Parameter expr_descr : Type.
Extract Inlined Constant expr_descr => "Flambda.expr_descr".
(* flambda.mli:70  and named = private | Simple of Simple.t ( ** Things that fit in a register (variables, symbols, constants). These do not have to be [Let]-bound but are allowed here for convenience. * ) | Prim of Flambda_primitive.t * Debuginfo.t ( ** Primitive operations (arithmetic, memory access, allocation, etc). * ) | Set_of_closures of Set_of_closures.t * Alloc_mode.For_allocations.t ( ** Definition of a... *)
Inductive named : Type :=
| Simple : Simple.t -> named
| Prim : Flambda_primitive.t -> Debuginfo.t -> named
| Set_of_closures : decl.Set_of_closures.t -> Alloc_mode.For_allocations.t -> named
| Static_consts : static_const_group -> named
| Rec_info : Rec_info_expr.t -> named.
(* flambda.mli:85  and let_cont_expr = private | Non_recursive of { handler : non_recursive_let_cont_handler; num_free_occurrences : Num_occurrences.t Or_unknown.t; ( ** [num_free_occurrences] can be used, for example, to decide whether to inline out a linearly-used continuation. It will always be strictly greater than zero. * ) is_applied_with_traps : bool; ( ** [is_applied_with_traps] is used to prevent inlinin... *)
Record non_recursive_payload_ : Type := { handler : non_recursive_let_cont_handler; num_free_occurrences : Or_unknown.t Num_occurrences.t; is_applied_with_traps : bool; can_be_lifted : bool }.
Inductive let_cont_expr : Type :=
| Non_recursive : non_recursive_payload_ -> let_cont_expr
| Recursive : recursive_let_cont_handlers -> let_cont_expr.
(* flambda.mli:101  and static_const_or_code = private | Code of function_params_and_body Code0.t | Deleted_code | Static_const of Static_const.t *)
Inductive static_const_or_code : Type :=
| Code : Code0.t function_params_and_body -> static_const_or_code
| Deleted_code : static_const_or_code
| Static_const : decl.Static_const.t -> static_const_or_code.
Parameter match_expr_descr : forall {Res : Type}, expr_descr -> (let_expr -> M Res) -> (let_cont_expr -> M Res) -> (Apply_expr.t -> M Res) -> (Apply_cont_expr.t -> M Res) -> (Switch_expr.t -> M Res) -> (string -> M Res) -> M Res.
Extract Inlined Constant match_expr_descr => "(fun x__0 f__1 f__2 f__3 f__4 f__5 f__6 -> match x__0 with Flambda.Let x__1 -> f__1 x__1 | Flambda.Let_cont x__1 -> f__2 x__1 | Flambda.Apply x__1 -> f__3 x__1 | Flambda.Apply_cont x__1 -> f__4 x__1 | Flambda.Switch x__1 -> f__5 x__1 | Flambda.Invalid { message = x__1 } -> f__6 x__1)".
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
  (* flambda.mli:143  include Expr_std.S_no_free_names with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda.Expr.print".
  (* flambda.mli:143  include Expr_std.S_no_free_names with type t := t *)
  Parameter apply_renaming : t -> Renaming.t -> M t.
  Extract Inlined Constant apply_renaming => "Flambda.Expr.apply_renaming".
  (* flambda.mli:148  val descr : t -> expr_descr *)
  Parameter descr : t -> M Flambda.expr_descr.
  Extract Inlined Constant descr => "Flambda.Expr.descr".
  (* flambda.mli:150  val create_let : let_expr -> t *)
  Parameter create_let : Flambda.let_expr -> M t.
  Extract Inlined Constant create_let => "Flambda.Expr.create_let".
  (* flambda.mli:153  val create_apply : Apply_expr.t -> t *)
  Parameter create_apply : Apply_expr.t -> M t.
  Extract Inlined Constant create_apply => "Flambda.Expr.create_apply".
  (* flambda.mli:156  val create_apply_cont : Apply_cont_expr.t -> t *)
  Parameter create_apply_cont : Apply_cont_expr.t -> M t.
  Extract Inlined Constant create_apply_cont => "Flambda.Expr.create_apply_cont".
  (* flambda.mli:160  val create_invalid : Invalid.t -> t *)
  Parameter create_invalid : Flambda.Invalid.t -> M t.
  Extract Inlined Constant create_invalid => "Flambda.Expr.create_invalid".
End Expr.
Module Named.
  (* flambda.mli:165  type t = named *)
  Definition t : Type := Flambda.named.
  Extract Inlined Constant t => "Flambda.Named.t".
  (* flambda.mli:167  include Expr_std.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda.Named.print".
  (* flambda.mli:167  include Expr_std.S with type t := t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Flambda.Named.free_names".
  (* flambda.mli:172  val create_simple : Simple.t -> t *)
  Parameter create_simple : Simple.t -> M t.
  Extract Inlined Constant create_simple => "Flambda.Named.create_simple".
  (* flambda.mli:179  val create_prim : Flambda_primitive.t -> Debuginfo.t -> t *)
  Parameter create_prim : Flambda_primitive.t -> Debuginfo.t -> M t.
  Extract Inlined Constant create_prim => "Flambda.Named.create_prim".
  (* flambda.mli:182  val create_set_of_closures : alloc_mode:Alloc_mode.For_allocations.t -> Set_of_closures.t -> t *)
  Parameter create_set_of_closures : Alloc_mode.For_allocations.t -> decl.Set_of_closures.t -> M t.
  Extract Inlined Constant create_set_of_closures => "Flambda.Named.create_set_of_closures".
  (* flambda.mli:187  val create_static_consts : static_const_group -> t *)
  Parameter create_static_consts : Flambda.static_const_group -> M t.
  Extract Inlined Constant create_static_consts => "Flambda.Named.create_static_consts".
  (* flambda.mli:191  val create_rec_info : Rec_info_expr.t -> t *)
  Parameter create_rec_info : Rec_info_expr.t -> M t.
  Extract Inlined Constant create_rec_info => "Flambda.Named.create_rec_info".
  (* flambda.mli:214  val at_most_generative_effects : t -> bool *)
  Parameter at_most_generative_effects : t -> M bool.
  Extract Inlined Constant at_most_generative_effects => "Flambda.Named.at_most_generative_effects".
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
  (* flambda.mli:338  val pattern_match : t -> f:(Bound_parameters.t -> handler:expr -> 'a) -> 'a *)
  Parameter pattern_match : forall {A : Type}, t -> (Bound_parameters.t -> Flambda.expr -> M A) -> M A.
  Extract Inlined Constant pattern_match => "Flambda.Continuation_handler.pattern_match".
  (* flambda.mli:374  val is_exn_handler : t -> bool *)
  Parameter is_exn_handler : t -> M bool.
  Extract Inlined Constant is_exn_handler => "Flambda.Continuation_handler.is_exn_handler".
  (* flambda.mli:376  val is_cold : t -> bool *)
  Parameter is_cold : t -> M bool.
  Extract Inlined Constant is_cold => "Flambda.Continuation_handler.is_cold".
End Continuation_handler.
Module Continuation_handlers.
  (* flambda.mli:382  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda.Continuation_handlers.t".
  (* flambda.mli:385  val to_map : t -> Continuation_handler.t Continuation.Lmap.t *)
  Parameter to_map : t -> M (Continuation.Lmap.t Flambda.Continuation_handler.t).
  Extract Inlined Constant to_map => "Flambda.Continuation_handlers.to_map".
  (* flambda.mli:391  val contains_exn_handler : t -> bool *)
  Parameter contains_exn_handler : t -> M bool.
  Extract Inlined Constant contains_exn_handler => "Flambda.Continuation_handlers.contains_exn_handler".
End Continuation_handlers.
Module Let_cont_expr.
  (* flambda.mli:422  type t = let_cont_expr *)
  Definition t : Type := Flambda.let_cont_expr.
  Extract Inlined Constant t => "Flambda.Let_cont_expr.t".
End Let_cont_expr.
Module Non_recursive_let_cont_handler.
  (* flambda.mli:464  type t = non_recursive_let_cont_handler *)
  Definition t : Type := Flambda.non_recursive_let_cont_handler.
  Extract Inlined Constant t => "Flambda.Non_recursive_let_cont_handler.t".
  (* flambda.mli:470  val pattern_match : t -> f:(Continuation.t -> body:expr -> 'a) -> 'a *)
  Parameter pattern_match : forall {A : Type}, t -> (Continuation.t -> Flambda.expr -> M A) -> M A.
  Extract Inlined Constant pattern_match => "Flambda.Non_recursive_let_cont_handler.pattern_match".
  (* flambda.mli:485  val handler : t -> Continuation_handler.t *)
  Parameter handler : t -> M Flambda.Continuation_handler.t.
  Extract Inlined Constant handler => "Flambda.Non_recursive_let_cont_handler.handler".
End Non_recursive_let_cont_handler.
Module Recursive_let_cont_handlers.
  (* flambda.mli:492  type t = recursive_let_cont_handlers *)
  Definition t : Type := Flambda.recursive_let_cont_handlers.
  Extract Inlined Constant t => "Flambda.Recursive_let_cont_handlers.t".
  (* flambda.mli:498  val pattern_match : t -> f: (invariant_params:Bound_parameters.t -> body:expr -> Continuation_handlers.t -> 'a) -> 'a *)
  Parameter pattern_match : forall {A : Type}, t -> (Bound_parameters.t -> Flambda.expr -> Flambda.Continuation_handlers.t -> M A) -> M A.
  Extract Inlined Constant pattern_match => "Flambda.Recursive_let_cont_handlers.pattern_match".
End Recursive_let_cont_handlers.
Module Function_params_and_body.
  (* flambda.mli:548  type t = function_params_and_body *)
  Definition t : Type := Flambda.function_params_and_body.
  Extract Inlined Constant t => "Flambda.Function_params_and_body.t".
  (* flambda.mli:556  val create : return_continuation:Continuation.t -> exn_continuation:Continuation.t -> Bound_parameters.t -> body:expr -> free_names_of_body:Name_occurrences.t Or_unknown.t -> my_closure:Variable.t -> my_alloc_mode:Alloc_mode.For_applications.t -> my_depth:Variable.t -> t *)
  Parameter create : Continuation.t -> Continuation.t -> Bound_parameters.t -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> Variable_.t -> Alloc_mode.For_applications.t -> Variable_.t -> M t.
  Extract Inlined Constant create => "Flambda.Function_params_and_body.create".
  (* flambda.mli:570  val pattern_match : t -> f: (return_continuation:Continuation.t ( ** The continuation parameter of the function, i.e. to where we must jump once the result of the function has been computed. If the continuation takes more than one argument then the backend will compile the function so that it returns multiple values. * ) -> exn_continuation:Continuation.t ( ** To where we must jump if applicati... *)
  Parameter pattern_match : forall {A : Type}, t -> (Continuation.t -> Continuation.t -> Bound_parameters.t -> Flambda.expr -> Variable_.t -> Or_unknown.t bool -> Alloc_mode.For_applications.t -> Variable_.t -> Or_unknown.t Name_occurrences.t -> M A) -> M A.
  Extract Inlined Constant pattern_match => "Flambda.Function_params_and_body.pattern_match".
  (* flambda.mli:634  val is_my_closure_used : t -> bool *)
  Parameter is_my_closure_used : t -> M bool.
  Extract Inlined Constant is_my_closure_used => "Flambda.Function_params_and_body.is_my_closure_used".
End Function_params_and_body.
Module Static_const_or_code.
  (* flambda.mli:638  type t = static_const_or_code *)
  Definition t : Type := Flambda.static_const_or_code.
  Extract Inlined Constant t => "Flambda.Static_const_or_code.t".
  (* flambda.mli:646  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda.Static_const_or_code.print".
  (* flambda.mli:650  val is_block : t -> bool *)
  Parameter is_block : t -> M bool.
  Extract Inlined Constant is_block => "Flambda.Static_const_or_code.is_block".
  (* flambda.mli:652  val is_set_of_closures : t -> bool *)
  Parameter is_set_of_closures : t -> M bool.
  Extract Inlined Constant is_set_of_closures => "Flambda.Static_const_or_code.is_set_of_closures".
  (* flambda.mli:654  val is_code : t -> bool *)
  Parameter is_code : t -> M bool.
  Extract Inlined Constant is_code => "Flambda.Static_const_or_code.is_code".
  (* flambda.mli:656  val create_code : Function_params_and_body.t Code0.t -> t *)
  Parameter create_code : Code0.t Flambda.Function_params_and_body.t -> M t.
  Extract Inlined Constant create_code => "Flambda.Static_const_or_code.create_code".
  (* flambda.mli:658  val deleted_code : t *)
  Parameter deleted_code : t.
  Extract Inlined Constant deleted_code => "Flambda.Static_const_or_code.deleted_code".
  (* flambda.mli:660  val create_static_const : Static_const.t -> t *)
  Parameter create_static_const : decl.Static_const.t -> M t.
  Extract Inlined Constant create_static_const => "Flambda.Static_const_or_code.create_static_const".
  (* flambda.mli:662  val to_code : t -> Function_params_and_body.t Code0.t option *)
  Parameter to_code : t -> M (option (Code0.t Flambda.Function_params_and_body.t)).
  Extract Inlined Constant to_code => "Flambda.Static_const_or_code.to_code".
End Static_const_or_code.
Module Static_const_group.
  (* flambda.mli:666  type t = static_const_group *)
  Definition t : Type := Flambda.static_const_group.
  Extract Inlined Constant t => "Flambda.Static_const_group.t".
  (* flambda.mli:674  val create : Static_const_or_code.t list -> t *)
  Parameter create : list Flambda.Static_const_or_code.t -> M t.
  Extract Inlined Constant create => "Flambda.Static_const_group.create".
End Static_const_group.
(* module Apply = Apply_expr: declared again here under this name. *)
Module Apply.
  (* apply_expr.mli:20  type t *)
  Definition t : Type := Apply_expr.t.
  Extract Inlined Constant t => "Flambda.Apply.t".
  (* apply_expr.mli:24  include Expr_std.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda.Apply.print".
  (* apply_expr.mli:24  include Expr_std.S with type t := t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Flambda.Apply.free_names".
  (* apply_expr.mli:26  val free_names_without_exn_continuation : t -> Name_occurrences.t *)
  Parameter free_names_without_exn_continuation : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names_without_exn_continuation => "Flambda.Apply.free_names_without_exn_continuation".
  (* module Result_continuation = Apply_expr.Result_continuation: declared again here under this name. *)
  Module Result_continuation.
    (* apply_expr.mli:31  type t = | Return of Continuation.t | Never_returns *)
    Definition t : Type := Apply_expr.Result_continuation.t.
    Extract Inlined Constant t => "Flambda.Apply.Result_continuation.t".
  End Result_continuation.
  (* module Position = Apply_expr.Position: declared again here under this name. *)
  Module Position.
    (* apply_expr.mli:41  type t = | Normal | Nontail *)
    Definition t : Type := Apply_expr.Position.t.
    Extract Inlined Constant t => "Flambda.Apply.Position.t".
  End Position.
  (* apply_expr.mli:49  val create : callee:Simple.t option -> continuation:Result_continuation.t -> Exn_continuation.t -> args:Simple.t list -> args_arity:[`Complex] Flambda_arity.t -> return_arity:[`Complex] Flambda_arity.t -> call_kind:Call_kind.t -> return_mode:Alloc_mode.For_applications.t -> Debuginfo.t -> inlined:Inlined_attribute.t -> inlining_state:Inlining_state.t -> probe:Probe.t -> position:Position.t -> r... *)
  Parameter create : option Simple.t -> Flambda.Apply.Result_continuation.t -> Exn_continuation.t -> list Simple.t -> Flambda_arity.t -> Flambda_arity.t -> Call_kind.t -> Alloc_mode.For_applications.t -> Debuginfo.t -> Inlined_attribute.t -> Inlining_state.t -> Probe.t -> Flambda.Apply.Position.t -> Inlining_history.Relative.t -> M t.
  Extract Inlined Constant create => "Flambda.Apply.create".
  (* apply_expr.mli:74  val callee : t -> Simple.t option *)
  Parameter callee : t -> M (option Simple.t).
  Extract Inlined Constant callee => "Flambda.Apply.callee".
  (* apply_expr.mli:77  val args : t -> Simple.t list *)
  Parameter args : t -> M (list Simple.t).
  Extract Inlined Constant args => "Flambda.Apply.args".
  (* apply_expr.mli:80  val args_arity : t -> [`Complex] Flambda_arity.t *)
  Parameter args_arity : t -> M Flambda_arity.t.
  Extract Inlined Constant args_arity => "Flambda.Apply.args_arity".
  (* apply_expr.mli:83  val return_arity : t -> [`Complex] Flambda_arity.t *)
  Parameter return_arity : t -> M Flambda_arity.t.
  Extract Inlined Constant return_arity => "Flambda.Apply.return_arity".
  (* apply_expr.mli:87  val call_kind : t -> Call_kind.t *)
  Parameter call_kind : t -> M Call_kind.t.
  Extract Inlined Constant call_kind => "Flambda.Apply.call_kind".
  (* apply_expr.mli:89  val return_mode : t -> Alloc_mode.For_applications.t *)
  Parameter return_mode : t -> M Alloc_mode.For_applications.t.
  Extract Inlined Constant return_mode => "Flambda.Apply.return_mode".
  (* apply_expr.mli:92  val continuation : t -> Result_continuation.t *)
  Parameter continuation : t -> M Flambda.Apply.Result_continuation.t.
  Extract Inlined Constant continuation => "Flambda.Apply.continuation".
  (* apply_expr.mli:95  val exn_continuation : t -> Exn_continuation.t *)
  Parameter exn_continuation : t -> M Exn_continuation.t.
  Extract Inlined Constant exn_continuation => "Flambda.Apply.exn_continuation".
  (* apply_expr.mli:98  val dbg : t -> Debuginfo.t *)
  Parameter dbg : t -> M Debuginfo.t.
  Extract Inlined Constant dbg => "Flambda.Apply.dbg".
  (* apply_expr.mli:102  val inlined : t -> Inlined_attribute.t *)
  Parameter inlined : t -> M Inlined_attribute.t.
  Extract Inlined Constant inlined => "Flambda.Apply.inlined".
  (* apply_expr.mli:105  val position : t -> Position.t *)
  Parameter position : t -> M Flambda.Apply.Position.t.
  Extract Inlined Constant position => "Flambda.Apply.position".
  (* apply_expr.mli:107  val erase_callee : t -> t *)
  Parameter erase_callee : t -> M t.
  Extract Inlined Constant erase_callee => "Flambda.Apply.erase_callee".
  (* apply_expr.mli:110  val with_continuation : t -> Result_continuation.t -> t *)
  Parameter with_continuation : t -> Flambda.Apply.Result_continuation.t -> M t.
  Extract Inlined Constant with_continuation => "Flambda.Apply.with_continuation".
  (* apply_expr.mli:114  val with_exn_continuation : t -> Exn_continuation.t -> t *)
  Parameter with_exn_continuation : t -> Exn_continuation.t -> M t.
  Extract Inlined Constant with_exn_continuation => "Flambda.Apply.with_exn_continuation".
  (* apply_expr.mli:117  val with_args : t -> Simple.t list -> args_arity:[`Complex] Flambda_arity.t -> t *)
  Parameter with_args : t -> list Simple.t -> Flambda_arity.t -> M t.
  Extract Inlined Constant with_args => "Flambda.Apply.with_args".
  (* apply_expr.mli:120  val with_call_kind : t -> Call_kind.t -> t *)
  Parameter with_call_kind : t -> Call_kind.t -> M t.
  Extract Inlined Constant with_call_kind => "Flambda.Apply.with_call_kind".
  (* apply_expr.mli:122  val inlining_state : t -> Inlining_state.t *)
  Parameter inlining_state : t -> M Inlining_state.t.
  Extract Inlined Constant inlining_state => "Flambda.Apply.inlining_state".
  (* apply_expr.mli:126  val probe : t -> Probe.t *)
  Parameter probe : t -> M Probe.t.
  Extract Inlined Constant probe => "Flambda.Apply.probe".
  (* apply_expr.mli:128  val relative_history : t -> Inlining_history.Relative.t *)
  Parameter relative_history : t -> M Inlining_history.Relative.t.
  Extract Inlined Constant relative_history => "Flambda.Apply.relative_history".
  (* apply_expr.mli:134  val with_inlined_attribute : t -> Inlined_attribute.t -> t *)
  Parameter with_inlined_attribute : t -> Inlined_attribute.t -> M t.
  Extract Inlined Constant with_inlined_attribute => "Flambda.Apply.with_inlined_attribute".
End Apply.
(* module Apply_cont = Apply_cont_expr: declared again here under this name. *)
Module Apply_cont.
  (* apply_cont_expr.mli:20  type t *)
  Definition t : Type := Apply_cont_expr.t.
  Extract Inlined Constant t => "Flambda.Apply_cont.t".
  (* apply_cont_expr.mli:22  include Expr_std.S with type t := t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Flambda.Apply_cont.free_names".
  (* apply_cont_expr.mli:26  val create : ?trap_action:Trap_action.t -> Continuation.t -> args:Simple.t list -> dbg:Debuginfo.t -> t *)
  Parameter create : option Trap_action.t -> Continuation.t -> list Simple.t -> Debuginfo.t -> M t.
  Extract Inlined Constant create => "(fun x__1 x__2 x__3 x__4 -> Flambda.Apply_cont.create ?trap_action:x__1 x__2 x__3 x__4)".
  (* apply_cont_expr.mli:33  val goto : Continuation.t -> t *)
  Parameter goto : Continuation.t -> M t.
  Extract Inlined Constant goto => "Flambda.Apply_cont.goto".
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
  (* apply_cont_expr.mli:51  val is_raise : t -> bool *)
  Parameter is_raise : t -> M bool.
  Extract Inlined Constant is_raise => "Flambda.Apply_cont.is_raise".
  (* apply_cont_expr.mli:53  val is_goto : t -> bool *)
  Parameter is_goto : t -> M bool.
  Extract Inlined Constant is_goto => "Flambda.Apply_cont.is_goto".
  (* apply_cont_expr.mli:55  val clear_trap_action : t -> t *)
  Parameter clear_trap_action : t -> M t.
  Extract Inlined Constant clear_trap_action => "Flambda.Apply_cont.clear_trap_action".
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
(* module Function_declarations = Function_declarations: declared again here under this name. *)
Module Function_declarations.
  (* function_declarations.mli:19  type t *)
  Definition t : Type := decl.Function_declarations.t.
  Extract Inlined Constant t => "Flambda.Function_declarations.t".
  (* function_declarations.mli:25  type code_id_in_function_declaration = | Deleted of { function_slot_size : int; dbg : Debuginfo.t } | Code_id of { code_id : Code_id.t; only_full_applications : bool } *)
  Definition code_id_in_function_declaration : Type := decl.Function_declarations.code_id_in_function_declaration.
  Extract Inlined Constant code_id_in_function_declaration => "Flambda.Function_declarations.code_id_in_function_declaration".
  (* function_declarations.mli:40  val create : code_id_in_function_declaration Function_slot.Lmap.t -> t *)
  Parameter create : Function_slot.Lmap.t code_id_in_function_declaration -> M t.
  Extract Inlined Constant create => "Flambda.Function_declarations.create".
  (* function_declarations.mli:44  val funs : t -> code_id_in_function_declaration Function_slot.Map.t *)
  Parameter funs : t -> M (Function_slot.Map.t code_id_in_function_declaration).
  Extract Inlined Constant funs => "Flambda.Function_declarations.funs".
  (* function_declarations.mli:48  val funs_in_order : t -> code_id_in_function_declaration Function_slot.Lmap.t *)
  Parameter funs_in_order : t -> M (Function_slot.Lmap.t code_id_in_function_declaration).
  Extract Inlined Constant funs_in_order => "Flambda.Function_declarations.funs_in_order".
End Function_declarations.
(* module Let = Flambda.Let_expr: declared again here under this name. *)
Module Let.
  (* flambda.mli:233  type t = let_expr *)
  Definition t : Type := Flambda.Let_expr.t.
  Extract Inlined Constant t => "Flambda.Let.t".
  (* flambda.mli:237  val create : Bound_pattern.t -> named -> body:expr -> free_names_of_body:Name_occurrences.t Or_unknown.t -> t *)
  Parameter create : Bound_pattern.t -> Flambda.named -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> M t.
  Extract Inlined Constant create => "Flambda.Let.create".
  (* flambda.mli:245  val defining_expr : t -> named *)
  Parameter defining_expr : t -> M Flambda.named.
  Extract Inlined Constant defining_expr => "Flambda.Let.defining_expr".
  (* flambda.mli:249  val pattern_match : t -> f:(Bound_pattern.t -> body:expr -> 'a) -> 'a *)
  Parameter pattern_match : forall {A : Type}, t -> (Bound_pattern.t -> Flambda.expr -> M A) -> M A.
  Extract Inlined Constant pattern_match => "Flambda.Let.pattern_match".
End Let.
(* module Let_cont = Flambda.Let_cont_expr: declared again here under this name. *)
Module Let_cont.
  (* flambda.mli:422  type t = let_cont_expr *)
  Definition t : Type := Flambda.Let_cont_expr.t.
  Extract Inlined Constant t => "Flambda.Let_cont.t".
  (* flambda.mli:429  val create_non_recursive : Continuation.t -> Continuation_handler.t -> body:expr -> free_names_of_body:Name_occurrences.t Or_unknown.t -> expr *)
  Parameter create_non_recursive : Continuation.t -> Flambda.Continuation_handler.t -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> M Flambda.expr.
  Extract Inlined Constant create_non_recursive => "Flambda.Let_cont.create_non_recursive".
  (* flambda.mli:446  val create_non_liftable : Continuation.t -> Continuation_handler.t -> body:expr -> free_names_of_body:Name_occurrences.t Or_unknown.t -> expr *)
  Parameter create_non_liftable : Continuation.t -> Flambda.Continuation_handler.t -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> M Flambda.expr.
  Extract Inlined Constant create_non_liftable => "Flambda.Let_cont.create_non_liftable".
End Let_cont.
(* module Set_of_closures = Set_of_closures: declared again here under this name. *)
Module Set_of_closures.
  (* set_of_closures.mli:17  type t *)
  Definition t : Type := decl.Set_of_closures.t.
  Extract Inlined Constant t => "Flambda.Set_of_closures.t".
  (* set_of_closures.mli:19  include Expr_std.S with type t := t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Flambda.Set_of_closures.free_names".
  (* set_of_closures.mli:29  val create : value_slots:Simple.t Value_slot.Map.t -> dbg:Debuginfo.t -> Function_declarations.t -> t *)
  Parameter create : Value_slot.Map.t Simple.t -> Debuginfo.t -> decl.Function_declarations.t -> M t.
  Extract Inlined Constant create => "Flambda.Set_of_closures.create".
  (* set_of_closures.mli:36  val function_decls : t -> Function_declarations.t *)
  Parameter function_decls : t -> M decl.Function_declarations.t.
  Extract Inlined Constant function_decls => "Flambda.Set_of_closures.function_decls".
  (* set_of_closures.mli:39  val value_slots : t -> Simple.t Value_slot.Map.t *)
  Parameter value_slots : t -> M (Value_slot.Map.t Simple.t).
  Extract Inlined Constant value_slots => "Flambda.Set_of_closures.value_slots".
  (* set_of_closures.mli:42  val debuginfo : t -> Debuginfo.t *)
  Parameter debuginfo : t -> M Debuginfo.t.
  Extract Inlined Constant debuginfo => "Flambda.Set_of_closures.debuginfo".
End Set_of_closures.
(* module Switch = Switch_expr: declared again here under this name. *)
Module Switch.
  (* switch_expr.mli:26  type t *)
  Definition t : Type := Switch_expr.t.
  Extract Inlined Constant t => "Flambda.Switch.t".
  (* switch_expr.mli:48  val scrutinee : t -> Simple.t *)
  Parameter scrutinee : t -> M Simple.t.
  Extract Inlined Constant scrutinee => "Flambda.Switch.scrutinee".
  (* switch_expr.mli:51  val condition_dbg : t -> Debuginfo.t *)
  Parameter condition_dbg : t -> M Debuginfo.t.
  Extract Inlined Constant condition_dbg => "Flambda.Switch.condition_dbg".
  (* switch_expr.mli:58  val arms : t -> Switch_arm.t Target_ocaml_int.Map.t *)
  Parameter arms : t -> M (Target_ocaml_int.Map.t Switch_arm.t).
  Extract Inlined Constant arms => "Flambda.Switch.arms".
End Switch.
Module Import_.
  (* module Apply = Apply_expr: declared again here under this name. *)
  Module Apply.
    (* apply_expr.mli:20  type t *)
    Definition t : Type := Apply_expr.t.
    Extract Inlined Constant t => "Flambda.Import.Apply.t".
    (* apply_expr.mli:24  include Expr_std.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Flambda.Import.Apply.print".
    (* apply_expr.mli:24  include Expr_std.S with type t := t *)
    Parameter free_names : t -> M Name_occurrences.t.
    Extract Inlined Constant free_names => "Flambda.Import.Apply.free_names".
    (* module Result_continuation = Apply_expr.Result_continuation: declared again here under this name. *)
    Module Result_continuation.
      (* apply_expr.mli:31  type t = | Return of Continuation.t | Never_returns *)
      Definition t : Type := Apply_expr.Result_continuation.t.
      Extract Inlined Constant t => "Flambda.Import.Apply.Result_continuation.t".
    End Result_continuation.
    (* apply_expr.mli:77  val args : t -> Simple.t list *)
    Parameter args : t -> M (list Simple.t).
    Extract Inlined Constant args => "Flambda.Import.Apply.args".
    (* apply_expr.mli:92  val continuation : t -> Result_continuation.t *)
    Parameter continuation : t -> M Flambda.Import_.Apply.Result_continuation.t.
    Extract Inlined Constant continuation => "Flambda.Import.Apply.continuation".
    (* apply_expr.mli:95  val exn_continuation : t -> Exn_continuation.t *)
    Parameter exn_continuation : t -> M Exn_continuation.t.
    Extract Inlined Constant exn_continuation => "Flambda.Import.Apply.exn_continuation".
    (* apply_expr.mli:98  val dbg : t -> Debuginfo.t *)
    Parameter dbg : t -> M Debuginfo.t.
    Extract Inlined Constant dbg => "Flambda.Import.Apply.dbg".
    (* apply_expr.mli:102  val inlined : t -> Inlined_attribute.t *)
    Parameter inlined : t -> M Inlined_attribute.t.
    Extract Inlined Constant inlined => "Flambda.Import.Apply.inlined".
    (* apply_expr.mli:112  val with_continuations : t -> Result_continuation.t -> Exn_continuation.t -> t *)
    Parameter with_continuations : t -> Flambda.Import_.Apply.Result_continuation.t -> Exn_continuation.t -> M t.
    Extract Inlined Constant with_continuations => "Flambda.Import.Apply.with_continuations".
    (* apply_expr.mli:122  val inlining_state : t -> Inlining_state.t *)
    Parameter inlining_state : t -> M Inlining_state.t.
    Extract Inlined Constant inlining_state => "Flambda.Import.Apply.inlining_state".
    (* apply_expr.mli:124  val inlining_arguments : t -> Inlining_arguments.t *)
    Parameter inlining_arguments : t -> M Inlining_arguments.t.
    Extract Inlined Constant inlining_arguments => "Flambda.Import.Apply.inlining_arguments".
    (* apply_expr.mli:128  val relative_history : t -> Inlining_history.Relative.t *)
    Parameter relative_history : t -> M Inlining_history.Relative.t.
    Extract Inlined Constant relative_history => "Flambda.Import.Apply.relative_history".
  End Apply.
  (* module Apply_cont = Apply_cont_expr: declared again here under this name. *)
  Module Apply_cont.
    (* apply_cont_expr.mli:20  type t *)
    Definition t : Type := Apply_cont_expr.t.
    Extract Inlined Constant t => "Flambda.Import.Apply_cont.t".
    (* apply_cont_expr.mli:22  include Expr_std.S with type t := t *)
    Parameter free_names : t -> M Name_occurrences.t.
    Extract Inlined Constant free_names => "Flambda.Import.Apply_cont.free_names".
    (* apply_cont_expr.mli:26  val create : ?trap_action:Trap_action.t -> Continuation.t -> args:Simple.t list -> dbg:Debuginfo.t -> t *)
    Parameter create : option Trap_action.t -> Continuation.t -> list Simple.t -> Debuginfo.t -> M t.
    Extract Inlined Constant create => "(fun x__1 x__2 x__3 x__4 -> Flambda.Import.Apply_cont.create ?trap_action:x__1 x__2 x__3 x__4)".
    (* apply_cont_expr.mli:35  val continuation : t -> Continuation.t *)
    Parameter continuation : t -> M Continuation.t.
    Extract Inlined Constant continuation => "Flambda.Import.Apply_cont.continuation".
    (* apply_cont_expr.mli:37  val args : t -> Simple.t list *)
    Parameter args : t -> M (list Simple.t).
    Extract Inlined Constant args => "Flambda.Import.Apply_cont.args".
    (* apply_cont_expr.mli:39  val trap_action : t -> Trap_action.t option *)
    Parameter trap_action : t -> M (option Trap_action.t).
    Extract Inlined Constant trap_action => "Flambda.Import.Apply_cont.trap_action".
    (* apply_cont_expr.mli:43  val with_continuation : t -> Continuation.t -> t *)
    Parameter with_continuation : t -> Continuation.t -> M t.
    Extract Inlined Constant with_continuation => "Flambda.Import.Apply_cont.with_continuation".
    (* apply_cont_expr.mli:45  val with_continuation_and_args : t -> Continuation.t -> args:Simple.t list -> t *)
    Parameter with_continuation_and_args : t -> Continuation.t -> list Simple.t -> M t.
    Extract Inlined Constant with_continuation_and_args => "Flambda.Import.Apply_cont.with_continuation_and_args".
    (* apply_cont_expr.mli:47  val update_args : t -> args:Simple.t list -> t *)
    Parameter update_args : t -> list Simple.t -> M t.
    Extract Inlined Constant update_args => "Flambda.Import.Apply_cont.update_args".
  End Apply_cont.
  (* module Continuation_handler = Flambda.Continuation_handler: declared again here under this name. *)
  Module Continuation_handler.
    (* flambda.mli:307  type t *)
    Definition t : Type := Flambda.Continuation_handler.t.
    Extract Inlined Constant t => "Flambda.Import.Continuation_handler.t".
    (* flambda.mli:309  val print : cont:Continuation.t -> recursive:Recursive.t -> Format.formatter -> t -> unit *)
    Parameter print : Continuation.t -> Recursive.t -> Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Flambda.Import.Continuation_handler.print".
    (* flambda.mli:319  val create : Bound_parameters.t -> handler:expr -> free_names_of_handler:Name_occurrences.t Or_unknown.t -> is_exn_handler:bool -> is_cold:bool -> t *)
    Parameter create : Bound_parameters.t -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> bool -> bool -> M t.
    Extract Inlined Constant create => "Flambda.Import.Continuation_handler.create".
  End Continuation_handler.
  (* module Expr = Flambda.Expr: declared again here under this name. *)
  Module Expr.
    (* flambda.mli:139  type t = expr *)
    Definition t : Type := Flambda.Expr.t.
    Extract Inlined Constant t => "Flambda.Import.Expr.t".
    (* flambda.mli:143  include Expr_std.S_no_free_names with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Flambda.Import.Expr.print".
    (* flambda.mli:143  include Expr_std.S_no_free_names with type t := t *)
    Parameter apply_renaming : t -> Renaming.t -> M t.
    Extract Inlined Constant apply_renaming => "Flambda.Import.Expr.apply_renaming".
    (* flambda.mli:148  val descr : t -> expr_descr *)
    Parameter descr : t -> M Flambda.expr_descr.
    Extract Inlined Constant descr => "Flambda.Import.Expr.descr".
    (* flambda.mli:150  val create_let : let_expr -> t *)
    Parameter create_let : Flambda.let_expr -> M t.
    Extract Inlined Constant create_let => "Flambda.Import.Expr.create_let".
    (* flambda.mli:153  val create_apply : Apply_expr.t -> t *)
    Parameter create_apply : Apply_expr.t -> M t.
    Extract Inlined Constant create_apply => "Flambda.Import.Expr.create_apply".
    (* flambda.mli:156  val create_apply_cont : Apply_cont_expr.t -> t *)
    Parameter create_apply_cont : Apply_cont_expr.t -> M t.
    Extract Inlined Constant create_apply_cont => "Flambda.Import.Expr.create_apply_cont".
    (* flambda.mli:158  val create_switch : Switch_expr.t -> t *)
    Parameter create_switch : Switch_expr.t -> M t.
    Extract Inlined Constant create_switch => "Flambda.Import.Expr.create_switch".
    (* flambda.mli:160  val create_invalid : Invalid.t -> t *)
    Parameter create_invalid : Flambda.Invalid.t -> M t.
    Extract Inlined Constant create_invalid => "Flambda.Import.Expr.create_invalid".
  End Expr.
  (* module Function_params_and_body = Flambda.Function_params_and_body: declared again here under this name. *)
  Module Function_params_and_body.
    (* flambda.mli:548  type t = function_params_and_body *)
    Definition t : Type := Flambda.Function_params_and_body.t.
    Extract Inlined Constant t => "Flambda.Import.Function_params_and_body.t".
    (* flambda.mli:556  val create : return_continuation:Continuation.t -> exn_continuation:Continuation.t -> Bound_parameters.t -> body:expr -> free_names_of_body:Name_occurrences.t Or_unknown.t -> my_closure:Variable.t -> my_alloc_mode:Alloc_mode.For_applications.t -> my_depth:Variable.t -> t *)
    Parameter create : Continuation.t -> Continuation.t -> Bound_parameters.t -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> Variable_.t -> Alloc_mode.For_applications.t -> Variable_.t -> M t.
    Extract Inlined Constant create => "Flambda.Import.Function_params_and_body.create".
    (* flambda.mli:634  val is_my_closure_used : t -> bool *)
    Parameter is_my_closure_used : t -> M bool.
    Extract Inlined Constant is_my_closure_used => "Flambda.Import.Function_params_and_body.is_my_closure_used".
  End Function_params_and_body.
  (* module Let = Flambda.Let_expr: declared again here under this name. *)
  Module Let.
    (* flambda.mli:233  type t = let_expr *)
    Definition t : Type := Flambda.Let_expr.t.
    Extract Inlined Constant t => "Flambda.Import.Let.t".
    (* flambda.mli:237  val create : Bound_pattern.t -> named -> body:expr -> free_names_of_body:Name_occurrences.t Or_unknown.t -> t *)
    Parameter create : Bound_pattern.t -> Flambda.named -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> M t.
    Extract Inlined Constant create => "Flambda.Import.Let.create".
    (* flambda.mli:245  val defining_expr : t -> named *)
    Parameter defining_expr : t -> M Flambda.named.
    Extract Inlined Constant defining_expr => "Flambda.Import.Let.defining_expr".
    (* flambda.mli:249  val pattern_match : t -> f:(Bound_pattern.t -> body:expr -> 'a) -> 'a *)
    Parameter pattern_match : forall {A : Type}, t -> (Bound_pattern.t -> Flambda.expr -> M A) -> M A.
    Extract Inlined Constant pattern_match => "Flambda.Import.Let.pattern_match".
  End Let.
  (* module Let_cont = Flambda.Let_cont_expr: declared again here under this name. *)
  Module Let_cont.
    (* flambda.mli:429  val create_non_recursive : Continuation.t -> Continuation_handler.t -> body:expr -> free_names_of_body:Name_occurrences.t Or_unknown.t -> expr *)
    Parameter create_non_recursive : Continuation.t -> Flambda.Continuation_handler.t -> Flambda.expr -> Or_unknown.t Name_occurrences.t -> M Flambda.expr.
    Extract Inlined Constant create_non_recursive => "Flambda.Import.Let_cont.create_non_recursive".
    (* flambda.mli:436  val create_non_recursive' : cont:Continuation.t -> Continuation_handler.t -> body:expr -> num_free_occurrences_of_cont_in_body:Num_occurrences.t Or_unknown.t -> is_applied_with_traps:bool -> expr *)
    Parameter create_non_recursive' : Continuation.t -> Flambda.Continuation_handler.t -> Flambda.expr -> Or_unknown.t Num_occurrences.t -> bool -> M Flambda.expr.
    Extract Inlined Constant create_non_recursive' => "Flambda.Import.Let_cont.create_non_recursive'".
    (* flambda.mli:454  val create_recursive : invariant_params:Bound_parameters.t -> Continuation_handler.t Continuation.Lmap.t -> body:expr -> expr *)
    Parameter create_recursive : Bound_parameters.t -> Continuation.Lmap.t Flambda.Continuation_handler.t -> Flambda.expr -> M Flambda.expr.
    Extract Inlined Constant create_recursive => "Flambda.Import.Let_cont.create_recursive".
  End Let_cont.
  (* module Named = Flambda.Named: declared again here under this name. *)
  Module Named.
    (* flambda.mli:165  type t = named *)
    Definition t : Type := Flambda.Named.t.
    Extract Inlined Constant t => "Flambda.Import.Named.t".
    (* flambda.mli:167  include Expr_std.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Flambda.Import.Named.print".
    (* flambda.mli:167  include Expr_std.S with type t := t *)
    Parameter free_names : t -> M Name_occurrences.t.
    Extract Inlined Constant free_names => "Flambda.Import.Named.free_names".
    (* flambda.mli:172  val create_simple : Simple.t -> t *)
    Parameter create_simple : Simple.t -> M t.
    Extract Inlined Constant create_simple => "Flambda.Import.Named.create_simple".
    (* flambda.mli:179  val create_prim : Flambda_primitive.t -> Debuginfo.t -> t *)
    Parameter create_prim : Flambda_primitive.t -> Debuginfo.t -> M t.
    Extract Inlined Constant create_prim => "Flambda.Import.Named.create_prim".
    (* flambda.mli:182  val create_set_of_closures : alloc_mode:Alloc_mode.For_allocations.t -> Set_of_closures.t -> t *)
    Parameter create_set_of_closures : Alloc_mode.For_allocations.t -> decl.Set_of_closures.t -> M t.
    Extract Inlined Constant create_set_of_closures => "Flambda.Import.Named.create_set_of_closures".
    (* flambda.mli:191  val create_rec_info : Rec_info_expr.t -> t *)
    Parameter create_rec_info : Rec_info_expr.t -> M t.
    Extract Inlined Constant create_rec_info => "Flambda.Import.Named.create_rec_info".
    (* flambda.mli:216  val fold_code_and_sets_of_closures : t -> init:'a -> f_code:('a -> function_params_and_body Code0.t -> 'a) -> f_set:('a -> Set_of_closures.t -> 'a) -> 'a *)
    Parameter fold_code_and_sets_of_closures : forall {A : Type}, t -> A -> (A -> Code0.t Flambda.function_params_and_body -> M A) -> (A -> decl.Set_of_closures.t -> M A) -> M A.
    Extract Inlined Constant fold_code_and_sets_of_closures => "Flambda.Import.Named.fold_code_and_sets_of_closures".
  End Named.
  (* module Set_of_closures = Set_of_closures: declared again here under this name. *)
  Module Set_of_closures.
    (* set_of_closures.mli:17  type t *)
    Definition t : Type := decl.Set_of_closures.t.
    Extract Inlined Constant t => "Flambda.Import.Set_of_closures.t".
    (* set_of_closures.mli:29  val create : value_slots:Simple.t Value_slot.Map.t -> dbg:Debuginfo.t -> Function_declarations.t -> t *)
    Parameter create : Value_slot.Map.t Simple.t -> Debuginfo.t -> decl.Function_declarations.t -> M t.
    Extract Inlined Constant create => "Flambda.Import.Set_of_closures.create".
    (* set_of_closures.mli:36  val function_decls : t -> Function_declarations.t *)
    Parameter function_decls : t -> M decl.Function_declarations.t.
    Extract Inlined Constant function_decls => "Flambda.Import.Set_of_closures.function_decls".
    (* set_of_closures.mli:39  val value_slots : t -> Simple.t Value_slot.Map.t *)
    Parameter value_slots : t -> M (Value_slot.Map.t Simple.t).
    Extract Inlined Constant value_slots => "Flambda.Import.Set_of_closures.value_slots".
    (* set_of_closures.mli:42  val debuginfo : t -> Debuginfo.t *)
    Parameter debuginfo : t -> M Debuginfo.t.
    Extract Inlined Constant debuginfo => "Flambda.Import.Set_of_closures.debuginfo".
  End Set_of_closures.
  (* module Static_const = Static_const: declared again here under this name. *)
  Module Static_const.
    (* static_const.mli:25  type t = private | Set_of_closures of Set_of_closures.t | Block of Tag.Scannable.t * Mutability.t * Flambda_kind.Scannable_block_shape.t * Simple.With_debuginfo.t list | Boxed_float32 of Numeric_types.Float32_by_bit_pattern.t Or_variable.t | Boxed_float of Numeric_types.Float_by_bit_pattern.t Or_variable.t | Boxed_int32 of Int32.t Or_variable.t | Boxed_int64 of Int64.t Or_variable.t | Boxed_nat... *)
    Definition t : Type := decl.Static_const.t.
    Extract Inlined Constant t => "Flambda.Import.Static_const.t".
    (* module Map = Static_const.Map: declared again here under this name. *)
    Module Map.
      (* static_const.mli:71  include Container_types.S with type t := t *)
      Definition t (A : Type) : Type := decl.Static_const.Map.t A.
      Extract Constant t "'a1" => "('a1) Flambda.Import.Static_const.Map.t".
    End Map.
  End Static_const.
  (* module Static_const_group = Flambda.Static_const_group: declared again here under this name. *)
  Module Static_const_group.
    (* flambda.mli:666  type t = static_const_group *)
    Definition t : Type := Flambda.Static_const_group.t.
    Extract Inlined Constant t => "Flambda.Import.Static_const_group.t".
    (* flambda.mli:674  val create : Static_const_or_code.t list -> t *)
    Parameter create : list Flambda.Static_const_or_code.t -> M t.
    Extract Inlined Constant create => "Flambda.Import.Static_const_group.create".
    (* flambda.mli:676  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Flambda.Import.Static_const_group.print".
    (* flambda.mli:678  val to_list : t -> Static_const_or_code.t list *)
    Parameter to_list : t -> M (list Flambda.Static_const_or_code.t).
    Extract Inlined Constant to_list => "Flambda.Import.Static_const_group.to_list".
    (* flambda.mli:684  val match_against_bound_static : t -> Bound_static.t -> init:'a -> code:('a -> Code_id.t -> Function_params_and_body.t Code0.t -> 'a) -> deleted_code:('a -> Code_id.t -> 'a) -> set_of_closures: ('a -> closure_symbols:Symbol.t Function_slot.Lmap.t -> Set_of_closures.t -> 'a) -> block_like:('a -> Symbol.t -> Static_const.t -> 'a) -> 'a *)
    Parameter match_against_bound_static : forall {A : Type}, t -> Bound_static.t -> A -> (A -> Code_id.t -> Code0.t Flambda.Function_params_and_body.t -> M A) -> (A -> Code_id.t -> M A) -> (A -> Function_slot.Lmap.t Symbol.t -> decl.Set_of_closures.t -> M A) -> (A -> Symbol.t -> decl.Static_const.t -> M A) -> M A.
    Extract Inlined Constant match_against_bound_static => "Flambda.Import.Static_const_group.match_against_bound_static".
    (* flambda.mli:699  val pieces_of_code : t -> Function_params_and_body.t Code0.t Code_id.Map.t *)
    Parameter pieces_of_code : t -> M (Code_id.Map.t (Code0.t Flambda.Function_params_and_body.t)).
    Extract Inlined Constant pieces_of_code => "Flambda.Import.Static_const_group.pieces_of_code".
  End Static_const_group.
  (* module Static_const_or_code = Flambda.Static_const_or_code: declared again here under this name. *)
  Module Static_const_or_code.
    (* flambda.mli:638  type t = static_const_or_code *)
    Definition t : Type := Flambda.Static_const_or_code.t.
    Extract Inlined Constant t => "Flambda.Import.Static_const_or_code.t".
    (* flambda.mli:656  val create_code : Function_params_and_body.t Code0.t -> t *)
    Parameter create_code : Code0.t Flambda.Function_params_and_body.t -> M t.
    Extract Inlined Constant create_code => "Flambda.Import.Static_const_or_code.create_code".
    (* flambda.mli:662  val to_code : t -> Function_params_and_body.t Code0.t option *)
    Parameter to_code : t -> M (option (Code0.t Flambda.Function_params_and_body.t)).
    Extract Inlined Constant to_code => "Flambda.Import.Static_const_or_code.to_code".
  End Static_const_or_code.
  (* module Switch = Switch_expr: declared again here under this name. *)
  Module Switch.
    (* switch_expr.mli:26  type t *)
    Definition t : Type := Switch_expr.t.
    Extract Inlined Constant t => "Flambda.Import.Switch.t".
    (* switch_expr.mli:28  include Expr_std.S with type t := t *)
    Parameter free_names : t -> M Name_occurrences.t.
    Extract Inlined Constant free_names => "Flambda.Import.Switch.free_names".
    (* switch_expr.mli:32  val create : condition_dbg:Debuginfo.t -> scrutinee:Simple.t -> arms:Switch_arm.t Target_ocaml_int.Map.t -> t *)
    Parameter create : Debuginfo.t -> Simple.t -> Target_ocaml_int.Map.t Switch_arm.t -> M t.
    Extract Inlined Constant create => "Flambda.Import.Switch.create".
  End Switch.
End Import_.
