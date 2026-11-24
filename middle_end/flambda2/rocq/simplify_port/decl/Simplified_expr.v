(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplified_expr], after its interface
   middle_end/flambda2/simplify/simplified_expr.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Apply_cont_rewrite_id Branch_annotations Closure_info Common_subexpression_elimination Debuginfo Flambda Flambda2_types Flambda_arity Lifted_constant_state Named_rewrite_id Removed_operations Simple Simplified_named Symbol Target_ocaml_int.

(* simplified_expr.mli:44  and simplified_defining_expr = private ( * CR-soon bclement: it seems like some fields don't actually have their place here. [removed_operations] could be accumulated in the basic block directly, and [at_unit_toplevel] and [closure_info] could be stored there as well (something went very wrong if these change in the middle of a basic block). * ) { bindings_to_place : Simplified_named.binding_to... *)
Parameter simplified_defining_expr : Type.
Extract Inlined Constant simplified_defining_expr => "Simplified_expr.simplified_defining_expr".
(* simplified_expr.mli:59  and simplified_handler = { params : Bound_parameters.t; simplified_handler : t; is_exn_handler : bool; is_cold : bool; extra_params_and_args : Continuation_extra_params_and_args.t; ( * Note: EPA.extra_params invariant_extra_params_and_args should always be equal to invariant_extra_params in stage4 * ) invariant_extra_params_and_args : Continuation_extra_params_and_args.t; rewrite_ids : Apply_co... *)
Parameter simplified_handler_ : Type.
Extract Inlined Constant simplified_handler_ => "Simplified_expr.simplified_handler".
(* simplified_expr.mli:71  and simplified_handlers_group = | Recursive of { simplified_continuation_handlers : simplified_handler Continuation.Map.t } | Non_recursive of { cont : Continuation.t; handler : simplified_handler; is_single_inlinable_use : bool } *)
Parameter simplified_handlers_group : Type.
Extract Inlined Constant simplified_handlers_group => "Simplified_expr.simplified_handlers_group".
(* simplified_expr.mli:81  and simplified_let_cont_handlers = { at_unit_toplevel : bool; handlers_from_the_outside_to_the_inside : simplified_handlers_group list; original_invariant_params : Bound_parameters.t; invariant_extra_params : Bound_parameters.t } *)
Parameter simplified_let_cont_handlers : Type.
Extract Inlined Constant simplified_let_cont_handlers => "Simplified_expr.simplified_let_cont_handlers".
(* simplified_expr.mli:88  and simplified_apply = private { apply : Apply.t; use_id : Apply_cont_rewrite_id.t option; exn_cont_use_id : Apply_cont_rewrite_id.t; result_arity : [`Complex] Flambda_arity.t; is_cold : bool } *)
Parameter simplified_apply_ : Type.
Extract Inlined Constant simplified_apply_ => "Simplified_expr.simplified_apply".
(* simplified_expr.mli:108  and simplified_switch = private { arms : (Apply_cont_expr.t * annotations:Branch_annotations.t * Apply_cont_rewrite_id.t * [`Unarized] Flambda_arity.t * Typing_env.t) Target_ocaml_int.Map.t; condition_dbg : Debuginfo.t; scrutinee : Simple.t; scrutinee_ty : flambda_type; shareable_constants : Symbol.t Static_const.Map.t; typing_env_before_switch : Typing_env.t; cse_before_switch : Common_subexpr... *)
Parameter simplified_switch_ : Type.
Extract Inlined Constant simplified_switch_ => "Simplified_expr.simplified_switch".
(* simplified_expr.mli:31  type t = private { simplified_lets_and_let_conts : simplified_lets_and_let_conts; simplified_terminator : simplified_terminator; removed_operations : Removed_operations.t; is_cold : bool } *)
(* PORT-GAP(type): it is recursive with a type that is declared after it: abstract, with a maker for each constructor and one eliminator. *)
Parameter t : Type.
Extract Inlined Constant t => "Simplified_expr.t".
(* simplified_expr.mli:38  and simplified_lets_and_let_conts = private | Simplified_terminator | Simplified_let of simplified_defining_expr * simplified_lets_and_let_conts | Simplified_let_cont of simplified_let_cont_handlers * simplified_lets_and_let_conts *)
Inductive simplified_lets_and_let_conts_ : Type :=
| Simplified_terminator : simplified_lets_and_let_conts_
| Simplified_let : simplified_defining_expr -> simplified_lets_and_let_conts_ -> simplified_lets_and_let_conts_
| Simplified_let_cont : simplified_let_cont_handlers -> simplified_lets_and_let_conts_ -> simplified_lets_and_let_conts_.
(* simplified_expr.mli:96  and simplified_terminator = private | Simplified_apply of simplified_apply | Simplified_apply_cont of simplified_apply_cont | Simplified_switch of simplified_switch | Simplified_invalid of Flambda.Invalid.t *)
(* PORT-GAP(type): it is recursive with a type that is declared after it: abstract, with a maker for each constructor and one eliminator. *)
Parameter simplified_terminator_ : Type.
Extract Inlined Constant simplified_terminator_ => "Simplified_expr.simplified_terminator".
(* simplified_expr.mli:102  and simplified_apply_cont = private { apply_cont : Apply_cont.t; args : Simple.t list; rewrite_id : Apply_cont_rewrite_id.t } *)
Record simplified_apply_cont_ : Type := { apply_cont : Flambda.Import_.Apply_cont.t; args : list Simple.t; rewrite_id : Apply_cont_rewrite_id.t }.
Parameter mk_t : simplified_lets_and_let_conts_ -> simplified_terminator_ -> Removed_operations.t -> bool -> t.
Extract Inlined Constant mk_t => "(fun x__1 x__2 x__3 x__4 -> { Simplified_expr.simplified_lets_and_let_conts = x__1; simplified_terminator = x__2; removed_operations = x__3; is_cold = x__4 })".
Parameter match_t : forall {Res : Type}, t -> (simplified_lets_and_let_conts_ -> simplified_terminator_ -> Removed_operations.t -> bool -> M Res) -> M Res.
Extract Inlined Constant match_t => "(fun x__0 f__1 -> let { Simplified_expr.simplified_lets_and_let_conts = x__1; simplified_terminator = x__2; removed_operations = x__3; is_cold = x__4 } = x__0 in f__1 x__1 x__2 x__3 x__4)".
Parameter mk_Simplified_apply : simplified_apply_ -> simplified_terminator_.
Extract Inlined Constant mk_Simplified_apply => "(fun x__1 -> Simplified_expr.Simplified_apply x__1)".
Parameter mk_Simplified_apply_cont : simplified_apply_cont_ -> simplified_terminator_.
Extract Inlined Constant mk_Simplified_apply_cont => "(fun x__1 -> Simplified_expr.Simplified_apply_cont x__1)".
Parameter mk_Simplified_switch : simplified_switch_ -> simplified_terminator_.
Extract Inlined Constant mk_Simplified_switch => "(fun x__1 -> Simplified_expr.Simplified_switch x__1)".
Parameter mk_Simplified_invalid : Flambda.Invalid.t -> simplified_terminator_.
Extract Inlined Constant mk_Simplified_invalid => "(fun x__1 -> Simplified_expr.Simplified_invalid x__1)".
Parameter match_simplified_terminator_ : forall {Res : Type}, simplified_terminator_ -> (simplified_apply_ -> M Res) -> (simplified_apply_cont_ -> M Res) -> (simplified_switch_ -> M Res) -> (Flambda.Invalid.t -> M Res) -> M Res.
Extract Inlined Constant match_simplified_terminator_ => "(fun x__0 f__1 f__2 f__3 f__4 -> match x__0 with Simplified_expr.Simplified_apply x__1 -> f__1 x__1 | Simplified_expr.Simplified_apply_cont x__1 -> f__2 x__1 | Simplified_expr.Simplified_switch x__1 -> f__3 x__1 | Simplified_expr.Simplified_invalid x__1 -> f__4 x__1)".
(* simplified_expr.mli:124  val notify_removed : operation:Removed_operations.t -> t -> t *)
Parameter notify_removed : Removed_operations.t -> t -> M t.
Extract Inlined Constant notify_removed => "Simplified_expr.notify_removed".
(* simplified_expr.mli:126  val mark_as_cold : t -> t *)
Parameter mark_as_cold : t -> M t.
Extract Inlined Constant mark_as_cold => "Simplified_expr.mark_as_cold".
(* simplified_expr.mli:128  val simplified_let : bindings_to_place:Simplified_named.binding_to_place list -> removed_operations:Removed_operations.t -> lifted_constants_from_defining_expr:Lifted_constant_state.t -> at_unit_toplevel:bool -> closure_info:Closure_info.t -> rewrite_id:Named_rewrite_id.t -> t -> t *)
Parameter simplified_let : list Simplified_named.binding_to_place -> Removed_operations.t -> Lifted_constant_state.t -> bool -> Closure_info.t -> Named_rewrite_id.t -> t -> M t.
Extract Inlined Constant simplified_let => "Simplified_expr.simplified_let".
(* simplified_expr.mli:138  val simplified_let_cont : simplified_let_cont_handlers -> t -> t *)
Parameter simplified_let_cont : simplified_let_cont_handlers -> t -> M t.
Extract Inlined Constant simplified_let_cont => "Simplified_expr.simplified_let_cont".
(* simplified_expr.mli:140  val simplified_apply : ?result_arity:[`Complex] Flambda_arity.t -> Apply.t -> use_id:Apply_cont_rewrite_id.t option -> exn_cont_use_id:Apply_cont_rewrite_id.t -> is_cold:bool -> t *)
Parameter simplified_apply : option Flambda_arity.t -> Flambda.Import_.Apply.t -> option Apply_cont_rewrite_id.t -> Apply_cont_rewrite_id.t -> bool -> M t.
Extract Inlined Constant simplified_apply => "(fun x__1 x__2 x__3 x__4 x__5 -> Simplified_expr.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)".
(* simplified_expr.mli:148  val simplified_apply_cont : Apply_cont.t -> args:Simple.t list -> rewrite_id:Apply_cont_rewrite_id.t -> t *)
Parameter simplified_apply_cont : Flambda.Import_.Apply_cont.t -> list Simple.t -> Apply_cont_rewrite_id.t -> M t.
Extract Inlined Constant simplified_apply_cont => "Simplified_expr.simplified_apply_cont".
(* simplified_expr.mli:151  val simplified_switch : arms: (Apply_cont_expr.t * annotations:Branch_annotations.t * Apply_cont_rewrite_id.t * [`Unarized] Flambda_arity.t * Typing_env.t) Target_ocaml_int.Map.t -> condition_dbg:Debuginfo.t -> scrutinee:Simple.t -> scrutinee_ty:flambda_type -> shareable_constants:Symbol.t Static_const.Map.t -> typing_env_before_switch:Typing_env.t -> cse_before_switch:Common_subexpression_elim... *)
Parameter simplified_switch : Target_ocaml_int.Map.t (tuple5 Apply_cont_expr.t Branch_annotations.t Apply_cont_rewrite_id.t Flambda_arity.t Flambda2_types.Typing_env.t) -> Debuginfo.t -> Simple.t -> Flambda2_types.flambda_type -> Flambda.Import_.Static_const.Map.t Symbol.t -> Flambda2_types.Typing_env.t -> Common_subexpression_elimination.t -> M t.
Extract Inlined Constant simplified_switch => "Simplified_expr.simplified_switch".
(* simplified_expr.mli:167  val simplified_invalid : Flambda.Invalid.t -> t *)
Parameter simplified_invalid : Flambda.Invalid.t -> M t.
Extract Inlined Constant simplified_invalid => "Simplified_expr.simplified_invalid".
