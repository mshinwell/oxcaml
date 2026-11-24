(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplified_expr], after its interface
   middle_end/flambda2/simplify/simplified_expr.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Apply_cont_rewrite_id Bound_parameters Branch_annotations Closure_info Common_subexpression_elimination Continuation Continuation_extra_params_and_args Debuginfo Flambda Flambda2_types Flambda_arity Lifted_constant_state Named_rewrite_id Removed_operations Simple Simplified_named Symbol Target_ocaml_int.

(* The tuple with labels (Apply_cont_expr.t * annotations:Branch_annotations.t * Apply_cont_rewrite_id.t * [ `Unarized ] Flambda_arity.t * Flambda2_types.Typing_env.t) that the interface writes: Rocq has no label in a tuple. [Arms_tuple] makes one, and a [match] takes it apart. *)
Inductive arms_tuple : Type :=
| Arms_tuple : Apply_cont_expr.t -> Branch_annotations.t -> Apply_cont_rewrite_id.t -> Flambda_arity.t_Unarized -> Flambda2_types.Typing_env.t -> arms_tuple.
Extract Inductive arms_tuple => "(Apply_cont_expr.t * annotations:Branch_annotations.t * Apply_cont_rewrite_id.t * [ `Unarized ] Flambda_arity.t * Flambda2_types.Typing_env.t)" [ "(fun (x__1, x__2, x__3, x__4, x__5) -> (x__1, ~annotations:x__2, x__3, x__4, x__5))" ] "(fun f__1 x__0 -> let (x__1, ~annotations:x__2, x__3, x__4, x__5) = x__0 in f__1 x__1 x__2 x__3 x__4 x__5)".
(* simplified_expr.mli:31  type t = private { simplified_lets_and_let_conts : simplified_lets_and_let_conts; simplified_terminator : simplified_terminator; removed_operations : Removed_operations.t; is_cold : bool } *)
(* PORT-GAP(type): it is a record that is recursive with other types: abstract, with no maker (OCaml makes no value of a private type outside its module) and one eliminator. *)
Parameter t : Type.
Extract Inlined Constant t => "Simplified_expr.t".
(* simplified_expr.mli:59  and simplified_handler = { params : Bound_parameters.t; simplified_handler : t; is_exn_handler : bool; is_cold : bool; extra_params_and_args : Continuation_extra_params_and_args.t; ( * Note: EPA.extra_params invariant_extra_params_and_args should always be equal to invariant_extra_params in stage4 * ) invariant_extra_params_and_args : Continuation_extra_params_and_args.t; rewrite_ids : Apply_co... *)
(* PORT-GAP(type): it is a record that is recursive with other types: abstract, with one maker and one eliminator. *)
Parameter simplified_handler_ : Type.
Extract Inlined Constant simplified_handler_ => "Simplified_expr.simplified_handler".
(* simplified_expr.mli:81  and simplified_let_cont_handlers = { at_unit_toplevel : bool; handlers_from_the_outside_to_the_inside : simplified_handlers_group list; original_invariant_params : Bound_parameters.t; invariant_extra_params : Bound_parameters.t } *)
(* PORT-GAP(type): it is a record that is recursive with other types: abstract, with one maker and one eliminator. *)
Parameter simplified_let_cont_handlers : Type.
Extract Inlined Constant simplified_let_cont_handlers => "Simplified_expr.simplified_let_cont_handlers".
(* simplified_expr.mli:44  and simplified_defining_expr = private ( * CR-soon bclement: it seems like some fields don't actually have their place here. [removed_operations] could be accumulated in the basic block directly, and [at_unit_toplevel] and [closure_info] could be stored there as well (something went very wrong if these change in the middle of a basic block). * ) { bindings_to_place : Simplified_named.binding_to... *)
Record simplified_defining_expr : Type := { bindings_to_place : list Simplified_named.binding_to_place; removed_operations : Removed_operations.t; lifted_constants_from_defining_expr : Lifted_constant_state.t; at_unit_toplevel : bool; closure_info : Closure_info.t; rewrite_id : Named_rewrite_id.t }.
(* simplified_expr.mli:38  and simplified_lets_and_let_conts = private | Simplified_terminator | Simplified_let of simplified_defining_expr * simplified_lets_and_let_conts | Simplified_let_cont of simplified_let_cont_handlers * simplified_lets_and_let_conts *)
Inductive simplified_lets_and_let_conts_ : Type :=
| Simplified_terminator : simplified_lets_and_let_conts_
| Simplified_let : simplified_defining_expr -> simplified_lets_and_let_conts_ -> simplified_lets_and_let_conts_
| Simplified_let_cont : simplified_let_cont_handlers -> simplified_lets_and_let_conts_ -> simplified_lets_and_let_conts_.
Extract Inductive simplified_lets_and_let_conts_ => "Simplified_expr.simplified_lets_and_let_conts" [ "Simplified_expr.Simplified_terminator" "Simplified_expr.Simplified_let" "Simplified_expr.Simplified_let_cont" ].
(* simplified_expr.mli:71  and simplified_handlers_group = | Recursive of { simplified_continuation_handlers : simplified_handler Continuation.Map.t } | Non_recursive of { cont : Continuation.t; handler : simplified_handler; is_single_inlinable_use : bool } *)
Inductive simplified_handlers_group : Type :=
| Recursive : Continuation.Map.t simplified_handler_ -> simplified_handlers_group
| Non_recursive : Continuation.t -> simplified_handler_ -> bool -> simplified_handlers_group.
Extract Inductive simplified_handlers_group => "Simplified_expr.simplified_handlers_group" [ "(fun x__1 -> (Simplified_expr.Recursive { simplified_continuation_handlers = x__1 } : Simplified_expr.simplified_handlers_group))" "(fun (x__1, x__2, x__3) -> (Simplified_expr.Non_recursive { cont = x__1; handler = x__2; is_single_inlinable_use = x__3 } : Simplified_expr.simplified_handlers_group))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Simplified_expr.simplified_handlers_group) with Simplified_expr.Recursive { simplified_continuation_handlers = x__1 } -> f__1 x__1 | Simplified_expr.Non_recursive { cont = x__1; handler = x__2; is_single_inlinable_use = x__3 } -> f__2 x__1 x__2 x__3)".
(* simplified_expr.mli:88  and simplified_apply = private { apply : Apply.t; use_id : Apply_cont_rewrite_id.t option; exn_cont_use_id : Apply_cont_rewrite_id.t; result_arity : [`Complex] Flambda_arity.t; is_cold : bool } *)
Record simplified_apply_ : Type := { apply : Flambda.Import_.Apply.t; use_id : option Apply_cont_rewrite_id.t; exn_cont_use_id : Apply_cont_rewrite_id.t; result_arity : Flambda_arity.t_Complex; is_cold : bool }.
(* simplified_expr.mli:102  and simplified_apply_cont = private { apply_cont : Apply_cont.t; args : Simple.t list; rewrite_id : Apply_cont_rewrite_id.t } *)
(* PORT-GAP(type): the name of a field of it is taken in Rocq: abstract, with no maker (OCaml makes no value of a private type outside its module) and one eliminator. *)
Parameter simplified_apply_cont_ : Type.
Extract Inlined Constant simplified_apply_cont_ => "Simplified_expr.simplified_apply_cont".
(* simplified_expr.mli:108  and simplified_switch = private { arms : (Apply_cont_expr.t * annotations:Branch_annotations.t * Apply_cont_rewrite_id.t * [`Unarized] Flambda_arity.t * Typing_env.t) Target_ocaml_int.Map.t; condition_dbg : Debuginfo.t; scrutinee : Simple.t; scrutinee_ty : flambda_type; shareable_constants : Symbol.t Static_const.Map.t; typing_env_before_switch : Typing_env.t; cse_before_switch : Common_subexpr... *)
Record simplified_switch_ : Type := { arms : Target_ocaml_int.Map.t arms_tuple; condition_dbg : Debuginfo.t; scrutinee : Simple.t; scrutinee_ty : Flambda2_types.flambda_type; shareable_constants : Flambda.Import_.Static_const.Map.t Symbol.t; typing_env_before_switch : Flambda2_types.Typing_env.t; cse_before_switch : Common_subexpression_elimination.t }.
(* simplified_expr.mli:96  and simplified_terminator = private | Simplified_apply of simplified_apply | Simplified_apply_cont of simplified_apply_cont | Simplified_switch of simplified_switch | Simplified_invalid of Flambda.Invalid.t *)
Inductive simplified_terminator_ : Type :=
| Simplified_apply : simplified_apply_ -> simplified_terminator_
| Simplified_apply_cont : simplified_apply_cont_ -> simplified_terminator_
| Simplified_switch : simplified_switch_ -> simplified_terminator_
| Simplified_invalid : Flambda.Invalid.t -> simplified_terminator_.
Extract Inductive simplified_terminator_ => "Simplified_expr.simplified_terminator" [ "Simplified_expr.Simplified_apply" "Simplified_expr.Simplified_apply_cont" "Simplified_expr.Simplified_switch" "Simplified_expr.Simplified_invalid" ].
Parameter match_t : forall {Res : Type}, t -> (simplified_lets_and_let_conts_ -> simplified_terminator_ -> Removed_operations.t -> bool -> M Res) -> M Res.
Extract Inlined Constant match_t => "(fun x__0 f__1 -> let { Simplified_expr.simplified_lets_and_let_conts = x__1; simplified_terminator = x__2; removed_operations = x__3; is_cold = x__4 } = x__0 in f__1 x__1 x__2 x__3 x__4)".
Parameter mk_simplified_handler_ : Bound_parameters.t -> t -> bool -> bool -> Continuation_extra_params_and_args.t -> Continuation_extra_params_and_args.t -> Apply_cont_rewrite_id.Set_.t -> simplified_handler_.
Extract Inlined Constant mk_simplified_handler_ => "(fun x__1 x__2 x__3 x__4 x__5 x__6 x__7 -> { Simplified_expr.params = x__1; simplified_handler = x__2; is_exn_handler = x__3; is_cold = x__4; extra_params_and_args = x__5; invariant_extra_params_and_args = x__6; rewrite_ids = x__7 })".
Parameter match_simplified_handler_ : forall {Res : Type}, simplified_handler_ -> (Bound_parameters.t -> t -> bool -> bool -> Continuation_extra_params_and_args.t -> Continuation_extra_params_and_args.t -> Apply_cont_rewrite_id.Set_.t -> M Res) -> M Res.
Extract Inlined Constant match_simplified_handler_ => "(fun x__0 f__1 -> let { Simplified_expr.params = x__1; simplified_handler = x__2; is_exn_handler = x__3; is_cold = x__4; extra_params_and_args = x__5; invariant_extra_params_and_args = x__6; rewrite_ids = x__7 } = x__0 in f__1 x__1 x__2 x__3 x__4 x__5 x__6 x__7)".
Parameter mk_simplified_let_cont_handlers : bool -> list simplified_handlers_group -> Bound_parameters.t -> Bound_parameters.t -> simplified_let_cont_handlers.
Extract Inlined Constant mk_simplified_let_cont_handlers => "(fun x__1 x__2 x__3 x__4 -> { Simplified_expr.at_unit_toplevel = x__1; handlers_from_the_outside_to_the_inside = x__2; original_invariant_params = x__3; invariant_extra_params = x__4 })".
Parameter match_simplified_let_cont_handlers : forall {Res : Type}, simplified_let_cont_handlers -> (bool -> list simplified_handlers_group -> Bound_parameters.t -> Bound_parameters.t -> M Res) -> M Res.
Extract Inlined Constant match_simplified_let_cont_handlers => "(fun x__0 f__1 -> let { Simplified_expr.at_unit_toplevel = x__1; handlers_from_the_outside_to_the_inside = x__2; original_invariant_params = x__3; invariant_extra_params = x__4 } = x__0 in f__1 x__1 x__2 x__3 x__4)".
Parameter match_simplified_apply_cont_ : forall {Res : Type}, simplified_apply_cont_ -> (Flambda.Import_.Apply_cont.t -> list Simple.t -> Apply_cont_rewrite_id.t -> M Res) -> M Res.
Extract Inlined Constant match_simplified_apply_cont_ => "(fun x__0 f__1 -> let { Simplified_expr.apply_cont = x__1; args = x__2; rewrite_id = x__3 } = x__0 in f__1 x__1 x__2 x__3)".
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
Parameter simplified_apply : option Flambda_arity.t_Complex -> Flambda.Import_.Apply.t -> option Apply_cont_rewrite_id.t -> Apply_cont_rewrite_id.t -> bool -> M t.
Extract Inlined Constant simplified_apply => "(fun x__1 x__2 x__3 x__4 x__5 -> Simplified_expr.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)".
(* simplified_expr.mli:148  val simplified_apply_cont : Apply_cont.t -> args:Simple.t list -> rewrite_id:Apply_cont_rewrite_id.t -> t *)
Parameter simplified_apply_cont : Flambda.Import_.Apply_cont.t -> list Simple.t -> Apply_cont_rewrite_id.t -> M t.
Extract Inlined Constant simplified_apply_cont => "Simplified_expr.simplified_apply_cont".
(* simplified_expr.mli:151  val simplified_switch : arms: (Apply_cont_expr.t * annotations:Branch_annotations.t * Apply_cont_rewrite_id.t * [`Unarized] Flambda_arity.t * Typing_env.t) Target_ocaml_int.Map.t -> condition_dbg:Debuginfo.t -> scrutinee:Simple.t -> scrutinee_ty:flambda_type -> shareable_constants:Symbol.t Static_const.Map.t -> typing_env_before_switch:Typing_env.t -> cse_before_switch:Common_subexpression_elim... *)
Parameter simplified_switch : Target_ocaml_int.Map.t arms_tuple -> Debuginfo.t -> Simple.t -> Flambda2_types.flambda_type -> Flambda.Import_.Static_const.Map.t Symbol.t -> Flambda2_types.Typing_env.t -> Common_subexpression_elimination.t -> M t.
Extract Inlined Constant simplified_switch => "Simplified_expr.simplified_switch".
(* simplified_expr.mli:167  val simplified_invalid : Flambda.Invalid.t -> t *)
Parameter simplified_invalid : Flambda.Invalid.t -> M t.
Extract Inlined Constant simplified_invalid => "Simplified_expr.simplified_invalid".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplified_expr. End Simplified_expr.
