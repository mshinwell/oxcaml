(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Lifted_constant], after its interface
   middle_end/flambda2/simplify/lifting/lifted_constant.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_static Code_id Flambda2_types Format Function_slot Name_occurrences Rebuilt_static_const Simple Symbol Symbol_projection Variable_.

Module Definition_.
  (* lifted_constant.mli:25  type descr = private | Code of Code_id.t | Set_of_closures of { typing_env : Typing_env.t; closure_symbols_with_types : (Symbol.t * Flambda2_types.t) Function_slot.Lmap.t; symbol_projections : Symbol_projection.t Variable.Map.t } | Block_like of { symbol : Symbol.t; typing_env : Typing_env.t; ty : Flambda2_types.t; symbol_projections : Symbol_projection.t Variable.Map.t } *)
  (* PORT-GAP(type): the name of the field [typing_env] is taken in Rocq: abstract, with a maker for each constructor and one eliminator. *)
  Parameter descr_ : Type.
  Extract Inlined Constant descr_ => "Lifted_constant.Definition.descr".
  Parameter mk_Code : Code_id.t -> descr_.
  Extract Inlined Constant mk_Code => "(fun x__1 -> Lifted_constant.Definition.Code x__1)".
  Parameter mk_Set_of_closures : Flambda2_types.Typing_env.t -> Function_slot.Lmap.t (Symbol.t * Flambda2_types.t) -> Variable_.Map.t Symbol_projection.t -> descr_.
  Extract Inlined Constant mk_Set_of_closures => "(fun x__1 x__2 x__3 -> Lifted_constant.Definition.Set_of_closures { typing_env = x__1; closure_symbols_with_types = x__2; symbol_projections = x__3 })".
  Parameter mk_Block_like : Symbol.t -> Flambda2_types.Typing_env.t -> Flambda2_types.t -> Variable_.Map.t Symbol_projection.t -> descr_.
  Extract Inlined Constant mk_Block_like => "(fun x__1 x__2 x__3 x__4 -> Lifted_constant.Definition.Block_like { symbol = x__1; typing_env = x__2; ty = x__3; symbol_projections = x__4 })".
  Parameter match_descr_ : forall {Res : Type}, descr_ -> (Code_id.t -> M Res) -> (Flambda2_types.Typing_env.t -> Function_slot.Lmap.t (Symbol.t * Flambda2_types.t) -> Variable_.Map.t Symbol_projection.t -> M Res) -> (Symbol.t -> Flambda2_types.Typing_env.t -> Flambda2_types.t -> Variable_.Map.t Symbol_projection.t -> M Res) -> M Res.
  Extract Inlined Constant match_descr_ => "(fun x__0 f__1 f__2 f__3 -> match x__0 with Lifted_constant.Definition.Code x__1 -> f__1 x__1 | Lifted_constant.Definition.Set_of_closures { typing_env = x__1; closure_symbols_with_types = x__2; symbol_projections = x__3 } -> f__2 x__1 x__2 x__3 | Lifted_constant.Definition.Block_like { symbol = x__1; typing_env = x__2; ty = x__3; symbol_projections = x__4 } -> f__3 x__1 x__2 x__3 x__4)".
  (* lifted_constant.mli:40  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Lifted_constant.Definition.t".
  (* lifted_constant.mli:42  val descr : t -> descr *)
  Parameter descr : t -> M descr_.
  Extract Inlined Constant descr => "Lifted_constant.Definition.descr".
  (* lifted_constant.mli:44  val defining_expr : t -> Rebuilt_static_const.t *)
  Parameter defining_expr : t -> M Rebuilt_static_const.t.
  Extract Inlined Constant defining_expr => "Lifted_constant.Definition.defining_expr".
  (* lifted_constant.mli:46  val typing_env : t -> Typing_env.t option *)
  Parameter typing_env : t -> M (option Flambda2_types.Typing_env.t).
  Extract Inlined Constant typing_env => "Lifted_constant.Definition.typing_env".
  (* lifted_constant.mli:48  val code : Code_id.t -> Rebuilt_static_const.t -> t *)
  Parameter code : Code_id.t -> Rebuilt_static_const.t -> M t.
  Extract Inlined Constant code => "Lifted_constant.Definition.code".
  (* lifted_constant.mli:50  val set_of_closures : Typing_env.t -> closure_symbols_with_types: (Symbol.t * Flambda2_types.t) Function_slot.Lmap.t -> symbol_projections:Symbol_projection.t Variable.Map.t -> Rebuilt_static_const.t -> t *)
  Parameter set_of_closures : Flambda2_types.Typing_env.t -> Function_slot.Lmap.t (Symbol.t * Flambda2_types.t) -> Variable_.Map.t Symbol_projection.t -> Rebuilt_static_const.t -> M t.
  Extract Inlined Constant set_of_closures => "Lifted_constant.Definition.set_of_closures".
  (* lifted_constant.mli:58  val block_like : Typing_env.t -> Symbol.t -> Flambda2_types.t -> symbol_projections:Symbol_projection.t Variable.Map.t -> Rebuilt_static_const.t -> t *)
  Parameter block_like : Flambda2_types.Typing_env.t -> Symbol.t -> Flambda2_types.t -> Variable_.Map.t Symbol_projection.t -> Rebuilt_static_const.t -> M t.
  Extract Inlined Constant block_like => "Lifted_constant.Definition.block_like".
  (* lifted_constant.mli:66  val bound_static : t -> Bound_static.t *)
  Parameter bound_static : t -> M Bound_static.t.
  Extract Inlined Constant bound_static => "Lifted_constant.Definition.bound_static".
  (* lifted_constant.mli:68  val free_names : t -> Name_occurrences.t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Lifted_constant.Definition.free_names".
  (* lifted_constant.mli:70  val symbol_projections : t -> Symbol_projection.t Variable.Map.t *)
  Parameter symbol_projections : t -> M (Variable_.Map.t Symbol_projection.t).
  Extract Inlined Constant symbol_projections => "Lifted_constant.Definition.symbol_projections".
End Definition_.
(* lifted_constant.mli:73  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Lifted_constant.t".
(* lifted_constant.mli:75  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Lifted_constant.print".
(* lifted_constant.mli:79  val create_block_like : Symbol.t -> symbol_projections:Symbol_projection.t Variable.Map.t -> Rebuilt_static_const.t -> Typing_env.t -> Flambda2_types.t -> t *)
Parameter create_block_like : Symbol.t -> Variable_.Map.t Symbol_projection.t -> Rebuilt_static_const.t -> Flambda2_types.Typing_env.t -> Flambda2_types.t -> M t.
Extract Inlined Constant create_block_like => "Lifted_constant.create_block_like".
(* lifted_constant.mli:87  val create_set_of_closures : Typing_env.t -> closure_symbols_with_types:(Symbol.t * Flambda2_types.t) Function_slot.Lmap.t -> symbol_projections:Symbol_projection.t Variable.Map.t -> Rebuilt_static_const.t -> t *)
Parameter create_set_of_closures : Flambda2_types.Typing_env.t -> Function_slot.Lmap.t (Symbol.t * Flambda2_types.t) -> Variable_.Map.t Symbol_projection.t -> Rebuilt_static_const.t -> M t.
Extract Inlined Constant create_set_of_closures => "Lifted_constant.create_set_of_closures".
(* lifted_constant.mli:94  val create_code : Code_id.t -> Rebuilt_static_const.t -> t *)
Parameter create_code : Code_id.t -> Rebuilt_static_const.t -> M t.
Extract Inlined Constant create_code => "Lifted_constant.create_code".
(* lifted_constant.mli:96  val create_definition : Definition.t -> t *)
Parameter create_definition : Lifted_constant.Definition_.t -> M t.
Extract Inlined Constant create_definition => "Lifted_constant.create_definition".
(* lifted_constant.mli:98  val definitions : t -> Definition.t list *)
Parameter definitions : t -> M (list Lifted_constant.Definition_.t).
Extract Inlined Constant definitions => "Lifted_constant.definitions".
(* lifted_constant.mli:100  val bound_static : t -> Bound_static.t *)
Parameter bound_static : t -> M Bound_static.t.
Extract Inlined Constant bound_static => "Lifted_constant.bound_static".
(* lifted_constant.mli:102  val defining_exprs : t -> Rebuilt_static_const.Group.t *)
Parameter defining_exprs : t -> M Rebuilt_static_const.Group.t.
Extract Inlined Constant defining_exprs => "Lifted_constant.defining_exprs".
(* lifted_constant.mli:104  val types_of_symbols : t -> (Typing_env.t * Flambda2_types.t) Symbol.Map.t *)
Parameter types_of_symbols : t -> M (Symbol.Map.t (Flambda2_types.Typing_env.t * Flambda2_types.t)).
Extract Inlined Constant types_of_symbols => "Lifted_constant.types_of_symbols".
(* lifted_constant.mli:106  val symbol_projections : t -> Symbol_projection.t Variable.Map.t *)
Parameter symbol_projections : t -> M (Variable_.Map.t Symbol_projection.t).
Extract Inlined Constant symbol_projections => "Lifted_constant.symbol_projections".
(* lifted_constant.mli:108  val concat : t list -> t *)
Parameter concat : list t -> M t.
Extract Inlined Constant concat => "Lifted_constant.concat".
(* lifted_constant.mli:110  val is_fully_static : t -> bool *)
Parameter is_fully_static : t -> M bool.
Extract Inlined Constant is_fully_static => "Lifted_constant.is_fully_static".
(* lifted_constant.mli:112  val all_defined_symbols : t -> Symbol.Set.t *)
Parameter all_defined_symbols : t -> M Symbol.Set_.t.
Extract Inlined Constant all_defined_symbols => "Lifted_constant.all_defined_symbols".
(* lifted_constant.mli:114  val free_names_of_defining_exprs : t -> Name_occurrences.t *)
Parameter free_names_of_defining_exprs : t -> M Name_occurrences.t.
Extract Inlined Constant free_names_of_defining_exprs => "Lifted_constant.free_names_of_defining_exprs".
(* lifted_constant.mli:116  val apply_projection : t -> Symbol_projection.t -> Simple.t option *)
Parameter apply_projection : t -> Symbol_projection.t -> M (option Simple.t).
Extract Inlined Constant apply_projection => "Lifted_constant.apply_projection".
