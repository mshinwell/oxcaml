(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flow_types], after its interface
   middle_end/flambda2/simplify/flow/flow_types.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

Module Cont_arg.
  (* flow_types.mli:27  type t = | Function_result | Simple of Simple.t | New_let_binding of Variable.t * Name_occurrences.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Cont_arg.t".
  (* flow_types.mli:32  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Cont_arg.print".
End Cont_arg.
Module Mutable_prim.
  (* flow_types.mli:39  type t = | Is_int of Variable.t | Get_tag of Variable.t | Block_load of { bak : Flambda_primitive.Block_access_kind.t; mut : Mutability.t; block : Variable.t; field : int } | Block_set of { bak : Flambda_primitive.Block_access_kind.t; block : Variable.t; field : int; value : Simple.t } | Make_block of { kind : Flambda_primitive.Block_kind.t; mut : Mutability.t; alloc_mode : Alloc_mode.For_alloc... *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Mutable_prim.t".
  (* flow_types.mli:61  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Mutable_prim.print".
End Mutable_prim.
Module Mutable_let_prim.
  (* flow_types.mli:68  type t = { bound_var : Variable.t; prim : Mutable_prim.t; original_prim : Flambda_primitive.t; named_rewrite_id : Named_rewrite_id.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Mutable_let_prim.t".
  (* flow_types.mli:75  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Mutable_let_prim.print".
  Module List.
    (* flow_types.mli:78  type nonrec t = t list *)
    Definition t : Type := list Flow_types.Mutable_let_prim.t.
    Extract Inlined Constant t => "Flow_types.Mutable_let_prim.List.t".
    (* flow_types.mli:80  val print_rev : Format.formatter -> t -> unit *)
    Parameter print_rev : Format.formatter -> t -> M unit.
    Extract Inlined Constant print_rev => "Flow_types.Mutable_let_prim.List.print_rev".
  End List.
End Mutable_let_prim.
Module Continuation_info.
  (* flow_types.mli:88  type t = { continuation : Continuation.t; recursive : bool; is_exn_handler : bool; params : Bound_parameters.t; parent_continuation : Continuation.t option; used_in_handler : Name_occurrences.t; bindings : Name_occurrences.t Name.Map.t; direct_aliases : Simple.t Variable.Map.t; mutable_let_prims_rev : Mutable_let_prim.List.t; defined : Variable.Set.t; code_ids : Name_occurrences.t Code_id.Map.t... *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Continuation_info.t".
  (* flow_types.mli:105  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Continuation_info.print".
End Continuation_info.
Module Acc.
  (* flow_types.mli:112  type t = { stack : Continuation_info.t list; map : Continuation_info.t Continuation.Map.t; extra : Continuation_extra_params_and_args.t Continuation.Map.t; lifted_constants : Lifted_constant_state.t; dummy_toplevel_cont : Continuation.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Acc.t".
  (* flow_types.mli:120  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Acc.print".
End Acc.
Module Reachable_code_ids.
  (* flow_types.mli:127  type t = { live_code_ids : Code_id.Set.t; ( ** The set of code ids live/reachable. * ) ancestors_of_live_code_ids : Code_id.Set.t ( ** The set of code ids that are ancestors of at least one live code id. * ) } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Reachable_code_ids.t".
  (* flow_types.mli:134  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Reachable_code_ids.print".
End Reachable_code_ids.
Module Data_flow_result.
  (* flow_types.mli:141  type t = { required_names : Name.Set.t; ( ** The set of all variables that are in fact used to compute the returned value of the function being analyzed. * ) reachable_code_ids : Reachable_code_ids.t Or_unknown.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Data_flow_result.t".
  (* flow_types.mli:148  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Data_flow_result.print".
End Data_flow_result.
Module Continuation_param_aliases.
  (* flow_types.mli:155  type recursive_continuation_wrapper = | No_wrapper | Wrapper_needed *)
  Parameter recursive_continuation_wrapper_ : Type.
  Extract Inlined Constant recursive_continuation_wrapper_ => "Flow_types.Continuation_param_aliases.recursive_continuation_wrapper".
  (* flow_types.mli:159  type t = { removed_aliased_params_and_extra_params : Variable.Set.t; lets_to_introduce : Simple.t Variable.Lmap.t; ( * We are using a [Variable.Lmap.t] here in order to ensure a stable order for the introduced [lets]. * ) extra_args_for_aliases : Variable.Set.t; recursive_continuation_wrapper : recursive_continuation_wrapper } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Continuation_param_aliases.t".
  (* flow_types.mli:168  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Continuation_param_aliases.print".
End Continuation_param_aliases.
Module Alias_result.
  (* flow_types.mli:175  type t = { aliases_kind : Flambda_kind.t Variable.Map.t; continuation_parameters : Continuation_param_aliases.t Continuation.Map.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Alias_result.t".
  (* flow_types.mli:180  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Alias_result.print".
End Alias_result.
Module Mutable_unboxing_result.
  (* flow_types.mli:187  type t = { did_unbox_a_mutable_block : bool; additional_epa : Continuation_extra_params_and_args.t Continuation.Map.t; let_rewrites : Named_rewrite.t Named_rewrite_id.Map.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Mutable_unboxing_result.t".
  (* flow_types.mli:193  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Mutable_unboxing_result.print".
End Mutable_unboxing_result.
Module Flow_result.
  (* flow_types.mli:200  type t = { data_flow_result : Data_flow_result.t; aliases_result : Alias_result.t; mutable_unboxing_result : Mutable_unboxing_result.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow_types.Flow_result.t".
  (* flow_types.mli:206  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow_types.Flow_result.print".
End Flow_result.
