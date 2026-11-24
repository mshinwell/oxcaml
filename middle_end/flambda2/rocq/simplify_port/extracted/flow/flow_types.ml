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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/flow/Flow_types.v, which follows
   middle_end/flambda2/simplify/flow/flow_types.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad

module Cont_arg = struct
  type t =
    | Function_result
    | Simple of Simple.t
    | New_let_binding of Variable.t * Name_occurrences.t

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf = function
    | Function_result -> Format.fprintf ppf "Function_result"
    | Simple s -> Simple.print ppf s
    | New_let_binding (v, _) ->
      Format.fprintf ppf "New_let_binding %a" Variable.print v
end

module Mutable_prim = struct
  type t =
    | Is_int of Variable.t
    | Get_tag of Variable.t
    | Block_load of
        { bak : Flambda_primitive.Block_access_kind.t;
          mut : Mutability.t;
          block : Variable.t;
          field : int
        }
    | Block_set of
        { bak : Flambda_primitive.Block_access_kind.t;
          block : Variable.t;
          field : int;
          value : Simple.t
        }
    | Make_block of
        { kind : Flambda_primitive.Block_kind.t;
          mut : Mutability.t;
          alloc_mode : Alloc_mode.For_allocations.t;
          fields : Simple.t list
        }

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf x =
    (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
      match x__0 with
      | Is_int x__1 -> f__1 x__1
      | Get_tag x__1 -> f__2 x__1
      | Block_load { bak = x__1; mut = x__2; block = x__3; field = x__4 } ->
        f__3 x__1 x__2 x__3 x__4
      | Block_set { bak = x__1; block = x__2; field = x__3; value = x__4 } ->
        f__4 x__1 x__2 x__3 x__4
      | Make_block { kind = x__1; mut = x__2; alloc_mode = x__3; fields = x__4 }
        ->
        f__5 x__1 x__2 x__3 x__4)
      (fun v -> Format.fprintf ppf "Is_int (%a)" Variable.print v)
      (fun v -> Format.fprintf ppf "Get_tag (%a)" Variable.print v)
      (fun _ _ block field ->
        Format.fprintf ppf "Block_load (%a, %i)" Variable.print block field)
      (fun _ block field value ->
        Format.fprintf ppf "Block_set (%a, %i, %a)" Variable.print block field
          Simple.print value)
      (fun _ _ _ fields ->
        Format.fprintf ppf "Make_block [%a]" Simple.List.print fields)
      x
end

module Mutable_let_prim = struct
  module Coq__1 = struct
    type t =
      { bound_var : Variable.t;
        prim : Mutable_prim.t;
        original_prim : Flambda_primitive.t;
        named_rewrite_id : Named_rewrite_id.t
      }
  end

  include Coq__1

  (** val bound_var : t -> Variable.t **)

  let bound_var t0 = t0.bound_var

  (** val prim : t -> Mutable_prim.t **)

  let prim t0 = t0.prim

  (** val original_prim : t -> Flambda_primitive.t **)

  let original_prim t0 = t0.original_prim

  (** val named_rewrite_id : t -> Named_rewrite_id.t **)

  let named_rewrite_id t0 = t0.named_rewrite_id

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let { bound_var = bound_var0;
          prim = prim0;
          original_prim = _;
          named_rewrite_id = _
        } =
      t0
    in
    Format.fprintf ppf "%a = %a" Variable.print bound_var0 Mutable_prim.print
      prim0

  module List = struct
    type t = Coq__1.t list

    (** val print_rev : Format.formatter -> t -> unit coq_M **)

    let print_rev ppf l =
      Format.fprintf ppf "[%a]"
        ((fun x__1 x__2 x__3 x__4 ->
           Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
           (Some Format.pp_print_space) print)
        (List.rev l)
  end
end

module Continuation_info = struct
  type t =
    { continuation : Continuation.t;
      recursive : bool;
      is_exn_handler : bool;
      params : Bound_parameters.t;
      parent_continuation : Continuation.t option;
      used_in_handler : Name_occurrences.t;
      bindings : Name_occurrences.t Name.Map.t;
      direct_aliases : Simple.t Variable_.Map.t;
      mutable_let_prims_rev : Mutable_let_prim.List.t;
      defined : Variable.Set.t;
      code_ids : Name_occurrences.t Code_id.Map.t;
      value_slots : Name_occurrences.t Name.Map.t Value_slot.Map.t;
      apply_cont_args :
        Cont_arg.t Numeric_types.Int.Map.t Continuation_callsite_map.t
    }

  (** val continuation : t -> Continuation.t **)

  let continuation t0 = t0.continuation

  (** val recursive : t -> bool **)

  let recursive t0 = t0.recursive

  (** val is_exn_handler : t -> bool **)

  let is_exn_handler t0 = t0.is_exn_handler

  (** val params : t -> Bound_parameters.t **)

  let params t0 = t0.params

  (** val parent_continuation : t -> Continuation.t option **)

  let parent_continuation t0 = t0.parent_continuation

  (** val used_in_handler : t -> Name_occurrences.t **)

  let used_in_handler t0 = t0.used_in_handler

  (** val bindings : t -> Name_occurrences.t Name.Map.t **)

  let bindings t0 = t0.bindings

  (** val direct_aliases : t -> Simple.t Variable_.Map.t **)

  let direct_aliases t0 = t0.direct_aliases

  (** val mutable_let_prims_rev : t -> Mutable_let_prim.List.t **)

  let mutable_let_prims_rev t0 = t0.mutable_let_prims_rev

  (** val defined : t -> Variable.Set.t **)

  let defined t0 = t0.defined

  (** val code_ids : t -> Name_occurrences.t Code_id.Map.t **)

  let code_ids t0 = t0.code_ids

  (** val value_slots : t -> Name_occurrences.t Name.Map.t Value_slot.Map.t **)

  let value_slots t0 = t0.value_slots

  (** val apply_cont_args : t -> Cont_arg.t Numeric_types.Int.Map.t
      Continuation_callsite_map.t **)

  let apply_cont_args t0 = t0.apply_cont_args

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let { continuation = continuation0;
          recursive = recursive0;
          is_exn_handler = is_exn_handler0;
          params = params0;
          parent_continuation = parent_continuation0;
          used_in_handler = used_in_handler0;
          bindings = bindings0;
          direct_aliases = direct_aliases0;
          mutable_let_prims_rev = mutable_let_prims_rev0;
          defined = defined0;
          code_ids = code_ids0;
          value_slots = value_slots0;
          apply_cont_args = apply_cont_args0
        } =
      t0
    in
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(continuation %a)@]@ %s%s@[<hov 1>(params %a)@]@ \
       @[<hov 1>(parent_continuation %a)@]@ @[<hov 1>(used_in_handler %a)@]@ \
       @[<hov 1>(bindings %a)@]@ @[<hov 1>(direct_aliases %a)@]@ @[<hov \
       1>(ref_prims %a)@]@ @[<hov 1>(defined %a)@]@ @[<hov 1>(code_ids %a)@]@ \
       @[<hov 1>(value_slots %a)@]@ @[<hov 1>(apply_cont_args %a)@])@]"
      Continuation.print continuation0
      (if recursive0 then "(recursive) " else "")
      (if is_exn_handler0 then "(exn_handler) " else "")
      Bound_parameters.print params0
      ((fun x__1 x__2 x__3 x__4 ->
         Format.pp_print_option ?none:x__1 x__2 x__3 x__4)
         (Some (fun ppf0 _ -> Format.fprintf ppf0 "root"))
         Continuation.print)
      parent_continuation0 Name_occurrences.print used_in_handler0
      (Name.Map.print Name_occurrences.print)
      bindings0
      (Variable.Map.print Simple.print)
      direct_aliases0 Mutable_let_prim.List.print_rev mutable_let_prims_rev0
      Variable.Set.print defined0
      (Code_id.Map.print Name_occurrences.print)
      code_ids0
      (Value_slot.Map.print (Name.Map.print Name_occurrences.print))
      value_slots0
      (Continuation.Map.print
         (Apply_cont_rewrite_id.Map.print
            (Numeric_types.Int.Map.print Cont_arg.print)))
      apply_cont_args0
end

module Acc = struct
  type t =
    { stack : Continuation_info.t list;
      map : Continuation_info.t Continuation.Map.t;
      extra : Continuation_extra_params_and_args.t Continuation.Map.t;
      lifted_constants : Lifted_constant_state.t;
      dummy_toplevel_cont : Continuation.t
    }

  (** val stack : t -> Continuation_info.t list **)

  let stack t0 = t0.stack

  (** val map : t -> Continuation_info.t Continuation.Map.t **)

  let map t0 = t0.map

  (** val extra : t -> Continuation_extra_params_and_args.t Continuation.Map.t **)

  let extra t0 = t0.extra

  (** val lifted_constants : t -> Lifted_constant_state.t **)

  let lifted_constants t0 = t0.lifted_constants

  (** val dummy_toplevel_cont : t -> Continuation.t **)

  let dummy_toplevel_cont t0 = t0.dummy_toplevel_cont

  (** val print_stack : Format.formatter -> Continuation_info.t list -> unit
      coq_M **)

  let print_stack ppf stack0 =
    Format.fprintf ppf "@[<v 1>(%a)@]"
      ((fun x__1 x__2 x__3 x__4 ->
         Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
         (Some Format.pp_print_space) Continuation_info.print)
      stack0

  (** val print_map : Format.formatter -> Continuation_info.t Continuation.Map.t
      -> unit coq_M **)

  let print_map ppf map0 =
    Continuation.Map.print Continuation_info.print ppf map0

  (** val print_extra : Format.formatter -> Continuation_extra_params_and_args.t
      Continuation.Map.t -> unit coq_M **)

  let print_extra ppf extra0 =
    Continuation.Map.print Continuation_extra_params_and_args.print ppf extra0

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let { stack = stack0;
          map = map0;
          extra = extra0;
          lifted_constants = lifted_constants0;
          dummy_toplevel_cont = _
        } =
      t0
    in
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(stack %a)@]@ @[<hov 1>(map %a)@]@ @[<hov 1>(extra \
       %a)@]@ @[<hov 1>(lifted_constants %a)@])@]"
      print_stack stack0 print_map map0 print_extra extra0
      Lifted_constant_state.print lifted_constants0
end

module Reachable_code_ids = struct
  type t =
    { live_code_ids : Code_id.Set.t;
      ancestors_of_live_code_ids : Code_id.Set.t
    }

  (** val live_code_ids : t -> Code_id.Set.t **)

  let live_code_ids t0 = t0.live_code_ids

  (** val ancestors_of_live_code_ids : t -> Code_id.Set.t **)

  let ancestors_of_live_code_ids t0 = t0.ancestors_of_live_code_ids

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let { live_code_ids = live_code_ids0;
          ancestors_of_live_code_ids = ancestors_of_live_code_ids0
        } =
      t0
    in
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(live_code_ids@ %a)@]@ @[<hov \
       1>(ancestors_of_live_code_ids@ %a)@])@]"
      Code_id.Set.print live_code_ids0 Code_id.Set.print
      ancestors_of_live_code_ids0
end

module Data_flow_result = struct
  type t =
    { required_names : Name.Set.t;
      reachable_code_ids : Reachable_code_ids.t Or_unknown.t
    }

  (** val required_names : t -> Name.Set.t **)

  let required_names t0 = t0.required_names

  (** val reachable_code_ids : t -> Reachable_code_ids.t Or_unknown.t **)

  let reachable_code_ids t0 = t0.reachable_code_ids

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let { required_names = required_names0;
          reachable_code_ids = reachable_code_ids0
        } =
      t0
    in
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(required_names@ %a)@]@ @[<hov \
       1>(reachable_code_ids@ %a)@]@ )@]"
      Name.Set.print required_names0
      (Or_unknown.print Reachable_code_ids.print)
      reachable_code_ids0
end

module Continuation_param_aliases = struct
  type recursive_continuation_wrapper =
    | No_wrapper
    | Wrapper_needed

  type t =
    { removed_aliased_params_and_extra_params : Variable.Set.t;
      lets_to_introduce : Simple.t Variable.Lmap.t;
      extra_args_for_aliases : Variable.Set.t;
      recursive_continuation_wrapper : recursive_continuation_wrapper
    }

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    (fun f__1 x__0 ->
      let { removed_aliased_params_and_extra_params = x__1;
            lets_to_introduce = x__2;
            extra_args_for_aliases = x__3;
            recursive_continuation_wrapper = x__4
          } =
        x__0
      in
      f__1 x__1 x__2 x__3 x__4)
      (fun removed_aliased_params_and_extra_params lets_to_introduce
           extra_args_for_aliases recursive_continuation_wrapper0 ->
        let pp_wrapper =
         fun ppf0 x ->
          match x with
          | No_wrapper -> ()
          | Wrapper_needed ->
            Format.fprintf ppf0
              "@ @[<hov 1>(recursive_continuation_wrapper needed)@]"
        in
        Format.fprintf ppf
          "@[<hov 1>(@[<hov 1>(removed_aliased_params_and_extra_params %a)@]@ \
           @[<hov 1>(lets_to_introduce %a)@]@[<hov 1>(extra_args_for_aliases \
           %a)@]%a)@]"
          Variable.Set.print removed_aliased_params_and_extra_params
          (Variable.Lmap.print Simple.print)
          lets_to_introduce Variable.Set.print extra_args_for_aliases pp_wrapper
          recursive_continuation_wrapper0)
      t0
end

module Alias_result = struct
  type t =
    { aliases_kind : Flambda_kind.t Variable_.Map.t;
      continuation_parameters : Continuation_param_aliases.t Continuation.Map.t
    }

  (** val aliases_kind : t -> Flambda_kind.t Variable_.Map.t **)

  let aliases_kind t0 = t0.aliases_kind

  (** val continuation_parameters : t -> Continuation_param_aliases.t
      Continuation.Map.t **)

  let continuation_parameters t0 = t0.continuation_parameters

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let { aliases_kind = aliases_kind0;
          continuation_parameters = continuation_parameters0
        } =
      t0
    in
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(aliases_kind@ %a)@]@ @[<hov \
       1>(continuation_parameters@ %a)@])@]"
      (Variable.Map.print Flambda_kind.print)
      aliases_kind0
      (Continuation.Map.print Continuation_param_aliases.print)
      continuation_parameters0
end

module Mutable_unboxing_result = struct
  type t =
    { did_unbox_a_mutable_block : bool;
      additional_epa : Continuation_extra_params_and_args.t Continuation.Map.t;
      let_rewrites : Named_rewrite.t Named_rewrite_id.Map.t
    }

  (** val did_unbox_a_mutable_block : t -> bool **)

  let did_unbox_a_mutable_block t0 = t0.did_unbox_a_mutable_block

  (** val additional_epa : t -> Continuation_extra_params_and_args.t
      Continuation.Map.t **)

  let additional_epa t0 = t0.additional_epa

  (** val let_rewrites : t -> Named_rewrite.t Named_rewrite_id.Map.t **)

  let let_rewrites t0 = t0.let_rewrites

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let { did_unbox_a_mutable_block = did_unbox_a_mutable_block0;
          additional_epa = additional_epa0;
          let_rewrites = let_rewrites0
        } =
      t0
    in
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(did_unbox_a_mutable_block@ %b)@]@ @[<hov \
       1>(additional_epa@ %a)@]@ @[<hov 1>(let_rewrites@ %a)@])@]"
      did_unbox_a_mutable_block0
      (Continuation.Map.print Continuation_extra_params_and_args.print)
      additional_epa0
      (Named_rewrite_id.Map.print Named_rewrite.print)
      let_rewrites0
end

module Flow_result = struct
  type t =
    { data_flow_result : Data_flow_result.t;
      aliases_result : Alias_result.t;
      mutable_unboxing_result : Mutable_unboxing_result.t
    }

  (** val data_flow_result : t -> Data_flow_result.t **)

  let data_flow_result t0 = t0.data_flow_result

  (** val aliases_result : t -> Alias_result.t **)

  let aliases_result t0 = t0.aliases_result

  (** val mutable_unboxing_result : t -> Mutable_unboxing_result.t **)

  let mutable_unboxing_result t0 = t0.mutable_unboxing_result

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let { data_flow_result = data_flow_result0;
          aliases_result = aliases_result0;
          mutable_unboxing_result = mutable_unboxing_result0
        } =
      t0
    in
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(data_flow_result@ %a)@]@ @[<hov 1>(aliases_result@ \
       %a)@]@ @[<hov 1>(mutable_unboxing_result@ %a)@])@]"
      Data_flow_result.print data_flow_result0 Alias_result.print
      aliases_result0 Mutable_unboxing_result.print mutable_unboxing_result0
end
