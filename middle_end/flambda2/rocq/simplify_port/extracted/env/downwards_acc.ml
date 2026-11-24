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
   middle_end/flambda2/rocq/simplify_port/env/Downwards_acc.v, which follows
   middle_end/flambda2/simplify/env/downwards_acc.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

module CUE = Continuation_uses_env
module DE = Downwards_env
module LCS = Lifted_constant_state
module TE = Flambda2_types.Typing_env
open Port_monad

type t =
  { denv : Downwards_env.t;
    continuation_uses_env : Continuation_uses_env.t;
    shareable_constants : Symbol.t Static_const.Map.t;
    used_value_slots : Name_occurrences.t;
    lifted_constants : Lifted_constant_state.t;
    flow_acc : Flow.Acc.t;
    demoted_exn_handlers : Continuation.Set.t;
    code_ids_to_remember : Code_id.Set.t;
    code_ids_to_never_delete : Code_id.Set.t;
    code_ids_never_simplified : Code_id.Set.t;
    slot_offsets : Slot_offsets.t Code_id.Map.t;
    debuginfo_rewrites : Debuginfo.t Simple.Map.t;
    are_lifting_conts : Are_lifting_conts.t;
    lifted_continuations : (Downwards_env.t * Original_handlers.t) list;
    continuation_lifting_budget : int;
    continuations_to_specialize : Continuation.Set.t;
    specialization_map : Continuation.t Continuation_callsite_map.t
  }

(** val denv : t -> Downwards_env.t **)

let denv t0 = t0.denv

(** val continuation_uses_env : t -> Continuation_uses_env.t **)

let continuation_uses_env t0 = t0.continuation_uses_env

(** val shareable_constants : t -> Symbol.t Static_const.Map.t **)

let shareable_constants t0 = t0.shareable_constants

(** val used_value_slots : t -> Name_occurrences.t **)

let used_value_slots t0 = t0.used_value_slots

(** val lifted_constants : t -> Lifted_constant_state.t **)

let lifted_constants t0 = t0.lifted_constants

(** val flow_acc : t -> Flow.Acc.t **)

let flow_acc t0 = t0.flow_acc

(** val demoted_exn_handlers : t -> Continuation.Set.t **)

let demoted_exn_handlers t0 = t0.demoted_exn_handlers

(** val code_ids_to_remember : t -> Code_id.Set.t **)

let code_ids_to_remember t0 = t0.code_ids_to_remember

(** val code_ids_to_never_delete : t -> Code_id.Set.t **)

let code_ids_to_never_delete t0 = t0.code_ids_to_never_delete

(** val code_ids_never_simplified : t -> Code_id.Set.t **)

let code_ids_never_simplified t0 = t0.code_ids_never_simplified

(** val slot_offsets : t -> Slot_offsets.t Code_id.Map.t **)

let slot_offsets t0 = t0.slot_offsets

(** val debuginfo_rewrites : t -> Debuginfo.t Simple.Map.t **)

let debuginfo_rewrites t0 = t0.debuginfo_rewrites

(** val are_lifting_conts : t -> Are_lifting_conts.t **)

let are_lifting_conts t0 = t0.are_lifting_conts

(** val lifted_continuations : t -> (Downwards_env.t * Original_handlers.t) list
    **)

let lifted_continuations t0 = t0.lifted_continuations

(** val continuation_lifting_budget : t -> int **)

let continuation_lifting_budget t0 = t0.continuation_lifting_budget

(** val continuations_to_specialize : t -> Continuation.Set.t **)

let continuations_to_specialize t0 = t0.continuations_to_specialize

(** val specialization_map : t -> Continuation.t Continuation_callsite_map.t **)

let specialization_map t0 = t0.specialization_map

(** val print_lifted_cont : Format.formatter -> (Downwards_env.t *
    Original_handlers.t) -> unit coq_M **)

let print_lifted_cont ppf = function
  | denv0, original_handlers ->
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(denv %a)@]@ @[<hov 1>(original_handlers %a)@])@]"
      Downwards_env.print denv0 Original_handlers.print original_handlers

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  let { denv = denv0;
        continuation_uses_env = continuation_uses_env0;
        shareable_constants = shareable_constants0;
        used_value_slots = used_value_slots0;
        lifted_constants = lifted_constants0;
        flow_acc = flow_acc0;
        demoted_exn_handlers = demoted_exn_handlers0;
        code_ids_to_remember = code_ids_to_remember0;
        code_ids_to_never_delete = code_ids_to_never_delete0;
        code_ids_never_simplified = code_ids_never_simplified0;
        slot_offsets = slot_offsets0;
        debuginfo_rewrites = debuginfo_rewrites0;
        are_lifting_conts = are_lifting_conts0;
        lifted_continuations = lifted_continuations0;
        continuation_lifting_budget = continuation_lifting_budget0;
        continuations_to_specialize = continuations_to_specialize0;
        specialization_map = specialization_map0
      } =
    t0
  in
  Format.fprintf ppf
    "@[<hov 1>(@[<hov 1>(denv@ %a)@]@ @[<hov 1>(continuation_uses_env@ %a)@]@ \
     @[<hov 1>(shareable_constants@ %a)@]@ @[<hov 1>(used_value_slots@ %a)@]@ \
     @[<hov 1>(lifted_constant_state@ %a)@]@ @[<hov 1>(flow_acc@ %a)@]@ @[<hov \
     1>(demoted_exn_handlers@ %a)@]@ @[<hov 1>(code_ids_to_remember@ %a)@]@ \
     @[<hov 1>(code_ids_to_never_delete@ %a)@]@ @[<hov \
     1>(code_ids_never_simplified@ %a)@]@ @[<hov 1>(slot_offsets@ %a)@ @[<hov \
     1>(debuginfo_rewrites@ %a)@]@ @[<hov 1>(are_lifting_conts@ %a)@]@ @[<hov \
     1>(lifted_continuations@ %a)@]@ @[<hov 1>(continuation_lifting_budget \
     %d)@]@ @[<hov 1>(continuations_to_specialize %a)@]@ @[<hov \
     1>(specialization_map %a)@])@]"
    Downwards_env.print denv0 Continuation_uses_env.print continuation_uses_env0
    (Static_const.Map.print Symbol.print)
    shareable_constants0 Name_occurrences.print used_value_slots0
    Lifted_constant_state.print lifted_constants0 Flow.Acc.print flow_acc0
    Continuation.Set.print demoted_exn_handlers0 Code_id.Set.print
    code_ids_to_remember0 Code_id.Set.print code_ids_to_never_delete0
    Code_id.Set.print code_ids_never_simplified0
    (Code_id.Map.print Slot_offsets.print)
    slot_offsets0
    (Simple.Map.print Debuginfo.print_compact)
    debuginfo_rewrites0 Are_lifting_conts.print are_lifting_conts0
    ((fun x__1 x__2 x__3 x__4 ->
       Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
       (Some Format.pp_print_space) print_lifted_cont)
    lifted_continuations0 continuation_lifting_budget0 Continuation.Set.print
    continuations_to_specialize0
    (Continuation.Map.print
       (Apply_cont_rewrite_id.Map.print Continuation.print))
    specialization_map0

(** val create : Downwards_env.t -> Slot_offsets.t Code_id.Map.t ->
    Continuation_uses_env.t -> t coq_M **)

let create denv0 slot_offsets0 continuation_uses_env0 =
  let continuation_lifting_budget0 =
    Flambda_features.Expert.cont_lifting_budget ()
  in
  let are_lifting_conts0 =
    Are_lifting_conts.no_lifting Are_lifting_conts.At_toplevel
  in
  let flow_acc0 = Flow.Acc.empty () in
  { denv = denv0;
    continuation_uses_env = continuation_uses_env0;
    shareable_constants = Static_const.Map.empty;
    used_value_slots = Name_occurrences.empty;
    lifted_constants = Lifted_constant_state.empty;
    flow_acc = flow_acc0;
    demoted_exn_handlers = Continuation.Set.empty;
    code_ids_to_remember = Code_id.Set.empty;
    code_ids_to_never_delete = Code_id.Set.empty;
    code_ids_never_simplified = Code_id.Set.empty;
    slot_offsets = slot_offsets0;
    debuginfo_rewrites = Simple.Map.empty;
    are_lifting_conts = are_lifting_conts0;
    lifted_continuations = [];
    continuation_lifting_budget = continuation_lifting_budget0;
    continuations_to_specialize = Continuation.Set.empty;
    specialization_map = Continuation.Map.empty
  }

(** val with_flow_acc : Flow.Acc.t -> t -> t coq_M **)

let with_flow_acc flow_acc0 t0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = flow_acc0;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val map_flow_acc : t -> (Flow.Acc.t -> Flow.Acc.t coq_M) -> t coq_M **)

let map_flow_acc t0 f =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = f t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val map_denv : t -> (Downwards_env.t -> Downwards_env.t coq_M) -> t coq_M **)

let map_denv t0 f =
  { denv = f t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val with_denv : t -> Downwards_env.t -> t coq_M **)

let with_denv t0 denv0 =
  { denv = denv0;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val with_continuation_uses_env : t -> Continuation_uses_env.t -> t coq_M **)

let with_continuation_uses_env t0 cont_uses_env =
  { denv = t0.denv;
    continuation_uses_env = cont_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val record_continuation : t -> Continuation.t -> [ `Unarized ]
    Flambda_arity.t -> t coq_M **)

let record_continuation t0 cont arity =
  let cont_uses_env =
    Continuation_uses_env.record_continuation t0.continuation_uses_env cont
      arity
  in
  with_continuation_uses_env t0 cont_uses_env

(** val record_continuation_use : t -> Continuation.t -> Continuation_use_kind.t
    -> Downwards_env.t -> Flambda2_types.t list -> (t * Apply_cont_rewrite_id.t)
    coq_M **)

let record_continuation_use t0 cont use_kind env_at_use arg_types =
  let cont_uses_env, id =
    Continuation_uses_env.record_continuation_use t0.continuation_uses_env cont
      use_kind env_at_use arg_types
  in
  with_continuation_uses_env t0 cont_uses_env, id

(** val delete_continuation_uses : t -> Continuation.t -> t coq_M **)

let delete_continuation_uses t0 cont =
  let cont_uses_env =
    Continuation_uses_env.delete_continuation_uses t0.continuation_uses_env cont
  in
  with_continuation_uses_env t0 cont_uses_env

(** val num_continuation_uses : t -> Continuation.t -> int coq_M **)

let num_continuation_uses t0 cont =
  Continuation_uses_env.num_continuation_uses t0.continuation_uses_env cont

(** val code_age_relation : t -> Flambda2_types.Code_age_relation.t coq_M **)

let code_age_relation t0 =
  Flambda2_types.Typing_env.code_age_relation (Downwards_env.typing_env t0.denv)

(** val with_code_age_relation : t -> Flambda2_types.Code_age_relation.t -> t
    coq_M **)

let with_code_age_relation t0 code_age_relation0 =
  let typing_env0 =
    Flambda2_types.Typing_env.with_code_age_relation
      (Downwards_env.typing_env t0.denv)
      code_age_relation0
  in
  with_denv t0 (Downwards_env.with_typing_env t0.denv typing_env0)

(** val typing_env : t -> Flambda2_types.Typing_env.t coq_M **)

let typing_env t0 = Downwards_env.typing_env t0.denv

(** val add_variable : t -> Bound_var.t -> Flambda2_types.t -> t coq_M **)

let add_variable t0 var ty =
  with_denv t0 (Downwards_env.add_variable t0.denv var ty)

(** val get_typing_env_no_more_than_one_use : t -> Continuation.t ->
    Flambda2_types.Typing_env.t option coq_M **)

let get_typing_env_no_more_than_one_use t0 k =
  Continuation_uses_env.get_typing_env_no_more_than_one_use
    t0.continuation_uses_env k

(** val add_to_lifted_constant_accumulator : unit option -> t ->
    Lifted_constant_state.t -> t coq_M **)

let add_to_lifted_constant_accumulator also_add_to_env t0 constants =
  let also_add_to_env0 =
    match also_add_to_env with
    | Some u ->
      let () = u in
      true
    | None -> false
  in
  let lifted_constants0 =
    Lifted_constant_state.union t0.lifted_constants constants
  in
  let denv0 =
    if also_add_to_env0
    then
      (fun x__1 x__2 x__3 ->
        Downwards_env.add_lifted_constant_state ?maybe_already_defined:x__1 x__2
          x__3)
        None t0.denv constants
    else t0.denv
  in
  { denv = denv0;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = lifted_constants0;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val get_lifted_constants : t -> Lifted_constant_state.t coq_M **)

let get_lifted_constants t0 = t0.lifted_constants

(** val clear_lifted_constants : t -> t coq_M **)

let clear_lifted_constants t0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = Lifted_constant_state.empty;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val no_lifted_constants : t -> bool coq_M **)

let no_lifted_constants t0 = Lifted_constant_state.is_empty t0.lifted_constants

(** val get_and_clear_lifted_constants : t -> (t * Lifted_constant_state.t)
    coq_M **)

let get_and_clear_lifted_constants t0 =
  let constants = t0.lifted_constants in
  let t1 = clear_lifted_constants t0 in
  t1, constants

(** val set_lifted_constants : t -> Lifted_constant_state.t -> t coq_M **)

let set_lifted_constants t0 consts =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = consts;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val find_shareable_constant : t -> Static_const.t -> Symbol.t option coq_M **)

let find_shareable_constant t0 static_const =
  Static_const.Map.find_opt static_const t0.shareable_constants

(** val consider_constant_for_sharing : t -> Symbol.t -> Static_const.t -> t
    coq_M **)

let consider_constant_for_sharing t0 symbol static_const =
  if not (Static_const.can_share static_const)
  then t0
  else
    { denv = t0.denv;
      continuation_uses_env = t0.continuation_uses_env;
      shareable_constants =
        Static_const.Map.add static_const symbol t0.shareable_constants;
      used_value_slots = t0.used_value_slots;
      lifted_constants = t0.lifted_constants;
      flow_acc = t0.flow_acc;
      demoted_exn_handlers = t0.demoted_exn_handlers;
      code_ids_to_remember = t0.code_ids_to_remember;
      code_ids_to_never_delete = t0.code_ids_to_never_delete;
      code_ids_never_simplified = t0.code_ids_never_simplified;
      slot_offsets = t0.slot_offsets;
      debuginfo_rewrites = t0.debuginfo_rewrites;
      are_lifting_conts = t0.are_lifting_conts;
      lifted_continuations = t0.lifted_continuations;
      continuation_lifting_budget = t0.continuation_lifting_budget;
      continuations_to_specialize = t0.continuations_to_specialize;
      specialization_map = t0.specialization_map
    }

(** val with_shareable_constants : t -> Symbol.t Static_const.Map.t -> t coq_M **)

let with_shareable_constants t0 shareable_constants0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = shareable_constants0;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val add_use_of_value_slot : t -> Value_slot.t -> t coq_M **)

let add_use_of_value_slot t0 value_slot =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots =
      Name_occurrences.add_value_slot_in_projection t0.used_value_slots
        value_slot Name_mode.normal;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val all_continuations_used : t -> Continuation.Set.t coq_M **)

let all_continuations_used t0 =
  Continuation_uses_env.all_continuations_used t0.continuation_uses_env

(** val with_used_value_slots : t -> Name_occurrences.t -> t coq_M **)

let with_used_value_slots t0 used_value_slots0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = used_value_slots0;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val add_code_ids_to_remember : t -> Code_id.Set.t -> t coq_M **)

let add_code_ids_to_remember t0 code_ids =
  if Downwards_env.at_unit_toplevel t0.denv
  then t0
  else
    { denv = t0.denv;
      continuation_uses_env = t0.continuation_uses_env;
      shareable_constants = t0.shareable_constants;
      used_value_slots = t0.used_value_slots;
      lifted_constants = t0.lifted_constants;
      flow_acc = t0.flow_acc;
      demoted_exn_handlers = t0.demoted_exn_handlers;
      code_ids_to_remember = Code_id.Set.union code_ids t0.code_ids_to_remember;
      code_ids_to_never_delete = t0.code_ids_to_never_delete;
      code_ids_never_simplified = t0.code_ids_never_simplified;
      slot_offsets = t0.slot_offsets;
      debuginfo_rewrites = t0.debuginfo_rewrites;
      are_lifting_conts = t0.are_lifting_conts;
      lifted_continuations = t0.lifted_continuations;
      continuation_lifting_budget = t0.continuation_lifting_budget;
      continuations_to_specialize = t0.continuations_to_specialize;
      specialization_map = t0.specialization_map
    }

(** val with_code_ids_to_remember : t -> Code_id.Set.t -> t coq_M **)

let with_code_ids_to_remember t0 code_ids_to_remember0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = code_ids_to_remember0;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val add_code_ids_to_never_delete : t -> Code_id.Set.t -> t coq_M **)

let add_code_ids_to_never_delete t0 code_ids =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete =
      Code_id.Set.union code_ids t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val with_code_ids_to_never_delete : t -> Code_id.Set.t -> t coq_M **)

let with_code_ids_to_never_delete t0 code_ids_to_never_delete0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = code_ids_to_never_delete0;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val add_code_ids_never_simplified : t -> Code_id.Set.t -> t coq_M **)

let add_code_ids_never_simplified t0 old_code_ids =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified =
      Code_id.Set.union old_code_ids t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val with_code_ids_never_simplified : t -> Code_id.Set.t -> t coq_M **)

let with_code_ids_never_simplified t0 code_ids_never_simplified0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = code_ids_never_simplified0;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val are_rebuilding_terms : t -> Are_rebuilding_terms.t coq_M **)

let are_rebuilding_terms t0 = Downwards_env.are_rebuilding_terms t0.denv

(** val demote_exn_handler : t -> Continuation.t -> t coq_M **)

let demote_exn_handler t0 cont =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = Continuation.Set.add cont t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val with_slot_offsets : t -> Slot_offsets.t Code_id.Map.t -> t coq_M **)

let with_slot_offsets t0 slot_offsets0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = slot_offsets0;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val find_debuginfo_rewrite : t -> Simple.t -> Debuginfo.t option coq_M **)

let find_debuginfo_rewrite t0 bound_to =
  Simple.Map.find_opt bound_to t0.debuginfo_rewrites

(** val merge_debuginfo_rewrite : t -> Simple.t -> Debuginfo.t -> t coq_M **)

let merge_debuginfo_rewrite t0 bound_to dbg =
  let dbg0 =
    match find_debuginfo_rewrite t0 bound_to with
    | Some earlier_dbg -> Debuginfo.merge earlier_dbg dbg
    | None -> dbg
  in
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = Simple.Map.add bound_to dbg0 t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val with_are_lifting_conts : t -> Are_lifting_conts.t -> t coq_M **)

let with_are_lifting_conts t0 are_lifting_conts0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = are_lifting_conts0;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val get_and_clear_lifted_continuations : t -> (t * (Downwards_env.t *
    Original_handlers.t) list) coq_M **)

let get_and_clear_lifted_continuations t0 =
  ( { denv = t0.denv;
      continuation_uses_env = t0.continuation_uses_env;
      shareable_constants = t0.shareable_constants;
      used_value_slots = t0.used_value_slots;
      lifted_constants = t0.lifted_constants;
      flow_acc = t0.flow_acc;
      demoted_exn_handlers = t0.demoted_exn_handlers;
      code_ids_to_remember = t0.code_ids_to_remember;
      code_ids_to_never_delete = t0.code_ids_to_never_delete;
      code_ids_never_simplified = t0.code_ids_never_simplified;
      slot_offsets = t0.slot_offsets;
      debuginfo_rewrites = t0.debuginfo_rewrites;
      are_lifting_conts = t0.are_lifting_conts;
      lifted_continuations = [];
      continuation_lifting_budget = t0.continuation_lifting_budget;
      continuations_to_specialize = t0.continuations_to_specialize;
      specialization_map = t0.specialization_map
    },
    t0.lifted_continuations )

(** val add_lifted_continuation : Downwards_env.t -> Original_handlers.t -> t ->
    t coq_M **)

let add_lifted_continuation denv0 original_handlers t0 =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = (denv0, original_handlers) :: t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val get_continuation_lifting_budget : t -> int coq_M **)

let get_continuation_lifting_budget t0 =
  let budget = t0.continuation_lifting_budget in
  if budget < 0 then max_int else budget

(** val with_continuation_lifting_budget : t -> int -> t coq_M **)

let with_continuation_lifting_budget t0 budget =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val reset_continuation_lifting_budget : t -> t coq_M **)

let reset_continuation_lifting_budget t0 =
  with_continuation_lifting_budget t0
    (Flambda_features.Expert.cont_lifting_budget ())

(** val decrease_continuation_lifting_budget : t -> int -> t coq_M **)

let decrease_continuation_lifting_budget t0 cost =
  if t0.continuation_lifting_budget < 0
  then t0
  else
    with_continuation_lifting_budget t0
      (max 0 (t0.continuation_lifting_budget - cost))

(** val prepare_for_speculative_inlining : t -> t coq_M **)

let prepare_for_speculative_inlining dacc =
  let dacc0 =
    map_denv dacc (fun denv0 ->
        Downwards_env.set_do_not_rebuild_terms_and_disable_inlining denv0
          Downwards_env.Disable_inlining_reason.Speculative_inlining)
  in
  with_are_lifting_conts dacc0
    (Are_lifting_conts.no_lifting Are_lifting_conts.In_speculative_inlining)

(** val add_continuation_to_specialize : t -> Continuation.t -> t coq_M **)

let add_continuation_to_specialize t0 cont =
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize =
      Continuation.Set.add cont t0.continuations_to_specialize;
    specialization_map = t0.specialization_map
  }

(** val add_specialization : t -> Apply_cont_rewrite_id.t -> Continuation.t ->
    Continuation.t -> t coq_M **)

let add_specialization t0 id old specialized =
  let specialization_map0 =
    Continuation_callsite_map.add old id specialized t0.specialization_map
  in
  { denv = t0.denv;
    continuation_uses_env = t0.continuation_uses_env;
    shareable_constants = t0.shareable_constants;
    used_value_slots = t0.used_value_slots;
    lifted_constants = t0.lifted_constants;
    flow_acc = t0.flow_acc;
    demoted_exn_handlers = t0.demoted_exn_handlers;
    code_ids_to_remember = t0.code_ids_to_remember;
    code_ids_to_never_delete = t0.code_ids_to_never_delete;
    code_ids_never_simplified = t0.code_ids_never_simplified;
    slot_offsets = t0.slot_offsets;
    debuginfo_rewrites = t0.debuginfo_rewrites;
    are_lifting_conts = t0.are_lifting_conts;
    lifted_continuations = t0.lifted_continuations;
    continuation_lifting_budget = t0.continuation_lifting_budget;
    continuations_to_specialize = t0.continuations_to_specialize;
    specialization_map = specialization_map0
  }

let add_to_lifted_constant_accumulator ?also_add_to_env t constants =
  add_to_lifted_constant_accumulator also_add_to_env t constants
