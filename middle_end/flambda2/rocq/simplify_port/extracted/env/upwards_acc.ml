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
   middle_end/flambda2/rocq/simplify_port/env/Upwards_acc.v, which follows
   middle_end/flambda2/simplify/env/upwards_acc.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

module ART = Are_rebuilding_terms
module DA = Downwards_acc
module DE = Downwards_env
module LCS = Lifted_constant_state
module TE = Flambda2_types.Typing_env
module UE = Upwards_env
open Port_monad

type t =
  { uenv : Upwards_env.t;
    creation_dacc : Downwards_acc.t;
    lifted_constants : Lifted_constant_state.t;
    all_code : Exported_code.t;
    name_occurrences : Name_occurrences.t;
    cost_metrics : Cost_metrics.t;
    slot_offsets : Slot_offsets.t Or_unknown.t;
    flow_result : Flow_types.Flow_result.t;
    resimplify : bool
  }

(** val uenv : t -> Upwards_env.t **)

let uenv t0 = t0.uenv

(** val creation_dacc : t -> Downwards_acc.t **)

let creation_dacc t0 = t0.creation_dacc

(** val lifted_constants : t -> Lifted_constant_state.t **)

let lifted_constants t0 = t0.lifted_constants

(** val all_code : t -> Exported_code.t **)

let all_code t0 = t0.all_code

(** val name_occurrences : t -> Name_occurrences.t **)

let name_occurrences t0 = t0.name_occurrences

(** val cost_metrics : t -> Cost_metrics.t **)

let cost_metrics t0 = t0.cost_metrics

(** val slot_offsets : t -> Slot_offsets.t Or_unknown.t **)

let slot_offsets t0 = t0.slot_offsets

(** val flow_result : t -> Flow_types.Flow_result.t **)

let flow_result t0 = t0.flow_result

(** val resimplify : t -> bool **)

let resimplify t0 = t0.resimplify

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  let { uenv = uenv0;
        creation_dacc = _;
        lifted_constants = lifted_constants0;
        all_code = _;
        name_occurrences = name_occurrences0;
        cost_metrics = cost_metrics0;
        slot_offsets = slot_offsets0;
        flow_result = flow_result0;
        resimplify = resimplify0
      } =
    t0
  in
  Format.fprintf ppf
    "@[<hov 1>(@[<hov 1>(uenv@ %a)@]@ @[<hov 1>(lifted_constants@ %a)@]@ \
     @[<hov 1>(name_occurrences@ %a)@]@ @[<hov 1>(cost_metrics@ %a)@]@ @[<hov \
     1>(slot_offsets@ %a@)@]@ @[<hov 1>(flow_result@ %a)@]%a)@]"
    Upwards_env.print uenv0 Lifted_constant_state.print lifted_constants0
    Name_occurrences.print name_occurrences0 Cost_metrics.print cost_metrics0
    (Or_unknown.print Slot_offsets.print)
    slot_offsets0 Flow_types.Flow_result.print flow_result0
    (if resimplify0
     then fun ppf0 _ -> Format.fprintf ppf0 "@ @[<hov 1>(should_resimplify)@]"
     else fun _ _ -> ())
    ()

(** val create : Flow_types.Flow_result.t -> bool -> Upwards_env.t ->
    Downwards_acc.t -> t coq_M **)

let create flow_result0 compute_slot_offsets uenv0 dacc =
  let slot_offsets0 =
    if compute_slot_offsets
    then Or_unknown.Known Slot_offsets.empty
    else Or_unknown.Unknown
  in
  { uenv = uenv0;
    creation_dacc = dacc;
    lifted_constants = Lifted_constant_state.empty;
    all_code = Exported_code.empty;
    name_occurrences = Name_occurrences.empty;
    cost_metrics = Cost_metrics.zero;
    slot_offsets = slot_offsets0;
    flow_result = flow_result0;
    resimplify = false
  }

(** val code_age_relation : t -> Flambda2_types.Code_age_relation.t coq_M **)

let code_age_relation t0 =
  Flambda2_types.Typing_env.code_age_relation
    (Downwards_acc.typing_env t0.creation_dacc)

(** val get_and_clear_lifted_constants : t -> (t * Lifted_constant_state.t)
    coq_M **)

let get_and_clear_lifted_constants t0 =
  ( { uenv = t0.uenv;
      creation_dacc = t0.creation_dacc;
      lifted_constants = Lifted_constant_state.empty;
      all_code = t0.all_code;
      name_occurrences = t0.name_occurrences;
      cost_metrics = t0.cost_metrics;
      slot_offsets = t0.slot_offsets;
      flow_result = t0.flow_result;
      resimplify = t0.resimplify
    },
    t0.lifted_constants )

(** val add_lifted_constant : t -> Lifted_constant.t -> t coq_M **)

let add_lifted_constant t0 const =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = Lifted_constant_state.add t0.lifted_constants const;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val are_rebuilding_terms : t -> Are_rebuilding_terms.t coq_M **)

let are_rebuilding_terms t0 =
  Downwards_env.are_rebuilding_terms (Downwards_acc.denv t0.creation_dacc)

(** val with_lifted_constants : t -> Lifted_constant_state.t -> t coq_M **)

let with_lifted_constants t0 lifted_constants0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = lifted_constants0;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val no_lifted_constants : t -> bool coq_M **)

let no_lifted_constants t0 = Lifted_constant_state.is_empty t0.lifted_constants

(** val map_uenv : t -> (Upwards_env.t -> Upwards_env.t coq_M) -> t coq_M **)

let map_uenv t0 f =
  { uenv = f t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val with_uenv : t -> Upwards_env.t -> t coq_M **)

let with_uenv t0 uenv0 =
  { uenv = uenv0;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val remember_code_for_cmx : t -> Code.t Code_id.Map.t -> t coq_M **)

let remember_code_for_cmx t0 code =
  if Are_rebuilding_terms.do_not_rebuild_terms (are_rebuilding_terms t0)
  then t0
  else
    let keep_code =
     fun code_id ->
      Code_id.Set.mem code_id
        (Downwards_acc.code_ids_to_remember t0.creation_dacc)
    in
    let all_code0 = Exported_code.add_code keep_code code t0.all_code in
    { uenv = t0.uenv;
      creation_dacc = t0.creation_dacc;
      lifted_constants = t0.lifted_constants;
      all_code = all_code0;
      name_occurrences = t0.name_occurrences;
      cost_metrics = t0.cost_metrics;
      slot_offsets = t0.slot_offsets;
      flow_result = t0.flow_result;
      resimplify = t0.resimplify
    }

(** val with_name_occurrences : t -> Name_occurrences.t -> t coq_M **)

let with_name_occurrences t0 name_occurrences0 =
  if name_occurrences0 == t0.name_occurrences
  then t0
  else
    { uenv = t0.uenv;
      creation_dacc = t0.creation_dacc;
      lifted_constants = t0.lifted_constants;
      all_code = t0.all_code;
      name_occurrences = name_occurrences0;
      cost_metrics = t0.cost_metrics;
      slot_offsets = t0.slot_offsets;
      flow_result = t0.flow_result;
      resimplify = t0.resimplify
    }

(** val clear_name_occurrences : t -> t coq_M **)

let clear_name_occurrences t0 = with_name_occurrences t0 Name_occurrences.empty

(** val add_free_names : t -> Name_occurrences.t -> t coq_M **)

let add_free_names t0 free_names =
  let name_occurrences0 =
    Name_occurrences.union t0.name_occurrences free_names
  in
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = name_occurrences0;
    cost_metrics = t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val used_value_slots : t -> Name_occurrences.t coq_M **)

let used_value_slots t0 = Downwards_acc.used_value_slots t0.creation_dacc

(** val shareable_constants : t -> Symbol.t Static_const.Map.t coq_M **)

let shareable_constants t0 = Downwards_acc.shareable_constants t0.creation_dacc

(** val remove_all_occurrences_of_free_names : t -> Name_occurrences.t -> t
    coq_M **)

let remove_all_occurrences_of_free_names t0 to_remove =
  let name_occurrences0 = Name_occurrences.diff t0.name_occurrences to_remove in
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = name_occurrences0;
    cost_metrics = t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val clear_cost_metrics : t -> t coq_M **)

let clear_cost_metrics t0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = Cost_metrics.zero;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val with_cost_metrics : Cost_metrics.t -> t -> t coq_M **)

let with_cost_metrics cost_metrics0 t0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = cost_metrics0;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val notify_added : Code_size.t -> t -> t coq_M **)

let notify_added code_size t0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = Cost_metrics.notify_added code_size t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val notify_removed : Removed_operations.t -> t -> t coq_M **)

let notify_removed operation t0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = Cost_metrics.notify_removed operation t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val add_cost_metrics : Cost_metrics.t -> t -> t coq_M **)

let add_cost_metrics cost_metrics0 t0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = Cost_metrics.( + ) t0.cost_metrics cost_metrics0;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val add_cost_metrics_and_with_name_occurrences : t -> Cost_metrics.t ->
    Name_occurrences.t -> t coq_M **)

let add_cost_metrics_and_with_name_occurrences t0 cost_metrics0
    name_occurrences0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = name_occurrences0;
    cost_metrics = Cost_metrics.( + ) t0.cost_metrics cost_metrics0;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val generate_phantom_lets : t -> bool coq_M **)

let generate_phantom_lets t0 =
  Downwards_env.generate_phantom_lets (Downwards_acc.denv t0.creation_dacc)

(** val is_demoted_exn_handler : t -> Continuation.t -> bool coq_M **)

let is_demoted_exn_handler t0 cont =
  Continuation.Set.mem cont
    (Downwards_acc.demoted_exn_handlers t0.creation_dacc)

(** val with_slot_offsets : t -> Slot_offsets.t Or_unknown.t -> t coq_M **)

let with_slot_offsets t0 slot_offsets0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = t0.cost_metrics;
    slot_offsets = slot_offsets0;
    flow_result = t0.flow_result;
    resimplify = t0.resimplify
  }

(** val required_names : t -> Name.Set.t coq_M **)

let required_names t0 =
  t0.flow_result.Flow_types.Flow_result.data_flow_result
    .Flow_types.Data_flow_result.required_names

(** val reachable_code_ids : t -> Flow_types.Reachable_code_ids.t Or_unknown.t
    coq_M **)

let reachable_code_ids t0 =
  t0.flow_result.Flow_types.Flow_result.data_flow_result
    .Flow_types.Data_flow_result.reachable_code_ids

(** val continuation_param_aliases : t -> Flow_types.Alias_result.t coq_M **)

let continuation_param_aliases t0 =
  t0.flow_result.Flow_types.Flow_result.aliases_result

(** val mutable_unboxing_result : t -> Flow_types.Mutable_unboxing_result.t
    coq_M **)

let mutable_unboxing_result t0 =
  t0.flow_result.Flow_types.Flow_result.mutable_unboxing_result

(** val set_resimplify : t -> t coq_M **)

let set_resimplify t0 =
  { uenv = t0.uenv;
    creation_dacc = t0.creation_dacc;
    lifted_constants = t0.lifted_constants;
    all_code = t0.all_code;
    name_occurrences = t0.name_occurrences;
    cost_metrics = t0.cost_metrics;
    slot_offsets = t0.slot_offsets;
    flow_result = t0.flow_result;
    resimplify = true
  }

(** val specialization_map : t -> Continuation.t Apply_cont_rewrite_id.Map.t
    Continuation.Map.t coq_M **)

let specialization_map t0 = Downwards_acc.specialization_map t0.creation_dacc
