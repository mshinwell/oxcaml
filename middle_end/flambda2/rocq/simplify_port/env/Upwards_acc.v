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

(* This file follows middle_end/flambda2/simplify/env/upwards_acc.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition under
   the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries
   [tmpN] and their order, the arguments by place, a setter [update_f] where
   the compiler writes [{ t with f }]) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Are_rebuilding_terms
  Code Code_id Code_size Continuation Cost_metrics Downwards_acc
  Downwards_env Exported_code Flambda2_types Flow_types Format
  Lifted_constant Lifted_constant_state Name Name_occurrences Or_unknown
  Removed_operations Slot_offsets Static_const Symbol Upwards_env.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17-22 *)
From SimplifyPort.abbrev.upwards_acc Require Import Port_abbreviations.
(*OCAML
module ART = Are_rebuilding_terms
module DA = Downwards_acc
module DE = Downwards_env
module LCS = Lifted_constant_state
module TE = Flambda2_types.Typing_env
module UE = Upwards_env
OCAML*)

(* 24-34 *)
Record t : Type :=
  { uenv : UE.t;
    creation_dacc : DA.t;
    lifted_constants : LCS.t;
    all_code : Exported_code.t;
    name_occurrences : Name_occurrences.t;
    cost_metrics : Cost_metrics.t;
    slot_offsets : Or_unknown.t Slot_offsets.t;
    flow_result : Flow_types.Flow_result.t;
    resimplify : bool
  }.

(* 36-58 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept, and
   the record pattern of the parameter is a match. *)
Definition print (ppf : Format.formatter) (t : Upwards_acc.t) : M unit :=
  match t with
  | {| uenv := uenv;
       creation_dacc := _;
       lifted_constants := lifted_constants;
       all_code := _;
       name_occurrences := name_occurrences;
       cost_metrics := cost_metrics;
       slot_offsets := slot_offsets;
       flow_result := flow_result;
       resimplify := resimplify
    |} =>
    let! tmp1 := papp1 Or_unknown.print Slot_offsets.print in
    Format.fprintf14 ppf
      "@[<hov 1>(@[<hov 1>(uenv@ %a)@]@ @[<hov 1>(lifted_constants@ %a)@]@ @[<hov 1>(name_occurrences@ %a)@]@ @[<hov 1>(cost_metrics@ %a)@]@ @[<hov 1>(slot_offsets@ %a@)@]@ @[<hov 1>(flow_result@ %a)@]%a)@]"
      UE.print uenv LCS.print lifted_constants Name_occurrences.print
      name_occurrences Cost_metrics.print cost_metrics tmp1 slot_offsets
      Flow_types.Flow_result.print flow_result
      (if resimplify
       then
         fun (ppf : Format.formatter) (_ : unit) =>
         Format.fprintf0 ppf "@ @[<hov 1>(should_resimplify)@]"
       else fun (_ppf : Format.formatter) (_ : unit) => ret tt)
      tt
  end.

(* 60-77 *)
Definition create (flow_result : Flow_types.Flow_result.t)
    (compute_slot_offsets : bool) (uenv : UE.t) (dacc : DA.t)
    : M Upwards_acc.t :=
  let& slot_offsets :=
    if compute_slot_offsets
    then Or_unknown.Known Slot_offsets.empty
    else Or_unknown.Unknown
  in
  ret
    {| uenv := uenv;
       creation_dacc := dacc;
       lifted_constants := LCS.empty;
       all_code := Exported_code.empty;
       name_occurrences := Name_occurrences.empty;
       (* [used_value_slots] must be kept separate from the normal free names
          tracking in [name_occurrences], since it is always accumulated, and
          never saved and restored (like free name information is when
          dealing with a [Let_cont]). *)
       cost_metrics := Cost_metrics.zero;
       slot_offsets := slot_offsets;
       flow_result := flow_result;
       resimplify := false
    |}.

(* PORT-GAP(loose): 79 and 81, [creation_dacc] and [uenv] are the
   projections of the record [t] under these names: they are pure in Rocq,
   and Rocq prints each as [let f t = t.f] after the type. The same holds of
   [lifted_constants] (85), [cost_metrics] (93), [all_code] (115),
   [name_occurrences] (117), [slot_offsets] (167) and [resimplify] (181). *)

(* 83 *)
Definition code_age_relation (t : Upwards_acc.t)
    : M Flambda2_types.Code_age_relation.t :=
  let! tmp1 := DA.typing_env t.(creation_dacc) in
  TE.code_age_relation tmp1.

(* 88, 91 and 97. [{ t with lifted_constants }]. *)
Definition update_lifted_constants (t : Upwards_acc.t)
    (lifted_constants : LCS.t) : Upwards_acc.t :=
  {| uenv := t.(uenv);
     creation_dacc := t.(creation_dacc);
     lifted_constants := lifted_constants;
     all_code := t.(all_code);
     name_occurrences := t.(name_occurrences);
     cost_metrics := t.(cost_metrics);
     slot_offsets := t.(slot_offsets);
     flow_result := t.(flow_result);
     resimplify := t.(resimplify)
  |}.
Extract Inlined Constant update_lifted_constants =>
  "(fun t lifted_constants -> { t with lifted_constants = lifted_constants })".

(* 87-88 *)
Definition get_and_clear_lifted_constants (t : Upwards_acc.t)
    : M (Upwards_acc.t * LCS.t) :=
  ret (update_lifted_constants t LCS.empty, t.(lifted_constants)).

(* 90-91 *)
Definition add_lifted_constant (t : Upwards_acc.t) (const : Lifted_constant.t)
    : M Upwards_acc.t :=
  let! tmp1 := LCS.add t.(lifted_constants) const in
  ret (update_lifted_constants t tmp1).

(* 95 *)
Definition are_rebuilding_terms (t : Upwards_acc.t) : M ART.t :=
  let! tmp1 := DA.denv t.(creation_dacc) in
  DE.are_rebuilding_terms tmp1.

(* 97 *)
Definition with_lifted_constants (t : Upwards_acc.t) (lifted_constants : LCS.t)
    : M Upwards_acc.t :=
  ret (update_lifted_constants t lifted_constants).

(* 99 *)
Definition no_lifted_constants (t : Upwards_acc.t) : M bool :=
  LCS.is_empty t.(lifted_constants).

(* 101 and 103. [{ t with uenv }]. *)
Definition update_uenv (t : Upwards_acc.t) (uenv : UE.t) : Upwards_acc.t :=
  {| uenv := uenv;
     creation_dacc := t.(creation_dacc);
     lifted_constants := t.(lifted_constants);
     all_code := t.(all_code);
     name_occurrences := t.(name_occurrences);
     cost_metrics := t.(cost_metrics);
     slot_offsets := t.(slot_offsets);
     flow_result := t.(flow_result);
     resimplify := t.(resimplify)
  |}.
Extract Inlined Constant update_uenv =>
  "(fun t uenv -> { t with uenv = uenv })".

(* 101 *)
Definition map_uenv (t : Upwards_acc.t) (f : UE.t -> M UE.t)
    : M Upwards_acc.t :=
  let! tmp1 := f t.(uenv) in
  ret (update_uenv t tmp1).

(* 103 *)
Definition with_uenv (t : Upwards_acc.t) (uenv : UE.t) : M Upwards_acc.t :=
  ret (update_uenv t uenv).

(* 113. [{ t with all_code }]. *)
Definition update_all_code (t : Upwards_acc.t)
    (all_code : Exported_code.t) : Upwards_acc.t :=
  {| uenv := t.(uenv);
     creation_dacc := t.(creation_dacc);
     lifted_constants := t.(lifted_constants);
     all_code := all_code;
     name_occurrences := t.(name_occurrences);
     cost_metrics := t.(cost_metrics);
     slot_offsets := t.(slot_offsets);
     flow_result := t.(flow_result);
     resimplify := t.(resimplify)
  |}.
Extract Inlined Constant update_all_code =>
  "(fun t all_code -> { t with all_code = all_code })".

(* 105-113 *)
Definition remember_code_for_cmx (t : Upwards_acc.t)
    (code : Code_id.Map.t Code.t) : M Upwards_acc.t :=
  let! tmp1 := are_rebuilding_terms t in
  let! tmp2 := ART.do_not_rebuild_terms tmp1 in
  if tmp2
  then ret t
  else
    let& keep_code :=
      fun (code_id : Code_id.t) =>
      let! tmp1 := DA.code_ids_to_remember t.(creation_dacc) in
      Code_id.Set_.mem code_id tmp1
    in
    let* all_code := Exported_code.add_code keep_code code t.(all_code) in
    ret (update_all_code t all_code).

(* 122, 129 and 139. [{ t with name_occurrences }]. *)
Definition update_name_occurrences (t : Upwards_acc.t)
    (name_occurrences : Name_occurrences.t) : Upwards_acc.t :=
  {| uenv := t.(uenv);
     creation_dacc := t.(creation_dacc);
     lifted_constants := t.(lifted_constants);
     all_code := t.(all_code);
     name_occurrences := name_occurrences;
     cost_metrics := t.(cost_metrics);
     slot_offsets := t.(slot_offsets);
     flow_result := t.(flow_result);
     resimplify := t.(resimplify)
  |}.
Extract Inlined Constant update_name_occurrences =>
  "(fun t name_occurrences -> { t with name_occurrences = name_occurrences })".

(* 119-122 *)
Definition with_name_occurrences (t : Upwards_acc.t)
    (name_occurrences : Name_occurrences.t) : M Upwards_acc.t :=
  let! tmp1 := phys_equal name_occurrences t.(Upwards_acc.name_occurrences) in
  if tmp1 then ret t else ret (update_name_occurrences t name_occurrences).

(* 124-125 *)
Definition clear_name_occurrences (t : Upwards_acc.t) : M Upwards_acc.t :=
  with_name_occurrences t Name_occurrences.empty.

(* 127-129 *)
Definition add_free_names (t : Upwards_acc.t) (free_names : Name_occurrences.t)
    : M Upwards_acc.t :=
  let* name_occurrences :=
    Name_occurrences.union t.(name_occurrences) free_names
  in
  ret (update_name_occurrences t name_occurrences).

(* 131 *)
Definition used_value_slots (t : Upwards_acc.t) : M Name_occurrences.t :=
  DA.used_value_slots t.(creation_dacc).

(* 133 *)
Definition shareable_constants (t : Upwards_acc.t)
    : M (Static_const.Map.t Symbol.t) :=
  DA.shareable_constants t.(creation_dacc).

(* 135-139 *)
Definition remove_all_occurrences_of_free_names (t : Upwards_acc.t)
    (to_remove : Name_occurrences.t) : M Upwards_acc.t :=
  let* name_occurrences :=
    Name_occurrences.diff t.(name_occurrences) to_remove
  in
  ret (update_name_occurrences t name_occurrences).

(* 141, 143, 146, 149-151 and 154. [{ t with cost_metrics }]. *)
Definition update_cost_metrics (t : Upwards_acc.t)
    (cost_metrics : Cost_metrics.t) : Upwards_acc.t :=
  {| uenv := t.(uenv);
     creation_dacc := t.(creation_dacc);
     lifted_constants := t.(lifted_constants);
     all_code := t.(all_code);
     name_occurrences := t.(name_occurrences);
     cost_metrics := cost_metrics;
     slot_offsets := t.(slot_offsets);
     flow_result := t.(flow_result);
     resimplify := t.(resimplify)
  |}.
Extract Inlined Constant update_cost_metrics =>
  "(fun t cost_metrics -> { t with cost_metrics = cost_metrics })".

(* 141 *)
Definition clear_cost_metrics (t : Upwards_acc.t) : M Upwards_acc.t :=
  ret (update_cost_metrics t Cost_metrics.zero).

(* 143 *)
Definition with_cost_metrics (cost_metrics : Cost_metrics.t)
    (t : Upwards_acc.t) : M Upwards_acc.t :=
  ret (update_cost_metrics t cost_metrics).

(* 145-146 *)
Definition notify_added (code_size : Code_size.t) (t : Upwards_acc.t)
    : M Upwards_acc.t :=
  let! tmp1 := Cost_metrics.notify_added code_size t.(cost_metrics) in
  ret (update_cost_metrics t tmp1).

(* 148-151 *)
Definition notify_removed (operation : Removed_operations.t)
    (t : Upwards_acc.t) : M Upwards_acc.t :=
  let! tmp1 := Cost_metrics.notify_removed operation t.(cost_metrics) in
  ret (update_cost_metrics t tmp1).

(* 153-154 *)
Definition add_cost_metrics (cost_metrics : Cost_metrics.t)
    (t : Upwards_acc.t) : M Upwards_acc.t :=
  let! tmp1 :=
    Cost_metrics.op_plus t.(Upwards_acc.cost_metrics) cost_metrics
  in
  ret (update_cost_metrics t tmp1).

(* 157. [{ t with cost_metrics; name_occurrences }]. *)
Definition update_cost_metrics_name_occurrences (t : Upwards_acc.t)
    (cost_metrics : Cost_metrics.t)
    (name_occurrences : Name_occurrences.t) : Upwards_acc.t :=
  {| uenv := t.(uenv);
     creation_dacc := t.(creation_dacc);
     lifted_constants := t.(lifted_constants);
     all_code := t.(all_code);
     name_occurrences := name_occurrences;
     cost_metrics := cost_metrics;
     slot_offsets := t.(slot_offsets);
     flow_result := t.(flow_result);
     resimplify := t.(resimplify)
  |}.
Extract Inlined Constant update_cost_metrics_name_occurrences =>
  "(fun t cost_metrics name_occurrences -> { t with cost_metrics =
   cost_metrics; name_occurrences = name_occurrences })".

(* 156-160 *)
Definition add_cost_metrics_and_with_name_occurrences (t : Upwards_acc.t)
    (cost_metrics : Cost_metrics.t) (name_occurrences : Name_occurrences.t)
    : M Upwards_acc.t :=
  let! tmp1 :=
    Cost_metrics.op_plus t.(Upwards_acc.cost_metrics) cost_metrics
  in
  ret (update_cost_metrics_name_occurrences t tmp1 name_occurrences).

(* 162 *)
Definition generate_phantom_lets (t : Upwards_acc.t) : M bool :=
  let! tmp1 := DA.denv t.(creation_dacc) in
  DE.generate_phantom_lets tmp1.

(* 164-165 *)
Definition is_demoted_exn_handler (t : Upwards_acc.t) (cont : Continuation.t)
    : M bool :=
  let! tmp1 := DA.demoted_exn_handlers t.(creation_dacc) in
  Continuation.Set_.mem cont tmp1.

(* 169. [{ t with slot_offsets }]. *)
Definition update_slot_offsets (t : Upwards_acc.t)
    (slot_offsets : Or_unknown.t Slot_offsets.t) : Upwards_acc.t :=
  {| uenv := t.(uenv);
     creation_dacc := t.(creation_dacc);
     lifted_constants := t.(lifted_constants);
     all_code := t.(all_code);
     name_occurrences := t.(name_occurrences);
     cost_metrics := t.(cost_metrics);
     slot_offsets := slot_offsets;
     flow_result := t.(flow_result);
     resimplify := t.(resimplify)
  |}.
Extract Inlined Constant update_slot_offsets =>
  "(fun t slot_offsets -> { t with slot_offsets = slot_offsets })".

(* 169 *)
Definition with_slot_offsets (t : Upwards_acc.t)
    (slot_offsets : Or_unknown.t Slot_offsets.t) : M Upwards_acc.t :=
  ret (update_slot_offsets t slot_offsets).

(* 171 *)
Definition required_names (t : Upwards_acc.t) : M Name.Set_.t :=
  ret
    t.(flow_result).(Flow_types.Flow_result.data_flow_result).(Flow_types.Data_flow_result.required_names).

(* 173 *)
Definition reachable_code_ids (t : Upwards_acc.t)
    : M (Or_unknown.t Flow_types.Reachable_code_ids.t) :=
  ret
    t.(flow_result).(Flow_types.Flow_result.data_flow_result).(Flow_types.Data_flow_result.reachable_code_ids).

(* 175 *)
Definition continuation_param_aliases (t : Upwards_acc.t)
    : M Flow_types.Alias_result.t :=
  ret t.(flow_result).(Flow_types.Flow_result.aliases_result).

(* 177 *)
Definition mutable_unboxing_result (t : Upwards_acc.t)
    : M Flow_types.Mutable_unboxing_result.t :=
  ret t.(flow_result).(Flow_types.Flow_result.mutable_unboxing_result).

(* 179. [{ t with resimplify }]. *)
Definition update_resimplify (t : Upwards_acc.t)
    (resimplify : bool) : Upwards_acc.t :=
  {| uenv := t.(uenv);
     creation_dacc := t.(creation_dacc);
     lifted_constants := t.(lifted_constants);
     all_code := t.(all_code);
     name_occurrences := t.(name_occurrences);
     cost_metrics := t.(cost_metrics);
     slot_offsets := t.(slot_offsets);
     flow_result := t.(flow_result);
     resimplify := resimplify
  |}.
Extract Inlined Constant update_resimplify =>
  "(fun t resimplify -> { t with resimplify = resimplify })".

(* 179 *)
Definition set_resimplify (t : Upwards_acc.t) : M Upwards_acc.t :=
  ret (update_resimplify t true).

(* 183. In the compiler: [DA.specialization_map (creation_dacc t)]; here
   [creation_dacc] is the projection. *)
Definition specialization_map (t : Upwards_acc.t)
    : M (Continuation.Map.t (Apply_cont_rewrite_id.Map.t Continuation.t)) :=
  DA.specialization_map t.(creation_dacc).
