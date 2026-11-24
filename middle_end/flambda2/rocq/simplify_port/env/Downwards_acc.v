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

(* This file follows middle_end/flambda2/simplify/env/downwards_acc.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the arguments by place, a setter
   [update_f] where the compiler writes [{ t with f }]) is that of GUIDE.md.
   No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Are_lifting_conts
  Are_rebuilding_terms Bound_var Code_id Continuation
  Continuation_callsite_map Continuation_use_kind Continuation_uses_env
  Debuginfo Downwards_env Flambda2_types Flambda_arity Flambda_features Flow
  Format Lifted_constant_state Name_mode Name_occurrences Original_handlers
  Simple Slot_offsets Static_const Stdlib_ Symbol Value_slot.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* PORT-GAP(verbatim): 17-20, the four abbreviations of modules are the
   compiler's text, and the Rocq text below writes the modules' own names.
   As Rocq modules ([Module DE := Downwards_env.]) they make Rocq write an
   [open] line for each of them and for what they name, and such a line can
   hide a module that the rest of the extracted file names. *)
(*OCAML
module CUE = Continuation_uses_env
module DE = Downwards_env
module LCS = Lifted_constant_state
module TE = Flambda2_types.Typing_env
OCAML*)

(* 22-43 *)
Record t : Type :=
  { denv : Downwards_env.t;
    continuation_uses_env : Continuation_uses_env.t;
    shareable_constants : Static_const.Map.t Symbol.t;
    used_value_slots : Name_occurrences.t;
    lifted_constants : Lifted_constant_state.t;
    flow_acc : Flow.Acc.t;
    demoted_exn_handlers : Continuation.Set_.t;
    code_ids_to_remember : Code_id.Set_.t;
    code_ids_to_never_delete : Code_id.Set_.t;
    code_ids_never_simplified : Code_id.Set_.t;
    slot_offsets : Code_id.Map.t Slot_offsets.t;
    debuginfo_rewrites : Simple.Map.t Debuginfo.t;
    are_lifting_conts : Are_lifting_conts.t;
    lifted_continuations : list (Downwards_env.t * Original_handlers.t);
    (* head of the list is the innermost continuation being lifted *)
    continuation_lifting_budget : int;
    continuations_to_specialize : Continuation.Set_.t;
    specialization_map : Continuation_callsite_map.t Continuation.t
  }.

(* 45-48 *)
(* PORT-GAP(loose): the pair pattern of the parameter is a [let]. *)
Definition print_lifted_cont (ppf : Format.formatter)
    (lifted_cont : Downwards_env.t * Original_handlers.t) : M unit :=
  let* '(denv, original_handlers) := ret lifted_cont in
  Format.fprintf4 ppf
    "@[<hov 1>(@[<hov 1>(denv %a)@]@ @[<hov 1>(original_handlers %a)@])@]"
    Downwards_env.print denv Original_handlers.print original_handlers.

(* 50-92 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept, and
   the record pattern of the parameter is a match. *)
Definition print (ppf : Format.formatter) (t : Downwards_acc.t) : M unit :=
  match t with
  | {| denv := denv;
       continuation_uses_env := continuation_uses_env;
       shareable_constants := shareable_constants;
       used_value_slots := used_value_slots;
       lifted_constants := lifted_constants;
       flow_acc := flow_acc;
       demoted_exn_handlers := demoted_exn_handlers;
       code_ids_to_remember := code_ids_to_remember;
       code_ids_to_never_delete := code_ids_to_never_delete;
       code_ids_never_simplified := code_ids_never_simplified;
       slot_offsets := slot_offsets;
       debuginfo_rewrites := debuginfo_rewrites;
       are_lifting_conts := are_lifting_conts;
       lifted_continuations := lifted_continuations;
       continuation_lifting_budget := continuation_lifting_budget;
       continuations_to_specialize := continuations_to_specialize;
       specialization_map := specialization_map
    |} =>
    (* PORT-GAP(papp): the printers of the maps and of the list are given
       their first arguments only (six places). *)
    let! tmp1 := papp1 Apply_cont_rewrite_id.Map.print Continuation.print in
    let! tmp2 := papp1 Continuation.Map.print tmp1 in
    let! tmp3 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space)
        print_lifted_cont
    in
    let! tmp4 := papp1 Simple.Map.print Debuginfo.print_compact in
    let! tmp5 := papp1 Code_id.Map.print Slot_offsets.print in
    let! tmp6 := papp1 Static_const.Map.print Symbol.print in
    Format.fprintf33 ppf
      "@[<hov 1>(@[<hov 1>(denv@ %a)@]@ @[<hov 1>(continuation_uses_env@ %a)@]@ @[<hov 1>(shareable_constants@ %a)@]@ @[<hov 1>(used_value_slots@ %a)@]@ @[<hov 1>(lifted_constant_state@ %a)@]@ @[<hov 1>(flow_acc@ %a)@]@ @[<hov 1>(demoted_exn_handlers@ %a)@]@ @[<hov 1>(code_ids_to_remember@ %a)@]@ @[<hov 1>(code_ids_to_never_delete@ %a)@]@ @[<hov 1>(code_ids_never_simplified@ %a)@]@ @[<hov 1>(slot_offsets@ %a)@ @[<hov 1>(debuginfo_rewrites@ %a)@]@ @[<hov 1>(are_lifting_conts@ %a)@]@ @[<hov 1>(lifted_continuations@ %a)@]@ @[<hov 1>(continuation_lifting_budget %d)@]@ @[<hov 1>(continuations_to_specialize %a)@]@ @[<hov 1>(specialization_map %a)@])@]"
      Downwards_env.print denv Continuation_uses_env.print
      continuation_uses_env tmp6 shareable_constants Name_occurrences.print
      used_value_slots Lifted_constant_state.print lifted_constants
      Flow.Acc.print flow_acc Continuation.Set_.print demoted_exn_handlers
      Code_id.Set_.print code_ids_to_remember Code_id.Set_.print
      code_ids_to_never_delete Code_id.Set_.print code_ids_never_simplified
      tmp5 slot_offsets tmp4 debuginfo_rewrites Are_lifting_conts.print
      are_lifting_conts tmp3 lifted_continuations continuation_lifting_budget
      Continuation.Set_.print continuations_to_specialize tmp2
      specialization_map
  end.

(* 94-112 *)
Definition create (denv : Downwards_env.t)
    (slot_offsets : Code_id.Map.t Slot_offsets.t)
    (continuation_uses_env : Continuation_uses_env.t) : M Downwards_acc.t :=
  (* PORT-GAP(record-order): three fields of the record are calls
     ([flow_acc], [are_lifting_conts], [continuation_lifting_budget]); they
     are taken in the order of the type, the last field first, and each is
     bound before the record is built. *)
  let* continuation_lifting_budget :=
    Flambda_features.Expert.cont_lifting_budget tt
  in
  let* are_lifting_conts :=
    Are_lifting_conts.no_lifting Are_lifting_conts.At_toplevel
  in
  let* flow_acc := Flow.Acc.empty tt in
  ret
    {| denv := denv;
       continuation_uses_env := continuation_uses_env;
       shareable_constants := Static_const.Map.empty;
       used_value_slots := Name_occurrences.empty;
       lifted_constants := Lifted_constant_state.empty;
       flow_acc := flow_acc;
       demoted_exn_handlers := Continuation.Set_.empty;
       code_ids_to_remember := Code_id.Set_.empty;
       code_ids_to_never_delete := Code_id.Set_.empty;
       code_ids_never_simplified := Code_id.Set_.empty;
       slot_offsets := slot_offsets;
       debuginfo_rewrites := Simple.Map.empty;
       are_lifting_conts := are_lifting_conts;
       lifted_continuations := [];
       continuation_lifting_budget := continuation_lifting_budget;
       continuations_to_specialize := Continuation.Set_.empty;
       specialization_map := Continuation.Map.empty
    |}.

(* PORT-GAP(loose): 114 and 116, [denv] and [flow_acc] are the projections
   of the record [t] under these names: they are pure in Rocq, and Rocq
   prints each as [let f t = t.f] after the type. The same holds of
   [continuation_uses_env] (151), [shareable_constants] (208),
   [used_value_slots] (217), [code_ids_to_remember] (232),
   [code_ids_to_never_delete] (243), [code_ids_never_simplified] (254),
   [demoted_exn_handlers] (266), [slot_offsets] (268), [are_lifting_conts]
   (286), [continuations_to_specialize] (328) and [specialization_map]
   (342). Where the compiler calls one of them ([denv t]), the Rocq text
   reads the field. *)

(* PORT-GAP(update): 118, [{ t with flow_acc }]. *)
Definition update_flow_acc (t : Downwards_acc.t)
    (flow_acc : Flow.Acc.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := flow_acc;
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_flow_acc =>
  "(fun t flow_acc -> { t with flow_acc = flow_acc })".

(* 118 *)
(* PORT-GAP(loose): the attribute [@inline always] is not kept, here and at
   [map_flow_acc], [map_denv] and [with_denv]. *)
Definition with_flow_acc (flow_acc : Flow.Acc.t) (t : Downwards_acc.t)
    : M Downwards_acc.t :=
  ret (update_flow_acc t flow_acc).

(* 120 *)
Definition map_flow_acc (t : Downwards_acc.t)
    (f : Flow.Acc.t -> M Flow.Acc.t) : M Downwards_acc.t :=
  let! tmp1 := f t.(flow_acc) in
  ret (update_flow_acc t tmp1).

(* PORT-GAP(update): 122, [{ t with denv }]. *)
Definition update_denv (t : Downwards_acc.t)
    (denv : Downwards_env.t) : Downwards_acc.t :=
  {| denv := denv;
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_denv =>
  "(fun t denv -> { t with denv = denv })".

(* 122 *)
Definition map_denv (t : Downwards_acc.t)
    (f : Downwards_env.t -> M Downwards_env.t) : M Downwards_acc.t :=
  let! tmp1 := f t.(denv) in
  ret (update_denv t tmp1).

(* 124 *)
Definition with_denv (t : Downwards_acc.t) (denv : Downwards_env.t)
    : M Downwards_acc.t :=
  ret (update_denv t denv).

(* PORT-GAP(update): 127, [{ t with continuation_uses_env }]. *)
Definition update_continuation_uses_env (t : Downwards_acc.t)
    (continuation_uses_env : Continuation_uses_env.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := continuation_uses_env;
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_continuation_uses_env =>
  "(fun t continuation_uses_env -> { t with continuation_uses_env =
   continuation_uses_env })".

(* 126-127 *)
Definition with_continuation_uses_env (t : Downwards_acc.t)
    (cont_uses_env : Continuation_uses_env.t) : M Downwards_acc.t :=
  ret (update_continuation_uses_env t cont_uses_env).

(* 129-133 *)
Definition record_continuation (t : Downwards_acc.t) (cont : Continuation.t)
    (arity : Flambda_arity.t_Unarized) : M Downwards_acc.t :=
  let* cont_uses_env :=
    Continuation_uses_env.record_continuation t.(continuation_uses_env) cont
      arity
  in
  with_continuation_uses_env t cont_uses_env.

(* 135-140 *)
Definition record_continuation_use (t : Downwards_acc.t)
    (cont : Continuation.t) (use_kind : Continuation_use_kind.t)
    (env_at_use : Downwards_env.t) (arg_types : list Flambda2_types.t)
    : M (Downwards_acc.t * Apply_cont_rewrite_id.t) :=
  let* '(cont_uses_env, id) :=
    Continuation_uses_env.record_continuation_use t.(continuation_uses_env)
      cont use_kind env_at_use arg_types
  in
  let! tmp1 := with_continuation_uses_env t cont_uses_env in
  ret (tmp1, id).

(* 142-146 *)
Definition delete_continuation_uses (t : Downwards_acc.t)
    (cont : Continuation.t) : M Downwards_acc.t :=
  let* cont_uses_env :=
    Continuation_uses_env.delete_continuation_uses t.(continuation_uses_env)
      cont
  in
  with_continuation_uses_env t cont_uses_env.

(* 148-149 *)
Definition num_continuation_uses (t : Downwards_acc.t) (cont : Continuation.t)
    : M int :=
  Continuation_uses_env.num_continuation_uses t.(continuation_uses_env) cont.

(* 153 *)
Definition code_age_relation (t : Downwards_acc.t)
    : M Flambda2_types.Code_age_relation.t :=
  let! tmp1 := Downwards_env.typing_env t.(denv) in
  Flambda2_types.Typing_env.code_age_relation tmp1.

(* 155-159 *)
Definition with_code_age_relation (t : Downwards_acc.t)
    (code_age_relation : Flambda2_types.Code_age_relation.t)
    : M Downwards_acc.t :=
  let* typing_env :=
    let! tmp1 := Downwards_env.typing_env t.(denv) in
    Flambda2_types.Typing_env.with_code_age_relation tmp1 code_age_relation
  in
  let! tmp1 := Downwards_env.with_typing_env t.(denv) typing_env in
  with_denv t tmp1.

(* 161 *)
Definition typing_env (t : Downwards_acc.t) : M Flambda2_types.Typing_env.t :=
  Downwards_env.typing_env t.(denv).

(* 163 *)
Definition add_variable (t : Downwards_acc.t) (var : Bound_var.t)
    (ty : Flambda2_types.t) : M Downwards_acc.t :=
  let! tmp1 := Downwards_env.add_variable t.(denv) var ty in
  with_denv t tmp1.

(* 165-166 *)
Definition get_typing_env_no_more_than_one_use (t : Downwards_acc.t)
    (k : Continuation.t) : M (option Flambda2_types.Typing_env.t) :=
  Continuation_uses_env.get_typing_env_no_more_than_one_use
    t.(continuation_uses_env) k.

(* PORT-GAP(update): 178, [{ t with lifted_constants; denv }]. *)
Definition update_lifted_constants_denv (t : Downwards_acc.t)
    (lifted_constants : Lifted_constant_state.t)
    (denv : Downwards_env.t) : Downwards_acc.t :=
  {| denv := denv;
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := lifted_constants;
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_lifted_constants_denv =>
  "(fun t lifted_constants denv -> { t with lifted_constants =
   lifted_constants; denv = denv })".

(* 168-178. The optional argument [?also_add_to_env] is by place; the
   wrapper at the end of the extracted file gives it its label. *)
Definition add_to_lifted_constant_accumulator (also_add_to_env : option unit)
    (t : Downwards_acc.t) (constants : Lifted_constant_state.t)
    : M Downwards_acc.t :=
  let& also_add_to_env :=
    match also_add_to_env with None => false | Some tt => true end
  in
  let* lifted_constants :=
    Lifted_constant_state.union t.(lifted_constants) constants
  in
  let* denv :=
    if also_add_to_env
    then
      Downwards_env.add_lifted_constant_state None t.(Downwards_acc.denv)
        constants
    else ret t.(Downwards_acc.denv)
  in
  ret (update_lifted_constants_denv t lifted_constants denv).

(* 180 *)
Definition get_lifted_constants (t : Downwards_acc.t)
    : M Lifted_constant_state.t :=
  ret t.(lifted_constants).

(* PORT-GAP(update): 182, [{ t with lifted_constants }]. *)
Definition update_lifted_constants (t : Downwards_acc.t)
    (lifted_constants : Lifted_constant_state.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := lifted_constants;
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_lifted_constants =>
  "(fun t lifted_constants -> { t with lifted_constants = lifted_constants })".

(* 182 *)
Definition clear_lifted_constants (t : Downwards_acc.t) : M Downwards_acc.t :=
  ret (update_lifted_constants t Lifted_constant_state.empty).

(* 184 *)
Definition no_lifted_constants (t : Downwards_acc.t) : M bool :=
  Lifted_constant_state.is_empty t.(lifted_constants).

(* 186-189 *)
Definition get_and_clear_lifted_constants (t : Downwards_acc.t)
    : M (Downwards_acc.t * Lifted_constant_state.t) :=
  let& constants := t.(lifted_constants) in
  let* t := clear_lifted_constants t in
  ret (t, constants).

(* 191 *)
Definition set_lifted_constants (t : Downwards_acc.t)
    (consts : Lifted_constant_state.t) : M Downwards_acc.t :=
  ret (update_lifted_constants t consts).

(* 193-194 *)
Definition find_shareable_constant (t : Downwards_acc.t)
    (static_const : Static_const.t) : M (option Symbol.t) :=
  Static_const.Map.find_opt static_const t.(shareable_constants).

(* PORT-GAP(update): 200, [{ t with shareable_constants }]. *)
Definition update_shareable_constants (t : Downwards_acc.t)
    (shareable_constants : Static_const.Map.t Symbol.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := shareable_constants;
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_shareable_constants =>
  "(fun t shareable_constants -> { t with shareable_constants =
   shareable_constants })".

(* 196-203 *)
Definition consider_constant_for_sharing (t : Downwards_acc.t)
    (symbol : Symbol.t) (static_const : Static_const.t)
    : M Downwards_acc.t :=
  let! tmp1 := Static_const.can_share static_const in
  if negb tmp1
  then ret t
  else
    let! tmp2 :=
      Static_const.Map.add static_const symbol t.(shareable_constants)
    in
    ret (update_shareable_constants t tmp2).

(* 205-206 *)
Definition with_shareable_constants (t : Downwards_acc.t)
    (shareable_constants : Static_const.Map.t Symbol.t) : M Downwards_acc.t :=
  ret (update_shareable_constants t shareable_constants).

(* PORT-GAP(update): 211, [{ t with used_value_slots }]. *)
Definition update_used_value_slots (t : Downwards_acc.t)
    (used_value_slots : Name_occurrences.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := used_value_slots;
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_used_value_slots =>
  "(fun t used_value_slots -> { t with used_value_slots = used_value_slots })".

(* 210-215 *)
Definition add_use_of_value_slot (t : Downwards_acc.t)
    (value_slot : Value_slot.t) : M Downwards_acc.t :=
  let! tmp1 :=
    Name_occurrences.add_value_slot_in_projection t.(used_value_slots)
      value_slot Name_mode.normal
  in
  ret (update_used_value_slots t tmp1).

(* 219-220 *)
Definition all_continuations_used (t : Downwards_acc.t)
    : M Continuation.Set_.t :=
  Continuation_uses_env.all_continuations_used t.(continuation_uses_env).

(* 222 *)
Definition with_used_value_slots (t : Downwards_acc.t)
    (used_value_slots : Name_occurrences.t) : M Downwards_acc.t :=
  ret (update_used_value_slots t used_value_slots).

(* PORT-GAP(update): 228, [{ t with code_ids_to_remember }]. *)
Definition update_code_ids_to_remember (t : Downwards_acc.t)
    (code_ids_to_remember : Code_id.Set_.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := code_ids_to_remember;
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_code_ids_to_remember =>
  "(fun t code_ids_to_remember -> { t with code_ids_to_remember =
   code_ids_to_remember })".

(* 224-230 *)
Definition add_code_ids_to_remember (t : Downwards_acc.t)
    (code_ids : Code_id.Set_.t) : M Downwards_acc.t :=
  let! tmp1 := Downwards_env.at_unit_toplevel t.(denv) in
  if tmp1
  then ret t
  else
    let! tmp2 := Code_id.Set_.union code_ids t.(code_ids_to_remember) in
    ret (update_code_ids_to_remember t tmp2).

(* 234-235 *)
Definition with_code_ids_to_remember (t : Downwards_acc.t)
    (code_ids_to_remember : Code_id.Set_.t) : M Downwards_acc.t :=
  ret (update_code_ids_to_remember t code_ids_to_remember).

(* PORT-GAP(update): 238, [{ t with code_ids_to_never_delete }]. *)
Definition update_code_ids_to_never_delete (t : Downwards_acc.t)
    (code_ids_to_never_delete : Code_id.Set_.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := code_ids_to_never_delete;
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_code_ids_to_never_delete =>
  "(fun t code_ids_to_never_delete -> { t with code_ids_to_never_delete =
   code_ids_to_never_delete })".

(* 237-241 *)
Definition add_code_ids_to_never_delete (t : Downwards_acc.t)
    (code_ids : Code_id.Set_.t) : M Downwards_acc.t :=
  let! tmp1 := Code_id.Set_.union code_ids t.(code_ids_to_never_delete) in
  ret (update_code_ids_to_never_delete t tmp1).

(* 245-246 *)
Definition with_code_ids_to_never_delete (t : Downwards_acc.t)
    (code_ids_to_never_delete : Code_id.Set_.t) : M Downwards_acc.t :=
  ret (update_code_ids_to_never_delete t code_ids_to_never_delete).

(* PORT-GAP(update): 249, [{ t with code_ids_never_simplified }]. *)
Definition update_code_ids_never_simplified (t : Downwards_acc.t)
    (code_ids_never_simplified : Code_id.Set_.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := code_ids_never_simplified;
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_code_ids_never_simplified =>
  "(fun t code_ids_never_simplified -> { t with code_ids_never_simplified =
   code_ids_never_simplified })".

(* 248-252 *)
Definition add_code_ids_never_simplified (t : Downwards_acc.t)
    (old_code_ids : Code_id.Set_.t) : M Downwards_acc.t :=
  let! tmp1 :=
    Code_id.Set_.union old_code_ids t.(code_ids_never_simplified)
  in
  ret (update_code_ids_never_simplified t tmp1).

(* 256-257 *)
Definition with_code_ids_never_simplified (t : Downwards_acc.t)
    (code_ids_never_simplified : Code_id.Set_.t) : M Downwards_acc.t :=
  ret (update_code_ids_never_simplified t code_ids_never_simplified).

(* 259 *)
Definition are_rebuilding_terms (t : Downwards_acc.t)
    : M Are_rebuilding_terms.t :=
  Downwards_env.are_rebuilding_terms t.(denv).

(* PORT-GAP(update): 262, [{ t with demoted_exn_handlers }]. *)
Definition update_demoted_exn_handlers (t : Downwards_acc.t)
    (demoted_exn_handlers : Continuation.Set_.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := demoted_exn_handlers;
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_demoted_exn_handlers =>
  "(fun t demoted_exn_handlers -> { t with demoted_exn_handlers =
   demoted_exn_handlers })".

(* 261-264 *)
Definition demote_exn_handler (t : Downwards_acc.t) (cont : Continuation.t)
    : M Downwards_acc.t :=
  let! tmp1 := Continuation.Set_.add cont t.(demoted_exn_handlers) in
  ret (update_demoted_exn_handlers t tmp1).

(* PORT-GAP(update): 270, [{ t with slot_offsets }]. *)
Definition update_slot_offsets (t : Downwards_acc.t)
    (slot_offsets : Code_id.Map.t Slot_offsets.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := slot_offsets;
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_slot_offsets =>
  "(fun t slot_offsets -> { t with slot_offsets = slot_offsets })".

(* 270 *)
Definition with_slot_offsets (t : Downwards_acc.t)
    (slot_offsets : Code_id.Map.t Slot_offsets.t) : M Downwards_acc.t :=
  ret (update_slot_offsets t slot_offsets).

(* 272-273 *)
Definition find_debuginfo_rewrite (t : Downwards_acc.t) (bound_to : Simple.t)
    : M (option Debuginfo.t) :=
  Simple.Map.find_opt bound_to t.(debuginfo_rewrites).

(* PORT-GAP(update): 281, [{ t with debuginfo_rewrites }]. *)
Definition update_debuginfo_rewrites (t : Downwards_acc.t)
    (debuginfo_rewrites : Simple.Map.t Debuginfo.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := debuginfo_rewrites;
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_debuginfo_rewrites =>
  "(fun t debuginfo_rewrites -> { t with debuginfo_rewrites =
   debuginfo_rewrites })".

(* 275-284. [Debuginfo.merge ~into:earlier_dbg dbg]: the arguments are in
   the order of the interface. *)
Definition merge_debuginfo_rewrite (t : Downwards_acc.t) (bound_to : Simple.t)
    (dbg : Debuginfo.t) : M Downwards_acc.t :=
  let* dbg :=
    let! tmp1 := find_debuginfo_rewrite t bound_to in
    match tmp1 with
    | None => ret dbg
    | Some earlier_dbg => Debuginfo.merge earlier_dbg dbg
    end
  in
  (* 283: [Simple.Map.add], or replace *)
  let! tmp1 := Simple.Map.add bound_to dbg t.(debuginfo_rewrites) in
  ret (update_debuginfo_rewrites t tmp1).

(* PORT-GAP(update): 288, [{ t with are_lifting_conts }]. *)
Definition update_are_lifting_conts (t : Downwards_acc.t)
    (are_lifting_conts : Are_lifting_conts.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := are_lifting_conts;
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_are_lifting_conts =>
  "(fun t are_lifting_conts -> { t with are_lifting_conts = are_lifting_conts
   })".

(* 288 *)
Definition with_are_lifting_conts (t : Downwards_acc.t)
    (are_lifting_conts : Are_lifting_conts.t) : M Downwards_acc.t :=
  ret (update_are_lifting_conts t are_lifting_conts).

(* PORT-GAP(update): 291, [{ t with lifted_continuations }]. *)
Definition update_lifted_continuations (t : Downwards_acc.t)
    (lifted_continuations : list (Downwards_env.t * Original_handlers.t))
    : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := lifted_continuations;
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_lifted_continuations =>
  "(fun t lifted_continuations -> { t with lifted_continuations =
   lifted_continuations })".

(* 290-291 *)
Definition get_and_clear_lifted_continuations (t : Downwards_acc.t)
    : M (Downwards_acc.t * list (Downwards_env.t * Original_handlers.t)) :=
  ret (update_lifted_continuations t [], t.(lifted_continuations)).

(* 293-296 *)
Definition add_lifted_continuation (denv : Downwards_env.t)
    (original_handlers : Original_handlers.t) (t : Downwards_acc.t)
    : M Downwards_acc.t :=
  ret
    (update_lifted_continuations t
       ((denv, original_handlers) :: t.(lifted_continuations))).

(* Invariant: budget < 0 means no limit on cont lifting *)
(* 299-301 *)
Definition get_continuation_lifting_budget (t : Downwards_acc.t) : M int :=
  let& budget := t.(continuation_lifting_budget) in
  if budget <? 0 then ret Stdlib_.max_int else ret budget.

(* PORT-GAP(update): 304, [{ t with continuation_lifting_budget }]. *)
Definition update_continuation_lifting_budget (t : Downwards_acc.t)
    (continuation_lifting_budget : int) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := continuation_lifting_budget;
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_continuation_lifting_budget =>
  "(fun t continuation_lifting_budget -> { t with continuation_lifting_budget
   = continuation_lifting_budget })".

(* 303-304 *)
Definition with_continuation_lifting_budget (t : Downwards_acc.t)
    (budget : int) : M Downwards_acc.t :=
  ret (update_continuation_lifting_budget t budget).

(* 306-308 *)
Definition reset_continuation_lifting_budget (t : Downwards_acc.t)
    : M Downwards_acc.t :=
  let! tmp1 := Flambda_features.Expert.cont_lifting_budget tt in
  with_continuation_lifting_budget t tmp1.

(* 310-315 *)
Definition decrease_continuation_lifting_budget (t : Downwards_acc.t)
    (cost : int) : M Downwards_acc.t :=
  if t.(continuation_lifting_budget) <? 0
  then ret t
  else
    with_continuation_lifting_budget t
      (Z.max 0 (t.(continuation_lifting_budget) - cost)).

(* 317-326. In the compiler: [map_denv ~f dacc]. *)
Definition prepare_for_speculative_inlining (dacc : Downwards_acc.t)
    : M Downwards_acc.t :=
  let* dacc :=
    map_denv dacc
      (fun denv =>
        Downwards_env.set_do_not_rebuild_terms_and_disable_inlining denv
          Downwards_env.Disable_inlining_reason.Speculative_inlining)
  in
  let! tmp1 :=
    Are_lifting_conts.no_lifting Are_lifting_conts.In_speculative_inlining
  in
  with_are_lifting_conts dacc tmp1.

(* PORT-GAP(update): 331, [{ t with continuations_to_specialize }]. *)
Definition update_continuations_to_specialize (t : Downwards_acc.t)
    (continuations_to_specialize : Continuation.Set_.t) : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := continuations_to_specialize;
     specialization_map := t.(specialization_map)
  |}.
Extract Inlined Constant update_continuations_to_specialize =>
  "(fun t continuations_to_specialize -> { t with continuations_to_specialize
   = continuations_to_specialize })".

(* 330-334 *)
Definition add_continuation_to_specialize (t : Downwards_acc.t)
    (cont : Continuation.t) : M Downwards_acc.t :=
  let! tmp1 := Continuation.Set_.add cont t.(continuations_to_specialize) in
  ret (update_continuations_to_specialize t tmp1).

(* PORT-GAP(update): 340, [{ t with specialization_map }]. *)
Definition update_specialization_map (t : Downwards_acc.t)
    (specialization_map : Continuation_callsite_map.t Continuation.t)
    : Downwards_acc.t :=
  {| denv := t.(denv);
     continuation_uses_env := t.(continuation_uses_env);
     shareable_constants := t.(shareable_constants);
     used_value_slots := t.(used_value_slots);
     lifted_constants := t.(lifted_constants);
     flow_acc := t.(flow_acc);
     demoted_exn_handlers := t.(demoted_exn_handlers);
     code_ids_to_remember := t.(code_ids_to_remember);
     code_ids_to_never_delete := t.(code_ids_to_never_delete);
     code_ids_never_simplified := t.(code_ids_never_simplified);
     slot_offsets := t.(slot_offsets);
     debuginfo_rewrites := t.(debuginfo_rewrites);
     are_lifting_conts := t.(are_lifting_conts);
     lifted_continuations := t.(lifted_continuations);
     continuation_lifting_budget := t.(continuation_lifting_budget);
     continuations_to_specialize := t.(continuations_to_specialize);
     specialization_map := specialization_map
  |}.
Extract Inlined Constant update_specialization_map =>
  "(fun t specialization_map -> { t with specialization_map =
   specialization_map })".

(* 336-340 *)
Definition add_specialization (t : Downwards_acc.t)
    (id : Apply_cont_rewrite_id.t) (old specialized : Continuation.t)
    : M Downwards_acc.t :=
  let* specialization_map :=
    Continuation_callsite_map.add old id specialized t.(specialization_map)
  in
  ret (update_specialization_map t specialization_map).

(* PORT-GAP(verbatim): the wrapper that gives the optional argument of
   [add_to_lifted_constant_accumulator] (168) its label. *)
(*OCAML-END
let add_to_lifted_constant_accumulator ?also_add_to_env t constants =
  add_to_lifted_constant_accumulator also_add_to_env t constants
OCAML-END*)
