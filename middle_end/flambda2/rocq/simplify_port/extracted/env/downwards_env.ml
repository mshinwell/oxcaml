(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/env/Downwards_env.v, which follows
   middle_end/flambda2/simplify/env/downwards_env.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Flambda.Import

type resolver =
  Compilation_unit.t -> Flambda2_types.Typing_env.Serializable.t option

type get_imported_code = unit -> Exported_code.t

open Port_monad
module CSE = Common_subexpression_elimination
module K = Flambda_kind
module BP = Bound_parameter
module T = Flambda2_types
module TE = Flambda2_types.Typing_env
module LCS = Lifted_constant_state
module LC = Lifted_constant

module Disable_inlining_reason = struct
  type t =
    | Stub
    | Speculative_inlining

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf = function
    | Stub -> Format.fprintf ppf "Stub"
    | Speculative_inlining -> Format.fprintf ppf "Speculative_inlining"
end

module Disable_inlining = struct
  type t =
    | Disable_inlining of Disable_inlining_reason.t
    | Do_not_disable_inlining

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf = function
    | Disable_inlining reason ->
      Format.fprintf ppf "@[<hov 1>(Disable_inlining %a)@]"
        Disable_inlining_reason.print reason
    | Do_not_disable_inlining -> Format.fprintf ppf "Do_not_disable_inlining"
end

type t =
  { round : int;
    machine_width : Target_system.Machine_width.t;
    typing_env : TE.t;
    inlined_debuginfo : Inlined_debuginfo.t;
    disable_inlining : Disable_inlining.t;
    disable_partial_application_stub_generation : bool;
    inlined_attribute_to_forward :
      (Inlined_attribute.t * forwarded_from:Inlined_debuginfo.t) option;
    inlining_state : Inlining_state.t;
    propagating_float_consts : bool;
    at_unit_toplevel : bool;
    unit_toplevel_return_continuation : Continuation.t;
    unit_toplevel_exn_continuation : Continuation.t;
    unit_toplevel_alloc_region : Variable.t;
    variables_defined_at_toplevel : Variable.Set.t;
    cse : CSE.t;
    comparison_results : Comparison_result.t Variable_.Map.t;
    are_rebuilding_terms : Are_rebuilding_terms.t;
    closure_info : Closure_info.t;
    get_imported_code : unit -> Exported_code.t coq_M;
    all_code : Code.t Code_id.Map.t;
    inlining_history_tracker : Inlining_history.Tracker.t;
    loopify_state : Loopify_state.t;
    replay_history : Replay_history.t;
    specialization_cost : Specialization_cost.t;
    join_analysis : Apply_cont_rewrite_id.t T.Join_analysis.t option;
    defined_variables_by_scope : Lifted_cont_params.t list;
    lifted : Variable.Set.t;
    cost_of_lifting_continuations_out_of_current_one : int;
    has_seen_a_non_liftable_continuation : bool;
    is_cold : bool
  }

(** val round : t -> int **)

let round t0 = t0.round

(** val machine_width : t -> Target_system.Machine_width.t **)

let machine_width t0 = t0.machine_width

(** val typing_env : t -> TE.t **)

let typing_env t0 = t0.typing_env

(** val inlined_debuginfo : t -> Inlined_debuginfo.t **)

let inlined_debuginfo t0 = t0.inlined_debuginfo

(** val disable_inlining : t -> Disable_inlining.t **)

let disable_inlining t0 = t0.disable_inlining

(** val disable_partial_application_stub_generation : t -> bool **)

let disable_partial_application_stub_generation t0 =
  t0.disable_partial_application_stub_generation

(** val inlined_attribute_to_forward : t -> (Inlined_attribute.t *
    forwarded_from:Inlined_debuginfo.t) option **)

let inlined_attribute_to_forward t0 = t0.inlined_attribute_to_forward

(** val inlining_state : t -> Inlining_state.t **)

let inlining_state t0 = t0.inlining_state

(** val propagating_float_consts : t -> bool **)

let propagating_float_consts t0 = t0.propagating_float_consts

(** val at_unit_toplevel : t -> bool **)

let at_unit_toplevel t0 = t0.at_unit_toplevel

(** val unit_toplevel_return_continuation : t -> Continuation.t **)

let unit_toplevel_return_continuation t0 = t0.unit_toplevel_return_continuation

(** val unit_toplevel_exn_continuation : t -> Continuation.t **)

let unit_toplevel_exn_continuation t0 = t0.unit_toplevel_exn_continuation

(** val unit_toplevel_alloc_region : t -> Variable.t **)

let unit_toplevel_alloc_region t0 = t0.unit_toplevel_alloc_region

(** val variables_defined_at_toplevel : t -> Variable.Set.t **)

let variables_defined_at_toplevel t0 = t0.variables_defined_at_toplevel

(** val cse : t -> CSE.t **)

let cse t0 = t0.cse

(** val comparison_results : t -> Comparison_result.t Variable_.Map.t **)

let comparison_results t0 = t0.comparison_results

(** val are_rebuilding_terms : t -> Are_rebuilding_terms.t **)

let are_rebuilding_terms t0 = t0.are_rebuilding_terms

(** val closure_info : t -> Closure_info.t **)

let closure_info t0 = t0.closure_info

(** val get_imported_code : t -> unit -> Exported_code.t coq_M **)

let get_imported_code t0 = t0.get_imported_code

(** val all_code : t -> Code.t Code_id.Map.t **)

let all_code t0 = t0.all_code

(** val inlining_history_tracker : t -> Inlining_history.Tracker.t **)

let inlining_history_tracker t0 = t0.inlining_history_tracker

(** val loopify_state : t -> Loopify_state.t **)

let loopify_state t0 = t0.loopify_state

(** val replay_history : t -> Replay_history.t **)

let replay_history t0 = t0.replay_history

(** val specialization_cost : t -> Specialization_cost.t **)

let specialization_cost t0 = t0.specialization_cost

(** val join_analysis : t -> Apply_cont_rewrite_id.t T.Join_analysis.t option **)

let join_analysis t0 = t0.join_analysis

(** val defined_variables_by_scope : t -> Lifted_cont_params.t list **)

let defined_variables_by_scope t0 = t0.defined_variables_by_scope

(** val lifted : t -> Variable.Set.t **)

let lifted t0 = t0.lifted

(** val cost_of_lifting_continuations_out_of_current_one : t -> int **)

let cost_of_lifting_continuations_out_of_current_one t0 =
  t0.cost_of_lifting_continuations_out_of_current_one

(** val has_seen_a_non_liftable_continuation : t -> bool **)

let has_seen_a_non_liftable_continuation t0 =
  t0.has_seen_a_non_liftable_continuation

(** val is_cold : t -> bool **)

let is_cold t0 = t0.is_cold

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  let { round = round0;
        machine_width = machine_width0;
        typing_env = typing_env0;
        inlined_debuginfo = inlined_debuginfo0;
        disable_inlining = disable_inlining0;
        disable_partial_application_stub_generation =
          disable_partial_application_stub_generation0;
        inlined_attribute_to_forward = inlined_attribute_to_forward0;
        inlining_state = inlining_state0;
        propagating_float_consts = propagating_float_consts0;
        at_unit_toplevel = at_unit_toplevel0;
        unit_toplevel_return_continuation = unit_toplevel_return_continuation0;
        unit_toplevel_exn_continuation = unit_toplevel_exn_continuation0;
        unit_toplevel_alloc_region = unit_toplevel_alloc_region0;
        variables_defined_at_toplevel = variables_defined_at_toplevel0;
        cse = cse0;
        comparison_results = comparison_results0;
        are_rebuilding_terms = are_rebuilding_terms0;
        closure_info = closure_info0;
        get_imported_code = _;
        all_code = all_code0;
        inlining_history_tracker = _;
        loopify_state = loopify_state0;
        replay_history = replay_history0;
        specialization_cost = specialization_cost0;
        join_analysis = join_analysis0;
        defined_variables_by_scope = defined_variables_by_scope0;
        lifted = _;
        cost_of_lifting_continuations_out_of_current_one =
          cost_of_lifting_continuations_out_of_current_one0;
        has_seen_a_non_liftable_continuation =
          has_seen_a_non_liftable_continuation0;
        is_cold = is_cold0
      } =
    t0
  in
  Misc.Sexp.print ppf
    [ (fun x__1 x__2 x__3 -> Misc.Sexp.d ?colour:x__1 x__2 x__3)
        None "round" round0;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "machine_width" machine_width0 Target_system.Machine_width.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "typing_env" typing_env0 TE.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "inlined_debuginfo" inlined_debuginfo0 Inlined_debuginfo.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "disable_inlining" disable_inlining0 Disable_inlining.print;
      (fun x__1 x__2 x__3 -> Misc.Sexp.b ?colour:x__1 x__2 x__3)
        None "disable_partial_application_stub_generation"
        disable_partial_application_stub_generation0;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.o ?colour:x__1 x__2 x__3 x__4)
        None "inlined_attribute_to_forward" inlined_attribute_to_forward0
        (fun ppf0 pat ->
          (fun f__1 x__0 ->
            match x__0 with x__1, ~forwarded_from:x__2 -> f__1 x__1 x__2)
            (fun attribute forwarded_from ->
              Format.fprintf ppf0 "%a@ %a" Inlined_attribute.print attribute
                Inlined_debuginfo.print forwarded_from)
            pat);
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "inlining_state" inlining_state0 Inlining_state.print;
      (fun x__1 x__2 x__3 -> Misc.Sexp.b ?colour:x__1 x__2 x__3)
        None "propagating_float_consts" propagating_float_consts0;
      (fun x__1 x__2 x__3 -> Misc.Sexp.b ?colour:x__1 x__2 x__3)
        None "at_unit_toplevel" at_unit_toplevel0;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "unit_toplevel_return_continuation"
        unit_toplevel_return_continuation0 Continuation.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "unit_toplevel_exn_continuation" unit_toplevel_exn_continuation0
        Continuation.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "unit_toplevel_alloc_region" unit_toplevel_alloc_region0
        Variable.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "variables_defined_at_toplevel" variables_defined_at_toplevel0
        Variable.Set.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "cse" cse0 CSE.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "comparison_results" comparison_results0
        (Variable.Map.print Comparison_result.print);
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "are_rebuilding_terms" are_rebuilding_terms0
        Are_rebuilding_terms.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "closure_info" closure_info0 Closure_info.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "all_code" all_code0
        (Code_id.Map.print Code.print);
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "loopify_state" loopify_state0 Loopify_state.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "replay_history" replay_history0 Replay_history.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "specialization_cost" specialization_cost0
        Specialization_cost.print;
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "join_analysis" join_analysis0
        ((fun x__1 x__2 x__3 x__4 ->
           Format.pp_print_option ?none:x__1 x__2 x__3 x__4)
           (Some (fun ppf0 _ -> Format.fprintf ppf0 "()"))
           T.Join_analysis.print);
      (fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)
        None "defined_variables_by_scope" defined_variables_by_scope0
        ((fun x__1 x__2 x__3 x__4 ->
           Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
           (Some Format.pp_print_space) Lifted_cont_params.print);
      (fun x__1 x__2 x__3 -> Misc.Sexp.d ?colour:x__1 x__2 x__3)
        None "cost_of_lifting_continuations_out_of_current_one"
        cost_of_lifting_continuations_out_of_current_one0;
      (fun x__1 x__2 x__3 -> Misc.Sexp.b ?colour:x__1 x__2 x__3)
        None "has_seen_a_non_liftable_continuation"
        has_seen_a_non_liftable_continuation0;
      (fun x__1 x__2 x__3 -> Misc.Sexp.b ?colour:x__1 x__2 x__3)
        None "is_cold" is_cold0 ]

(** val define_continuations : bool -> t -> Continuation.t list -> t coq_M **)

let define_continuations can_be_lifted t0 conts =
  let replay_history0 =
    Replay_history.define_continuations can_be_lifted conts t0.replay_history
  in
  (fun t replay_history -> { t with replay_history }) t0 replay_history0

(** val define_variable0 : bool -> t -> Bound_var.t -> K.t -> t coq_M **)

let define_variable0 extra t0 var kind =
  let replay_history0 =
    if extra
    then t0.replay_history
    else Replay_history.define_variable (Bound_var.var var) t0.replay_history
  in
  let defined_variables_by_scope0 =
    if extra || Variable.Set.mem (Bound_var.var var) t0.lifted
    then t0.defined_variables_by_scope
    else
      match t0.defined_variables_by_scope with
      | [] -> Misc.fatal_errorf "Empty stack of defined variables in denv."
      | variables_defined_in_current_continuation0 :: r ->
        let kind0 = Flambda_kind.With_subkind.anything kind in
        let variables_defined_in_current_continuation1 =
          Lifted_cont_params.new_param
            variables_defined_in_current_continuation0 replay_history0
            (Bound_parameter.create (Bound_var.var var) kind0
               (Bound_var.debug_uid var))
        in
        variables_defined_in_current_continuation1 :: r
  in
  let typing_env0 =
    let var0 = Bound_name.create_var var in
    TE.add_definition t0.typing_env var0 kind
  in
  let variables_defined_at_toplevel0 =
    if t0.at_unit_toplevel
    then Variable.Set.add (Bound_var.var var) t0.variables_defined_at_toplevel
    else t0.variables_defined_at_toplevel
  in
  (fun t
    typing_env
    replay_history
    variables_defined_at_toplevel
    defined_variables_by_scope
  ->
    { t with
      typing_env;
      replay_history;
      variables_defined_at_toplevel;
      defined_variables_by_scope
    })
    t0 typing_env0 replay_history0 variables_defined_at_toplevel0
    defined_variables_by_scope0

(** val define_variable : t -> Bound_var.t -> K.t -> t coq_M **)

let define_variable t0 var kind = define_variable0 false t0 var kind

(** val define_extra_variable : t -> Bound_var.t -> K.t -> t coq_M **)

let define_extra_variable t0 var kind = define_variable0 true t0 var kind

(** val create : int -> Target_system.Machine_width.t -> resolver ->
    get_imported_code -> bool -> Continuation.t -> Continuation.t -> Variable.t
    -> t coq_M **)

let create round0 machine_width0 resolver0 get_imported_code0
    propagating_float_consts0 unit_toplevel_exn_continuation0
    unit_toplevel_return_continuation0 toplevel_my_alloc_region =
  let typing_env0 = TE.create machine_width0 resolver0 in
  let specialization_cost0 =
    Specialization_cost.cannot_specialize Specialization_cost.At_toplevel
  in
  let inlining_history_tracker0 =
    Inlining_history.Tracker.empty (Current_unit.get_cu_exn ())
  in
  let inlining_state0 = Inlining_state.default round0 in
  { round = round0;
    machine_width = machine_width0;
    typing_env = typing_env0;
    inlined_debuginfo = Inlined_debuginfo.none;
    disable_inlining = Disable_inlining.Do_not_disable_inlining;
    disable_partial_application_stub_generation = false;
    inlined_attribute_to_forward = None;
    inlining_state = inlining_state0;
    propagating_float_consts = propagating_float_consts0;
    at_unit_toplevel = true;
    unit_toplevel_return_continuation = unit_toplevel_return_continuation0;
    unit_toplevel_exn_continuation = unit_toplevel_exn_continuation0;
    unit_toplevel_alloc_region = toplevel_my_alloc_region;
    variables_defined_at_toplevel = Variable.Set.empty;
    cse = CSE.empty;
    comparison_results = Variable.Map.empty;
    are_rebuilding_terms = Are_rebuilding_terms.are_rebuilding;
    closure_info = Closure_info.not_in_a_closure;
    get_imported_code = get_imported_code0;
    all_code = Code_id.Map.empty;
    inlining_history_tracker = inlining_history_tracker0;
    loopify_state = Loopify_state.do_not_loopify;
    replay_history = Replay_history.first_pass;
    specialization_cost = specialization_cost0;
    join_analysis = None;
    defined_variables_by_scope = Lifted_cont_params.empty :: [];
    lifted = Variable.Set.empty;
    cost_of_lifting_continuations_out_of_current_one = 0;
    has_seen_a_non_liftable_continuation = false;
    is_cold = false
  }

(** val resolver : t -> resolver coq_M **)

let resolver t0 = TE.resolver t0.typing_env

(** val get_continuation_scope : t -> Scope.t coq_M **)

let get_continuation_scope t0 = TE.current_scope t0.typing_env

(** val set_at_unit_toplevel_state : t -> bool -> t coq_M **)

let set_at_unit_toplevel_state =
 fun t at_unit_toplevel -> { t with at_unit_toplevel }

(** val is_defined_at_toplevel : t -> Variable.t -> bool coq_M **)

let is_defined_at_toplevel t0 var =
  Variable.Set.mem var t0.variables_defined_at_toplevel

(** val get_inlining_state : t -> Inlining_state.t coq_M **)

let get_inlining_state t0 = t0.inlining_state

(** val set_inlining_state : t -> Inlining_state.t -> t coq_M **)

let set_inlining_state = fun t inlining_state -> { t with inlining_state }

(** val relative_history : t -> Inlining_history.Relative.t coq_M **)

let relative_history t0 =
  Inlining_history.Tracker.relative t0.inlining_history_tracker

(** val set_inlining_history_tracker : Inlining_history.Tracker.t -> t -> t
    coq_M **)

let set_inlining_history_tracker inlining_history_tracker0 t0 =
  (fun t inlining_history_tracker -> { t with inlining_history_tracker })
    t0 inlining_history_tracker0

(** val increment_continuation_scope : t -> t coq_M **)

let increment_continuation_scope t0 =
  (fun t typing_env -> { t with typing_env })
    t0
    (TE.increment_scope t0.typing_env)

(** val bump_current_level_scope : t -> t coq_M **)

let bump_current_level_scope t0 =
  (fun t typing_env -> { t with typing_env })
    t0
    (TE.bump_current_level_scope t0.typing_env)

(** val enter_stub_function : t -> t coq_M **)

let enter_stub_function t0 =
  (fun t disable_inlining disable_partial_application_stub_generation ->
    { t with disable_inlining; disable_partial_application_stub_generation })
    t0 (Disable_inlining.Disable_inlining Disable_inlining_reason.Stub)
    (Flambda_features.simplify_stubs ()
    || t0.disable_partial_application_stub_generation)

(** val enter_set_of_closures : t -> t coq_M **)

let enter_set_of_closures t0 =
  let { round = round0;
        machine_width = machine_width0;
        typing_env = typing_env0;
        inlined_debuginfo = _;
        disable_inlining = disable_inlining0;
        disable_partial_application_stub_generation =
          disable_partial_application_stub_generation0;
        inlined_attribute_to_forward = _;
        inlining_state = inlining_state0;
        propagating_float_consts = propagating_float_consts0;
        at_unit_toplevel = _;
        unit_toplevel_return_continuation = unit_toplevel_return_continuation0;
        unit_toplevel_exn_continuation = unit_toplevel_exn_continuation0;
        unit_toplevel_alloc_region = unit_toplevel_alloc_region0;
        variables_defined_at_toplevel = variables_defined_at_toplevel0;
        cse = _;
        comparison_results = _;
        are_rebuilding_terms = are_rebuilding_terms0;
        closure_info = _;
        get_imported_code = get_imported_code0;
        all_code = all_code0;
        inlining_history_tracker = inlining_history_tracker0;
        loopify_state = _;
        replay_history = _;
        specialization_cost = _;
        join_analysis = _;
        defined_variables_by_scope = _;
        lifted = _;
        cost_of_lifting_continuations_out_of_current_one = _;
        has_seen_a_non_liftable_continuation = _;
        is_cold = _
      } =
    t0
  in
  let specialization_cost0 =
    Specialization_cost.cannot_specialize Specialization_cost.At_toplevel
  in
  let typing_env1 = TE.closure_env typing_env0 in
  { round = round0;
    machine_width = machine_width0;
    typing_env = typing_env1;
    inlined_debuginfo = Inlined_debuginfo.none;
    disable_inlining = disable_inlining0;
    disable_partial_application_stub_generation =
      disable_partial_application_stub_generation0;
    inlined_attribute_to_forward = None;
    inlining_state = inlining_state0;
    propagating_float_consts = propagating_float_consts0;
    at_unit_toplevel = false;
    unit_toplevel_return_continuation = unit_toplevel_return_continuation0;
    unit_toplevel_exn_continuation = unit_toplevel_exn_continuation0;
    unit_toplevel_alloc_region = unit_toplevel_alloc_region0;
    variables_defined_at_toplevel = variables_defined_at_toplevel0;
    cse = CSE.empty;
    comparison_results = Variable.Map.empty;
    are_rebuilding_terms = are_rebuilding_terms0;
    closure_info = Closure_info.in_a_set_of_closures;
    get_imported_code = get_imported_code0;
    all_code = all_code0;
    inlining_history_tracker = inlining_history_tracker0;
    loopify_state = Loopify_state.do_not_loopify;
    replay_history = Replay_history.first_pass;
    specialization_cost = specialization_cost0;
    join_analysis = None;
    defined_variables_by_scope = Lifted_cont_params.empty :: [];
    lifted = Variable.Set.empty;
    cost_of_lifting_continuations_out_of_current_one = 0;
    has_seen_a_non_liftable_continuation = false;
    is_cold = false
  }

(** val define_symbol : t -> Symbol.t -> K.t -> t coq_M **)

let define_symbol t0 sym kind =
  let typing_env0 =
    let sym0 = Bound_name.create (Name.symbol sym) Name_mode.normal in
    TE.add_definition t0.typing_env sym0 kind
  in
  (fun t typing_env -> { t with typing_env }) t0 typing_env0

(** val define_name : t -> Bound_name.t -> K.t -> t coq_M **)

let define_name t0 name kind =
  Name.pattern_match (Bound_name.name name)
    (fun var ->
      define_variable t0
        (Bound_var.create var Flambda_debug_uid.none
           (Bound_name.name_mode name))
        kind)
    (fun sym -> define_symbol t0 sym kind)

(** val add_variable0 : bool -> t -> Bound_var.t -> T.t -> t coq_M **)

let add_variable0 extra t0 var ty =
  let t1 = define_variable0 extra t0 var (T.kind ty) in
  (fun t typing_env -> { t with typing_env })
    t1
    (TE.add_equation t1.typing_env (Name.var (Bound_var.var var)) ty)

(** val add_variable : t -> Bound_var.t -> T.t -> t coq_M **)

let add_variable t0 var ty = add_variable0 false t0 var ty

(** val add_symbol : t -> Symbol.t -> T.t -> t coq_M **)

let add_symbol t0 sym ty =
  let t1 = define_symbol t0 sym (T.kind ty) in
  (fun t typing_env -> { t with typing_env })
    t1
    (TE.add_equation t1.typing_env (Name.symbol sym) ty)

(** val add_name : t -> Bound_name.t -> T.t -> t coq_M **)

let add_name t0 name ty =
  Name.pattern_match (Bound_name.name name)
    (fun var ->
      add_variable t0
        (Bound_var.create var Flambda_debug_uid.none
           (Bound_name.name_mode name))
        ty)
    (fun sym -> add_symbol t0 sym ty)

(** val add_equation_on_variable : t -> Variable.t -> T.t -> t coq_M **)

let add_equation_on_variable t0 var ty =
  let typing_env0 = TE.add_equation t0.typing_env (Name.var var) ty in
  (fun t typing_env -> { t with typing_env }) t0 typing_env0

(** val mem_name : t -> Name.t -> bool coq_M **)

let mem_name t0 name =
  (fun x__1 x__2 x__3 -> TE.mem ?min_name_mode:x__1 x__2 x__3)
    None t0.typing_env name

(** val mem_variable : t -> Variable.t -> bool coq_M **)

let mem_variable t0 var =
  (fun x__1 x__2 x__3 -> TE.mem ?min_name_mode:x__1 x__2 x__3)
    None t0.typing_env (Name.var var)

(** val add_equation_on_symbol : t -> Symbol.t -> T.t -> t coq_M **)

let add_equation_on_symbol t0 sym ty =
  let typing_env0 =
    let sym0 = Name.symbol sym in
    TE.add_equation t0.typing_env sym0 ty
  in
  (fun t typing_env -> { t with typing_env }) t0 typing_env0

(** val mem_symbol : t -> Symbol.t -> bool coq_M **)

let mem_symbol t0 sym = mem_name t0 (Name.symbol sym)

(** val find_symbol : t -> Symbol.t -> T.t coq_M **)

let find_symbol t0 sym = TE.find t0.typing_env (Name.symbol sym) (Some K.value)

(** val add_symbol_projection : t -> Variable.t -> Symbol_projection.t -> t
    coq_M **)

let add_symbol_projection t0 var proj =
  (fun t typing_env -> { t with typing_env })
    t0
    (TE.add_symbol_projection t0.typing_env var proj)

(** val find_symbol_projection : t -> Variable.t -> Symbol_projection.t option
    coq_M **)

let find_symbol_projection t0 var = TE.find_symbol_projection t0.typing_env var

(** val define_name_if_undefined : t -> Bound_name.t -> K.t -> t coq_M **)

let define_name_if_undefined t0 name kind =
  if
    (fun x__1 x__2 x__3 -> TE.mem ?min_name_mode:x__1 x__2 x__3)
      None t0.typing_env (Bound_name.name name)
  then t0
  else define_name t0 name kind

(** val add_equation_on_name : t -> Name.t -> T.t -> t coq_M **)

let add_equation_on_name t0 name ty =
  let typing_env0 = TE.add_equation t0.typing_env name ty in
  (fun t typing_env -> { t with typing_env }) t0 typing_env0

(** val define_parameters : bool -> t -> Bound_parameters.t -> t coq_M **)

let define_parameters extra t0 params =
  List.fold_left
    (fun t1 param ->
      let param_var, param_duid = BP.var_and_uid param in
      let var = Bound_var.create param_var param_duid Name_mode.normal in
      define_variable0 extra t1 var (K.With_subkind.kind (BP.kind param)))
    t0
    (Bound_parameters.to_list params)

(** val add_parameters : bool -> Name_mode.t option -> t -> Bound_parameters.t
    -> T.t list -> t coq_M **)

let add_parameters extra name_mode t0 params param_types =
  let name_mode0 =
    match name_mode with
    | Some name_mode0 -> name_mode0
    | None -> Name_mode.normal
  in
  let params' = params in
  let params0 = Bound_parameters.to_list params in
  let () =
    if List.compare_lengths params0 param_types <> 0
    then
      Misc.fatal_errorf
        "Mismatch between number of [params] and [param_types]:@ (%a)@ and@ %a"
        Bound_parameters.print params'
        ((fun x__1 x__2 x__3 x__4 ->
           Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
           (Some Format.pp_print_space) T.print)
        param_types
    else ()
  in
  List.fold_left2
    (fun t1 param param_type ->
      let param_var, param_duid = BP.var_and_uid param in
      let var = Bound_var.create param_var param_duid name_mode0 in
      add_variable0 extra t1 var param_type)
    t0 params0 param_types

(** val add_parameters_with_unknown_types : bool -> Alloc_mode.For_types.t list
    option -> Name_mode.t option -> t -> Bound_parameters.t -> t coq_M **)

let add_parameters_with_unknown_types extra alloc_modes name_mode t0 params =
  let params' = params in
  let params0 = Bound_parameters.to_list params in
  let alloc_modes0 =
    match alloc_modes with
    | Some alloc_modes0 ->
      let () =
        if List.compare_lengths alloc_modes0 params0 <> 0
        then
          Misc.fatal_errorf "Params and alloc modes do not match up:@ %a"
            Bound_parameters.print params'
        else ()
      in
      alloc_modes0
    | None -> List.map (fun _ -> Alloc_mode.For_types.unknown ()) params0
  in
  let param_types =
    ListLabels.map2
      (fun param alloc_mode ->
        (fun x__1 x__2 x__3 ->
          T.unknown_with_subkind ?alloc_mode:x__1 x__2 x__3)
          (Some alloc_mode) t0.machine_width (BP.kind param))
      params0 alloc_modes0
  in
  add_parameters extra name_mode t0 params' param_types

(** val mark_parameters_as_toplevel : t -> Bound_parameters.t -> t coq_M **)

let mark_parameters_as_toplevel t0 params =
  let variables_defined_at_toplevel0 =
    Variable.Set.union t0.variables_defined_at_toplevel
      (Bound_parameters.var_set params)
  in
  (fun t variables_defined_at_toplevel ->
    { t with variables_defined_at_toplevel })
    t0 variables_defined_at_toplevel0

(** val extend_typing_environment : t ->
    T.Typing_env_extension.With_extra_variables.t -> t coq_M **)

let extend_typing_environment t0 env_extension0 =
  let typing_env0 =
    TE.add_env_extension_with_extra_variables t0.typing_env env_extension0
  in
  (fun t typing_env -> { t with typing_env }) t0 typing_env0

(** val with_typing_env : t -> TE.t -> t coq_M **)

let with_typing_env = fun t typing_env -> { t with typing_env }

(** val map_typing_env : t -> (TE.t -> TE.t coq_M) -> t coq_M **)

let map_typing_env t0 f = with_typing_env t0 (f t0.typing_env)

(** val check_name_is_bound : t -> Name.t -> unit coq_M **)

let check_name_is_bound t0 name =
  if
    not
      ((fun x__1 x__2 x__3 -> TE.mem ?min_name_mode:x__1 x__2 x__3)
         None t0.typing_env name)
  then
    Misc.fatal_errorf "Unbound name %a in environment:@ %a" Name.print name
      print t0
  else ()

(** val check_simple_is_bound : t -> Simple.t -> unit coq_M **)

let check_simple_is_bound t0 simple =
  Simple.pattern_match simple
    (fun name _ -> check_name_is_bound t0 name)
    (fun _ -> ())

(** val mem_code : t -> Code_id.t -> bool coq_M **)

let mem_code t0 id =
  Code_id.Map.mem id t0.all_code
  || Exported_code.mem id (t0.get_imported_code ())

(** val find_code_metadata_exn : t -> Code_id.t -> Code_metadata.t coq_M **)

let find_code_metadata_exn t0 id =
  Port_monad.match_exn
    (fun _ -> Code_id.Map.find id t0.all_code)
    Port_monad.not_found
    (fun _ ->
      Port_monad.match_exn
        (fun _ -> Exported_code.find_exn (t0.get_imported_code ()) id)
        Port_monad.not_found
        (fun _ ->
          let _ = TE.resolver t0.typing_env (Code_id.get_compilation_unit id) in
          Code_or_metadata.code_metadata
            (Exported_code.find_exn (t0.get_imported_code ()) id))
        Code_or_metadata.code_metadata)
    Code.code_metadata

(** val find_code_exn : t -> Code_id.t -> Code_or_metadata.t coq_M **)

let find_code_exn t0 id =
  match Code_id.Map.find_or_null id t0.all_code with
  | Or_null.Null ->
    let _ = TE.resolver t0.typing_env (Code_id.get_compilation_unit id) in
    Exported_code.find_exn (t0.get_imported_code ()) id
  | Or_null.This code -> Code_or_metadata.create code

(** val define_code : t -> Code_id.t -> Code.t -> t coq_M **)

let define_code t0 code_id code =
  let () =
    if not (Code_id.in_compilation_unit code_id (Current_unit.get_cu_exn ()))
    then
      Misc.fatal_errorf
        "Cannot define code ID %a as it is from another unit:@ %a" Code_id.print
        code_id Code.print code
    else ()
  in
  let () =
    if not (Code_id.equal code_id (Code.code_id code))
    then
      Misc.fatal_errorf "Code ID %a does not match code ID in@ %a" Code_id.print
        code_id Code.print code
    else ()
  in
  let typing_env0 =
    TE.add_to_code_age_relation t0.typing_env code_id
      (Code.newer_version_of code)
  in
  let all_code0 = Code_id.Map.add code_id code t0.all_code in
  (fun t typing_env all_code -> { t with typing_env; all_code })
    t0 typing_env0 all_code0

(** val add_cse : t -> Flambda_primitive.Eligible_for_cse.t -> Simple.t ->
    Name_mode.t -> t coq_M **)

let add_cse t0 prim bound_to name_mode =
  if not (Name_mode.is_normal name_mode)
  then t0
  else
    let scope = get_continuation_scope t0 in
    let cse0 = CSE.add t0.cse prim bound_to scope in
    let comparison_results0 =
      let prim0 = Flambda_primitive.Eligible_for_cse.to_primitive prim in
      let bound_to_var = Simple.must_be_var bound_to in
      let comparison_result =
        Comparison_result.create prim0 t0.comparison_results
      in
      match comparison_result with
      | Some comp -> (
        match bound_to_var with
        | Some p ->
          let var, _ = p in
          Variable.Map.add var comp t0.comparison_results
        | None -> t0.comparison_results)
      | None -> t0.comparison_results
    in
    (fun t cse comparison_results -> { t with cse; comparison_results })
      t0 cse0 comparison_results0

(** val find_cse : t -> Flambda_primitive.Eligible_for_cse.t -> Simple.t option
    coq_M **)

let find_cse t0 prim = CSE.find t0.cse prim

(** val find_comparison_result : t -> Variable.t -> Comparison_result.t option
    coq_M **)

let find_comparison_result t0 var =
  Variable.Map.find_opt var t0.comparison_results

(** val with_cse : t -> CSE.t -> t coq_M **)

let with_cse = fun t cse -> { t with cse }

(** val set_do_not_rebuild_terms_and_disable_inlining : t ->
    Disable_inlining_reason.t -> t coq_M **)

let set_do_not_rebuild_terms_and_disable_inlining t0 disable_inlining_reason =
  (fun t are_rebuilding_terms disable_inlining ->
    { t with are_rebuilding_terms; disable_inlining })
    t0 Are_rebuilding_terms.are_not_rebuilding
    (Disable_inlining.Disable_inlining disable_inlining_reason)

(** val set_disable_inlining : t -> Disable_inlining_reason.t -> t coq_M **)

let set_disable_inlining t0 reason =
  (fun t disable_inlining -> { t with disable_inlining })
    t0 (Disable_inlining.Disable_inlining reason)

(** val set_rebuild_terms : t -> t coq_M **)

let set_rebuild_terms t0 =
  (fun t are_rebuilding_terms -> { t with are_rebuilding_terms })
    t0 Are_rebuilding_terms.are_rebuilding

(** val enter_closure : Code_id.t -> Continuation.t -> Continuation.t ->
    Variable.t -> Variable.t -> t -> t coq_M **)

let enter_closure code_id return_continuation exn_continuation my_closure
    my_alloc_region t0 =
  (fun t closure_info -> { t with closure_info })
    t0
    (Closure_info.in_a_closure code_id return_continuation exn_continuation
       my_closure my_alloc_region)

(** val inlining_arguments : t -> Inlining_arguments.t coq_M **)

let inlining_arguments t0 = Inlining_state.arguments t0.inlining_state

(** val set_inlining_arguments : Inlining_arguments.t -> t -> t coq_M **)

let set_inlining_arguments arguments t0 =
  (fun t inlining_state -> { t with inlining_state })
    t0
    (Inlining_state.with_arguments arguments t0.inlining_state)

(** val set_inlined_debuginfo : t -> t -> t coq_M **)

let set_inlined_debuginfo t0 from =
  (fun t inlined_debuginfo -> { t with inlined_debuginfo })
    t0 from.inlined_debuginfo

(** val inlined_attribute_to_forward_through_inlined_apply : t ->
    Inlined_debuginfo.t -> Inlined_attribute.t -> (Inlined_attribute.t *
    forwarded_from:Inlined_debuginfo.t) option coq_M **)

let inlined_attribute_to_forward_through_inlined_apply t0 from_apply_expr
    inlined_attribute =
  match inlined_attribute with
  | Inlined_attribute.Always_inlined _ ->
    let inlined = inlined_attribute in
    Some
      ((fun (x__1, x__2) -> x__1, ~forwarded_from:x__2)
         (inlined, from_apply_expr))
  | Inlined_attribute.Hint_inlined ->
    let inlined = inlined_attribute in
    Some
      ((fun (x__1, x__2) -> x__1, ~forwarded_from:x__2)
         (inlined, from_apply_expr))
  | Inlined_attribute.Forward_inlined ->
    Option.map
      (fun pat ->
        (fun f__1 x__0 ->
          match x__0 with x__1, ~forwarded_from:x__2 -> f__1 x__1 x__2)
          (fun inlined forwarded_from ->
            (fun (x__1, x__2) -> x__1, ~forwarded_from:x__2)
              (inlined, Inlined_debuginfo.merge forwarded_from from_apply_expr))
          pat)
      t0.inlined_attribute_to_forward
  | Inlined_attribute.Never_inlined ->
    let inlined = inlined_attribute in
    Some
      ((fun (x__1, x__2) -> x__1, ~forwarded_from:x__2)
         (inlined, from_apply_expr))
  | Inlined_attribute.Unroll (_, _) ->
    let inlined = inlined_attribute in
    Some
      ((fun (x__1, x__2) -> x__1, ~forwarded_from:x__2)
         (inlined, from_apply_expr))
  | Inlined_attribute.Default_inlined ->
    let inlined = inlined_attribute in
    Some
      ((fun (x__1, x__2) -> x__1, ~forwarded_from:x__2)
         (inlined, from_apply_expr))

(** val merge_inlined_debuginfo_and_forward_inlined_attribute : t ->
    Inlined_debuginfo.t -> Inlined_attribute.t -> t coq_M **)

let merge_inlined_debuginfo_and_forward_inlined_attribute t0 from_apply_expr
    inlined_attribute =
  let inlined_attribute_to_forward0 =
    inlined_attribute_to_forward_through_inlined_apply t0 from_apply_expr
      inlined_attribute
  in
  (fun t inlined_attribute_to_forward inlined_debuginfo ->
    { t with inlined_attribute_to_forward; inlined_debuginfo })
    t0 inlined_attribute_to_forward0
    (Inlined_debuginfo.merge t0.inlined_debuginfo from_apply_expr)

(** val add_inlined_debuginfo : t -> Debuginfo.t -> Debuginfo.t coq_M **)

let add_inlined_debuginfo t0 dbg =
  Inlined_debuginfo.rewrite t0.inlined_debuginfo dbg

(** val enter_inlined_apply : Code.t -> Apply.t -> bool -> t -> t coq_M **)

let enter_inlined_apply called_code apply was_inline_always t0 =
  let arguments =
    let arguments = Inlining_state.arguments t0.inlining_state in
    let arguments0 =
      Inlining_arguments.combine arguments (Code.inlining_arguments called_code)
    in
    Inlining_arguments.combine arguments0 (Apply.inlining_arguments apply)
  in
  let inlining_state0 =
    let is_stub = Code.stub called_code in
    let increment =
      if is_stub
      then 0
      else if was_inline_always
      then 1
      else Flambda_features.Inlining.depth_scaling_factor
    in
    Inlining_state.with_arguments arguments
      (Inlining_state.increment_depth t0.inlining_state is_stub increment)
  in
  let inlined_debuginfo0 =
    Inlined_debuginfo.create (Code.code_id called_code) (Apply.dbg apply)
  in
  let inlined_attribute_to_forward0 =
    inlined_attribute_to_forward_through_inlined_apply t0 inlined_debuginfo0
      (Apply.inlined apply)
  in
  (fun t
    inlined_debuginfo
    inlined_attribute_to_forward
    inlining_state
    inlining_history_tracker
  ->
    { t with
      inlined_debuginfo;
      inlined_attribute_to_forward;
      inlining_state;
      inlining_history_tracker
    })
    t0 inlined_debuginfo0 inlined_attribute_to_forward0 inlining_state0
    (Inlining_history.Tracker.enter_inlined_apply (Apply.dbg apply)
       (Code.absolute_history called_code)
       (Apply.relative_history apply)
       t0.inlining_history_tracker)

(** val generate_phantom_lets : t -> bool coq_M **)

let generate_phantom_lets t0 =
  Flambda_features.debug ()
  && Flambda_features.Expert.phantom_lets ()
  && Are_rebuilding_terms.do_rebuild_terms t0.are_rebuilding_terms

(** val set_loopify_state : Loopify_state.t -> t -> t coq_M **)

let set_loopify_state loopify_state0 t0 =
  (fun t loopify_state -> { t with loopify_state }) t0 loopify_state0

(** val with_code_age_relation : T.Code_age_relation.t -> t -> t coq_M **)

let with_code_age_relation code_age_relation t0 =
  (fun t typing_env -> { t with typing_env })
    t0
    (TE.with_code_age_relation t0.typing_env code_age_relation)

(** val with_join_analysis : Apply_cont_rewrite_id.t T.Join_analysis.t option ->
    t -> t coq_M **)

let with_join_analysis join_analysis0 t0 =
  (fun t join_analysis -> { t with join_analysis }) t0 join_analysis0

(** val with_replay_history : (Replay_history.t * bool) option -> t -> t coq_M **)

let with_replay_history replay t0 =
  let replay_history0 =
    match replay with
    | Some p ->
      let previous_history, always_inline = p in
      Replay_history.replay always_inline previous_history
    | None -> Replay_history.first_pass
  in
  (fun t replay_history -> { t with replay_history }) t0 replay_history0

(** val enter_continuation_handler : Lifted_cont_params.t -> t -> t coq_M **)

let enter_continuation_handler lifted_params t0 =
  let lifted0 =
    Lifted_cont_params.fold Variable.Set.empty
      (fun bp set -> Variable.Set.add (Bound_parameter.var bp) set)
      lifted_params
  in
  (fun t
    lifted
    defined_variables_by_scope
    cost_of_lifting_continuations_out_of_current_one
    has_seen_a_non_liftable_continuation
    specialization_cost
  ->
    { t with
      lifted;
      defined_variables_by_scope;
      cost_of_lifting_continuations_out_of_current_one;
      has_seen_a_non_liftable_continuation;
      specialization_cost
    })
    t0 lifted0
    (lifted_params :: t0.defined_variables_by_scope)
    0 false
    (Specialization_cost.can_specialize ())

(** val add_lifted_constant_state : unit option -> t -> LCS.t -> t coq_M **)

let add_lifted_constant_state maybe_already_defined denv lifted0 =
  let initial_denv = denv in
  let maybe_already_defined0 =
    match maybe_already_defined with
    | Some u ->
      let () = u in
      true
    | None -> false
  in
  let denv0 =
    LCS.fold lifted0 denv (fun denv0 lifted_constant ->
        let types_of_symbols = LC.types_of_symbols lifted_constant in
        Symbol.Map.fold
          (fun sym pat denv1 ->
            let _, typ = pat in
            if maybe_already_defined0 && mem_symbol denv1 sym
            then denv1
            else define_symbol denv1 sym (T.kind typ))
          types_of_symbols denv0)
  in
  let typing_env0 =
    let typing_env0 = denv0.typing_env in
    LCS.fold lifted0 typing_env0 (fun typing_env1 lifted_constant ->
        let types_of_symbols = LC.types_of_symbols lifted_constant in
        Symbol.Map.fold
          (fun sym pat typing_env2 ->
            let typing_env_at_definition, typ = pat in
            if maybe_already_defined0 && mem_symbol initial_denv sym
            then typing_env2
            else
              let sym0 = Name.symbol sym in
              let env_extension0 =
                T.make_suitable_for_environment typing_env_at_definition
                  (T.Everything_not_in typing_env2) ((sym0, typ) :: [])
              in
              TE.add_env_extension_with_extra_variables typing_env2
                env_extension0)
          types_of_symbols typing_env1)
  in
  LCS.fold lifted0 (with_typing_env denv0 typing_env0)
    (fun denv1 lifted_constant ->
      let pieces_of_code =
        Rebuilt_static_const.Group.pieces_of_code_including_those_not_rebuilt
          (LC.defining_exprs lifted_constant)
      in
      Code_id.Map.fold
        (fun code_id code denv2 ->
          if maybe_already_defined0 && mem_code denv2 code_id
          then denv2
          else define_code denv2 code_id code)
        pieces_of_code denv1)

(** val variables_defined_in_current_continuation : t -> Lifted_cont_params.t
    coq_M **)

let variables_defined_in_current_continuation t0 =
  match t0.defined_variables_by_scope with
  | [] -> Misc.fatal_errorf "Empty stack of defined_variables_by_scope in denv"
  | res :: _ -> res

(** val add_lifting_cost : int -> t -> t coq_M **)

let add_lifting_cost cost t0 =
  if cost < 0
  then Misc.fatal_errorf "Negative cost of lifting continuation"
  else
    (fun t cost_of_lifting_continuations_out_of_current_one ->
      { t with cost_of_lifting_continuations_out_of_current_one })
      t0
      (t0.cost_of_lifting_continuations_out_of_current_one + cost)

(** val set_has_seen_a_non_liftable_continuation : t -> t coq_M **)

let set_has_seen_a_non_liftable_continuation t0 =
  if t0.has_seen_a_non_liftable_continuation
  then t0
  else
    (fun t has_seen_a_non_liftable_continuation ->
      { t with has_seen_a_non_liftable_continuation })
      t0 true

(** val mark_as_cold : t -> t coq_M **)

let mark_as_cold t0 =
  if t0.is_cold then t0 else (fun t is_cold -> { t with is_cold }) t0 true

(** val must_inline : t -> bool coq_M **)

let must_inline t0 = Replay_history.must_inline t0.replay_history

(** val record_inlining_decision : Apply_expr.t ->
    Call_site_inlining_decision_type.t -> t -> t coq_M **)

let record_inlining_decision apply decision t0 =
  (fun t replay_history -> { t with replay_history })
    t0
    (Replay_history.record_inlining_decision apply decision t0.replay_history)

(** val map_specialization_cost : (Specialization_cost.t ->
    Specialization_cost.t coq_M) -> t -> t coq_M **)

let map_specialization_cost f t0 =
  let specialization_cost0 = f t0.specialization_cost in
  (fun t specialization_cost -> { t with specialization_cost })
    t0 specialization_cost0

(** val denv_for_lifted_continuation : t -> t -> t coq_M **)

let denv_for_lifted_continuation denv_for_join denv =
  { round = denv.round;
    machine_width = denv.machine_width;
    typing_env = denv_for_join.typing_env;
    inlined_debuginfo = denv.inlined_debuginfo;
    disable_inlining = denv.disable_inlining;
    disable_partial_application_stub_generation =
      denv.disable_partial_application_stub_generation;
    inlined_attribute_to_forward = denv.inlined_attribute_to_forward;
    inlining_state = denv.inlining_state;
    propagating_float_consts = denv.propagating_float_consts;
    at_unit_toplevel = denv_for_join.at_unit_toplevel;
    unit_toplevel_return_continuation = denv.unit_toplevel_return_continuation;
    unit_toplevel_exn_continuation = denv.unit_toplevel_exn_continuation;
    unit_toplevel_alloc_region = denv.unit_toplevel_alloc_region;
    variables_defined_at_toplevel = denv_for_join.variables_defined_at_toplevel;
    cse = denv_for_join.cse;
    comparison_results = denv_for_join.comparison_results;
    are_rebuilding_terms = denv.are_rebuilding_terms;
    closure_info = denv.closure_info;
    get_imported_code = denv.get_imported_code;
    all_code = denv_for_join.all_code;
    inlining_history_tracker = denv.inlining_history_tracker;
    loopify_state = denv.loopify_state;
    replay_history = denv_for_join.replay_history;
    specialization_cost = denv_for_join.specialization_cost;
    join_analysis = denv_for_join.join_analysis;
    defined_variables_by_scope = denv_for_join.defined_variables_by_scope;
    lifted = denv_for_join.lifted;
    cost_of_lifting_continuations_out_of_current_one =
      denv_for_join.cost_of_lifting_continuations_out_of_current_one;
    has_seen_a_non_liftable_continuation =
      denv_for_join.has_seen_a_non_liftable_continuation;
    is_cold = denv_for_join.is_cold
  }

let add_parameters extra ?name_mode t params param_types =
  add_parameters extra name_mode t params param_types

let add_parameters_with_unknown_types extra ?alloc_modes ?name_mode t params =
  add_parameters_with_unknown_types extra alloc_modes name_mode t params

let add_lifted_constant_state ?maybe_already_defined denv lifted =
  add_lifted_constant_state maybe_already_defined denv lifted
