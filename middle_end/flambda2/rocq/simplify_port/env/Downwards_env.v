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

(* This file follows middle_end/flambda2/simplify/env/downwards_env.ml
   (Git blob fe73117d4c5332850e055ad644d58f98927424f7), definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the arguments by place, a setter
   [update_...] where the compiler writes [{ t with ... }]) is that of
   GUIDE.md; the type [attribute_to_forward] for a tuple with a label; the
   names of the values that the form must name. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Apply_cont_rewrite_id Apply_expr
  Are_rebuilding_terms Bound_name Bound_parameter Bound_parameters Bound_var
  Call_site_inlining_decision_type Closure_info Code Code_id Code_metadata
  Code_or_metadata Common_subexpression_elimination Comparison_result
  Compilation_unit Continuation Current_unit Debuginfo Exported_code Flambda
  Flambda2_types Flambda_debug_uid Flambda_features Flambda_kind
  Flambda_primitive Format Inlined_attribute Inlined_debuginfo
  Inlining_arguments Inlining_history Inlining_state Int_ids Lifted_constant
  Lifted_constant_state Lifted_cont_params List ListLabels Loopify_state
  Misc Name Name_mode Option Or_null Rebuilt_static_const Replay_history
  Scope Simple Specialization_cost Symbol Symbol_projection Target_system
  Variable_.
Import Flambda.Import_.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda2_types.to_erase Or_null.t
   Specialization_cost.reason *)
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17 *)
(*OCAML
open! Flambda.Import
OCAML*)

(* 18-24 *)
From SimplifyPort.abbrev.downwards_env Require Import Port_abbreviations.
(*OCAML
module CSE = Common_subexpression_elimination
module K = Flambda_kind
module BP = Bound_parameter
module T = Flambda2_types
module TE = Flambda2_types.Typing_env
module LCS = Lifted_constant_state
module LC = Lifted_constant
OCAML*)

(* 26-29. The two types have the names of a function and of a field of the
   file: they are the compiler's text, and in Rocq they are [resolver_] and
   [get_imported_code_]. *)
(*OCAML
type resolver =
  Compilation_unit.t -> Flambda2_types.Typing_env.Serializable.t option

type get_imported_code = unit -> Exported_code.t
OCAML*)

(* 26-27 *)
Definition resolver_ : Type :=
  Compilation_unit.t -> M (option Flambda2_types.Typing_env.Serializable.t).
Extract Inlined Constant resolver_ => "resolver".

(* 29 *)
Definition get_imported_code_ : Type := unit -> M Exported_code.t.
Extract Inlined Constant get_imported_code_ => "get_imported_code".

(* 31-39 *)
Module Disable_inlining_reason.
  (* 32-34 *)
  Inductive t : Type :=
  | Stub
  | Speculative_inlining.

  (* 36-38 *)
  Definition print (ppf : Format.formatter) (x : t) : M unit :=
    match x with
    | Stub => Format.fprintf0 ppf "Stub"
    | Speculative_inlining => Format.fprintf0 ppf "Speculative_inlining"
    end.
End Disable_inlining_reason.

(* 41-51 *)
Module Disable_inlining.
  (* 42-44 *)
  Inductive t : Type :=
  | Disable_inlining (_ : Disable_inlining_reason.t)
  | Do_not_disable_inlining.

  (* 46-50 *)
  Definition print (ppf : Format.formatter) (x : t) : M unit :=
    match x with
    | Disable_inlining reason =>
      Format.fprintf2 ppf "@[<hov 1>(Disable_inlining %a)@]"
        Disable_inlining_reason.print reason
    | Do_not_disable_inlining =>
      Format.fprintf0 ppf "Do_not_disable_inlining"
    end.
End Disable_inlining.

(* PORT-GAP(type): 60-61, the field [inlined_attribute_to_forward] holds a
   tuple with a label, [(Inlined_attribute.t *
   forwarded_from:Inlined_debuginfo.t)], which Rocq cannot print. Here it is
   a type of one constructor, built and matched as the compiler's tuple. *)
Inductive attribute_to_forward : Type :=
| Attribute_to_forward :
    Inlined_attribute.t -> Inlined_debuginfo.t -> attribute_to_forward.
Extract Inductive attribute_to_forward => "(Inlined_attribute.t * forwarded_from:Inlined_debuginfo.t)" [ "(fun (x__1, x__2) -> (x__1, ~forwarded_from:x__2))" ] "(fun f__1 x__0 -> match x__0 with x__1, ~forwarded_from:x__2 -> f__1 x__1 x__2)".

(* 53-112 *)
Record t : Type :=
  { round : int;
    machine_width : Target_system.Machine_width.t;
    typing_env : TE.t;
    inlined_debuginfo : Inlined_debuginfo.t;
    disable_inlining : Disable_inlining.t;
    disable_partial_application_stub_generation : bool;
    inlined_attribute_to_forward : option attribute_to_forward;
    inlining_state : Inlining_state.t;
    propagating_float_consts : bool;
    at_unit_toplevel : bool;
    unit_toplevel_return_continuation : Continuation.t;
    unit_toplevel_exn_continuation : Continuation.t;
    unit_toplevel_alloc_region : Variable_.t;
    variables_defined_at_toplevel : Variable_.Set_.t;
    cse : CSE.t;
    comparison_results : Variable_.Map.t Comparison_result.t;
    are_rebuilding_terms : Are_rebuilding_terms.t;
    closure_info : Closure_info.t;
    get_imported_code : unit -> M Exported_code.t;
    all_code : Code_id.Map.t Code.t;
    inlining_history_tracker : Inlining_history.Tracker.t;
    loopify_state : Loopify_state.t;
    replay_history : Replay_history.t
    (* Replay history for the current continuation handler (or toplevel) *);
    specialization_cost : Specialization_cost.t
    (* Accumulator to record whether the handler of the current continuation can
       be specialized, or whether there are reasons why it could not (or rather
       why it would not be beneficial) *);
    join_analysis : option (T.Join_analysis.t Apply_cont_rewrite_id.t)
    (* Analysis from the latest join point. *);
    defined_variables_by_scope : list Lifted_cont_params.t
    (* Stack of variables defined. The first element of the list refers to
       variables defined by the current continuation, and the last element
       of the list to variables that are defined at toplevel. We use the
       type [Lifted_cont_params.t] because the current only use of this
       field is the continuation lifting process. *);
    lifted : Variable_.Set_.t
    (* This field provides a fast access to the set of parameters (as
       variables) added to the current continuation by the continuation
       lifting process. For these variables, it's important that we do not
       generate a fresh [Lifted_cont_param] when we execute
       [define_variable]. Note that this set will always be a subset of the
       head of the defined_variables_by_scope field. *);
    cost_of_lifting_continuations_out_of_current_one : int
    (* This cost is the number of parameters that would have to be created
       if we lifted all continuations that are defined in the current
       continuation's handler. *);
    has_seen_a_non_liftable_continuation : bool
    (* This flag is used to mark as non-liftable any continuation that is
       bound after a non-liftable continuation, since any continuation bound
       after a non-liftable continuation may refer to it.

       CR gbury: we may not need to do this if we had free_names on handlers
       that we have not explored yet. *);
    is_cold : bool
    (* This flag is used to mark cold contexts, i.e. the body of cold
       functions and continuations. *)
  }.

(* PORT-GAP(loose): 25 functions of the compiler only read the field of
   their name: each IS the projection of the record [t] under that name. It
   is pure in Rocq, and Rocq prints it as [let f t = t.f] after the type.
   They are [all_code] (278), [machine_width] (280), [typing_env] (284),
   [round] (286), [disable_inlining] (290),
   [disable_partial_application_stub_generation] (292-293),
   [inlined_attribute_to_forward] (295), [propagating_float_consts] (297),
   [unit_toplevel_exn_continuation] (299),
   [unit_toplevel_return_continuation] (301), [unit_toplevel_alloc_region]
   (303), [at_unit_toplevel] (305), [defined_variables_by_scope] (312),
   [inlining_history_tracker] (318), [cse] (606), [comparison_results]
   (608), [are_rebuilding_terms] (647), [closure_info] (657),
   [loopify_state] (760), [join_analysis] (771),
   [cost_of_lifting_continuations_out_of_current_one] (858-859),
   [has_seen_a_non_liftable_continuation] (870-871), [is_cold] (878),
   [replay_history] (884) and [specialization_cost] (896). Where the
   compiler calls one of them ([typing_env denv]), this file reads the
   field. *)

(* 114-188 *)
(* PORT-GAP(loose): the record pattern of the parameter is a match; 146,
   [let open! Misc.Sexp] is written out. *)
Definition print (ppf : Format.formatter) (t : Downwards_env.t) : M unit :=
  match t with
  | {| round := round;
       machine_width := machine_width;
       typing_env := typing_env;
       inlined_debuginfo := inlined_debuginfo;
       disable_inlining := disable_inlining;
       disable_partial_application_stub_generation :=
         disable_partial_application_stub_generation;
       inlined_attribute_to_forward := inlined_attribute_to_forward;
       inlining_state := inlining_state;
       propagating_float_consts := propagating_float_consts;
       at_unit_toplevel := at_unit_toplevel;
       unit_toplevel_return_continuation := unit_toplevel_return_continuation;
       unit_toplevel_exn_continuation := unit_toplevel_exn_continuation;
       unit_toplevel_alloc_region := unit_toplevel_alloc_region;
       variables_defined_at_toplevel := variables_defined_at_toplevel;
       cse := cse;
       comparison_results := comparison_results;
       are_rebuilding_terms := are_rebuilding_terms;
       closure_info := closure_info;
       get_imported_code := _;
       all_code := all_code;
       inlining_history_tracker := _;
       loopify_state := loopify_state;
       replay_history := replay_history;
       specialization_cost := specialization_cost;
       join_analysis := join_analysis;
       defined_variables_by_scope := defined_variables_by_scope;
       lifted := _;
       cost_of_lifting_continuations_out_of_current_one :=
         cost_of_lifting_continuations_out_of_current_one;
       has_seen_a_non_liftable_continuation :=
         has_seen_a_non_liftable_continuation;
       is_cold := is_cold
    |} =>
    (* 148-188: the elements of the list, the last first. *)
    let! tmp1 := Misc.Sexp.b None "is_cold" is_cold in
    let! tmp2 :=
      Misc.Sexp.b None "has_seen_a_non_liftable_continuation"
        has_seen_a_non_liftable_continuation
    in
    let! tmp3 :=
      Misc.Sexp.d None "cost_of_lifting_continuations_out_of_current_one"
        cost_of_lifting_continuations_out_of_current_one
    in
    let! tmp4 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space)
        Lifted_cont_params.print
    in
    let! tmp5 :=
      Misc.Sexp.a None "defined_variables_by_scope"
        defined_variables_by_scope tmp4
    in
    let! tmp6 :=
      papp2 Format.pp_print_option
        (Some
           (fun (ppf : Format.formatter) (_ : unit) =>
             Format.fprintf0 ppf "()"))
        T.Join_analysis.print
    in
    let! tmp7 := Misc.Sexp.a None "join_analysis" join_analysis tmp6 in
    let! tmp8 :=
      Misc.Sexp.a None "specialization_cost" specialization_cost
        Specialization_cost.print
    in
    let! tmp9 :=
      Misc.Sexp.a None "replay_history" replay_history Replay_history.print
    in
    let! tmp10 :=
      Misc.Sexp.a None "loopify_state" loopify_state Loopify_state.print
    in
    let! tmp11 := papp1 Code_id.Map.print Code.print in
    let! tmp12 := Misc.Sexp.a None "all_code" all_code tmp11 in
    let! tmp13 :=
      Misc.Sexp.a None "closure_info" closure_info Closure_info.print
    in
    let! tmp14 :=
      Misc.Sexp.a None "are_rebuilding_terms" are_rebuilding_terms
        Are_rebuilding_terms.print
    in
    let! tmp15 := papp1 Variable_.Map.print Comparison_result.print in
    let! tmp16 :=
      Misc.Sexp.a None "comparison_results" comparison_results tmp15
    in
    let! tmp17 := Misc.Sexp.a None "cse" cse CSE.print in
    let! tmp18 :=
      Misc.Sexp.a None "variables_defined_at_toplevel"
        variables_defined_at_toplevel Variable_.Set_.print
    in
    let! tmp19 :=
      Misc.Sexp.a None "unit_toplevel_alloc_region"
        unit_toplevel_alloc_region Variable_.print
    in
    let! tmp20 :=
      Misc.Sexp.a None "unit_toplevel_exn_continuation"
        unit_toplevel_exn_continuation Continuation.print
    in
    let! tmp21 :=
      Misc.Sexp.a None "unit_toplevel_return_continuation"
        unit_toplevel_return_continuation Continuation.print
    in
    let! tmp22 := Misc.Sexp.b None "at_unit_toplevel" at_unit_toplevel in
    let! tmp23 :=
      Misc.Sexp.b None "propagating_float_consts" propagating_float_consts
    in
    let! tmp24 :=
      Misc.Sexp.a None "inlining_state" inlining_state Inlining_state.print
    in
    let! tmp25 :=
      Misc.Sexp.o None "inlined_attribute_to_forward"
        inlined_attribute_to_forward
        (fun (ppf : Format.formatter) (pat : attribute_to_forward) =>
          match pat with
          | Attribute_to_forward attribute forwarded_from =>
            Format.fprintf4 ppf "%a@ %a" Inlined_attribute.print attribute
              Inlined_debuginfo.print forwarded_from
          end)
    in
    let! tmp26 :=
      Misc.Sexp.b None "disable_partial_application_stub_generation"
        disable_partial_application_stub_generation
    in
    let! tmp27 :=
      Misc.Sexp.a None "disable_inlining" disable_inlining
        Disable_inlining.print
    in
    let! tmp28 :=
      Misc.Sexp.a None "inlined_debuginfo" inlined_debuginfo
        Inlined_debuginfo.print
    in
    let! tmp29 := Misc.Sexp.a None "typing_env" typing_env TE.print in
    let! tmp30 :=
      Misc.Sexp.a None "machine_width" machine_width
        Target_system.Machine_width.print
    in
    let! tmp31 := Misc.Sexp.d None "round" round in
    Misc.Sexp.print ppf
      [ tmp31; tmp30; tmp29; tmp28; tmp27; tmp26; tmp25; tmp24; tmp23; tmp22;
        tmp21; tmp20; tmp19; tmp18; tmp17; tmp16; tmp14; tmp13; tmp12; tmp10;
        tmp9; tmp8; tmp7; tmp5; tmp3; tmp2; tmp1 ]
  end.

(* 194, 782 and 887-890. [{ t with replay_history }]. *)
Definition update_replay_history (t : Downwards_env.t)
    (replay_history : Replay_history.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := replay_history;
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_replay_history =>
  "(fun t replay_history -> { t with replay_history = replay_history })".

(* 190-194. In the compiler: [~can_be_lifted t conts]. *)
Definition define_continuations (can_be_lifted : bool) (t : Downwards_env.t)
    (conts : list Continuation.t) : M Downwards_env.t :=
  let* replay_history :=
    Replay_history.define_continuations can_be_lifted conts
      t.(Downwards_env.replay_history)
  in
  ret (update_replay_history t replay_history).

(* 227-232. [{ t with typing_env; replay_history;
   variables_defined_at_toplevel; defined_variables_by_scope }]. *)
Definition update_typing_env_replay_history_variables_defined_at_toplevel_defined_variables_by_scope
    (t : Downwards_env.t) (typing_env : TE.t)
    (replay_history : Replay_history.t)
    (variables_defined_at_toplevel : Variable_.Set_.t)
    (defined_variables_by_scope : list Lifted_cont_params.t)
    : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := typing_env; inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := variables_defined_at_toplevel;
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := replay_history;
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := defined_variables_by_scope;
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_typing_env_replay_history_variables_defined_at_toplevel_defined_variables_by_scope =>
  "(fun t typing_env replay_history variables_defined_at_toplevel
   defined_variables_by_scope -> { t with typing_env = typing_env;
   replay_history = replay_history; variables_defined_at_toplevel =
   variables_defined_at_toplevel; defined_variables_by_scope =
   defined_variables_by_scope })".

(* 196-232. In the compiler: [~extra t var kind]. *)
Definition define_variable0 (extra : bool) (t : Downwards_env.t)
    (var : Bound_var.t) (kind : K.t) : M Downwards_env.t :=
  let* replay_history :=
    if extra
    then ret t.(Downwards_env.replay_history)
    else
      let! tmp1 := Bound_var.var var in
      Replay_history.define_variable tmp1 t.(Downwards_env.replay_history)
  in
  (* 202-217 *)
  let* defined_variables_by_scope :=
    let! tmp1 :=
      or_else extra
        (let! tmp2 := Bound_var.var var in
         Variable_.Set_.mem tmp2 t.(Downwards_env.lifted))
    in
    if tmp1
    then ret t.(Downwards_env.defined_variables_by_scope)
    else
      match t.(Downwards_env.defined_variables_by_scope) with
      | [] => fatal_errorf0 "Empty stack of defined variables in denv."
      | variables_defined_in_current_continuation :: r =>
        let* kind := Flambda_kind.With_subkind.anything kind in
        let* variables_defined_in_current_continuation :=
          let! tmp1 := Bound_var.debug_uid var in
          let! tmp2 := Bound_var.var var in
          let! tmp3 := Bound_parameter.create tmp2 kind tmp1 in
          Lifted_cont_params.new_param
            variables_defined_in_current_continuation replay_history tmp3
        in
        ret (variables_defined_in_current_continuation :: r)
      end
  in
  (* 218-221 *)
  let* typing_env :=
    let* var := Bound_name.create_var var in
    TE.add_definition t.(Downwards_env.typing_env) var kind
  in
  let* variables_defined_at_toplevel :=
    if t.(Downwards_env.at_unit_toplevel)
    then
      let! tmp1 := Bound_var.var var in
      Variable_.Set_.add tmp1 t.(Downwards_env.variables_defined_at_toplevel)
    else ret t.(Downwards_env.variables_defined_at_toplevel)
  in
  ret
    (update_typing_env_replay_history_variables_defined_at_toplevel_defined_variables_by_scope
       t typing_env replay_history variables_defined_at_toplevel
       defined_variables_by_scope).

(* 234-235 *)
(* PORT-GAP(loose): the attribute [@inlined hint] is not kept, here and at
   238, 414, 420, 423, 429 and 432. *)
Definition define_variable (t : Downwards_env.t) (var : Bound_var.t)
    (kind : K.t) : M Downwards_env.t :=
  define_variable0 false t var kind.

(* 237-238 *)
Definition define_extra_variable (t : Downwards_env.t) (var : Bound_var.t)
    (kind : K.t) : M Downwards_env.t :=
  define_variable0 true t var kind.

(* 240-276. In the compiler: [~round ~machine_width ~(resolver : resolver)
   ~(get_imported_code : get_imported_code) ~propagating_float_consts
   ~unit_toplevel_exn_continuation ~unit_toplevel_return_continuation
   ~toplevel_my_alloc_region]. *)
Definition create (round : int)
    (machine_width : Target_system.Machine_width.t) (resolver : resolver_)
    (get_imported_code : get_imported_code_) (propagating_float_consts : bool)
    (unit_toplevel_exn_continuation : Continuation.t)
    (unit_toplevel_return_continuation : Continuation.t)
    (toplevel_my_alloc_region : Variable_.t) : M Downwards_env.t :=
  let* typing_env := TE.create machine_width resolver in
  (* PORT-GAP(record-order): 245-276, three fields of the record have a
     call: [specialization_cost], the last of them in the type, first; then
     [inlining_history_tracker]; then [inlining_state].
     VERDICT (record_order/README.md, place 3): COMMUTE, FAILURES ORDERED. No
     call writes when it succeeds. One call alone can fail
     ([Current_unit.get_cu_exn], when no unit is set; it prints its message
     before it fails), so the order chooses nothing. *)
  let* specialization_cost :=
    Specialization_cost.cannot_specialize Specialization_cost.At_toplevel
  in
  let* inlining_history_tracker :=
    let! tmp1 := Current_unit.get_cu_exn tt in
    Inlining_history.Tracker.empty tmp1
  in
  let* inlining_state := Inlining_state.default round in
  ret
    {| round := round;
       machine_width := machine_width;
       typing_env := typing_env;
       inlined_debuginfo := Inlined_debuginfo.none;
       disable_inlining := Disable_inlining.Do_not_disable_inlining;
       disable_partial_application_stub_generation := false;
       inlined_attribute_to_forward := None;
       inlining_state := inlining_state;
       propagating_float_consts := propagating_float_consts;
       at_unit_toplevel := true;
       unit_toplevel_return_continuation := unit_toplevel_return_continuation;
       unit_toplevel_exn_continuation := unit_toplevel_exn_continuation;
       unit_toplevel_alloc_region := toplevel_my_alloc_region;
       variables_defined_at_toplevel := Variable_.Set_.empty;
       cse := CSE.empty;
       comparison_results := Variable_.Map.empty;
       are_rebuilding_terms := Are_rebuilding_terms.are_rebuilding;
       closure_info := Closure_info.not_in_a_closure;
       get_imported_code := get_imported_code;
       all_code := Code_id.Map.empty;
       inlining_history_tracker := inlining_history_tracker;
       loopify_state := Loopify_state.do_not_loopify;
       replay_history := Replay_history.first_pass;
       specialization_cost := specialization_cost;
       join_analysis := None;
       defined_variables_by_scope := [Lifted_cont_params.empty];
       lifted := Variable_.Set_.empty;
       cost_of_lifting_continuations_out_of_current_one := 0;
       has_seen_a_non_liftable_continuation := false;
       is_cold := false
    |}.

(* 282 *)
(* PORT-GAP(papp): [TE.resolver] is given its first argument only, and its
   definition has ONE parameter
   (middle_end/flambda2/types/env/typing_env.ml:337: it takes the
   environment and gives back one of its fields): the use runs the
   definition, which reads that field, as the compiler's own use at this
   place does. *)
Definition resolver (t : Downwards_env.t) : M resolver_ :=
  papp1 TE.resolver t.(Downwards_env.typing_env).

(* 288 *)
Definition get_continuation_scope (t : Downwards_env.t) : M Scope.t :=
  TE.current_scope t.(Downwards_env.typing_env).

(* 307. [{ t with at_unit_toplevel }]. *)
Definition update_at_unit_toplevel (t : Downwards_env.t)
    (at_unit_toplevel : bool) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := at_unit_toplevel;
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_at_unit_toplevel =>
  "(fun t at_unit_toplevel -> { t with at_unit_toplevel = at_unit_toplevel })".

(* 307 *)
Definition set_at_unit_toplevel_state (t : Downwards_env.t)
    (at_unit_toplevel : bool) : M Downwards_env.t :=
  ret (update_at_unit_toplevel t at_unit_toplevel).

(* 309-310 *)
Definition is_defined_at_toplevel (t : Downwards_env.t) (var : Variable_.t)
    : M bool :=
  Variable_.Set_.mem var t.(Downwards_env.variables_defined_at_toplevel).

(* 314 *)
Definition get_inlining_state (t : Downwards_env.t) : M Inlining_state.t :=
  ret t.(Downwards_env.inlining_state).

(* 316 and 663-665. [{ t with inlining_state }]. *)
Definition update_inlining_state (t : Downwards_env.t)
    (inlining_state : Inlining_state.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := inlining_state;
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_inlining_state =>
  "(fun t inlining_state -> { t with inlining_state = inlining_state })".

(* 316 *)
Definition set_inlining_state (t : Downwards_env.t)
    (inlining_state : Inlining_state.t) : M Downwards_env.t :=
  ret (update_inlining_state t inlining_state).

(* 320-321 *)
Definition relative_history (t : Downwards_env.t)
    : M Inlining_history.Relative.t :=
  Inlining_history.Tracker.relative t.(Downwards_env.inlining_history_tracker).

(* 324. [{ t with inlining_history_tracker }]. *)
Definition update_inlining_history_tracker (t : Downwards_env.t)
    (inlining_history_tracker : Inlining_history.Tracker.t)
    : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := inlining_history_tracker;
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_inlining_history_tracker =>
  "(fun t inlining_history_tracker -> { t with inlining_history_tracker =
   inlining_history_tracker })".

(* 323-324 *)
Definition set_inlining_history_tracker
    (inlining_history_tracker : Inlining_history.Tracker.t)
    (t : Downwards_env.t) : M Downwards_env.t :=
  ret (update_inlining_history_tracker t inlining_history_tracker).

(* 327, 330, 409, 424-426, 433, 448, 459, 466, 477, 540, 542 and 765-767. [{ t
   with typing_env }]. *)
Definition update_typing_env (t : Downwards_env.t) (typing_env : TE.t)
    : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := typing_env; inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_typing_env =>
  "(fun t typing_env -> { t with typing_env = typing_env })".

(* 326-327 *)
Definition increment_continuation_scope (t : Downwards_env.t)
    : M Downwards_env.t :=
  let! tmp1 := TE.increment_scope t.(Downwards_env.typing_env) in
  ret (update_typing_env t tmp1).

(* 329-330 *)
Definition bump_current_level_scope (t : Downwards_env.t)
    : M Downwards_env.t :=
  let! tmp1 := TE.bump_current_level_scope t.(Downwards_env.typing_env) in
  ret (update_typing_env t tmp1).

(* 333-338. [{ t with disable_inlining;
   disable_partial_application_stub_generation }]. *)
Definition update_disable_inlining_disable_partial_application_stub_generation
    (t : Downwards_env.t) (disable_inlining : Disable_inlining.t)
    (disable_partial_application_stub_generation : bool) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := disable_inlining;
     disable_partial_application_stub_generation :=
       disable_partial_application_stub_generation;
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_disable_inlining_disable_partial_application_stub_generation =>
  "(fun t disable_inlining disable_partial_application_stub_generation -> { t
   with disable_inlining = disable_inlining;
   disable_partial_application_stub_generation =
   disable_partial_application_stub_generation })".

(* 332-338 *)
Definition enter_stub_function (t : Downwards_env.t) : M Downwards_env.t :=
  let! tmp1 := Flambda_features.simplify_stubs tt in
  ret
    (update_disable_inlining_disable_partial_application_stub_generation t
       (Disable_inlining.Disable_inlining Disable_inlining_reason.Stub)
       (tmp1
        || t.(Downwards_env.disable_partial_application_stub_generation))).

(* 340-402 *)
(* PORT-GAP(loose): the record pattern of the parameter is a match. *)
Definition enter_set_of_closures (t : Downwards_env.t) : M Downwards_env.t :=
  match t with
  | {| machine_width := machine_width;
       round := round;
       typing_env := typing_env;
       inlined_debuginfo := _;
       disable_inlining := disable_inlining;
       disable_partial_application_stub_generation :=
         disable_partial_application_stub_generation;
       inlined_attribute_to_forward := _;
       inlining_state := inlining_state;
       propagating_float_consts := propagating_float_consts;
       at_unit_toplevel := _;
       unit_toplevel_return_continuation := unit_toplevel_return_continuation;
       unit_toplevel_exn_continuation := unit_toplevel_exn_continuation;
       unit_toplevel_alloc_region := unit_toplevel_alloc_region;
       variables_defined_at_toplevel := variables_defined_at_toplevel;
       cse := _;
       comparison_results := _;
       are_rebuilding_terms := are_rebuilding_terms;
       closure_info := _;
       get_imported_code := get_imported_code;
       all_code := all_code;
       inlining_history_tracker := inlining_history_tracker;
       loopify_state := _;
       replay_history := _;
       specialization_cost := _;
       defined_variables_by_scope := _;
       lifted := _;
       cost_of_lifting_continuations_out_of_current_one := _;
       has_seen_a_non_liftable_continuation := _;
       join_analysis := _;
       is_cold := _
    |} =>
    (* PORT-GAP(record-order): 372-402, two fields of the record have a
       call: [specialization_cost], the later one in the type, first; then
       [typing_env].
       VERDICT (record_order/README.md, place 4): COMMUTE. [TE.closure_env] and
       [Specialization_cost.cannot_specialize]: no write, no read of state, no
       failure. *)
    let* specialization_cost :=
      Specialization_cost.cannot_specialize Specialization_cost.At_toplevel
    in
    let* typing_env := TE.closure_env typing_env in
    ret
      {| round := round;
         machine_width := machine_width;
         typing_env := typing_env;
         inlined_debuginfo := Inlined_debuginfo.none;
         disable_inlining := disable_inlining;
         disable_partial_application_stub_generation :=
           disable_partial_application_stub_generation;
         inlined_attribute_to_forward := None;
         inlining_state := inlining_state;
         propagating_float_consts := propagating_float_consts;
         at_unit_toplevel := false;
         unit_toplevel_return_continuation :=
           unit_toplevel_return_continuation;
         unit_toplevel_exn_continuation := unit_toplevel_exn_continuation;
         unit_toplevel_alloc_region := unit_toplevel_alloc_region;
         variables_defined_at_toplevel := variables_defined_at_toplevel;
         cse := CSE.empty;
         comparison_results := Variable_.Map.empty;
         are_rebuilding_terms := are_rebuilding_terms;
         closure_info := Closure_info.in_a_set_of_closures;
         get_imported_code := get_imported_code;
         all_code := all_code;
         inlining_history_tracker := inlining_history_tracker;
         loopify_state := Loopify_state.do_not_loopify;
         replay_history := Replay_history.first_pass;
         specialization_cost := specialization_cost;
         join_analysis := None;
         defined_variables_by_scope := [Lifted_cont_params.empty];
         lifted := Variable_.Set_.empty;
         cost_of_lifting_continuations_out_of_current_one := 0;
         has_seen_a_non_liftable_continuation := false;
         is_cold := false
      |}
  end.

(* 404-409 *)
Definition define_symbol (t : Downwards_env.t) (sym : Symbol.t) (kind : K.t)
    : M Downwards_env.t :=
  let* typing_env :=
    let* sym :=
      let! tmp1 := Name.symbol sym in
      Bound_name.create tmp1 Name_mode.normal
    in
    TE.add_definition t.(Downwards_env.typing_env) sym kind
  in
  ret (update_typing_env t typing_env).

(* 411-420. [Name.pattern_match name ~var ~symbol]: the arguments are in
   the order of the interface. *)
(* PORT-GAP(loose): 413 and 420, the attribute [@inline] of the two
   functions is not kept. *)
Definition define_name (t : Downwards_env.t) (name : Bound_name.t) (kind : K.t)
    : M Downwards_env.t :=
  let! tmp1 := Bound_name.name name in
  Name.pattern_match tmp1
    (fun var =>
      let! tmp2 := Bound_name.name_mode name in
      let! tmp3 := Bound_var.create var Flambda_debug_uid.none tmp2 in
      define_variable t tmp3 kind)
    (fun sym => define_symbol t sym kind).

(* 422-426. In the compiler: [~extra t var ty]. *)
Definition add_variable0 (extra : bool) (t : Downwards_env.t)
    (var : Bound_var.t) (ty : T.t) : M Downwards_env.t :=
  let* t :=
    let! tmp1 := T.kind ty in
    define_variable0 extra t var tmp1
  in
  let! tmp1 := Bound_var.var var in
  let! tmp2 := Name.var tmp1 in
  let! tmp3 := TE.add_equation t.(Downwards_env.typing_env) tmp2 ty in
  ret (update_typing_env t tmp3).

(* 428-429 *)
Definition add_variable (t : Downwards_env.t) (var : Bound_var.t) (ty : T.t)
    : M Downwards_env.t :=
  add_variable0 false t var ty.

(* 431-433 *)
Definition add_symbol (t : Downwards_env.t) (sym : Symbol.t) (ty : T.t)
    : M Downwards_env.t :=
  let* t :=
    let! tmp1 := T.kind ty in
    define_symbol t sym tmp1
  in
  let! tmp1 := Name.symbol sym in
  let! tmp2 := TE.add_equation t.(Downwards_env.typing_env) tmp1 ty in
  ret (update_typing_env t tmp2).

(* 435-444 *)
(* PORT-GAP(loose): 437 and 444, the attribute [@inline] of the two
   functions is not kept. *)
Definition add_name (t : Downwards_env.t) (name : Bound_name.t) (ty : T.t)
    : M Downwards_env.t :=
  let! tmp1 := Bound_name.name name in
  Name.pattern_match tmp1
    (fun var =>
      let! tmp2 := Bound_name.name_mode name in
      let! tmp3 := Bound_var.create var Flambda_debug_uid.none tmp2 in
      add_variable t tmp3 ty)
    (fun sym => add_symbol t sym ty).

(* 446-448 *)
Definition add_equation_on_variable (t : Downwards_env.t) (var : Variable_.t)
    (ty : T.t) : M Downwards_env.t :=
  let* typing_env :=
    let! tmp1 := Name.var var in
    TE.add_equation t.(Downwards_env.typing_env) tmp1 ty
  in
  ret (update_typing_env t typing_env).

(* 450 *)
Definition mem_name (t : Downwards_env.t) (name : Name.t) : M bool :=
  TE.mem None t.(Downwards_env.typing_env) name.

(* 452 *)
Definition mem_variable (t : Downwards_env.t) (var : Variable_.t) : M bool :=
  let! tmp1 := Name.var var in
  TE.mem None t.(Downwards_env.typing_env) tmp1.

(* 454-459 *)
Definition add_equation_on_symbol (t : Downwards_env.t) (sym : Symbol.t)
    (ty : T.t) : M Downwards_env.t :=
  let* typing_env :=
    let* sym := Name.symbol sym in
    TE.add_equation t.(Downwards_env.typing_env) sym ty
  in
  ret (update_typing_env t typing_env).

(* 461 *)
Definition mem_symbol (t : Downwards_env.t) (sym : Symbol.t) : M bool :=
  let! tmp1 := Name.symbol sym in
  mem_name t tmp1.

(* 463 *)
Definition find_symbol (t : Downwards_env.t) (sym : Symbol.t) : M T.t :=
  let! tmp1 := Name.symbol sym in
  TE.find t.(Downwards_env.typing_env) tmp1 (Some K.value).

(* 465-466 *)
Definition add_symbol_projection (t : Downwards_env.t) (var : Variable_.t)
    (proj : Symbol_projection.t) : M Downwards_env.t :=
  let! tmp1 := TE.add_symbol_projection t.(Downwards_env.typing_env) var proj in
  ret (update_typing_env t tmp1).

(* 468 *)
Definition find_symbol_projection (t : Downwards_env.t) (var : Variable_.t)
    : M (option Symbol_projection.t) :=
  TE.find_symbol_projection t.(Downwards_env.typing_env) var.

(* 470-473 *)
Definition define_name_if_undefined (t : Downwards_env.t) (name : Bound_name.t)
    (kind : K.t) : M Downwards_env.t :=
  let! tmp1 := Bound_name.name name in
  let! tmp2 := TE.mem None t.(Downwards_env.typing_env) tmp1 in
  if tmp2 then ret t else define_name t name kind.

(* 475-477 *)
Definition add_equation_on_name (t : Downwards_env.t) (name : Name.t) (ty : T.t)
    : M Downwards_env.t :=
  let* typing_env := TE.add_equation t.(Downwards_env.typing_env) name ty in
  ret (update_typing_env t typing_env).

(* 479-486. In the compiler: [~extra t ~params]. *)
Definition define_parameters (extra : bool) (t : Downwards_env.t)
    (params : Bound_parameters.t) : M Downwards_env.t :=
  let! tmp1 := Bound_parameters.to_list params in
  List.fold_left
    (fun (t : Downwards_env.t) param =>
      let* '(param_var, param_duid) := BP.var_and_uid param in
      let* var := Bound_var.create param_var param_duid Name_mode.normal in
      let! tmp2 := BP.kind param in
      let! tmp3 := K.With_subkind.kind tmp2 in
      define_variable0 extra t var tmp3)
    t tmp1.

(* 488-504. In the compiler: [~extra ?(name_mode = Name_mode.normal) t
   params ~param_types]; the default of [name_mode] is the first line of
   the body. *)
Definition add_parameters (extra : bool) (name_mode : option Name_mode.t)
    (t : Downwards_env.t) (params : Bound_parameters.t) (param_types : list T.t)
    : M Downwards_env.t :=
  let& name_mode :=
    match name_mode with
    | Some name_mode => name_mode
    | None => Name_mode.normal
    end
  in
  let& params' := params in
  let* params := Bound_parameters.to_list params in
  (let! tmp1 := List.compare_lengths params param_types in
   if tmp1 <>? 0
   then
     let! tmp2 :=
       papp2 Format.pp_print_list (Some Format.pp_print_space) T.print
     in
     fatal_errorf4
       "Mismatch between number of [params] and [param_types]:@ (%a)@ and@ %a"
       Bound_parameters.print params' tmp2 param_types
   else ret tt) ;;
  List.fold_left2
    (fun (t : Downwards_env.t) param param_type =>
      let* '(param_var, param_duid) := BP.var_and_uid param in
      let* var := Bound_var.create param_var param_duid name_mode in
      add_variable0 extra t var param_type)
    t params param_types.
(* PORT-GAP(verbatim): the wrapper that gives [add_parameters] its optional
   argument [?name_mode]. *)
(*OCAML-END
let add_parameters extra ?name_mode t params param_types =
  add_parameters extra name_mode t params param_types
OCAML-END*)

(* 506-524. In the compiler: [~extra ?alloc_modes ?name_mode t params]. *)
Definition add_parameters_with_unknown_types (extra : bool)
    (alloc_modes : option (list Alloc_mode.For_types.t))
    (name_mode : option Name_mode.t) (t : Downwards_env.t)
    (params : Bound_parameters.t) : M Downwards_env.t :=
  let& params' := params in
  let* params := Bound_parameters.to_list params in
  let* alloc_modes :=
    match alloc_modes with
    | Some alloc_modes =>
      (let! tmp1 := List.compare_lengths alloc_modes params in
       if tmp1 <>? 0
       then
         fatal_errorf2 "Params and alloc modes do not match up:@ %a"
           Bound_parameters.print params'
       else ret tt) ;;
      ret alloc_modes
    | None => List.map (fun _ => Alloc_mode.For_types.unknown tt) params
    end
  in
  (* 519-523. [ListLabels.map2 params alloc_modes ~f] and
     [T.unknown_with_subkind ~alloc_mode kind ~machine_width]: the arguments
     are in the order of the interfaces. *)
  let* param_types :=
    ListLabels.map2
      (fun param alloc_mode =>
        let! tmp1 := BP.kind param in
        T.unknown_with_subkind (Some alloc_mode)
          t.(Downwards_env.machine_width) tmp1)
      params alloc_modes
  in
  add_parameters extra name_mode t params' param_types.
(* PORT-GAP(verbatim): the wrapper that gives
   [add_parameters_with_unknown_types] its optional arguments [?alloc_modes]
   and [?name_mode]. *)
(*OCAML-END
let add_parameters_with_unknown_types extra ?alloc_modes ?name_mode t params =
  add_parameters_with_unknown_types extra alloc_modes name_mode t params
OCAML-END*)

(* 531. [{ t with variables_defined_at_toplevel }]. *)
Definition update_variables_defined_at_toplevel (t : Downwards_env.t)
    (variables_defined_at_toplevel : Variable_.Set_.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := variables_defined_at_toplevel;
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_variables_defined_at_toplevel =>
  "(fun t variables_defined_at_toplevel -> { t with
   variables_defined_at_toplevel = variables_defined_at_toplevel })".

(* 526-531 *)
Definition mark_parameters_as_toplevel (t : Downwards_env.t)
    (params : Bound_parameters.t) : M Downwards_env.t :=
  let* variables_defined_at_toplevel :=
    let! tmp1 := Bound_parameters.var_set params in
    Variable_.Set_.union t.(Downwards_env.variables_defined_at_toplevel) tmp1
  in
  ret (update_variables_defined_at_toplevel t variables_defined_at_toplevel).

(* 533-540 *)
Definition extend_typing_environment (t : Downwards_env.t)
    (env_extension : T.Typing_env_extension.With_extra_variables.t)
    : M Downwards_env.t :=
  (* There doesn't seem any need to augment [t.variables_defined_at_toplevel]
     here for the existential variables, since they will have [In_types]
     mode. *)
  let* typing_env :=
    TE.add_env_extension_with_extra_variables
      t.(Downwards_env.typing_env) env_extension
  in
  ret (update_typing_env t typing_env).

(* 542 *)
Definition with_typing_env (t : Downwards_env.t) (typing_env : TE.t)
    : M Downwards_env.t :=
  ret (update_typing_env t typing_env).

(* 544. In the compiler: [t ~f]. *)
Definition map_typing_env (t : Downwards_env.t) (f : TE.t -> M TE.t)
    : M Downwards_env.t :=
  let! tmp1 := f t.(Downwards_env.typing_env) in
  with_typing_env t tmp1.

(* 546-550 *)
Definition check_name_is_bound (t : Downwards_env.t) (name : Name.t)
    : M unit :=
  let! tmp1 := TE.mem None t.(Downwards_env.typing_env) name in
  if negb tmp1
  then
    fatal_errorf4 "Unbound name %a in environment:@ %a" Name.print name print
      t
  else ret tt.

(* 552-555. [Simple.pattern_match simple ~name ~const]: the arguments are
   in the order of the interface. *)
Definition check_simple_is_bound (t : Downwards_env.t) (simple : Simple.t)
    : M unit :=
  Simple.pattern_match simple
    (fun name (_ : Int_ids.Coercion.t) => check_name_is_bound t name)
    (fun _ => ret tt).

(* 557-558 *)
Definition mem_code (t : Downwards_env.t) (id : Code_id.t) : M bool :=
  let! tmp1 := Code_id.Map.mem id t.(Downwards_env.all_code) in
  or_else tmp1
    (let! tmp2 := t.(Downwards_env.get_imported_code) tt in
     Exported_code.mem id tmp2).

(* 560-575 *)
Definition find_code_metadata_exn (t : Downwards_env.t) (id : Code_id.t)
    : M Code_metadata.t :=
  match_exn
    (fun _ => Code_id.Map.find id t.(Downwards_env.all_code))
    Not_found
    (fun _ =>
      (* We don't care which unit the metadata is coming from, so if we have
         already loaded the metadata in imported code, return it. *)
      match_exn
        (fun _ =>
          let! tmp1 := t.(Downwards_env.get_imported_code) tt in
          Exported_code.find_exn tmp1 id)
        Not_found
        (fun _ =>
          (* Sometimes the metadata is not properly reexported; try to force
             loading it. *)
          let* _ :=
            let! tmp1 := Code_id.get_compilation_unit id in
            TE.resolver t.(Downwards_env.typing_env) tmp1
          in
          let! tmp1 := t.(Downwards_env.get_imported_code) tt in
          let! tmp2 := Exported_code.find_exn tmp1 id in
          Code_or_metadata.code_metadata tmp2)
        (fun code_or_metadata =>
          Code_or_metadata.code_metadata code_or_metadata))
    (fun code => Code.code_metadata code).

(* 577-588 *)
Definition find_code_exn (t : Downwards_env.t) (id : Code_id.t)
    : M Code_or_metadata.t :=
  let! tmp1 := Code_id.Map.find_or_null id t.(Downwards_env.all_code) in
  match tmp1 with
  | Or_null.This code => Code_or_metadata.create code
  | Or_null.Null =>
    (* We might have already loaded the metadata, from another unit that
       references it. However we force loading of the corresponding .cmx to make
       sure that we will have access to the actual code (assuming the .cmx isn't
       missing). *)
    let* _ :=
      let! tmp1 := Code_id.get_compilation_unit id in
      TE.resolver t.(Downwards_env.typing_env) tmp1
    in
    let! tmp1 := t.(Downwards_env.get_imported_code) tt in
    Exported_code.find_exn tmp1 id
  end.

(* 604. [{ t with typing_env; all_code }]. *)
Definition update_typing_env_all_code (t : Downwards_env.t) (typing_env : TE.t)
    (all_code : Code_id.Map.t Code.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := typing_env; inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := all_code;
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_typing_env_all_code =>
  "(fun t typing_env all_code -> { t with typing_env = typing_env; all_code =
   all_code })".

(* 590-604. In the compiler: [t ~code_id ~code]. *)
Definition define_code (t : Downwards_env.t) (code_id : Code_id.t)
    (code : Code.t) : M Downwards_env.t :=
  (let! tmp1 := Current_unit.get_cu_exn tt in
   let! tmp2 := Code_id.in_compilation_unit code_id tmp1 in
   if negb tmp2
   then
     fatal_errorf4 "Cannot define code ID %a as it is from another unit:@ %a"
       Code_id.print code_id Code.print code
   else ret tt) ;;
  (let! tmp1 := Code.code_id code in
   let! tmp2 := Code_id.equal code_id tmp1 in
   if negb tmp2
   then
     fatal_errorf4 "Code ID %a does not match code ID in@ %a" Code_id.print
       code_id Code.print code
   else ret tt) ;;
  let* typing_env :=
    let! tmp1 := Code.newer_version_of code in
    TE.add_to_code_age_relation t.(Downwards_env.typing_env) code_id tmp1
  in
  let* all_code := Code_id.Map.add code_id code t.(Downwards_env.all_code) in
  ret (update_typing_env_all_code t typing_env all_code).

(* 626. [{ t with cse; comparison_results }]. *)
Definition update_cse_comparison_results (t : Downwards_env.t) (cse : CSE.t)
    (comparison_results : Variable_.Map.t Comparison_result.t)
    : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := cse; comparison_results := comparison_results;
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_cse_comparison_results =>
  "(fun t cse comparison_results -> { t with cse = cse; comparison_results =
   comparison_results })".

(* 610-626. In the compiler: [t prim ~bound_to ~name_mode]. *)
(* PORT-GAP(loose): 618-621, the two matched values are calls: each is
   bound to a name first, the second one first. *)
Definition add_cse (t : Downwards_env.t)
    (prim : Flambda_primitive.Eligible_for_cse.t) (bound_to : Simple.t)
    (name_mode : Name_mode.t) : M Downwards_env.t :=
  let! tmp1 := Name_mode.is_normal name_mode in
  if negb tmp1
  then ret t
  else
    let* scope := get_continuation_scope t in
    let* cse := CSE.add t.(Downwards_env.cse) prim bound_to scope in
    let* comparison_results :=
      let* prim := Flambda_primitive.Eligible_for_cse.to_primitive prim in
      let* bound_to_var := Simple.must_be_var bound_to in
      let* comparison_result :=
        Comparison_result.create prim t.(Downwards_env.comparison_results)
      in
      match comparison_result, bound_to_var with
      | None, _ | _, None => ret t.(Downwards_env.comparison_results)
      | Some comp, Some (var, _) =>
        Variable_.Map.add var comp t.(Downwards_env.comparison_results)
      end
    in
    ret (update_cse_comparison_results t cse comparison_results).

(* 628 *)
Definition find_cse (t : Downwards_env.t)
    (prim : Flambda_primitive.Eligible_for_cse.t) : M (option Simple.t) :=
  CSE.find t.(Downwards_env.cse) prim.

(* 630-631 *)
Definition find_comparison_result (t : Downwards_env.t) (var : Variable_.t)
    : M (option Comparison_result.t) :=
  Variable_.Map.find_opt var t.(Downwards_env.comparison_results).

(* 633. [{ t with cse }]. *)
Definition update_cse (t : Downwards_env.t) (cse : CSE.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := cse; comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_cse => "(fun t cse -> { t with cse = cse })".

(* 633 *)
Definition with_cse (t : Downwards_env.t) (cse : CSE.t) : M Downwards_env.t :=
  ret (update_cse t cse).

(* 636-639. [{ t with are_rebuilding_terms; disable_inlining }]. *)
Definition update_are_rebuilding_terms_disable_inlining (t : Downwards_env.t)
    (are_rebuilding_terms : Are_rebuilding_terms.t)
    (disable_inlining : Disable_inlining.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := disable_inlining;
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := are_rebuilding_terms;
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_are_rebuilding_terms_disable_inlining =>
  "(fun t are_rebuilding_terms disable_inlining -> { t with
   are_rebuilding_terms = are_rebuilding_terms; disable_inlining =
   disable_inlining })".

(* 635-639 *)
Definition set_do_not_rebuild_terms_and_disable_inlining
    (t : Downwards_env.t)
    (disable_inlining_reason : Disable_inlining_reason.t)
    : M Downwards_env.t :=
  ret
    (update_are_rebuilding_terms_disable_inlining t
       Are_rebuilding_terms.are_not_rebuilding
       (Disable_inlining.Disable_inlining disable_inlining_reason)).

(* 642. [{ t with disable_inlining }]. *)
Definition update_disable_inlining (t : Downwards_env.t)
    (disable_inlining : Disable_inlining.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := disable_inlining;
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_disable_inlining =>
  "(fun t disable_inlining -> { t with disable_inlining = disable_inlining })".

(* 641-642 *)
Definition set_disable_inlining (t : Downwards_env.t)
    (reason : Disable_inlining_reason.t) : M Downwards_env.t :=
  ret (update_disable_inlining t (Disable_inlining.Disable_inlining reason)).

(* 645. [{ t with are_rebuilding_terms }]. *)
Definition update_are_rebuilding_terms (t : Downwards_env.t)
    (are_rebuilding_terms : Are_rebuilding_terms.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := are_rebuilding_terms;
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_are_rebuilding_terms =>
  "(fun t are_rebuilding_terms -> { t with are_rebuilding_terms =
   are_rebuilding_terms })".

(* 644-645 *)
Definition set_rebuild_terms (t : Downwards_env.t) : M Downwards_env.t :=
  ret (update_are_rebuilding_terms t Are_rebuilding_terms.are_rebuilding).

(* 651-655. [{ t with closure_info }]. *)
Definition update_closure_info (t : Downwards_env.t)
    (closure_info : Closure_info.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := closure_info; get_imported_code := t.(get_imported_code);
     all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_closure_info =>
  "(fun t closure_info -> { t with closure_info = closure_info })".

(* 649-655. In the compiler: [code_id ~return_continuation
   ~exn_continuation ~my_closure ~my_alloc_region t]. *)
Definition enter_closure (code_id : Code_id.t)
    (return_continuation exn_continuation : Continuation.t)
    (my_closure my_alloc_region : Variable_.t) (t : Downwards_env.t)
    : M Downwards_env.t :=
  let! tmp1 :=
    Closure_info.in_a_closure code_id return_continuation exn_continuation
      my_closure my_alloc_region
  in
  ret (update_closure_info t tmp1).

(* 659-660 *)
(* PORT-GAP(loose): the parameter of the compiler is the pattern [{
   inlining_state; _ }]; here the field is read. *)
Definition inlining_arguments (t : Downwards_env.t)
    : M Inlining_arguments.t :=
  Inlining_state.arguments t.(Downwards_env.inlining_state).

(* 662-665 *)
Definition set_inlining_arguments (arguments : Inlining_arguments.t)
    (t : Downwards_env.t) : M Downwards_env.t :=
  let! tmp1 :=
    Inlining_state.with_arguments arguments t.(Downwards_env.inlining_state)
  in
  ret (update_inlining_state t tmp1).

(* 671. [{ t with inlined_debuginfo }]. *)
Definition update_inlined_debuginfo (t : Downwards_env.t)
    (inlined_debuginfo : Inlined_debuginfo.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := inlined_debuginfo;
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_inlined_debuginfo =>
  "(fun t inlined_debuginfo -> { t with inlined_debuginfo = inlined_debuginfo
   })".

(* 670-671. In the compiler: [t ~from]. *)
Definition set_inlined_debuginfo (t from : Downwards_env.t)
    : M Downwards_env.t :=
  ret (update_inlined_debuginfo t from.(Downwards_env.inlined_debuginfo)).

(* 673-685. In the compiler: [t ~from_apply_expr ~inlined_attribute]. *)
(* PORT-GAP(loose): 683-685, the name [inlined] that the pattern gives to
   the matched value is a [let] in the case. *)
Definition inlined_attribute_to_forward_through_inlined_apply
    (t : Downwards_env.t) (from_apply_expr : Inlined_debuginfo.t)
    (inlined_attribute : Inlined_attribute.t)
    : M (option attribute_to_forward) :=
  match inlined_attribute with
  | Inlined_attribute.Forward_inlined =>
    Option.map
      (fun (pat : attribute_to_forward) =>
        match pat with
        | Attribute_to_forward inlined forwarded_from =>
          let! tmp1 := Inlined_debuginfo.merge forwarded_from from_apply_expr in
          ret (Attribute_to_forward inlined tmp1)
        end)
      t.(Downwards_env.inlined_attribute_to_forward)
  | Inlined_attribute.Always_inlined _ | Inlined_attribute.Hint_inlined
  | Inlined_attribute.Never_inlined | Inlined_attribute.Unroll _ _
  | Inlined_attribute.Default_inlined =>
    let& inlined := inlined_attribute in
    ret (Some (Attribute_to_forward inlined from_apply_expr))
  end.

(* 693-697. [{ t with inlined_attribute_to_forward; inlined_debuginfo }]. *)
Definition update_inlined_attribute_to_forward_inlined_debuginfo
    (t : Downwards_env.t)
    (inlined_attribute_to_forward : option attribute_to_forward)
    (inlined_debuginfo : Inlined_debuginfo.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := inlined_debuginfo;
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := inlined_attribute_to_forward;
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_inlined_attribute_to_forward_inlined_debuginfo =>
  "(fun t inlined_attribute_to_forward inlined_debuginfo -> { t with
   inlined_attribute_to_forward = inlined_attribute_to_forward;
   inlined_debuginfo = inlined_debuginfo })".

(* 687-697. In the compiler: [t ~from_apply_expr ~inlined_attribute]. *)
Definition merge_inlined_debuginfo_and_forward_inlined_attribute
    (t : Downwards_env.t) (from_apply_expr : Inlined_debuginfo.t)
    (inlined_attribute : Inlined_attribute.t) : M Downwards_env.t :=
  let* inlined_attribute_to_forward :=
    inlined_attribute_to_forward_through_inlined_apply t from_apply_expr
      inlined_attribute
  in
  let! tmp1 :=
    Inlined_debuginfo.merge t.(Downwards_env.inlined_debuginfo)
      from_apply_expr
  in
  ret
    (update_inlined_attribute_to_forward_inlined_debuginfo t
       inlined_attribute_to_forward tmp1).

(* 699-700 *)
Definition add_inlined_debuginfo (t : Downwards_env.t) (dbg : Debuginfo.t)
    : M Debuginfo.t :=
  Inlined_debuginfo.rewrite t.(Downwards_env.inlined_debuginfo) dbg.

(* 741-751. [{ t with inlined_debuginfo; inlined_attribute_to_forward;
   inlining_state; inlining_history_tracker }]. *)
Definition update_inlined_debuginfo_inlined_attribute_to_forward_inlining_state_inlining_history_tracker
    (t : Downwards_env.t) (inlined_debuginfo : Inlined_debuginfo.t)
    (inlined_attribute_to_forward : option attribute_to_forward)
    (inlining_state : Inlining_state.t)
    (inlining_history_tracker : Inlining_history.Tracker.t)
    : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := inlined_debuginfo;
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := inlined_attribute_to_forward;
     inlining_state := inlining_state;
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := inlining_history_tracker;
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_inlined_debuginfo_inlined_attribute_to_forward_inlining_state_inlining_history_tracker =>
  "(fun t inlined_debuginfo inlined_attribute_to_forward inlining_state
   inlining_history_tracker -> { t with inlined_debuginfo = inlined_debuginfo;
   inlined_attribute_to_forward = inlined_attribute_to_forward; inlining_state
   = inlining_state; inlining_history_tracker = inlining_history_tracker })".

(* 702-751. In the compiler: [~called_code ~apply ~was_inline_always t]. *)
Definition enter_inlined_apply (called_code : Code.t) (apply : Apply.t)
    (was_inline_always : bool) (t : Downwards_env.t) : M Downwards_env.t :=
  (* 703-713 *)
  let* arguments :=
    let* arguments :=
      Inlining_state.arguments t.(Downwards_env.inlining_state)
    in
    let* arguments :=
      let! tmp1 := Code.inlining_arguments called_code in
      Inlining_arguments.combine arguments tmp1
    in
    let! tmp1 := Apply.inlining_arguments apply in
    Inlining_arguments.combine arguments tmp1
  in
  (* 714-731 *)
  let* inlining_state :=
    (* The depth limit for [@inline always] and [@inlined always] is really to
       make sure the compiler terminates if user code containing implicit
       recursion turns into explicit recursion within Flambda. We want to honour
       the user's requests for these attributes basically all the time. As such
       inlining when these attributes are in effect affects the depth limit much
       less than in other scenarios. *)
    let* is_stub := Code.stub called_code in
    let& increment :=
      if is_stub
      then 0
      else if was_inline_always
      then 1
      else Flambda_features.Inlining.depth_scaling_factor
    in
    let! tmp1 :=
      Inlining_state.increment_depth t.(Downwards_env.inlining_state) is_stub
        increment
    in
    Inlining_state.with_arguments arguments tmp1
  in
  (* 732-740 *)
  let* inlined_debuginfo :=
    let! tmp1 := Apply.dbg apply in
    let! tmp2 := Code.code_id called_code in
    Inlined_debuginfo.create tmp2 tmp1
  in
  let* inlined_attribute_to_forward :=
    let! tmp1 := Apply.inlined apply in
    inlined_attribute_to_forward_through_inlined_apply t inlined_debuginfo
      tmp1
  in
  (* 745-750. [Inlining_history.Tracker.enter_inlined_apply ~callee ~dbg
     ~apply_relative_history tracker]: the arguments are in the order of
     the interface. *)
  let! tmp1 := Apply.relative_history apply in
  let! tmp2 := Code.absolute_history called_code in
  let! tmp3 := Apply.dbg apply in
  let! tmp4 :=
    Inlining_history.Tracker.enter_inlined_apply tmp3 tmp2 tmp1
      t.(Downwards_env.inlining_history_tracker)
  in
  ret
    (update_inlined_debuginfo_inlined_attribute_to_forward_inlining_state_inlining_history_tracker
       t inlined_debuginfo inlined_attribute_to_forward inlining_state tmp4).

(* 753-758 *)
Definition generate_phantom_lets (t : Downwards_env.t) : M bool :=
  let! tmp1 := Flambda_features.debug tt in
  and_then tmp1
    (let! tmp2 := Flambda_features.Expert.phantom_lets tt in
     (* It would be a waste of time generating phantom lets when not rebuilding
        terms, since they have no effect on cost metrics. *)
     and_then tmp2
       (Are_rebuilding_terms.do_rebuild_terms
          t.(Downwards_env.are_rebuilding_terms))).

(* 762. [{ t with loopify_state }]. *)
Definition update_loopify_state (t : Downwards_env.t)
    (loopify_state : Loopify_state.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := loopify_state; replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_loopify_state =>
  "(fun t loopify_state -> { t with loopify_state = loopify_state })".

(* 762 *)
Definition set_loopify_state (loopify_state : Loopify_state.t)
    (t : Downwards_env.t) : M Downwards_env.t :=
  ret (update_loopify_state t loopify_state).

(* 764-767 *)
Definition with_code_age_relation (code_age_relation : T.Code_age_relation.t)
    (t : Downwards_env.t) : M Downwards_env.t :=
  let! tmp1 :=
    TE.with_code_age_relation t.(Downwards_env.typing_env) code_age_relation
  in
  ret (update_typing_env t tmp1).

(* 769. [{ t with join_analysis }]. *)
Definition update_join_analysis (t : Downwards_env.t)
    (join_analysis : option (T.Join_analysis.t Apply_cont_rewrite_id.t))
    : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := join_analysis;
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_join_analysis =>
  "(fun t join_analysis -> { t with join_analysis = join_analysis })".

(* 769 *)
Definition with_join_analysis
    (join_analysis : option (T.Join_analysis.t Apply_cont_rewrite_id.t))
    (t : Downwards_env.t) : M Downwards_env.t :=
  ret (update_join_analysis t join_analysis).

(* 773-782 *)
Definition with_replay_history (replay : option (Replay_history.t * bool))
    (t : Downwards_env.t) : M Downwards_env.t :=
  let* replay_history :=
    match replay with
    | None => ret Replay_history.first_pass
    | Some (previous_history, always_inline) =>
      Replay_history.replay always_inline previous_history
    end
  in
  ret (update_replay_history t replay_history).

(* 790-801. [{ t with lifted; defined_variables_by_scope;
   cost_of_lifting_continuations_out_of_current_one;
   has_seen_a_non_liftable_continuation; specialization_cost }]. *)
Definition update_lifted_defined_variables_by_scope_cost_of_lifting_continuations_out_of_current_one_has_seen_a_non_liftable_continuation_specialization_cost
    (t : Downwards_env.t) (lifted : Variable_.Set_.t)
    (defined_variables_by_scope : list Lifted_cont_params.t)
    (cost_of_lifting_continuations_out_of_current_one : int)
    (has_seen_a_non_liftable_continuation : bool)
    (specialization_cost : Specialization_cost.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := specialization_cost;
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := defined_variables_by_scope;
     lifted := lifted;
     cost_of_lifting_continuations_out_of_current_one :=
       cost_of_lifting_continuations_out_of_current_one;
     has_seen_a_non_liftable_continuation :=
       has_seen_a_non_liftable_continuation;
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_lifted_defined_variables_by_scope_cost_of_lifting_continuations_out_of_current_one_has_seen_a_non_liftable_continuation_specialization_cost =>
  "(fun t lifted defined_variables_by_scope
   cost_of_lifting_continuations_out_of_current_one
   has_seen_a_non_liftable_continuation specialization_cost -> { t with lifted
   = lifted; defined_variables_by_scope = defined_variables_by_scope;
   cost_of_lifting_continuations_out_of_current_one =
   cost_of_lifting_continuations_out_of_current_one;
   has_seen_a_non_liftable_continuation =
   has_seen_a_non_liftable_continuation; specialization_cost =
   specialization_cost })".

(* 784-801. [Lifted_cont_params.fold ~init ~f lifted_params]: the arguments
   are in the order of the interface. *)
Definition enter_continuation_handler (lifted_params : Lifted_cont_params.t)
    (t : Downwards_env.t) : M Downwards_env.t :=
  let* lifted :=
    Lifted_cont_params.fold Variable_.Set_.empty
      (fun bp set =>
        let! tmp1 := Bound_parameter.var bp in
        Variable_.Set_.add tmp1 set)
      lifted_params
  in
  let! tmp1 := Specialization_cost.can_specialize tt in
  ret
    (update_lifted_defined_variables_by_scope_cost_of_lifting_continuations_out_of_current_one_has_seen_a_non_liftable_continuation_specialization_cost
       t lifted
       (lifted_params :: t.(Downwards_env.defined_variables_by_scope)) 0
       (* we only do shallow lifting : thus the question of whether a continuation
          k' can be lifted out of the handler of a continuation k, does not depend
          on whether k has been lifted or not (or was liftable or not). Therefore
          we reset the `has_seen_a_non_liftable_continuation` when we enter a new
          continuation handler *)
       false tmp1).

(* 803-851. [LCS.fold lifted ~init ~f]: the arguments are in the order of
   the interface. *)
Definition add_lifted_constant_state (maybe_already_defined : option unit)
    (denv : Downwards_env.t) (lifted : LCS.t) : M Downwards_env.t :=
  let& initial_denv := denv in
  let& maybe_already_defined :=
    match maybe_already_defined with None => false | Some tt => true end
  in
  (* 808-817 *)
  let* denv :=
    LCS.fold lifted denv
      (fun (denv : Downwards_env.t) lifted_constant =>
        let* types_of_symbols := LC.types_of_symbols lifted_constant in
        Symbol.Map.fold
          (fun sym pat (denv : Downwards_env.t) =>
            let* '(_denv, typ) := ret pat in
            let! tmp1 :=
              and_then maybe_already_defined (mem_symbol denv sym)
            in
            if tmp1
            then ret denv
            else
              let! tmp2 := T.kind typ in
              define_symbol denv sym tmp2)
          types_of_symbols denv)
  in
  (* 818-839 *)
  let* typing_env :=
    let& typing_env := denv.(Downwards_env.typing_env) in
    LCS.fold lifted typing_env
      (fun typing_env lifted_constant =>
        let* types_of_symbols := LC.types_of_symbols lifted_constant in
        Symbol.Map.fold
          (fun sym pat typing_env =>
            let* '(typing_env_at_definition, typ) := ret pat in
            let! tmp1 :=
              and_then maybe_already_defined (mem_symbol initial_denv sym)
            in
            if tmp1
            then ret typing_env
            else
              let* sym := Name.symbol sym in
              let* env_extension :=
                T.make_suitable_for_environment typing_env_at_definition
                  (T.Everything_not_in typing_env) [(sym, typ)]
              in
              TE.add_env_extension_with_extra_variables
                typing_env env_extension)
          types_of_symbols typing_env)
  in
  (* 840-851 *)
  let! tmp1 := with_typing_env denv typing_env in
  LCS.fold lifted tmp1
    (fun (denv : Downwards_env.t) lifted_constant =>
      let* pieces_of_code :=
        let! tmp2 := LC.defining_exprs lifted_constant in
        Rebuilt_static_const.Group.pieces_of_code_including_those_not_rebuilt
          tmp2
      in
      Code_id.Map.fold
        (fun code_id code (denv : Downwards_env.t) =>
          let! tmp2 := and_then maybe_already_defined (mem_code denv code_id) in
          if tmp2 then ret denv else define_code denv code_id code)
        pieces_of_code denv).
(* PORT-GAP(verbatim): the wrapper that gives [add_lifted_constant_state]
   its optional argument [?maybe_already_defined]. *)
(*OCAML-END
let add_lifted_constant_state ?maybe_already_defined denv lifted =
  add_lifted_constant_state maybe_already_defined denv lifted
OCAML-END*)

(* 853-856 *)
Definition variables_defined_in_current_continuation (t : Downwards_env.t)
    : M Lifted_cont_params.t :=
  match t.(Downwards_env.defined_variables_by_scope) with
  | [] => fatal_errorf0 "Empty stack of defined_variables_by_scope in denv"
  | res :: _ => ret res
  end.

(* 865-868. [{ t with cost_of_lifting_continuations_out_of_current_one }]. *)
Definition update_cost_of_lifting_continuations_out_of_current_one
    (t : Downwards_env.t)
    (cost_of_lifting_continuations_out_of_current_one : int)
    : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       cost_of_lifting_continuations_out_of_current_one;
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_cost_of_lifting_continuations_out_of_current_one =>
  "(fun t cost_of_lifting_continuations_out_of_current_one -> { t with
   cost_of_lifting_continuations_out_of_current_one =
   cost_of_lifting_continuations_out_of_current_one })".

(* 861-868 *)
Definition add_lifting_cost (cost : int) (t : Downwards_env.t)
    : M Downwards_env.t :=
  if cost <? 0
  then fatal_errorf0 "Negative cost of lifting continuation"
  else
    ret
      (update_cost_of_lifting_continuations_out_of_current_one t
         (t.(Downwards_env.cost_of_lifting_continuations_out_of_current_one)
          + cost)).

(* 876. [{ t with has_seen_a_non_liftable_continuation }]. *)
Definition update_has_seen_a_non_liftable_continuation (t : Downwards_env.t)
    (has_seen_a_non_liftable_continuation : bool) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       has_seen_a_non_liftable_continuation;
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_has_seen_a_non_liftable_continuation =>
  "(fun t has_seen_a_non_liftable_continuation -> { t with
   has_seen_a_non_liftable_continuation = has_seen_a_non_liftable_continuation
   })".

(* 873-876 *)
Definition set_has_seen_a_non_liftable_continuation (t : Downwards_env.t)
    : M Downwards_env.t :=
  if t.(Downwards_env.has_seen_a_non_liftable_continuation)
  then ret t
  else
    ret (update_has_seen_a_non_liftable_continuation t true).

(* 880. [{ t with is_cold }]. *)
Definition update_is_cold (t : Downwards_env.t) (is_cold : bool)
    : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := t.(specialization_cost);
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := is_cold |}.
Extract Inlined Constant update_is_cold =>
  "(fun t is_cold -> { t with is_cold = is_cold })".

(* 880 *)
Definition mark_as_cold (t : Downwards_env.t) : M Downwards_env.t :=
  if t.(Downwards_env.is_cold)
  then ret t
  else
    ret (update_is_cold t true).

(* 882 *)
Definition must_inline (t : Downwards_env.t) : M bool :=
  Replay_history.must_inline t.(Downwards_env.replay_history).

(* 886-890. In the compiler: [~apply decision t]. *)
Definition record_inlining_decision (apply : Apply_expr.t)
    (decision : Call_site_inlining_decision_type.t) (t : Downwards_env.t)
    : M Downwards_env.t :=
  let! tmp1 :=
    Replay_history.record_inlining_decision apply decision
      t.(Downwards_env.replay_history)
  in
  ret (update_replay_history t tmp1).

(* 894. [{ t with specialization_cost }]. *)
Definition update_specialization_cost (t : Downwards_env.t)
    (specialization_cost : Specialization_cost.t) : Downwards_env.t :=
  {| round := t.(round); machine_width := t.(machine_width);
     typing_env := t.(typing_env); inlined_debuginfo := t.(inlined_debuginfo);
     disable_inlining := t.(disable_inlining);
     disable_partial_application_stub_generation :=
       t.(disable_partial_application_stub_generation);
     inlined_attribute_to_forward := t.(inlined_attribute_to_forward);
     inlining_state := t.(inlining_state);
     propagating_float_consts := t.(propagating_float_consts);
     at_unit_toplevel := t.(at_unit_toplevel);
     unit_toplevel_return_continuation :=
       t.(unit_toplevel_return_continuation);
     unit_toplevel_exn_continuation := t.(unit_toplevel_exn_continuation);
     unit_toplevel_alloc_region := t.(unit_toplevel_alloc_region);
     variables_defined_at_toplevel := t.(variables_defined_at_toplevel);
     cse := t.(cse); comparison_results := t.(comparison_results);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     closure_info := t.(closure_info);
     get_imported_code := t.(get_imported_code); all_code := t.(all_code);
     inlining_history_tracker := t.(inlining_history_tracker);
     loopify_state := t.(loopify_state); replay_history := t.(replay_history);
     specialization_cost := specialization_cost;
     join_analysis := t.(join_analysis);
     defined_variables_by_scope := t.(defined_variables_by_scope);
     lifted := t.(lifted);
     cost_of_lifting_continuations_out_of_current_one :=
       t.(cost_of_lifting_continuations_out_of_current_one);
     has_seen_a_non_liftable_continuation :=
       t.(has_seen_a_non_liftable_continuation);
     is_cold := t.(is_cold) |}.
Extract Inlined Constant update_specialization_cost =>
  "(fun t specialization_cost -> { t with specialization_cost =
   specialization_cost })".

(* 892-894. In the compiler: [~f t]. *)
Definition map_specialization_cost
    (f : Specialization_cost.t -> M Specialization_cost.t)
    (t : Downwards_env.t) : M Downwards_env.t :=
  let* specialization_cost := f t.(Downwards_env.specialization_cost) in
  ret (update_specialization_cost t specialization_cost).

(* 898-945. In the compiler: [~denv_for_join ~denv]. *)
Definition denv_for_lifted_continuation (denv_for_join denv : Downwards_env.t)
    : M Downwards_env.t :=
  (* At this point, we are lifting a continuation k' with handler [handler], out
     of a continuation k, and:

     - [denv_for_join] is the denv just before the let_cont for k

     - [denv] is the denv just before the let_cont for k'

     And we need to decide which parts of denv to use to simplify the handler of
     k' after they are lifted out from the handler of k. *)
  (* 908-945: the fields are in the order of the compiler's text. *)
  ret
    {| (* denv *)
       machine_width := denv.(Downwards_env.machine_width);
       inlined_debuginfo := denv.(Downwards_env.inlined_debuginfo);
       disable_inlining := denv.(Downwards_env.disable_inlining);
       disable_partial_application_stub_generation :=
         denv.(Downwards_env.disable_partial_application_stub_generation);
       inlined_attribute_to_forward :=
         denv.(Downwards_env.inlined_attribute_to_forward);
       inlining_state := denv.(Downwards_env.inlining_state);
       inlining_history_tracker :=
         denv.(Downwards_env.inlining_history_tracker);
       (* denv_for_join *)
       all_code := denv_for_join.(Downwards_env.all_code);
       typing_env := denv_for_join.(Downwards_env.typing_env);
       at_unit_toplevel := denv_for_join.(Downwards_env.at_unit_toplevel);
       variables_defined_at_toplevel :=
         denv_for_join.(Downwards_env.variables_defined_at_toplevel);
       cse := denv_for_join.(Downwards_env.cse);
       comparison_results := denv_for_join.(Downwards_env.comparison_results);
       replay_history := denv_for_join.(Downwards_env.replay_history);
       specialization_cost :=
         denv_for_join.(Downwards_env.specialization_cost);
       join_analysis := denv_for_join.(Downwards_env.join_analysis);
       defined_variables_by_scope :=
         denv_for_join.(Downwards_env.defined_variables_by_scope);
       lifted := denv_for_join.(Downwards_env.lifted);
       cost_of_lifting_continuations_out_of_current_one :=
         denv_for_join.(Downwards_env.cost_of_lifting_continuations_out_of_current_one);
       has_seen_a_non_liftable_continuation :=
         denv_for_join.(Downwards_env.has_seen_a_non_liftable_continuation);
       is_cold := denv_for_join.(Downwards_env.is_cold);
       (* For the following fields, both denvs should have the same value of these
          fields *)
       round := denv.(Downwards_env.round);
       propagating_float_consts :=
         denv.(Downwards_env.propagating_float_consts);
       unit_toplevel_return_continuation :=
         denv.(Downwards_env.unit_toplevel_return_continuation);
       unit_toplevel_exn_continuation :=
         denv.(Downwards_env.unit_toplevel_exn_continuation);
       unit_toplevel_alloc_region :=
         denv.(Downwards_env.unit_toplevel_alloc_region);
       are_rebuilding_terms := denv.(Downwards_env.are_rebuilding_terms);
       closure_info := denv.(Downwards_env.closure_info);
       get_imported_code := denv.(Downwards_env.get_imported_code);
       loopify_state := denv.(Downwards_env.loopify_state)
    |}.
