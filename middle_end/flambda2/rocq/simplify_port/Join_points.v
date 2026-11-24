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

(* This file follows middle_end/flambda2/simplify/join_points.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries
   [tmpN] and their order) is that of GUIDE.md; the local function
   [general_case] of [compute_handler_env]. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter
  Bound_parameters Common_subexpression_elimination Continuation_use_kind
  Flambda_debug_uid Flambda_features Flambda_kind Format List Name Name_mode
  One_continuation_use Option Or_bottom Or_invalid Profile Replay_history
  Scope Simple Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open Simplify_import
OCAML*)

(* 18 *)
From SimplifyPort.abbrev.join_points Require Import Port_abbreviations.
(*OCAML
module U = One_continuation_use
OCAML*)

(* 20-25 *)
Record result : Type := {
  handler_env : DE.t;
  extra_params_and_args : Continuation_extra_params_and_args.t;
  is_single_inlinable_use : bool;
  escapes : bool
}.

(* 27-53 *)
Definition introduce_extra_params_in_use_env (epa : EPA.t)
    '((T3 denv_at_use use_id kind)
      : tuple3 DE.t Apply_cont_rewrite_id.t Continuation_use_kind.t)
    : M (option (tuple3 TE.t Apply_cont_rewrite_id.t Continuation_use_kind.t))
    :=
  let* tenv_at_use := DE.typing_env denv_at_use in
  let* tenv_at_use :=
    let! tmp1 := EPA.extra_params epa in
    TE.add_definitions_of_params tenv_at_use tmp1
  in
  (* 32-38: the case of the exception, then those of the value. *)
  match_exn
    (fun _ =>
      let! tmp1 := EPA.extra_args epa in
      Apply_cont_rewrite_id.Map.find use_id tmp1)
    Not_found
    (fun _ =>
      fatal_errorf4
        "No extra args for rewrite Id %a@.Extra params and args: %a"
        Apply_cont_rewrite_id.print use_id EPA.print epa)
    (fun extra_args =>
      match extra_args with
      | Or_invalid.Invalid => ret None
      | Or_invalid.Ok extra_args =>
        let* tenv_at_use :=
          let! tmp1 := EPA.extra_params epa in
          let! tmp2 := Bound_parameters.to_list tmp1 in
          List.fold_left2
            (fun tenv_at_use param (arg : EPA.Extra_arg.t) =>
              match arg with
              | EPA.Extra_arg.Already_in_scope s =>
                let! tmp3 := BP.kind param in
                let! tmp4 := Flambda_kind.With_subkind.kind tmp3 in
                let! tmp5 := T.alias_type_of tmp4 s in
                let! tmp6 := BP.name param in
                TE.add_equation tenv_at_use tmp6 tmp5
              | EPA.Extra_arg.New_let_binding _ _
              | EPA.Extra_arg.New_let_binding_with_named_args _ _ =>
                ret tenv_at_use
              end)
            tenv_at_use tmp2 extra_args
        in
        ret (Some (T3 tenv_at_use use_id kind))
      end).

(* 55-74 *)
Definition introduce_extra_params_for_join (denv : DE.t)
    (use_envs_with_ids :
      list (tuple3 DE.t Apply_cont_rewrite_id.t Continuation_use_kind.t))
    (extra_params_and_args : EPA.t)
    : M (DE.t
         * list (tuple3 TE.t Apply_cont_rewrite_id.t Continuation_use_kind.t))
    :=
  let! tmp1 := EPA.is_empty extra_params_and_args in
  if tmp1
  then
    let* use_tenvs_with_ids :=
      List.map
        (fun '(T3 denv_at_use use_id kind) =>
          let! tmp1 := DE.typing_env denv_at_use in
          ret (T3 tmp1 use_id kind))
        use_envs_with_ids
    in
    ret (denv, use_tenvs_with_ids)
  else
    let* extra_params := EPA.extra_params extra_params_and_args in
    let* denv := DE.define_parameters true denv extra_params in
    let* use_envs_with_ids :=
      (* 71: a function of this file, given its first argument. *)
      List.filter_map
        (introduce_extra_params_in_use_env extra_params_and_args)
        use_envs_with_ids
    in
    ret (denv, use_envs_with_ids).

(* 76-130 *)
Definition add_extra_params_from_join_analysis (denv : DE.t)
    (analysis : T.Join_analysis.t Apply_cont_rewrite_id.t)
    (use_envs_with_ids' :
      list (tuple3 TE.t Apply_cont_rewrite_id.t Continuation_use_kind.t))
    : M (DE.t * EPA.t) :=
  let* handler_env := DE.typing_env denv in
  (* 78-94 *)
  let& add_one_extra_param :=
    fun (name_hint : option string) (name : Name.t) (kind : Flambda_kind.t)
        (extra_args : Apply_cont_rewrite_id.Map.t EPA.Extra_arg.t)
        (extra_params_and_args : EPA.t) (env_extension : TEE.t) =>
    (* PORT-GAP(loose): 78, the optional parameter [?(name_hint =
       "join_param")] of a local function is an [option] by place, and its
       default is this match. *)
    let* name_hint :=
      match name_hint with
      | Some name_hint => ret name_hint
      | None => ret "join_param"
      end
    in
    let* join_param := Variable_.create None name_hint kind in
    let& join_param_duid := Flambda_debug_uid.none in
    let* extra_param :=
      let! tmp1 := K.With_subkind.anything kind in
      BP.create join_param tmp1 join_param_duid
    in
    let* env_extension :=
      let! tmp1 := Simple.name name in
      let! tmp2 := T.alias_type_of kind tmp1 in
      let! tmp3 := Name.var join_param in
      TEE.add_or_replace_equation env_extension tmp3 tmp2
    in
    let* extra_params_and_args :=
      EPA.add extra_params_and_args Apply_cont_rewrite_id.Set_.empty
        extra_param extra_args
    in
    ret (extra_params_and_args, env_extension)
  in
  (* 95-123: [fold_variables_created_at_join ~f analysis ~init]; the case of
     the exception, then that of the value. *)
  let* '(extra_params_and_args, env_extension) :=
    T.Join_analysis.fold_variables_created_at_join
      (fun name simples kind '(extra_params_and_args, env_extension) =>
        match_exn
          (fun _ =>
            let! tmp1 := Simple.name name in
            TE.get_canonical_simple_exn handler_env (Some Name_mode.normal)
              None tmp1)
          Not_found
          (fun _ =>
            let* extra_args :=
              T.Join_analysis.Simples_at_join.fold_definitions_at_uses
                (* 106: the second parameter is the pattern
                   [(At_normal_mode simple_at_use)]. *)
                (fun use_id definition_at_use extra_args =>
                  let* '(T.Join_analysis.Simples_at_join.At_normal_mode
                           simple_at_use) :=
                    ret definition_at_use
                  in
                  Apply_cont_rewrite_id.Map.add use_id
                    (EPA.Extra_arg.Already_in_scope simple_at_use) extra_args)
                simples Apply_cont_rewrite_id.Map.empty
            in
            let* has_extra_arg_in_all_uses :=
              List.for_all
                (fun '(T3 _tenv_at_use use_id _use_kind) =>
                  Apply_cont_rewrite_id.Map.mem use_id extra_args)
                use_envs_with_ids'
            in
            if negb has_extra_arg_in_all_uses
            then ret (extra_params_and_args, env_extension)
            else
              add_one_extra_param None name kind extra_args
                extra_params_and_args env_extension)
          (fun _ => ret (extra_params_and_args, env_extension)))
      analysis (EPA.empty, TEE.empty)
  in
  (* 124-130 *)
  let* extra_params := EPA.extra_params extra_params_and_args in
  let* denv := DE.define_parameters true denv extra_params in
  let* denv :=
    DE.map_typing_env denv
      (fun tenv => TE.add_env_extension tenv env_extension)
  in
  ret (denv, extra_params_and_args).

(* 132-254 *)
Definition join (cut_after : option Scope.t) (denv : DE.t)
    (params : Bound_parameters.t) (consts_lifted_after_fork : LCS.t)
    (use_envs_with_ids :
      list (tuple3 DE.t Apply_cont_rewrite_id.t Continuation_use_kind.t))
    (previous_extra_params_and_args : EPA.t)
    : M (tuple3 DE.t (option (T.Join_analysis.t Apply_cont_rewrite_id.t))
           EPA.t) :=
  let* definition_scope := DE.get_continuation_scope denv in
  let* extra_lifted_consts_in_use_envs :=
    LCS.all_defined_symbols consts_lifted_after_fork
  in
  (* PORT-GAP(loose): 138, [let module CSE =
     Common_subexpression_elimination in] is not kept: the module has its
     full name below. *)
  (* 139-148 *)
  let* cse_join_result :=
    let* typing_env := DE.typing_env denv in
    (let! tmp1 := TE.current_scope typing_env in
     let! tmp2 := Scope.equal definition_scope tmp1 in
     assert_ tmp2) ;;
    let! tmp1 := DE.cse denv in
    Common_subexpression_elimination.join typing_env tmp1 use_envs_with_ids
      (fun '(T3 use_env _ _) => DE.typing_env use_env)
      (fun '(T3 _ id _) => ret id)
      (fun '(T3 use_env _ _) => DE.cse use_env)
      params
  in
  (* 149-156 *)
  let* extra_params_and_args :=
    match cse_join_result with
    | None => ret previous_extra_params_and_args
    | Some cse_join_result =>
      EPA.concat
        cse_join_result.(Common_subexpression_elimination.Join_result.extra_params)
        previous_extra_params_and_args
    end
  in
  (* 157-160 *)
  let* '(denv, use_envs_with_ids') :=
    introduce_extra_params_for_join denv use_envs_with_ids
      extra_params_and_args
  in
  let* extra_allowed_names :=
    match cse_join_result with
    | None => ret NO.empty
    | Some cse_join_result =>
      ret
        cse_join_result.(Common_subexpression_elimination.Join_result.extra_allowed_names)
    end
  in
  let* cut_after := Option.value cut_after definition_scope in
  (* 167-173 *)
  let* '(handler_env, join_analysis) :=
    let! tmp1 := EPA.extra_params extra_params_and_args in
    let! tmp2 := Bound_parameters.append params tmp1 in
    let! tmp3 := DE.typing_env denv in
    T.cut_and_n_way_join tmp3 use_envs_with_ids' tmp2 cut_after
      extra_lifted_consts_in_use_envs extra_allowed_names
  in
  let* handler_env :=
    match cse_join_result with
    | None => ret handler_env
    | Some cse_join_result =>
      TE.add_env_extension handler_env
        cse_join_result.(Common_subexpression_elimination.Join_result.env_extension)
    end
  in
  (* 180-185 *)
  let* denv :=
    let* denv := DE.with_typing_env denv handler_env in
    match cse_join_result with
    | None => ret denv
    | Some cse_join_result =>
      DE.with_cse denv
        cse_join_result.(Common_subexpression_elimination.Join_result.cse_at_join_point)
    end
  in
  (* 186-253 *)
  let* '(denv, extra_params_and_args) :=
    (* If we have a join analysis available (i.e. if we are using the new n-way
       join), use it to introduce additional extra params and args after
       performing the typing env join.

       More specifically, we introduce variables at the "normal" name mode for
       all of the variables introduced during the typing env join that have a
       value at the "normal" name mode in all uses.

       This is a more precise implementation of the CSE join specifically for
       the projections that are tracked in the typing env (such as `Is_int` and
       `Get_tag`), but also does part of the work of unboxing (specifically,
       unboxing where all of the unboxed fields exist at the "normal" name mode
       in all uses).

       This fixes a regression in the new join: since the new join is better
       than the old one at recovering aliases, there are situations where the
       CSE join (which lives {b outside} the alias environment) gets confused
       and fails to join e.g. equations `y = Is_int(x)` with `y = Is_int(1)`,
       where we know that `x = 1` in the second environment. See:

       https://github.com/oxcaml/oxcaml/issues/5721

       and

       https://github.com/oxcaml/oxcaml/issues/3181 *)
    (* CR bclement: Once the old join is gone, this should be able to entirely
      supersede the tracking of projections (`Is_int`, `Get_tag`, `Is_null`,
      etc.) in the CSE environment and allow the typing env to take over. *)
    (* CR bclement: We could (should?) in fact create normal mode variables for
       the existential variables that are created during the join and have a
       value in "normal" name mode at all the uses where they are defined, but
       are not necessarily defined in all uses.

       This would allow to improve simplifications in patterns where we perform
       the same match multiple times, such as the following snippet:
     *)
    (* type t = A | B of int | C | D of int
     *
     * let f ~g x y =
     *   let a : string =
     *     match x with
     *     | A -> "a"
     *     | B _ -> "b"
     *     | C -> "c"
     *     | D _ -> "d"
     *   in
     *   let _ : unit = g a in
     *   match x with
     *   | A -> "A"
     *   | B _ -> "B"
     *   | C -> "C"
     *   | D _ -> "D"
     *)
    (* where we currently keep one instances of `%untag_imm x` and `%get_tag x` per
       instance of `match x` but we could eliminate all except the last one. *)
    match join_analysis with
    | None => ret (denv, extra_params_and_args)
    | Some analysis =>
      let* '(denv, join_extra_params_and_args) :=
        add_extra_params_from_join_analysis denv analysis use_envs_with_ids'
      in
      let* extra_params_and_args :=
        EPA.concat extra_params_and_args join_extra_params_and_args
      in
      ret (denv, extra_params_and_args)
    end
  in
  ret (T3 denv join_analysis extra_params_and_args).

(* 256-303 *)
Definition add_equations_on_params (typing_env : TE.t) (is_recursive : bool)
    (params' : Bound_parameters.t) (param_types : list T.t) : M TE.t :=
  let* params := Bound_parameters.to_list params' in
  (* PORT-GAP(loose): 259-266, the compiler uses this local function at
     two types (it never returns): at [unit] (274) and at the type of the
     result (278). A local function of Rocq has one type: here it is that
     of the result, and at 274 its result is ignored. *)
  let& number_of_parameters_mismatch :=
    fun (_ : unit) =>
    (* PORT-GAP(papp): 264, [Format.pp_print_list] is given its first two
       arguments only. *)
    let! tmp1 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space) T.print
    in
    (fatal_errorf4
       "Mismatch between number of continuation parameters and arguments at a use site:@ (%a)@ and@ %a"
       Bound_parameters.print params' tmp1 param_types
      : M TE.t)
  in
  (* 267-302: a local [let rec], on the list [params]. *)
  let add_equations_on_params :=
    fix add_equations_on_params (typing_env : TE.t) (params : list BP.t)
        (param_types : list T.t) {struct params} : M TE.t :=
      match params with
      | [] =>
        (let! tmp1 := Flambda_features.check_invariants tt in
         if
           tmp1 && negb is_recursive
           && match param_types with
              | [] => false
              | _ :: _ => true
              end
         then
           let! tmp2 := number_of_parameters_mismatch tt in
           ignore tmp2
         else ret tt) ;;
        ret typing_env
      | param :: params =>
        match param_types with
        | [] => number_of_parameters_mismatch tt
        | param_type :: param_types =>
          let* name := Bound_parameter.name param in
          let* kind := Bound_parameter.kind param in
          let* typing_env :=
            let! tmp1 :=
              Flambda_kind.With_subkind.has_useful_subkind_info kind
            in
            if tmp1
            then
              let* raw_kind := Flambda_kind.With_subkind.kind kind in
              let* type_from_kind :=
                let! tmp1 := TE.machine_width typing_env in
                T.unknown_with_subkind None tmp1 kind
              in
              let! tmp1 := T.meet typing_env type_from_kind param_type in
              match tmp1 with
              | Or_bottom.Bottom =>
                (* This should really replace the corresponding uses with
                   [Invalid], but this seems an unusual situation, so we don't do
                   that currently. *)
                let! tmp1 := T.bottom raw_kind in
                TE.add_equation typing_env name tmp1
              | Or_bottom.Ok (meet_ty, typing_env) =>
                TE.add_equation typing_env name meet_ty
              end
            else TE.add_equation typing_env name param_type
          in
          add_equations_on_params typing_env params param_types
        end
      end
  in
  add_equations_on_params typing_env params param_types.

(* 305-315 *)
Definition compute_use_env_with_ids (replay : option (Replay_history.t * bool))
    (is_recursive : bool) (params : Bound_parameters.t) (use : U.t)
    : M (tuple3 DE.t Apply_cont_rewrite_id.t Continuation_use_kind.t) :=
  let& add_or_meet_param_type :=
    fun (typing_env : TE.t) =>
    let* param_types := U.arg_types use in
    add_equations_on_params typing_env is_recursive params param_types
  in
  let* use_env :=
    let* use_env :=
      let! tmp1 := U.env_at_use use in
      DE.with_replay_history replay tmp1
    in
    let* use_env := DE.define_parameters false use_env params in
    DE.map_typing_env use_env add_or_meet_param_type
  in
  let! tmp1 := U.use_kind use in
  let! tmp2 := U.id use in
  ret (T3 use_env tmp2 tmp1).

(* 317-442 *)
Definition compute_handler_env (replay : option (Replay_history.t * bool))
    (cut_after : option Scope.t) (uses : list U.t) (is_recursive : bool)
    (env_at_fork : DE.t) (consts_lifted_after_fork : LCS.t)
    (params : Bound_parameters.t) (previous_extra_params_and_args : EPA.t)
    : M result :=
  (* PORT-GAP(loose): 385-442, the body of the case [_] is this local
     function, so that it is written once: the case [[use]] has a guard
     ([when], 323-327), which is an [if] whose [else] is that body too. *)
  let& general_case :=
    fun (_ : unit) =>
    let* use_envs_with_ids :=
      (* 388: a function of this file, given its first three arguments. *)
      List.map (compute_use_env_with_ids None is_recursive params) uses
    in
    (* This is the general case.

       The lifted constants are put into the _fork_ environment now because it
       overall makes things easier; the join operation can just discard any
       equation about a lifted constant (any such equation could not be
       materially more precise anyway). *)
    let* denv := DE.with_replay_history replay env_at_fork in
    let* denv :=
      DE.add_lifted_constant_state None denv consts_lifted_after_fork
    in
    (* 399-402 *)
    let* should_do_join :=
      let! tmp1 := Flambda_features.join_points tt in
      ret
        (tmp1
         || match use_envs_with_ids with
            | [] | [_] => true
            | _ :: _ :: _ => false
            end)
    in
    (* 403-422 *)
    let* '(T3 handler_env join_analysis extra_params_and_args) :=
      if should_do_join
      then
        (* No need to add equations, as they will be computed from the use
           environments *)
        let* denv := DE.define_parameters false denv params in
        Profile.record_call (Some true) "join"
          (fun _ =>
            join cut_after denv params consts_lifted_after_fork
              use_envs_with_ids previous_extra_params_and_args)
      else
        (* Define parameters with basic equations from the subkinds *)
        let* denv :=
          DE.add_parameters_with_unknown_types false None None denv params
        in
        let* denv :=
          let! tmp1 := EPA.extra_params previous_extra_params_and_args in
          DE.add_parameters_with_unknown_types true None None denv tmp1
        in
        ret (T3 denv None previous_extra_params_and_args)
    in
    let* handler_env := DE.with_join_analysis join_analysis handler_env in
    let* only_cold_uses :=
      List.for_all (fun '(T3 use_env _ _) => DE.is_cold use_env)
        use_envs_with_ids
    in
    let* handler_env :=
      if only_cold_uses then DE.mark_as_cold handler_env else ret handler_env
    in
    (* 430-437 *)
    let* escapes :=
      List.exists_
        (fun '(T3 _ _ cont_use_kind) =>
          match (cont_use_kind : Continuation_use_kind.t) with
          | Continuation_use_kind.Inlinable
          | Continuation_use_kind.Non_inlinable false => ret false
          | Continuation_use_kind.Non_inlinable true => ret true
          end)
        use_envs_with_ids
    in
    ret
      {| handler_env := handler_env;
         extra_params_and_args := extra_params_and_args;
         is_single_inlinable_use := false;
         escapes := escapes |}
  in
  (* Augment the environment at each use with the parameter definitions and
     associated equations. *)
  match uses with
  | [use] =>
    (* 323-327: the guard. *)
    let! tmp1 :=
      and_then (negb is_recursive)
        (let! tmp2 := U.use_kind use in
         match tmp2 with
         | Continuation_use_kind.Inlinable => ret true
         | Continuation_use_kind.Non_inlinable _ => ret false
         end)
    in
    if tmp1
    then
      (* First add the extra params and args equations in the typing env *)
      (* 329-331: [let ((use_env, _use_id, _use_kind) as use) = ...] *)
      let* use := compute_use_env_with_ids replay is_recursive params use in
      let* '(T3 use_env _use_id _use_kind) := ret use in
      let* use_tenv :=
        let! tmp1 :=
          introduce_extra_params_in_use_env previous_extra_params_and_args use
        in
        match tmp1 with
        | Some (T3 use_env _ _) => ret use_env
        | None =>
          fatal_errorf0
            "Apply_cont of a single-use inlinable continuation is Invalid."
        end
      in
      let* use_env := DE.with_typing_env use_env use_tenv in
      (* There is only one use of the continuation and it is inlinable. No join
         calculations are required.

         We need to make sure any lifted constants generated during the
         simplification of the body are in the returned environment for the
         handler. Otherwise we might share a constant based on information in [DA]
         but then find the definition of the corresponding constant isn't in [DE].
         Note that some of the constants may already be defined (for example
         because they were defined on the path between the fork point and this
         particular use). *)
      (* 358-361 *)
      let* handler_env :=
        DE.add_lifted_constant_state (Some tt) use_env consts_lifted_after_fork
      in
      (* The use environment might have a deeper inlining depth increment than the
         fork environment. (e.g. where an [Apply] was inlined, revealing the
         linear inlinable use of the continuation). We need to make sure the
         handler is simplified using the depth from the fork environment. Likewise
         for the inlining history tracker and debuginfo. *)
      let* handler_env :=
        let! tmp1 := DE.get_inlining_state env_at_fork in
        DE.set_inlining_state handler_env tmp1
      in
      let* handler_env :=
        let! tmp1 := DE.inlining_history_tracker env_at_fork in
        DE.set_inlining_history_tracker tmp1 handler_env
      in
      let* handler_env := DE.set_inlined_debuginfo handler_env env_at_fork in
      let* handler_env :=
        let! tmp1 := DE.at_unit_toplevel env_at_fork in
        DE.set_at_unit_toplevel_state handler_env tmp1
      in
      ret
        {| handler_env := handler_env;
           extra_params_and_args := previous_extra_params_and_args;
           is_single_inlinable_use := true;
           escapes := false |}
    else general_case tt
  | _ => general_case tt
  end.

(* PORT-GAP(verbatim): 317, the two optional parameters of
   [compute_handler_env]. *)
(*OCAML-END
let compute_handler_env ?replay ?cut_after uses is_recursive env_at_fork
    consts_lifted_after_fork params previous_extra_params_and_args =
  compute_handler_env replay cut_after uses is_recursive env_at_fork
    consts_lifted_after_fork params previous_extra_params_and_args
OCAML-END*)
