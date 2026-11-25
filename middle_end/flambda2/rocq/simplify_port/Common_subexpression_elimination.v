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

(* This file follows
   middle_end/flambda2/simplify/common_subexpression_elimination.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order, the fuel of the local recursive function [do_rounds]) is
   that of GUIDE.md. The file does not import Simplify_import, which the
   compiler's file cannot open: its twelve abbreviations of modules are its
   own. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_name Bound_parameter
  Bound_parameters Continuation_extra_params_and_args Flambda2_types
  Flambda_debug_uid Flambda_features Flambda_kind Flambda_primitive Format
  ListLabels Name Name_mode Name_occurrences Or_invalid Scope Simple Stdlib_
  Target_system Variable_.
From SimplifyPort.decl Require Import Common_subexpression_elimination__local.
(* CONSTRUCTORS-WITHOUT-MODULE: Continuation_extra_params_and_args.t
   Flambda_primitive.t Flambda_primitive.unary_primitive Or_invalid.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17: [Simplify_import] cannot be used owing to a circular dependency. *)
(* 18-29 *)
From SimplifyPort.abbrev.common_subexpression_elimination Require Import Port_abbreviations.
(*OCAML
module EA = Continuation_extra_params_and_args.Extra_arg
module EP = Flambda_primitive.Eligible_for_cse
module EPA = Continuation_extra_params_and_args
module K = Flambda_kind
module BP = Bound_parameter
module NM = Name_mode
module P = Flambda_primitive
module RI = Apply_cont_rewrite_id
module T = Flambda2_types
module TE = Flambda2_types.Typing_env
module TEE = Flambda2_types.Typing_env_extension
module List = ListLabels
OCAML*)

(* 31-74 *)
(* PORT-GAP(loose): 31-44, the signature of [T0], in which the type is
   private, is not kept. *)
Module T0.
  (* 45-48 *)
  Record t : Type := {
    by_scope : Scope.Map.t (EP.Map.t Simple.t);
    combined : EP.Map.t Simple.t
  }.

  (* 50-56 *)
  (* PORT-GAP(loose): 50, the attribute [@ocamlformat "disable"] is not
     kept. *)
  Definition print (ppf : Format.formatter)
      '({| by_scope := by_scope; combined := combined |} : t) : M unit :=
    (* 55-56 *)
    let! tmp1 := papp1 EP.Map.print Simple.print in
    let! tmp2 := papp1 EP.Map.print Simple.print in
    let! tmp3 := papp1 Scope.Map.print tmp2 in
    Format.fprintf4 ppf
      "@[<hov 1>(@[<hov 1>(by_scope@ %a)@]@ @[<hov 1>(combined@ %a)@]@]" tmp3
      by_scope tmp1 combined.

  (* 58 *)
  Definition empty : t :=
    {| by_scope := Scope.Map.empty; combined := EP.Map.empty |}.

  (* 60-71. In the compiler: [t prim ~bound_to scope]. *)
  Definition add (t : T0.t) (prim : EP.t) (bound_to : Simple.t)
      (scope : Scope.t) : M T0.t :=
    match_exn
      (fun _ => EP.Map.find prim t.(combined))
      Not_found
      (fun _ =>
        let* level :=
          match_exn
            (fun _ => Scope.Map.find scope t.(by_scope))
            Not_found
            (fun _ => EP.Map.singleton prim bound_to)
            (fun level => EP.Map.add prim bound_to level)
        in
        let* by_scope := Scope.Map.add (* replace *) scope level t.(by_scope) in
        let* combined := EP.Map.add prim bound_to t.(T0.combined) in
        ret {| by_scope := by_scope; combined := combined |})
      (fun _bound_to => ret t).

  (* 73 *)
  Definition find (t : T0.t) (prim : EP.t) : M (option Simple.t) :=
    EP.Map.find_opt prim t.(combined).
End T0.

(* 76 *)
(* PORT-GAP(loose): 76, [include T0] is written as one definition for each
   item of the signature of [T0]. *)
Definition t : Type := T0.t.
Definition print := T0.print.
Definition empty : t := T0.empty.
Definition add := T0.add.
Definition find := T0.find.

(* 78-122 *)
(* The module [Rhs_kind] applies a functor of the compiler; its OCaml text is
   the compiler's, and decl/Common_subexpression_elimination__local.v declares
   what the file uses of it. *)
(*OCAML
module Rhs_kind : sig
  type t =
    | Needs_extra_binding of { bound_to : Simple.t }
    | Rhs_in_scope of { bound_to : Simple.t }

  val bound_to : t -> Simple.t

  include Container_types.S with type t := t
end = struct
  type t =
    | Needs_extra_binding of { bound_to : Simple.t }
    | Rhs_in_scope of { bound_to : Simple.t }

  let bound_to t =
    match t with
    | Needs_extra_binding { bound_to } | Rhs_in_scope { bound_to } -> bound_to

  include Container_types.Make (struct
    type nonrec t = t

    let [@ocamlformat "disable"] print ppf t =
      match t with
      | Needs_extra_binding { bound_to; } ->
        Format.fprintf ppf "@[<hov 1>(Needs_extra_binding@ %a)@]"
          Simple.print bound_to
      | Rhs_in_scope { bound_to; } ->
        Format.fprintf ppf "@[<hov 1>(Rhs_in_scope@ %a)@]"
          Simple.print bound_to

    let hash _ = Misc.fatal_error "Rhs_kind.hash not yet implemented"

    let equal _ = Misc.fatal_error "Rhs_kind.equal not yet implemented"

    let compare t1 t2 =
      match t1, t2 with
      | ( Needs_extra_binding { bound_to = bound_to1 },
          Needs_extra_binding { bound_to = bound_to2 } ) ->
        Simple.compare bound_to1 bound_to2
      | ( Rhs_in_scope { bound_to = bound_to1 },
          Rhs_in_scope { bound_to = bound_to2 } ) ->
        Simple.compare bound_to1 bound_to2
      | Needs_extra_binding _, _ -> -1
      | Rhs_in_scope _, _ -> 1
  end)
end
OCAML*)

(* 124-245. In the compiler: [~typing_env_at_fork ~cse_at_each_use ~params
   prev_cse extra_bindings env_extension]. *)
Definition cse_with_eligible_lhs (typing_env_at_fork : TE.t)
    (cse_at_each_use : list (tuple3 TE.t RI.t (EP.Map.t Simple.t)))
    (params : list Bound_parameter.t) (prev_cse : EP.Map.t Simple.t)
    (extra_bindings : EPA.t) (env_extension : TEE.t)
    : M (EP.Map.t (RI.Map.t Rhs_kind.t)) :=
  let* params_set :=
    let! tmp1 := List.map Bound_parameter.name params in
    Name.Set_.of_list tmp1
  in
  let* params := List.map Bound_parameter.simple params in
  let& is_param :=
    fun (simple : Simple.t) =>
    Simple.pattern_match simple
      (fun name _ => Name.Set_.mem name params_set)
      (fun _ => ret false)
  in
  (* 135-240. [List.fold_left cse_at_each_use ~init ~f]: the arguments are in
     the order of the interface. *)
  List.fold_left
    (fun (eligible : EP.Map.t (RI.Map.t Rhs_kind.t))
         '(T3 env_at_use id cse : tuple3 TE.t RI.t (EP.Map.t Simple.t)) =>
      (* 137-180 *)
      let* find_new_name :=
        let& find_param :=
          fun (simple : Simple.t) (params : list Simple.t) =>
          List.find_opt
            (fun param =>
              match_exn
                (fun _ =>
                  TE.get_canonical_simple_exn env_at_use (Some NM.normal)
                    (Some NM.normal) param)
                Not_found
                (fun _ => ret false)
                (fun arg => Simple.equal arg simple))
            params
        in
        match extra_bindings with
        | EPA.Empty => ret (fun (arg : Simple.t) => find_param arg params)
        | EPA.Non_empty extra_params extra_args =>
          let! tmp1 := RI.Map.find id extra_args in
          match tmp1 with
          | Or_invalid.Invalid =>
            ret (fun (_arg : Simple.t) => ret (None : option Simple.t))
          | Or_invalid.Ok extra_args =>
            (* PORT-GAP(loose): 155-173, a recursion on the list [args]. The
               local function is used once, under the [fun arg] of 174: the
               extraction writes its definition there, in the case [None],
               and not before the [fun]. *)
            let find_name :=
              fix find_name (simple : Simple.t)
                  (params : list Bound_parameter.t) (args : list EA.t)
                  {struct args} : M (option Simple.t) :=
                match args, params with
                | [], [] => ret None
                | [], _ | _, [] =>
                  fatal_error "Mismatching params and args arity"
                | arg :: args, param :: params =>
                  match arg with
                  | EA.Already_in_scope arg =>
                    (* 162: [when Simple.equal arg simple] *)
                    let! tmp1 := Simple.equal arg simple in
                    if tmp1
                    then
                      (* If [param] has an extra equation associated to it, we
                         shouldn't propagate equations on it as it will mess
                         with the application of constraints later *)
                      let! tmp2 := BP.name param in
                      let! tmp3 := TEE.has_equation tmp2 env_extension in
                      if tmp3
                      then ret None
                      else
                        let! tmp4 := BP.simple param in
                        ret (Some tmp4)
                    else find_name simple params args
                  | EA.New_let_binding _ _
                  | EA.New_let_binding_with_named_args _ _ =>
                    find_name simple params args
                  end
                end
            in
            ret
              (fun (arg : Simple.t) =>
                (* PORT-GAP(loose): 175-179, the compiler matches the call,
                   and its second case is [Some _ as r]; here the result of
                   the call is bound under that name, then matched. *)
                let* r := find_param arg params in
                match r with
                | None =>
                  let! tmp1 := Bound_parameters.to_list extra_params in
                  find_name arg tmp1 extra_args
                | Some _ => ret r
                end)
          end
        end
      in
      (* 181-240 *)
      EP.Map.fold
        (fun (prim : EP.t) (bound_to : Simple.t)
             (eligible : EP.Map.t (RI.Map.t Rhs_kind.t)) =>
          let* prim :=
            EP.filter_map_args prim
              (fun arg =>
                match_exn
                  (fun _ =>
                    TE.get_canonical_simple_exn env_at_use (Some NM.normal)
                      (Some NM.normal) arg)
                  Not_found
                  (fun _ => ret None)
                  (fun arg =>
                    (* PORT-GAP(loose): 191-196, as at 175-179: the result of
                       the call is bound as [arg_opt], then matched. *)
                    let* arg_opt := find_new_name arg in
                    match arg_opt with
                    | None =>
                      let! tmp1 := TE.mem_simple None typing_env_at_fork arg in
                      if tmp1 then ret (Some arg) else ret None
                    | Some _ => ret arg_opt
                    end))
          in
          match prim with
          | None => ret eligible
          | Some prim =>
            (* 200: [when EP.Map.mem prim prev_cse] *)
            let! tmp1 := EP.Map.mem prim prev_cse in
            if tmp1
            then (* We've already got it from a previous round *)
              ret eligible
            else
              match_exn
                (fun _ =>
                  TE.get_canonical_simple_exn env_at_use (Some NM.normal)
                    (Some NM.normal) bound_to)
                Not_found
                (fun _ => ret eligible)
                (fun bound_to =>
                  let* bound_to :=
                    let! tmp2 := is_param bound_to in
                    if negb tmp2
                    then ret (Some bound_to)
                    else
                      let* aliases :=
                        let! tmp3 :=
                          TE.aliases_of_simple env_at_use NM.normal bound_to
                        in
                        TE.Alias_set.filter tmp3
                          (fun simple =>
                            let! tmp4 := is_param simple in
                            ret (negb tmp4))
                      in
                      TE.Alias_set.get_singleton aliases
                  in
                  match bound_to with
                  | None => ret eligible
                  | Some bound_to =>
                    let* bound_to :=
                      let! tmp5 :=
                        TE.mem_simple None typing_env_at_fork bound_to
                      in
                      if tmp5
                      then ret (Rhs_kind.Rhs_in_scope bound_to)
                      else ret (Rhs_kind.Needs_extra_binding bound_to)
                    in
                    match_exn
                      (fun _ => EP.Map.find prim eligible)
                      Not_found
                      (fun _ =>
                        let! tmp6 := RI.Map.singleton id bound_to in
                        EP.Map.add prim tmp6 eligible)
                      (fun from_prev_levels =>
                        let* map := RI.Map.add id bound_to from_prev_levels in
                        EP.Map.add prim map eligible)
                  end)
          end)
        cse eligible)
    EP.Map.empty cse_at_each_use.

(* 247-250 *)
Record extra_binding : Type := {
  extra_param : BP.t;
  extra_args : RI.Map.t EA.t
}.

(* 252-297. In the compiler: [~machine_width ~cse_at_each_use prim
   bound_to_map (cse, extra_bindings, env_extension, allowed)]. *)
Definition join_one_cse_equation
    (machine_width : Target_system.Machine_width.t)
    (cse_at_each_use : list (tuple3 TE.t RI.t (EP.Map.t Simple.t)))
    (prim : EP.t) (bound_to_map : RI.Map.t Rhs_kind.t)
    '(T4 cse extra_bindings env_extension allowed
       : tuple4 (EP.Map.t Simple.t) (list (EP.t * extra_binding)) TEE.t
           Name_occurrences.t)
    : M
        (tuple4 (EP.Map.t Simple.t) (list (EP.t * extra_binding)) TEE.t
           Name_occurrences.t) :=
  let* has_value_on_all_paths :=
    List.for_all
      (fun '(T3 _ id _ : tuple3 TE.t RI.t (EP.Map.t Simple.t)) =>
        RI.Map.mem id bound_to_map)
      cse_at_each_use
  in
  if negb has_value_on_all_paths
  then ret (T4 cse extra_bindings env_extension allowed)
  else
    let* bound_to_set :=
      let! tmp1 := RI.Map.data bound_to_map in
      Rhs_kind.Set_.of_list tmp1
    in
    let! tmp1 := Rhs_kind.Set_.get_singleton bound_to_set in
    match tmp1 with
    | Some (Rhs_kind.Rhs_in_scope bound_to) =>
      let! tmp2 := EP.Map.add prim bound_to cse in
      ret (T4 tmp2 extra_bindings env_extension allowed)
    | None | Some (Rhs_kind.Needs_extra_binding _) =>
      let* prim_result_kind :=
        let! tmp2 := EP.to_primitive prim in
        P.result_kind' tmp2
      in
      let* var := Variable_.create None "cse_param" prim_result_kind in
      let& var_duid := Flambda_debug_uid.none in
      let* extra_param :=
        let! tmp2 := K.With_subkind.anything prim_result_kind in
        BP.create var tmp2 var_duid
      in
      let* bound_to := RI.Map.map Rhs_kind.bound_to bound_to_map in
      let* cse :=
        let! tmp2 := Simple.var var in
        EP.Map.add prim tmp2 cse
      in
      let* extra_args :=
        RI.Map.map (fun simple => ret (EA.Already_in_scope simple)) bound_to
      in
      let& extra_binding :=
        {| extra_param := extra_param; extra_args := extra_args |}
      in
      let* env_extension :=
        (* For the primitives Is_int and Get_tag, they're strongly linked to
           their argument: additional information on the cse parameter should
           translate into additional information on the argument. This can be
           done by giving them the appropriate type. The same could be done for
           a lot of the other non-arithmetic primitives, but in the other cases
           the join of the types will usually give us the relevant equation
           anyway. *)
        (* PORT-GAP(loose): 285, the attribute [@ocaml.warning
           "-fragile-match"] is not kept. *)
        let! tmp2 := EP.to_primitive prim in
        match tmp2 with
        | P.Unary (P.Is_int true) scrutinee =>
          let! tmp3 := Name.var var in
          TEE.add_is_int_relation machine_width env_extension tmp3 scrutinee
        | P.Unary P.Get_tag block =>
          let! tmp3 := Name.var var in
          TEE.add_get_tag_relation env_extension tmp3 block
        | _ => ret env_extension
        end
      in
      let* allowed :=
        let! tmp2 := Name.var var in
        Name_occurrences.add_name allowed tmp2 NM.normal
      in
      ret
        (T4 cse ((prim, extra_binding) :: extra_bindings) env_extension allowed)
    end.

(* 299-320. In the compiler: [({ by_scope; _ } as t) ~scope_at_fork]. *)
Definition cut_cse_environment '({| T0.by_scope := by_scope |} as t)
    (scope_at_fork : Scope.t) : M (EP.Map.t Simple.t) :=
  (* This extracts those CSE equations that arose between the fork point and
     each use of the continuation in question. *)
  let* '(T3 _ _ levels) := Scope.Map.split scope_at_fork by_scope in
  Scope.Map.fold
    (fun (scope : Scope.t) (equations result : EP.Map.t Simple.t) =>
      (* PORT-GAP(loose): 305-319, the compiler's handler is [Invalid_argument
         _ as exn -> ...; raise exn]; here the handler takes the argument of
         the exception and raises [Invalid_argument] of it again. *)
      try_with
        (fun _ => EP.Map.disjoint_union None None equations result)
        Stdlib_.Invalid_argument
        (fun exn =>
          (* 314-317 *)
          (let! tmp1 := papp1 EP.Map.print Simple.print in
           let! tmp2 := papp1 EP.Map.print Simple.print in
           Format.eprintf10
             "cut_cse_environment failed:@ 
t = %a@ 
scope_at_fork = %a@ 
scope = %a@ 
equations = %a@ 
result=%a@ 

"
             print t Scope.print scope_at_fork Scope.print scope tmp2
             equations tmp1 result) ;;
          raise_ Stdlib_.Invalid_argument exn))
    levels EP.Map.empty.

(* 322-329 *)
Module Join_result.
  (* 323-328 *)
  (* 323: [type nonrec t]: the field [cse_at_join_point] has the type [t] of
     the file. *)
  Record t : Type := {
    cse_at_join_point : T0.t;
    extra_params : EPA.t;
    env_extension : TEE.t;
    extra_allowed_names : Name_occurrences.t
  }.
End Join_result.

(* 331-462. In the compiler: [~typing_env_at_fork ~cse_at_fork
   ~cse_at_each_use ~params ~scope_at_fork]. *)
Definition join0 (typing_env_at_fork : TE.t) (cse_at_fork : T0.t)
    (cse_at_each_use : list (tuple3 TE.t RI.t (EP.Map.t Simple.t)))
    (params : Bound_parameters.t) (scope_at_fork : Scope.t)
    : M (option Join_result.t) :=
  let* params := Bound_parameters.to_list params in
  (* CSE equations have a left-hand side specifying a primitive and a right-hand
     side specifying a [Simple]. The left-hand side is matched against portions
     of terms. As such, the [Simple]s therein must have name mode [Normal],
     since we do not do CSE for phantom bindings (see [Simplify_common]). It
     follows that any CSE equation whose left-hand side involves a name not
     defined at the fork point, having canonicalised such name, cannot be
     propagated. This step also canonicalises the right-hand sides of the CSE
     equations. *)
  (* 342-412 *)
  let& compute_cse_one_round :=
    fun (prev_cse : EP.Map.t Simple.t) (extra_params : EPA.t)
        (typing_env_with_extra_params : TE.t) (env_extension : TEE.t)
        (allowed : Name_occurrences.t) =>
    let* new_cse :=
      cse_with_eligible_lhs typing_env_at_fork cse_at_each_use params prev_cse
        extra_params env_extension
    in
    (* To make use of a CSE equation at or after the join point, its right-hand
       side must have the same value, no matter which path is taken from the
       fork point to the join point. We filter out equations that do not satisfy
       this. Sometimes we can force an equation to satisfy the property by
       explicitly passing the value of the right-hand side as an extra parameter
       to the continuation at the join point. *)
    (* 354-361: [join_one_cse_equation], a function of the file, is given its
       first two arguments. *)
    let* '(T4 cse' extra_bindings env_extension' allowed) :=
      let! tmp1 := TE.machine_width typing_env_at_fork in
      EP.Map.fold
        (join_one_cse_equation tmp1 cse_at_each_use)
        new_cse
        (T4 EP.Map.empty [] TEE.empty allowed)
    in
    (* 362-369 *)
    let* sorted_extra_bindings :=
      List.sort
        (fun (pat1 pat2 : EP.t * extra_binding) =>
          let* '(prim1, _) := ret pat1 in
          let* '(prim2, _) := ret pat2 in
          let! tmp1 := EP.to_primitive prim2 in
          let! tmp2 := EP.to_primitive prim1 in
          (* 366-367 *)
          let! tmp3 :=
            papp1 TE.stable_compare_simples typing_env_with_extra_params
          in
          P.compare_primitive_application tmp3 tmp2 tmp1)
        extra_bindings
    in
    (* 370-390. 379-381, [EPA.add extra_bindings ~extra_param ~extra_args
       ~invalids]: the arguments are in the order of the interface. *)
    let* '(extra_params', typing_env_with_extra_params') :=
      List.fold_left
        (fun (pat1 : EPA.t * TE.t) (pat2 : EP.t * extra_binding) =>
          let* '(extra_bindings, typing_env_with_extra_params) := ret pat1 in
          let* '(_, {| extra_param := extra_param; extra_args := extra_args |}) :=
            ret pat2
          in
          let* extra_bindings :=
            EPA.add extra_bindings Apply_cont_rewrite_id.Set_.empty extra_param
              extra_args
          in
          (* We need to add the new variable to the typing env in order to be
             able to compute binding times for the following rounds. *)
          let* typing_env_with_extra_params :=
            let! tmp1 := BP.kind extra_param in
            let! tmp2 := K.With_subkind.kind tmp1 in
            let! tmp3 := BP.name extra_param in
            let! tmp4 := Bound_name.create tmp3 Name_mode.normal in
            TE.add_definition typing_env_with_extra_params tmp4 tmp2
          in
          ret (extra_bindings, typing_env_with_extra_params))
        (EPA.empty, typing_env_with_extra_params)
        sorted_extra_bindings
    in
    let* need_other_round :=
      (* If we introduce new parameters, then CSE equations involving the
         corresponding arguments can be considered again, so we need another
         round. *)
      let! tmp1 := EPA.is_empty extra_params' in
      ret (negb tmp1)
    in
    let* cse := EP.Map.disjoint_union None None prev_cse cse' in
    (* The order of cse arguments does not matter since only simples already in
       scope are used as extra arguments. *)
    let* extra_params := EPA.concat extra_params' extra_params in
    let* env_extension := TEE.disjoint_union env_extension env_extension' in
    ret
      (T6 cse extra_params typing_env_with_extra_params' env_extension allowed
         need_other_round)
  in
  (* 413-438 *)
  let* '(T4 cse extra_params env_extension allowed) :=
    let_fuel! fuel in
    let do_rounds :=
      fix do_rounds (fuel : Port_monad.fuel) (current_round : int)
          (cse : EP.Map.t Simple.t) (extra_params : EPA.t)
          (typing_env_with_extra_params : TE.t) (env_extension : TEE.t)
          (allowed : Name_occurrences.t) {struct fuel}
          : M (tuple4 (EP.Map.t Simple.t) EPA.t TEE.t Name_occurrences.t) :=
        recursive! fuel in
        let* '(T6 cse extra_params typing_env_with_extra_params env_extension
                 allowed need_other_round) :=
          compute_cse_one_round cse extra_params typing_env_with_extra_params
            env_extension allowed
        in
        let! tmp1 :=
          and_then need_other_round
            (let! tmp2 := Flambda_features.cse_depth tt in
             ret (current_round <? tmp2))
        in
        if tmp1
        then
          do_rounds fuel (Z.succ current_round) cse extra_params
            typing_env_with_extra_params env_extension allowed
        else
          (* Either a fixpoint has been reached or we've already explored far
             enough *)
          ret (T4 cse extra_params env_extension allowed)
    in
    do_rounds fuel 1 EP.Map.empty EPA.empty typing_env_at_fork TEE.empty
      Name_occurrences.empty
  in
  let* have_propagated_something := mk_ref false in
  (* 440-454 *)
  let* cse_at_join_point :=
    (* Any CSE equation whose right-hand side identifies a name in the [allowed]
       set is propagated. We don't need to check the left-hand sides because we
       know all of those names are in [typing_env_at_fork]. *)
    EP.Map.fold
      (fun (prim : EP.t) (bound_to : Simple.t) (cse : T0.t) =>
        (* 446-450, [Simple.pattern_match bound_to ~const ~name]: the
           arguments are in the order of the interface. *)
        let* propagate :=
          Simple.pattern_match bound_to
            (fun name _ => Name_occurrences.mem_name allowed name)
            (fun _ => ret true)
        in
        if negb propagate
        then ret cse
        else
          set have_propagated_something true ;;
          let! tmp1 := Scope.next scope_at_fork in
          add cse prim bound_to tmp1)
      cse cse_at_fork
  in
  let! tmp1 := get have_propagated_something in
  if negb tmp1
  then ret None
  else
    ret
      (Some
         {| Join_result.cse_at_join_point := cse_at_join_point;
            Join_result.extra_params := extra_params;
            Join_result.env_extension := env_extension;
            Join_result.extra_allowed_names := allowed
         |}).

(* 464-481. In the compiler: [~typing_env_at_fork ~cse_at_fork ~use_info
   ~get_typing_env ~get_rewrite_id ~get_cse ~params]. *)
Definition join {A : Type} (typing_env_at_fork : TE.t) (cse_at_fork : T0.t)
    (use_info : list A) (get_typing_env : A -> M TE.t)
    (get_rewrite_id : A -> M RI.t) (get_cse : A -> M T0.t)
    (params : Bound_parameters.t) : M (option Join_result.t) :=
  let* scope_at_fork := TE.current_scope typing_env_at_fork in
  let* no_equations := mk_ref false in
  let* cse_at_each_use :=
    List.map
      (fun (use : A) =>
        let* t := get_cse use in
        let* cse_between_fork_and_use := cut_cse_environment t scope_at_fork in
        (* If one branch doesn't have any equations, then the join is going to
           be empty *)
        (let! tmp1 := EP.Map.is_empty cse_between_fork_and_use in
         if tmp1 then set no_equations true else ret tt) ;;
        let! tmp2 := get_rewrite_id use in
        let! tmp3 := get_typing_env use in
        ret (T3 tmp3 tmp2 cse_between_fork_and_use))
      use_info
  in
  let! tmp1 := get no_equations in
  if tmp1
  then ret None
  else
    join0 typing_env_at_fork cse_at_fork cse_at_each_use params scope_at_fork.
