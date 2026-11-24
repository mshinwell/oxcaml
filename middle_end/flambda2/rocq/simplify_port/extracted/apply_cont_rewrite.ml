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
   middle_end/flambda2/rocq/simplify_port/Apply_cont_rewrite.v, which follows
   middle_end/flambda2/simplify/apply_cont_rewrite.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

module EPA = Continuation_extra_params_and_args
module EA = EPA.Extra_arg
module Id = Apply_cont_rewrite_id
open Port_abbreviations
open Port_monad

type used =
  | Unused
  | Used
  | Used_as_invariant

type t =
  { original_params_usage : used list;
    extra_params_usage : used list;
    extra_args : EA.t list Or_invalid.t Id.Map.t;
    original_params : Bound_parameters.t;
    extra_params : Bound_parameters.t
  }

(** val original_params_usage : t -> used list **)

let original_params_usage t0 = t0.original_params_usage

(** val extra_params_usage : t -> used list **)

let extra_params_usage t0 = t0.extra_params_usage

(** val extra_args : t -> EA.t list Or_invalid.t Id.Map.t **)

let extra_args t0 = t0.extra_args

(** val original_params : t -> Bound_parameters.t **)

let original_params t0 = t0.original_params

(** val extra_params : t -> Bound_parameters.t **)

let extra_params t0 = t0.extra_params

(** val print_used : Format.formatter -> used -> unit coq_M **)

let print_used ppf = function
  | Unused -> Format.fprintf ppf "unused"
  | Used -> Format.fprintf ppf "used"
  | Used_as_invariant -> Format.fprintf ppf "invariant"

(** val print_params_used : Format.formatter -> (Bound_parameters.t * used list)
    -> unit coq_M **)

let print_params_used ppf = function
  | params, usage ->
    Format.fprintf ppf "(%a)"
      ((fun x__1 x__2 x__3 x__4 ->
         Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
         (Some Format.pp_print_space) (fun ppf0 pat0 ->
           let param, used0 = pat0 in
           Format.fprintf ppf0 "(%a:@ %a)" Bound_parameter.print param
             print_used used0))
      (List.combine (Bound_parameters.to_list params) usage)

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf pat =
  let { original_params_usage = original_params_usage0;
        extra_params_usage = extra_params_usage0;
        extra_args = extra_args0;
        original_params = original_params0;
        extra_params = extra_params0
      } =
    pat
  in
  Format.fprintf ppf
    "@[<hov 1>(@[<hov 1>(original_params@ (%a))@]@ @[<hov 1>(extra_params@ \
     %a)@]@ @[<hov 1>(extra_args@ %a)@])@]"
    print_params_used
    (original_params0, original_params_usage0)
    print_params_used
    (extra_params0, extra_params_usage0)
    (Id.Map.print
       (Or_invalid.print
          ((fun x__1 x__2 x__3 x__4 ->
             Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
             (Some Format.pp_print_space) EA.print)))
    extra_args0

(** val does_nothing : t -> bool coq_M **)

let does_nothing t0 =
  List.for_all
    (fun x ->
      match x with Unused -> false | Used -> true | Used_as_invariant -> false)
    t0.original_params_usage
  && List.for_all
       (fun x ->
         match x with
         | Unused -> true
         | Used -> false
         | Used_as_invariant -> false)
       t0.extra_params_usage

(** val create : Bound_parameters.t -> EPA.t -> (Bound_parameter.t -> used
    coq_M) -> t coq_M **)

let create original_params0 extra_params_and_args decide_param_usage =
  let extra_params0 = EPA.extra_params extra_params_and_args in
  let extra_args0 = EPA.extra_args extra_params_and_args in
  let () = Bound_parameters.check_no_duplicates original_params0 in
  let () = Bound_parameters.check_no_duplicates extra_params0 in
  let original_params_usage0 =
    List.map decide_param_usage (Bound_parameters.to_list original_params0)
  in
  let extra_params_usage0 =
    List.map decide_param_usage (Bound_parameters.to_list extra_params0)
  in
  { original_params_usage = original_params_usage0;
    extra_params_usage = extra_params_usage0;
    extra_args = extra_args0;
    original_params = original_params0;
    extra_params = extra_params0
  }

(** val original_params_arity : t -> (_) Flambda_arity.t coq_M **)

let original_params_arity t0 = Bound_parameters.arity t0.original_params

(** val partition_used : 'a1 list -> used list -> ('a1 list * 'a1 list) coq_M **)

let rec partition_used l usage =
  match l with
  | [] -> (
    match usage with
    | [] -> [], []
    | _ :: _ ->
      Misc.fatal_error
        "Apply_cont_rewrite.partition_used: list and usage must have the same \
         length")
  | x :: l0 -> (
    match usage with
    | [] ->
      Misc.fatal_error
        "Apply_cont_rewrite.partition_used: list and usage must have the same \
         length"
    | u :: usage0 -> (
      match u with
      | Unused -> partition_used l0 usage0
      | Used ->
        let invariant, normal = partition_used l0 usage0 in
        invariant, x :: normal
      | Used_as_invariant ->
        let invariant, normal = partition_used l0 usage0 in
        x :: invariant, normal))

(** val get_unused : 'a1 list -> used list -> 'a1 list coq_M **)

let rec get_unused l usage =
  match l with
  | [] -> (
    match usage with
    | [] -> []
    | _ :: _ ->
      Misc.fatal_errorf
        "Apply_cont_rewrite.get_unused: list and usage must have the same \
         length")
  | x :: l0 -> (
    match usage with
    | [] ->
      Misc.fatal_errorf
        "Apply_cont_rewrite.get_unused: list and usage must have the same \
         length"
    | u :: usage0 -> (
      match u with
      | Unused -> x :: get_unused l0 usage0
      | Used -> get_unused l0 usage0
      | Used_as_invariant -> get_unused l0 usage0))

(** val get_used_params : t -> (Bound_parameters.t * Bound_parameters.t) coq_M **)

let get_used_params rewrite =
  let invariant_params, variant_params =
    partition_used
      (Bound_parameters.to_list rewrite.original_params)
      rewrite.original_params_usage
  in
  let invariant_extra_params, variant_extra_params =
    partition_used
      (Bound_parameters.to_list rewrite.extra_params)
      rewrite.extra_params_usage
  in
  ( Bound_parameters.create (invariant_params @ invariant_extra_params),
    Bound_parameters.create (variant_params @ variant_extra_params) )

(** val get_unused_params : t -> Bound_parameters.t coq_M **)

let get_unused_params rewrite =
  let unused_params =
    get_unused
      (Bound_parameters.to_list rewrite.original_params)
      rewrite.original_params_usage
  in
  let unused_extra_params =
    get_unused
      (Bound_parameters.to_list rewrite.extra_params)
      rewrite.extra_params_usage
  in
  Bound_parameters.create (unused_params @ unused_extra_params)

type rewrite_apply_cont_ctx =
  | Apply_cont
  | Apply_expr of Simple.t list

(** val extra_args_list : t -> Id.t -> EA.t list Or_invalid.t coq_M **)

let extra_args_list rewrite id =
  Port_monad.try_with
    (fun _ -> Id.Map.find id rewrite.extra_args)
    Port_monad.not_found
    (fun _ ->
      match rewrite.extra_params_usage with
      | [] -> Or_invalid.Ok []
      | _ :: _ ->
        Misc.fatal_errorf
          "Apply_cont_rewrite.extra_args_list:@ Could not find extra args but \
           extra params were not empty for id %a"
          Apply_cont_rewrite_id.print id)

(** val make_rewrite : t -> Target_system.Machine_width.t ->
    rewrite_apply_cont_ctx -> Id.t -> Simple.t list -> ((Bound_var.t,
    Code_size.t, Flambda.Named.t) Port_monad.tuple3 list * Simple.t list)
    Or_invalid.t coq_M **)

let make_rewrite rewrite machine_width ctx id args =
  let invariant_args, args0 =
    partition_used args rewrite.original_params_usage
  in
  match extra_args_list rewrite id with
  | Or_invalid.Ok extra_args_list0 ->
    let extra_invariant_args_rev, extra_args_rev, extra_lets, _ =
      List.fold_left2
        (fun pat ->
          let ( extra_invariant_args_rev,
                extra_args_rev,
                extra_lets,
                required_by_other_extra_args ) =
            pat
          in
          fun arg used0 ->
            let extra_arg, extra_let, free_names, defined_names =
              match arg with
              | EA.Already_in_scope simple ->
                simple, [], Simple.free_names simple, Name_occurrences.empty
              | EA.New_let_binding (temp, prim) ->
                let temp_duid = Flambda_debug_uid.none in
                let extra_let =
                  ( Bound_var.create temp temp_duid Name_mode.normal,
                    Code_size.prim machine_width prim,
                    Flambda.Named.create_prim prim Debuginfo.none )
                in
                ( Simple.var temp,
                  extra_let :: [],
                  Flambda_primitive.free_names prim,
                  Name_occurrences.singleton_variable temp Name_mode.normal )
              | EA.New_let_binding_with_named_args (temp, gen_prim) ->
                let temp_duid = Flambda_debug_uid.none in
                let prim =
                  match ctx with
                  | Apply_cont ->
                    Misc.fatal_errorf
                      "Apply_cont rewrites should not need to name arguments, \
                       since they are already named."
                  | Apply_expr function_return_values ->
                    gen_prim function_return_values
                in
                let extra_let =
                  ( Bound_var.create temp temp_duid Name_mode.normal,
                    Code_size.prim machine_width prim,
                    Flambda.Named.create_prim prim Debuginfo.none )
                in
                ( Simple.var temp,
                  extra_let :: [],
                  Flambda_primitive.free_names prim,
                  Name_occurrences.singleton_variable temp Name_mode.normal )
            in
            let required_let, extra_invariant_args_rev0, extra_args_rev0 =
              match used0 with
              | Unused ->
                ( Name_occurrences.inter_domain_is_non_empty defined_names
                    required_by_other_extra_args,
                  extra_invariant_args_rev,
                  extra_args_rev )
              | Used ->
                true, extra_invariant_args_rev, extra_arg :: extra_args_rev
              | Used_as_invariant ->
                true, extra_arg :: extra_invariant_args_rev, extra_args_rev
            in
            if required_let
            then
              ( extra_invariant_args_rev0,
                extra_args_rev0,
                extra_let @ extra_lets,
                Name_occurrences.union free_names required_by_other_extra_args )
            else
              ( extra_invariant_args_rev0,
                extra_args_rev0,
                extra_lets,
                required_by_other_extra_args ))
        ([], [], [], Name_occurrences.empty)
        extra_args_list0 rewrite.extra_params_usage
    in
    Or_invalid.Ok
      ( extra_lets,
        invariant_args
        @ List.rev_append extra_invariant_args_rev args0
        @ List.rev extra_args_rev )
  | Or_invalid.Invalid -> Or_invalid.Invalid

(** val rewrite_exn_continuation : t -> Id.t -> Exn_continuation.t ->
    Exn_continuation.t coq_M **)

let rewrite_exn_continuation rewrite id exn_cont =
  let exn_cont_arity = Exn_continuation.arity exn_cont in
  let () =
    if
      not
        (Flambda_arity.equal_ignoring_subkinds exn_cont_arity
           (original_params_arity rewrite))
    then
      Misc.fatal_errorf
        "Arity of exception continuation %a does not match@ [original_params] \
         (%a)"
        Exn_continuation.print exn_cont Bound_parameters.print
        rewrite.original_params
    else ()
  in
  let () = assert (Flambda_arity.cardinal_unarized exn_cont_arity >= 1) in
  let () =
    match List.hd rewrite.original_params_usage with
    | Unused ->
      Misc.fatal_errorf
        "The usage of the exn parameter of the continuation rewrite should be \
         [Used]: %a"
        print rewrite
    | Used -> ()
    | Used_as_invariant ->
      Misc.fatal_errorf
        "The usage of the exn parameter of the continuation rewrite should be \
         [Used]: %a"
        print rewrite
  in
  let () =
    if
      List.exists
        (fun x ->
          match x with
          | Unused -> false
          | Used -> false
          | Used_as_invariant -> true)
        (rewrite.original_params_usage @ rewrite.extra_params_usage)
    then
      Misc.fatal_errorf
        "An exception continuation should never have invariant parameters: %a"
        print rewrite
    else ()
  in
  let _, extra_args0 =
    partition_used
      (Exn_continuation.extra_args exn_cont)
      (List.tl rewrite.original_params_usage)
  in
  let _, extra_args1 =
    let extra_args_list0 =
      match extra_args_list rewrite id with
      | Or_invalid.Ok extra_args_list0 ->
        List.map2
          (fun arg extra_param ->
            match arg with
            | EA.Already_in_scope simple ->
              simple, Bound_parameter.kind extra_param
            | EA.New_let_binding (_, _) ->
              Misc.fatal_error
                "[New_let_binding] are currently forbidden for exn \
                 continuation rewrites"
            | EA.New_let_binding_with_named_args (_, _) ->
              Misc.fatal_error
                "[New_let_binding] are currently forbidden for exn \
                 continuation rewrites")
          extra_args_list0
          (Bound_parameters.to_list rewrite.extra_params)
      | Or_invalid.Invalid ->
        Misc.fatal_error
          "[Invalid] extra args are currently not allowed for exn continuation \
           rewrites"
    in
    partition_used extra_args_list0 rewrite.extra_params_usage
  in
  let extra_args2 = extra_args0 @ extra_args1 in
  Exn_continuation.create (Exn_continuation.exn_handler exn_cont) extra_args2
