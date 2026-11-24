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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/env/Upwards_env.v, which follows
   middle_end/flambda2/simplify/env/upwards_env.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad

type t =
  { continuations : Continuation_in_env.t Continuation.Map.t;
    cold_continuations : Continuation.Set.t;
    continuation_shortcuts : Continuation_shortcut.t Continuation.Map.t;
    unique_handlers_map :
      Continuation.t Rebuilt_expr.Unique_continuation_handlers.t;
    apply_cont_rewrites : Apply_cont_rewrite.t Continuation.Map.t;
    are_rebuilding_terms : Are_rebuilding_terms.t;
    machine_width : Target_system.Machine_width.t
  }

(** val continuations : t -> Continuation_in_env.t Continuation.Map.t **)

let continuations t0 = t0.continuations

(** val cold_continuations : t -> Continuation.Set.t **)

let cold_continuations t0 = t0.cold_continuations

(** val continuation_shortcuts : t -> Continuation_shortcut.t Continuation.Map.t
    **)

let continuation_shortcuts t0 = t0.continuation_shortcuts

(** val unique_handlers_map : t -> Continuation.t
    Rebuilt_expr.Unique_continuation_handlers.t **)

let unique_handlers_map t0 = t0.unique_handlers_map

(** val apply_cont_rewrites : t -> Apply_cont_rewrite.t Continuation.Map.t **)

let apply_cont_rewrites t0 = t0.apply_cont_rewrites

(** val are_rebuilding_terms : t -> Are_rebuilding_terms.t **)

let are_rebuilding_terms t0 = t0.are_rebuilding_terms

(** val machine_width : t -> Target_system.Machine_width.t **)

let machine_width t0 = t0.machine_width

(** val create : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> t
    coq_M **)

let create are_rebuilding_terms0 machine_width0 =
  { continuations = Continuation.Map.empty;
    cold_continuations = Continuation.Set.empty;
    continuation_shortcuts = Continuation.Map.empty;
    unique_handlers_map = Rebuilt_expr.Unique_continuation_handlers.empty;
    apply_cont_rewrites = Continuation.Map.empty;
    are_rebuilding_terms = are_rebuilding_terms0;
    machine_width = machine_width0
  }

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  let { continuations = continuations0;
        cold_continuations = cold_continuations0;
        continuation_shortcuts = continuation_shortcuts0;
        unique_handlers_map = _;
        apply_cont_rewrites = apply_cont_rewrites0;
        are_rebuilding_terms = are_rebuilding_terms0;
        machine_width = _
      } =
    t0
  in
  Format.fprintf ppf
    "@[<hov 1>(@[<hov 1>(continuations@ %a)@]@ @[<hov 1>(cold_continuations@ \
     %a)@]@ @[<hov 1>(continuation_shortcuts@ %a)@]@ @[<hov \
     1>(apply_cont_rewrites@ %a)@])@]"
    (Continuation.Map.print (Continuation_in_env.print are_rebuilding_terms0))
    continuations0 Continuation.Set.print cold_continuations0
    (Continuation.Map.print Continuation_shortcut.print)
    continuation_shortcuts0
    (Continuation.Map.print Apply_cont_rewrite.print)
    apply_cont_rewrites0

(** val find_continuation : t -> Continuation.t -> Continuation_in_env.t coq_M **)

let find_continuation t0 cont =
  Port_monad.match_exn
    (fun _ -> Continuation.Map.find cont t0.continuations)
    Port_monad.not_found
    (fun _ ->
      Misc.fatal_errorf "Unbound continuation %a in upwards environment:@ %a"
        Continuation.print cont print t0)
    (fun cont_in_env -> cont_in_env)

(** val mem_continuation : t -> Continuation.t -> bool coq_M **)

let mem_continuation t0 cont = Continuation.Map.mem cont t0.continuations

(** val is_cold_continuation : t -> Continuation.t -> bool coq_M **)

let is_cold_continuation t0 cont =
  Continuation.Set.mem cont t0.cold_continuations

(** val check_shortcut_transitivity : t -> Continuation.t -> Continuation.t ->
    unit coq_M **)

let check_shortcut_transitivity t0 cont shortcut_to =
  if
    Flambda_features.check_invariants ()
    && Continuation.Map.mem shortcut_to t0.continuation_shortcuts
  then
    Misc.fatal_errorf
      "@[<hov 2>The continuation shortcut map does not represent the \
       transitive closure of shortcut equations on continuations:@ %a, \
       shortcut for %a, is already bound in %a@]"
      Continuation.print shortcut_to Continuation.print cont print t0
  else ()

(** val find_continuation_shortcut : t -> Continuation.t ->
    Continuation_shortcut.t option coq_M **)

let find_continuation_shortcut t0 cont =
  match Continuation.Map.find_or_null cont t0.continuation_shortcuts with
  | Null -> None
  | This shortcut_to ->
    let () =
      check_shortcut_transitivity t0 cont
        (Continuation_shortcut.continuation shortcut_to)
    in
    Some shortcut_to

(** val find_unique_continuation_handler : Are_rebuilding_terms.t -> t ->
    Bound_parameters.t -> Rebuilt_expr.t -> bool -> Name_occurrences.t ->
    (Continuation.t * Simple.t list) option coq_M **)

let find_unique_continuation_handler are_rebuilding_terms0 t0 params handler
    is_exn_handler free_names_without_params =
  Rebuilt_expr.Unique_continuation_handlers.find_opt are_rebuilding_terms0
    params handler is_exn_handler free_names_without_params
    t0.unique_handlers_map

(** val add_continuation0 : t -> Continuation.t -> Continuation_in_env.t -> t
    coq_M **)

let add_continuation0 t0 cont cont_in_env =
  let continuations0 = Continuation.Map.add cont cont_in_env t0.continuations in
  (fun t continuations -> { t with continuations }) t0 continuations0

(** val add_unique_continuation_handler : Are_rebuilding_terms.t -> t ->
    Continuation.t -> Bound_parameters.t -> Rebuilt_expr.t -> bool ->
    Name_occurrences.t -> t coq_M **)

let add_unique_continuation_handler are_rebuilding_terms0 t0 cont params handler
    is_exn_handler free_names_without_params =
  if !Dwarf_flags.gdwarf_may_alter_codegen
  then t0
  else
    let unique_handlers_map0 =
      Rebuilt_expr.Unique_continuation_handlers.add are_rebuilding_terms0 params
        handler is_exn_handler free_names_without_params cont
        t0.unique_handlers_map
    in
    (fun t unique_handlers_map -> { t with unique_handlers_map })
      t0 unique_handlers_map0

(** val add_cold_continuation : t -> Continuation.t -> t coq_M **)

let add_cold_continuation t0 cont =
  let cold_continuations0 = Continuation.Set.add cont t0.cold_continuations in
  (fun t cold_continuations -> { t with cold_continuations })
    t0 cold_continuations0

(** val add_non_inlinable_continuation : Are_rebuilding_terms.t -> t ->
    Continuation.t -> bool -> Bound_parameters.t -> (Rebuilt_expr.t *
    is_exn_handler:bool * free_names_without_params:Name_occurrences.t)
    Or_unknown.t -> t coq_M **)

let add_non_inlinable_continuation are_rebuilding_terms0 t0 cont is_cold params
    handler =
  let t1 = if is_cold then add_cold_continuation t0 cont else t0 in
  let t2, handler0 =
    match handler with
    | Or_unknown.Known h ->
      (fun f__1 x__0 ->
        match x__0 with
        | x__1, ~is_exn_handler:x__2, ~free_names_without_params:x__3 ->
          f__1 x__1 x__2 x__3)
        (fun handler0 is_exn_handler free_names_without_params ->
          if not is_cold
          then
            ( add_unique_continuation_handler are_rebuilding_terms0 t1 cont
                params handler0 is_exn_handler free_names_without_params,
              Or_unknown.Known handler0 )
          else t1, Or_unknown.Unknown)
        h
    | Or_unknown.Unknown -> t1, Or_unknown.Unknown
  in
  if Bound_parameters.is_empty params
  then
    add_continuation0 t2 cont
      ((fun x__1 ->
         (Continuation_in_env.Non_inlinable_zero_arity { handler = x__1 }
           : Continuation_in_env.t))
         handler0)
  else
    let arity = Bound_parameters.arity params in
    add_continuation0 t2 cont
      ((fun x__1 ->
         (Continuation_in_env.Non_inlinable_non_zero_arity { arity = x__1 }
           : Continuation_in_env.t))
         arity)

(** val add_invalid_continuation : t -> Continuation.t -> [ `Unarized ]
    Flambda_arity.t -> t coq_M **)

let add_invalid_continuation t0 cont arity =
  add_continuation0 t0 cont
    ((fun x__1 ->
       (Continuation_in_env.Invalid { arity = x__1 } : Continuation_in_env.t))
       arity)

(** val continuation_arity : t -> Continuation.t -> [ `Unarized ]
    Flambda_arity.t coq_M **)

let continuation_arity t0 cont =
  Continuation_in_env.arity (find_continuation t0 cont)

(** val add_continuation_shortcut : t -> Continuation.t -> Bound_parameters.t ->
    Continuation.t -> Simple.t list -> t coq_M **)

let add_continuation_shortcut t0 cont params shortcut_to args =
  let () =
    if Continuation.Map.mem shortcut_to t0.continuation_shortcuts
    then
      Misc.fatal_errorf
        "Cannot add continuation shortcut %a (as shortcut to %a); the target \
         continuation is itself a shortcut"
        Continuation.print cont Continuation.print shortcut_to
    else ()
  in
  match Continuation.Map.find_or_null cont t0.continuation_shortcuts with
  | Null ->
    let shortcut = Continuation_shortcut.create params shortcut_to args in
    let () =
      match Continuation_shortcut.to_alias shortcut with
      | Some alias_for ->
        let arity = Bound_parameters.arity params in
        let alias_for_arity = continuation_arity t0 alias_for in
        if not (Flambda_arity.equal_ignoring_subkinds arity alias_for_arity)
        then
          Misc.fatal_errorf
            "%a (arity %a) cannot be an alias for %a (arity %a) since the two \
             continuations differ in arity"
            Continuation.print cont Flambda_arity.print arity Continuation.print
            alias_for Flambda_arity.print alias_for_arity
        else ()
      | None -> ()
    in
    let continuation_shortcuts0 =
      Continuation.Map.add cont shortcut t0.continuation_shortcuts
    in
    (fun t continuation_shortcuts -> { t with continuation_shortcuts })
      t0 continuation_shortcuts0
  | This existing_shortcut ->
    Misc.fatal_errorf
      "Cannot add continuation shortcut %a (as shortcut to%a); the source \
       continuation is already deemed to be a shortcut (to %a)"
      Continuation.print cont Continuation.print shortcut_to Continuation.print
      (Continuation_shortcut.continuation existing_shortcut)

(** val add_linearly_used_inlinable_continuation : t -> Continuation.t ->
    Bound_parameters.t -> Rebuilt_expr.t -> Name_occurrences.t -> Cost_metrics.t
    -> t coq_M **)

let add_linearly_used_inlinable_continuation t0 cont params handler
    free_names_of_handler cost_metrics_of_handler =
  add_continuation0 t0 cont
    ((fun (x__1, x__2, x__3, x__4) ->
       (Continuation_in_env.Linearly_used_and_inlinable
          { params = x__1;
            handler = x__2;
            free_names_of_handler = x__3;
            cost_metrics_of_handler = x__4
          }
         : Continuation_in_env.t))
       (params, handler, free_names_of_handler, cost_metrics_of_handler))

(** val add_function_return_or_exn_continuation : t -> Continuation.t -> bool ->
    [ `Unarized ] Flambda_arity.t -> t coq_M **)

let add_function_return_or_exn_continuation t0 cont is_cold arity =
  let t1 = if is_cold then add_cold_continuation t0 cont else t0 in
  add_continuation0 t1 cont
    ((fun x__1 ->
       (Continuation_in_env.Toplevel_or_function_return_or_exn_continuation
          { arity = x__1 }
         : Continuation_in_env.t))
       arity)

(** val add_apply_cont_rewrite : t -> Continuation.t -> Apply_cont_rewrite.t ->
    t coq_M **)

let add_apply_cont_rewrite t0 cont rewrite =
  let () =
    if Continuation.Map.mem cont t0.apply_cont_rewrites
    then
      Misc.fatal_errorf "Cannot redefine [Apply_cont_rewrite] for %a"
        Continuation.print cont
    else ()
  in
  let apply_cont_rewrites0 =
    Continuation.Map.add cont rewrite t0.apply_cont_rewrites
  in
  (fun t apply_cont_rewrites -> { t with apply_cont_rewrites })
    t0 apply_cont_rewrites0

(** val replace_apply_cont_rewrite : t -> Continuation.t -> Apply_cont_rewrite.t
    -> t coq_M **)

let replace_apply_cont_rewrite t0 cont rewrite =
  let () =
    if not (Continuation.Map.mem cont t0.apply_cont_rewrites)
    then
      Misc.fatal_errorf "Must redefine [Apply_cont_rewrite] for %a"
        Continuation.print cont
    else ()
  in
  let apply_cont_rewrites0 =
    Continuation.Map.add cont rewrite t0.apply_cont_rewrites
  in
  (fun t apply_cont_rewrites -> { t with apply_cont_rewrites })
    t0 apply_cont_rewrites0

(** val find_apply_cont_rewrite : t -> Continuation.t -> Apply_cont_rewrite.t
    option coq_M **)

let find_apply_cont_rewrite t0 cont =
  Continuation.Map.find_opt cont t0.apply_cont_rewrites
