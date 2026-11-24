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

(* This file follows middle_end/flambda2/simplify/env/upwards_env.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition under
   the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries
   [tmpN] and their order, the arguments by place, a setter [update_f] where
   the compiler writes [{ t with f }]) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite Are_rebuilding_terms
  Bound_parameters Continuation Continuation_in_env Continuation_shortcut
  Cost_metrics Dwarf_flags Flambda_arity Flambda_features Format
  Name_occurrences Or_null Or_unknown Rebuilt_expr Simple Target_system.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17-27 *)
Record t : Type :=
  { continuations : Continuation.Map.t Continuation_in_env.t;
    cold_continuations : Continuation.Set_.t;
    continuation_shortcuts : Continuation.Map.t Continuation_shortcut.t;
    unique_handlers_map :
      Rebuilt_expr.Unique_continuation_handlers.t Continuation.t;
    apply_cont_rewrites : Continuation.Map.t Apply_cont_rewrite.t;
    (* this [are_rebuilding_terms] is **only** used for printing *)
    are_rebuilding_terms : Are_rebuilding_terms.t;
    machine_width : Target_system.Machine_width.t
  }.

(* 29-37 *)
Definition create (are_rebuilding_terms : Are_rebuilding_terms.t)
    (machine_width : Target_system.Machine_width.t) : M Upwards_env.t :=
  ret
    {| continuations := Continuation.Map.empty;
       cold_continuations := Continuation.Set_.empty;
       continuation_shortcuts := Continuation.Map.empty;
       unique_handlers_map := Rebuilt_expr.Unique_continuation_handlers.empty;
       apply_cont_rewrites := Continuation.Map.empty;
       are_rebuilding_terms := are_rebuilding_terms;
       machine_width := machine_width
    |}.

(* PORT-GAP(loose): 39, [machine_width] is the projection [machine_width] of
   the record [t]: it is pure in Rocq, and Rocq prints it as [let
   machine_width t = t.machine_width] after the type. *)

(* 41-57 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept, and
   the record pattern of the parameter is a match. *)
Definition print (ppf : Format.formatter) (t : Upwards_env.t) : M unit :=
  match t with
  | {| continuations := continuations;
       cold_continuations := cold_continuations;
       continuation_shortcuts := continuation_shortcuts;
       unique_handlers_map := _;
       apply_cont_rewrites := apply_cont_rewrites;
       are_rebuilding_terms := are_rebuilding_terms;
       machine_width := _
    |} =>
    (* PORT-GAP(papp): [Continuation.Map.print] is given its first argument
       only, three times, and [Continuation_in_env.print] once. *)
    let! tmp1 := papp1 Continuation.Map.print Apply_cont_rewrite.print in
    let! tmp2 := papp1 Continuation.Map.print Continuation_shortcut.print in
    let! tmp3 := papp1 Continuation_in_env.print are_rebuilding_terms in
    let! tmp4 := papp1 Continuation.Map.print tmp3 in
    Format.fprintf8 ppf
      "@[<hov 1>(@[<hov 1>(continuations@ %a)@]@ @[<hov 1>(cold_continuations@ %a)@]@ @[<hov 1>(continuation_shortcuts@ %a)@]@ @[<hov 1>(apply_cont_rewrites@ %a)@])@]"
      tmp4 continuations Continuation.Set_.print cold_continuations tmp2
      continuation_shortcuts tmp1 apply_cont_rewrites
  end.

(* 59-64 *)
Definition find_continuation (t : Upwards_env.t) (cont : Continuation.t)
    : M Continuation_in_env.t :=
  match_exn
    (fun _ => Continuation.Map.find cont t.(continuations))
    Not_found
    (fun _ =>
      fatal_errorf4 "Unbound continuation %a in upwards environment:@ %a"
        Continuation.print cont print t)
    (fun cont_in_env => ret cont_in_env).

(* 66 *)
Definition mem_continuation (t : Upwards_env.t) (cont : Continuation.t)
    : M bool :=
  Continuation.Map.mem cont t.(continuations).

(* 68 *)
Definition is_cold_continuation (t : Upwards_env.t) (cont : Continuation.t)
    : M bool :=
  Continuation.Set_.mem cont t.(cold_continuations).

(* 70-79 *)
Definition check_shortcut_transitivity (t : Upwards_env.t)
    (cont shortcut_to : Continuation.t) : M unit :=
  let! tmp1 := Flambda_features.check_invariants tt in
  let! tmp2 :=
    and_then tmp1
      (Continuation.Map.mem shortcut_to t.(continuation_shortcuts))
  in
  if tmp2
  then
    fatal_errorf6
      "@[<hov 2>The continuation shortcut map does not represent the transitive closure of shortcut equations on continuations:@ %a, shortcut for %a, is already bound in %a@]"
      Continuation.print shortcut_to Continuation.print cont print t
  else ret tt.

(* 81-87 *)
Definition find_continuation_shortcut (t : Upwards_env.t)
    (cont : Continuation.t) : M (option Continuation_shortcut.t) :=
  let! tmp1 := Continuation.Map.find_or_null cont t.(continuation_shortcuts) in
  match tmp1 with
  | Or_null.Null => ret None
  | Or_null.This shortcut_to =>
    (let! tmp1 := Continuation_shortcut.continuation shortcut_to in
     check_shortcut_transitivity t cont tmp1) ;;
    ret (Some shortcut_to)
  end.

(* 89-92. [Rebuilt_expr.Unique_continuation_handlers.find_opt
   are_rebuilding_terms params handler t.unique_handlers_map ~is_exn_handler
   ~free_names_without_params]: the arguments are in the order of the
   interface. *)
Definition find_unique_continuation_handler
    (are_rebuilding_terms : Are_rebuilding_terms.t) (t : Upwards_env.t)
    (params : Bound_parameters.t) (handler : Rebuilt_expr.t)
    (is_exn_handler : bool) (free_names_without_params : Name_occurrences.t)
    : M (option (Continuation.t * list Simple.t)) :=
  Rebuilt_expr.Unique_continuation_handlers.find_opt are_rebuilding_terms
    params handler is_exn_handler free_names_without_params
    t.(unique_handlers_map).

(* PORT-GAP(update): 96, [{ t with continuations }]. *)
Definition update_continuations (t : Upwards_env.t)
    (continuations : Continuation.Map.t Continuation_in_env.t)
    : Upwards_env.t :=
  {| continuations := continuations;
     cold_continuations := t.(cold_continuations);
     continuation_shortcuts := t.(continuation_shortcuts);
     unique_handlers_map := t.(unique_handlers_map);
     apply_cont_rewrites := t.(apply_cont_rewrites);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     machine_width := t.(machine_width)
  |}.
Extract Inlined Constant update_continuations =>
  "(fun t x__1 -> { t with continuations = x__1 })".

(* 94-96 *)
Definition add_continuation0 (t : Upwards_env.t) (cont : Continuation.t)
    (cont_in_env : Continuation_in_env.t) : M Upwards_env.t :=
  let* continuations :=
    Continuation.Map.add cont cont_in_env t.(continuations)
  in
  ret (update_continuations t continuations).

(* PORT-GAP(update): 108, [{ t with unique_handlers_map }]. *)
Definition update_unique_handlers_map (t : Upwards_env.t)
    (unique_handlers_map :
      Rebuilt_expr.Unique_continuation_handlers.t Continuation.t)
    : Upwards_env.t :=
  {| continuations := t.(continuations);
     cold_continuations := t.(cold_continuations);
     continuation_shortcuts := t.(continuation_shortcuts);
     unique_handlers_map := unique_handlers_map;
     apply_cont_rewrites := t.(apply_cont_rewrites);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     machine_width := t.(machine_width)
  |}.
Extract Inlined Constant update_unique_handlers_map =>
  "(fun t x__1 -> { t with unique_handlers_map = x__1 })".

(* 98-108. [Rebuilt_expr.Unique_continuation_handlers.add
   are_rebuilding_terms params handler cont t.unique_handlers_map
   ~is_exn_handler ~free_names_without_params]: the arguments are in the
   order of the interface. *)
Definition add_unique_continuation_handler
    (are_rebuilding_terms : Are_rebuilding_terms.t) (t : Upwards_env.t)
    (cont : Continuation.t) (params : Bound_parameters.t)
    (handler : Rebuilt_expr.t) (is_exn_handler : bool)
    (free_names_without_params : Name_occurrences.t) : M Upwards_env.t :=
  let! tmp1 := get Dwarf_flags.gdwarf_may_alter_codegen in
  if tmp1
  then ret t
  else
    let* unique_handlers_map :=
      Rebuilt_expr.Unique_continuation_handlers.add are_rebuilding_terms
        params handler is_exn_handler free_names_without_params cont
        t.(unique_handlers_map)
    in
    ret (update_unique_handlers_map t unique_handlers_map).

(* PORT-GAP(update): 112, [{ t with cold_continuations }]. *)
Definition update_cold_continuations (t : Upwards_env.t)
    (cold_continuations : Continuation.Set_.t) : Upwards_env.t :=
  {| continuations := t.(continuations);
     cold_continuations := cold_continuations;
     continuation_shortcuts := t.(continuation_shortcuts);
     unique_handlers_map := t.(unique_handlers_map);
     apply_cont_rewrites := t.(apply_cont_rewrites);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     machine_width := t.(machine_width)
  |}.
Extract Inlined Constant update_cold_continuations =>
  "(fun t x__1 -> { t with cold_continuations = x__1 })".

(* 110-112 *)
Definition add_cold_continuation (t : Upwards_env.t) (cont : Continuation.t)
    : M Upwards_env.t :=
  let* cold_continuations :=
    Continuation.Set_.add cont t.(cold_continuations)
  in
  ret (update_cold_continuations t cold_continuations).

(* PORT-GAP(type): 119, the handler that [add_non_inlinable_continuation]
   takes is a tuple with labels, [(Rebuilt_expr.t * is_exn_handler:bool *
   free_names_without_params:Name_occurrences.t)], which Rocq cannot print
   and decl/Upwards_env.v gives as a tuple without labels. Here it is a type
   of one constructor, built and matched as the compiler's tuple. *)
Inductive handler_with_labels : Type :=
| Handler_with_labels :
    Rebuilt_expr.t -> bool -> Name_occurrences.t -> handler_with_labels.
Extract Inductive handler_with_labels => "(Rebuilt_expr.t * is_exn_handler:bool * free_names_without_params:Name_occurrences.t)" [ "(fun (x__1, x__2, x__3) -> (x__1, ~is_exn_handler:x__2, ~free_names_without_params:x__3))" ] "(fun f__1 x__0 -> match x__0 with x__1, ~is_exn_handler:x__2, ~free_names_without_params:x__3 -> f__1 x__1 x__2 x__3)".

(* 114-134. The compiler's comment of lines 121-124, a note for later, is
   left out. *)
Definition add_non_inlinable_continuation
    (are_rebuilding_terms : Are_rebuilding_terms.t) (t : Upwards_env.t)
    (cont : Continuation.t) (is_cold : bool) (params : Bound_parameters.t)
    (handler : Or_unknown.t handler_with_labels) : M Upwards_env.t :=
  let* t := if is_cold then add_cold_continuation t cont else ret t in
  let* '(t, handler) :=
    match handler with
    | Or_unknown.Known
        (Handler_with_labels handler is_exn_handler free_names_without_params)
      =>
      (* 120: [when not is_cold] *)
      if negb is_cold
      then
        let! tmp1 :=
          add_unique_continuation_handler are_rebuilding_terms t cont params
            handler is_exn_handler free_names_without_params
        in
        ret (tmp1, Or_unknown.Known handler)
      else ret (t, Or_unknown.Unknown)
    | Or_unknown.Unknown => ret (t, Or_unknown.Unknown)
    end
  in
  let! tmp1 := Bound_parameters.is_empty params in
  if tmp1
  then
    add_continuation0 t cont
      (Continuation_in_env.Non_inlinable_zero_arity handler)
  else
    let* arity := Bound_parameters.arity params in
    add_continuation0 t cont
      (Continuation_in_env.Non_inlinable_non_zero_arity arity).

(* 136-137 *)
Definition add_invalid_continuation (t : Upwards_env.t)
    (cont : Continuation.t) (arity : Flambda_arity.t_Unarized)
    : M Upwards_env.t :=
  add_continuation0 t cont (Continuation_in_env.Invalid arity).

(* 139-140: [a |> f] is [f a] *)
Definition continuation_arity (t : Upwards_env.t) (cont : Continuation.t)
    : M Flambda_arity.t_Unarized :=
  let! tmp1 := find_continuation t cont in
  Continuation_in_env.arity tmp1.

(* PORT-GAP(update): 177, [{ t with continuation_shortcuts }]. *)
Definition update_continuation_shortcuts (t : Upwards_env.t)
    (continuation_shortcuts : Continuation.Map.t Continuation_shortcut.t)
    : Upwards_env.t :=
  {| continuations := t.(continuations);
     cold_continuations := t.(cold_continuations);
     continuation_shortcuts := continuation_shortcuts;
     unique_handlers_map := t.(unique_handlers_map);
     apply_cont_rewrites := t.(apply_cont_rewrites);
     are_rebuilding_terms := t.(are_rebuilding_terms);
     machine_width := t.(machine_width)
  |}.
Extract Inlined Constant update_continuation_shortcuts =>
  "(fun t x__1 -> { t with continuation_shortcuts = x__1 })".

(* 142-177 *)
Definition add_continuation_shortcut (t : Upwards_env.t)
    (cont : Continuation.t) (params : Bound_parameters.t)
    (shortcut_to : Continuation.t) (args : list Simple.t)
    : M Upwards_env.t :=
  (let! tmp1 := Continuation.Map.mem shortcut_to t.(continuation_shortcuts) in
   if tmp1
   then
     fatal_errorf4
       "Cannot add continuation shortcut %a (as shortcut to %a); the target continuation is itself a shortcut"
       Continuation.print cont Continuation.print shortcut_to
   else ret tt) ;;
  let! tmp1 := Continuation.Map.find_or_null cont t.(continuation_shortcuts) in
  match tmp1 with
  | Or_null.This existing_shortcut =>
    let! tmp1 := Continuation_shortcut.continuation existing_shortcut in
    fatal_errorf6
      "Cannot add continuation shortcut %a (as shortcut to%a); the source continuation is already deemed to be a shortcut (to %a)"
      Continuation.print cont Continuation.print shortcut_to
      Continuation.print tmp1
  | Or_null.Null =>
    let* shortcut := Continuation_shortcut.create params shortcut_to args in
    (* For now we keep the pre-existing check for aliases, but ideally we
       should check that the arities match after applying the substitution.
       However it seems like we should have a more general mechanism for
       checking arities when applying continuations that's independent of
       shortcuts. *)
    (let! tmp1 := Continuation_shortcut.to_alias shortcut in
     match tmp1 with
     | Some alias_for =>
       let* arity := Bound_parameters.arity params in
       let* alias_for_arity := continuation_arity t alias_for in
       let! tmp1 :=
         Flambda_arity.equal_ignoring_subkinds arity alias_for_arity
       in
       if negb tmp1
       then
         fatal_errorf8
           "%a (arity %a) cannot be an alias for %a (arity %a) since the two continuations differ in arity"
           Continuation.print cont Flambda_arity.print arity
           Continuation.print alias_for Flambda_arity.print alias_for_arity
       else ret tt
     | None => ret tt
     end) ;;
    let* continuation_shortcuts :=
      Continuation.Map.add cont shortcut t.(continuation_shortcuts)
    in
    ret (update_continuation_shortcuts t continuation_shortcuts)
  end.

(* 179-183 *)
Definition add_linearly_used_inlinable_continuation (t : Upwards_env.t)
    (cont : Continuation.t) (params : Bound_parameters.t)
    (handler : Rebuilt_expr.t) (free_names_of_handler : Name_occurrences.t)
    (cost_metrics_of_handler : Cost_metrics.t) : M Upwards_env.t :=
  add_continuation0 t cont
    (Continuation_in_env.Linearly_used_and_inlinable params handler
       free_names_of_handler cost_metrics_of_handler).

(* 185-188 *)
Definition add_function_return_or_exn_continuation (t : Upwards_env.t)
    (cont : Continuation.t) (is_cold : bool)
    (arity : Flambda_arity.t_Unarized) : M Upwards_env.t :=
  let* t := if is_cold then add_cold_continuation t cont else ret t in
  add_continuation0 t cont
    (Continuation_in_env.Toplevel_or_function_return_or_exn_continuation
       arity).

(* PORT-GAP(update): 198, [{ t with apply_cont_rewrites }]. *)
Definition update_apply_cont_rewrites (t : Upwards_env.t)
    (apply_cont_rewrites : Continuation.Map.t Apply_cont_rewrite.t)
    : Upwards_env.t :=
  {| continuations := t.(continuations);
     cold_continuations := t.(cold_continuations);
     continuation_shortcuts := t.(continuation_shortcuts);
     unique_handlers_map := t.(unique_handlers_map);
     apply_cont_rewrites := apply_cont_rewrites;
     are_rebuilding_terms := t.(are_rebuilding_terms);
     machine_width := t.(machine_width)
  |}.
Extract Inlined Constant update_apply_cont_rewrites =>
  "(fun t x__1 -> { t with apply_cont_rewrites = x__1 })".

(* 190-198 *)
Definition add_apply_cont_rewrite (t : Upwards_env.t) (cont : Continuation.t)
    (rewrite : Apply_cont_rewrite.t) : M Upwards_env.t :=
  (let! tmp1 := Continuation.Map.mem cont t.(apply_cont_rewrites) in
   if tmp1
   then
     fatal_errorf2 "Cannot redefine [Apply_cont_rewrite] for %a"
       Continuation.print cont
   else ret tt) ;;
  let* apply_cont_rewrites :=
    Continuation.Map.add cont rewrite t.(apply_cont_rewrites)
  in
  ret (update_apply_cont_rewrites t apply_cont_rewrites).

(* 200-208 *)
Definition replace_apply_cont_rewrite (t : Upwards_env.t)
    (cont : Continuation.t) (rewrite : Apply_cont_rewrite.t)
    : M Upwards_env.t :=
  (let! tmp1 := Continuation.Map.mem cont t.(apply_cont_rewrites) in
   if negb tmp1
   then
     fatal_errorf2 "Must redefine [Apply_cont_rewrite] for %a"
       Continuation.print cont
   else ret tt) ;;
  let* apply_cont_rewrites :=
    Continuation.Map.add cont rewrite t.(apply_cont_rewrites)
  in
  ret (update_apply_cont_rewrites t apply_cont_rewrites).

(* 210-211 *)
Definition find_apply_cont_rewrite (t : Upwards_env.t) (cont : Continuation.t)
    : M (option Apply_cont_rewrite.t) :=
  Continuation.Map.find_opt cont t.(apply_cont_rewrites).
