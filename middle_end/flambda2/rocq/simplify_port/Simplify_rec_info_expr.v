(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplify_rec_info_expr.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the recursive function)
   is that of GUIDE.md. The file does not import Simplify_import, which the
   compiler's file does not open: its five abbreviations of modules are its
   own. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Downwards_acc Downwards_env Flambda2_types
  Flambda_features Flambda_kind Format Int Int_ids Name Name_mode Or_infinity
  Rec_info_expr Simple.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda2_types.meet_shortcut
   Flambda2_types.reification_result Int_ids.Rec_info_expr.Unrolling_state.t
   Int_ids.Rec_info_expr.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17-21 *)
From SimplifyPort.abbrev.simplify_rec_info_expr Require Import Port_abbreviations.
(*OCAML
module DA = Downwards_acc
module DE = Downwards_env
module K = Flambda_kind
module T = Flambda2_types
module TE = T.Typing_env
OCAML*)

(* 23-38 *)
Definition compute_succ (depth : Or_infinity.t int)
    (unrolling : Rec_info_expr.Unrolling_state.t)
    : M Rec_info_expr.t :=
  let& depth :=
    match depth with
    | Or_infinity.Finite n => Or_infinity.Finite (n + 1)
    | Or_infinity.Infinity => Or_infinity.Infinity
    end
  in
  let* unrolling :=
    match unrolling with
    | Int_ids.Rec_info_expr.Unrolling_state.Not_unrolling
    | Int_ids.Rec_info_expr.Unrolling_state.Do_not_unroll => ret unrolling
    | Int_ids.Rec_info_expr.Unrolling_state.Unrolling remaining_depth =>
      if remaining_depth <=? 0
      then ret unrolling
      else
        let& remaining_depth := remaining_depth - 1 in
        Rec_info_expr.Unrolling_state.unrolling remaining_depth
    end
  in
  Rec_info_expr.const depth unrolling.

(* 40-53 *)
Definition compute_unroll_to (depth : Or_infinity.t int)
    (old_unrolling_state : Rec_info_expr.Unrolling_state.t) (unroll_to : int)
    : M Rec_info_expr.t :=
  (* Take the maximum of the two unroll depths. This allows an external caller
     to specify more unrolling than the recursive call sites do. *)
  let* unrolling :=
    match old_unrolling_state with
    | Int_ids.Rec_info_expr.Unrolling_state.Not_unrolling =>
      Rec_info_expr.Unrolling_state.unrolling unroll_to
    | Int_ids.Rec_info_expr.Unrolling_state.Unrolling remaining_depth =>
      if remaining_depth >=? unroll_to
      then ret old_unrolling_state
      else Rec_info_expr.Unrolling_state.unrolling unroll_to
    | Int_ids.Rec_info_expr.Unrolling_state.Do_not_unroll =>
      ret old_unrolling_state
    end
  in
  Rec_info_expr.const depth unrolling.

(* 55-57 *)
Inductive on_unknown : Type :=
| Leave_unevaluated
| Assume_value (value : Rec_info_expr.t).

(* 59-121 *)
Fixpoint simplify_rec_info_expr0 (fuel : fuel) (denv : DE.t)
    (orig : Rec_info_expr.t) (on_unknown : on_unknown) {struct fuel}
    : M Rec_info_expr.t :=
  recursive! fuel in
  match orig with
  | Int_ids.Rec_info_expr.Const _ _ => ret orig
  | Int_ids.Rec_info_expr.Var dv =>
    (* PORT-GAP(loose): 62, the attribute [@local] is not kept. *)
    let& normal_case :=
      fun (_ : unit) =>
      let* ty :=
        let! tmp1 := Name.var dv in
        let! tmp2 := DE.typing_env denv in
        TE.find tmp2 tmp1 (Some K.rec_info)
      in
      let! tmp1 := DE.typing_env denv in
      let! tmp2 := T.meet_rec_info tmp1 ty in
      match tmp2 with
      | T.Known_result rec_info_expr =>
        (* All bound names are fresh, so fine to use the same environment *)
        simplify_rec_info_expr0 fuel denv rec_info_expr on_unknown
      | T.Need_meet | T.Invalid =>
        (* The invalid case can happen if the current context is itself invalid,
           which should be rare but not anomalous. Treat invalid cases as
           unknown -- it is annoying to propagate the invalid to coercions and
           smiples, and we'll figure out that the context is invalid as soon as
           we simplify a regular primitive anyways. *)
        match on_unknown with
        | Leave_unevaluated => ret orig
        | Assume_value value => ret value
        end
      end
    in
    (* Normally, we would expect that all variables appearing in a
       [Rec_info_expr] are available in the current context.

       However, when the "erase in-types depth variables" flag is set, we might
       see depth variables appearing inside coercions that only exist at the
       [In_types] name mode: these come from the value slots of the current
       closure. Without that flag, we would have explicitly set those variables
       to have type [Rec_info_expr.do_not_inline]; but with the flag, we have
       left them as is when entering the set of closures and need to replace
       them with [Rec_info_expr.do_not_inline] explicitly here.

       mshinwell: Leo and I have discussed allowing In_types variables in
       closures, which should cover this case, if we allowed such variables to
       be of kinds other than [Value]. *)
    (* 91-106. 101-103, [TE.get_canonical_simple_exn (DE.typing_env denv)
       ~min_name_mode:Name_mode.normal (Simple.var dv)]: the arguments are
       in the order of the interface. *)
    let! tmp1 := Flambda_features.erase_in_types_depth_variables tt in
    if tmp1
    then
      (* Note that we use [get_canonical_simple_exn] to check if the variable
         has an alias at [Normal] name mode, rather than simply checking (with
         [TE.mem ~min_name_mode]) that the variable itself has [Normal] name
         mode.

         While it is unlikely to matter, checking the canonical is more robust
         and avoids accidentally preventing more inlining than necessary. *)
      match_exn
        (fun _ =>
          let! tmp1 := Simple.var dv in
          let! tmp2 := DE.typing_env denv in
          TE.get_canonical_simple_exn tmp2 (Some Name_mode.normal) None tmp1)
        Not_found
        (fun _ => ret Rec_info_expr.do_not_inline)
        (fun _canonical => normal_case tt)
    else normal_case tt
  | Int_ids.Rec_info_expr.Succ ri =>
    (* PORT-GAP(loose): 108-111, the compiler matches the call, and its
       second case is [(Var _ | Succ _ | Unroll_to _) as new_ri]; here the
       result of the call is bound under that name, then matched. *)
    let* new_ri := simplify_rec_info_expr0 fuel denv ri on_unknown in
    match new_ri with
    | Int_ids.Rec_info_expr.Const depth unrolling =>
      compute_succ depth unrolling
    | Int_ids.Rec_info_expr.Var _ | Int_ids.Rec_info_expr.Succ _
    | Int_ids.Rec_info_expr.Unroll_to _ _ =>
      let! tmp1 := phys_equal ri new_ri in
      if tmp1 then ret orig else Rec_info_expr.succ new_ri
    end
  | Int_ids.Rec_info_expr.Unroll_to unroll_depth ri =>
    (* PORT-GAP(loose): 113-120, as for [Succ]: the result of the call is
       bound as [new_ri], then matched. *)
    let* new_ri := simplify_rec_info_expr0 fuel denv ri on_unknown in
    match new_ri with
    | Int_ids.Rec_info_expr.Const depth unrolling =>
      compute_unroll_to depth unrolling unroll_depth
    | Int_ids.Rec_info_expr.Var _ | Int_ids.Rec_info_expr.Succ _
    | Int_ids.Rec_info_expr.Unroll_to _ _ =>
      let! tmp1 := phys_equal ri new_ri in
      if tmp1 then ret orig else Rec_info_expr.unroll_to unroll_depth new_ri
    end
  end.

(* 123-128 *)
Definition simplify_rec_info_expr (dacc : DA.t)
    (rec_info_expr : Rec_info_expr.t) : M Rec_info_expr.t :=
  let* ans :=
    let_fuel! fuel in
    let! tmp1 := DA.denv dacc in
    simplify_rec_info_expr0 fuel tmp1 rec_info_expr Leave_unevaluated
  in
  ret ans.

(* 130-138 *)
Module Evaluated_rec_info_expr.
  (* 131-134 *)
  Record t : Type := {
    depth : Or_infinity.t int;
    unrolling : Rec_info_expr.Unrolling_state.t
  }.

  (* 136-137 *)
  (* PORT-GAP(loose): 136, the attribute [@ocamlformat "disable"] is not
     kept. *)
  Definition print (ppf : Format.formatter)
      '({| depth := depth; unrolling := unrolling |} : t) : M unit :=
    let! tmp1 := Rec_info_expr.const depth unrolling in
    Rec_info_expr.print ppf tmp1.
End Evaluated_rec_info_expr.

(* 140-148 *)
Definition evaluate_rec_info_expr (dacc : DA.t)
    (rec_info_expr : Rec_info_expr.t) : M Evaluated_rec_info_expr.t :=
  let_fuel! fuel in
  let! tmp1 := DA.denv dacc in
  let! tmp2 :=
    simplify_rec_info_expr0 fuel tmp1 rec_info_expr
      (Assume_value Rec_info_expr.unknown)
  in
  match tmp2 with
  | Int_ids.Rec_info_expr.Const depth unrolling =>
    ret
      {| Evaluated_rec_info_expr.depth := depth;
         Evaluated_rec_info_expr.unrolling := unrolling
      |}
  | Int_ids.Rec_info_expr.Var _ | Int_ids.Rec_info_expr.Succ _
  | Int_ids.Rec_info_expr.Unroll_to _ _ =>
    fatal_errorf4 "Unable to evaluate@ %a@ with@ dacc@ %a" Rec_info_expr.print
      rec_info_expr DA.print dacc
  end.

(* 150-154 *)
Definition depth_may_exceed (dacc : DA.t)
    (rec_info_expr : Rec_info_expr.t) (bound : int) : M bool :=
  let* '{| Evaluated_rec_info_expr.depth := depth |} :=
    evaluate_rec_info_expr dacc rec_info_expr
  in
  let! tmp1 :=
    Or_infinity.compare Int.compare depth (Or_infinity.Finite bound)
  in
  ret (tmp1 >? 0).

(* 156-159 *)
Definition known_remaining_unrolling_depth (dacc : DA.t)
    (rec_info_expr : Rec_info_expr.t) : M (option int) :=
  let! tmp1 := evaluate_rec_info_expr dacc rec_info_expr in
  match tmp1 with
  | {| Evaluated_rec_info_expr.unrolling :=
         Int_ids.Rec_info_expr.Unrolling_state.Unrolling remaining_depth
    |} =>
    ret (Some remaining_depth)
  | {| Evaluated_rec_info_expr.unrolling :=
         (Int_ids.Rec_info_expr.Unrolling_state.Not_unrolling
         | Int_ids.Rec_info_expr.Unrolling_state.Do_not_unroll)
    |} =>
    ret None
  end.

(* 161-164 *)
Definition can_unroll (dacc : DA.t) (rec_info_expr : Rec_info_expr.t)
    : M bool :=
  let! tmp1 := evaluate_rec_info_expr dacc rec_info_expr in
  match tmp1 with
  | {| Evaluated_rec_info_expr.unrolling :=
         Int_ids.Rec_info_expr.Unrolling_state.Do_not_unroll
    |} =>
    ret false
  | {| Evaluated_rec_info_expr.unrolling :=
         (Int_ids.Rec_info_expr.Unrolling_state.Not_unrolling
         | Int_ids.Rec_info_expr.Unrolling_state.Unrolling _)
    |} =>
    ret true
  end.
