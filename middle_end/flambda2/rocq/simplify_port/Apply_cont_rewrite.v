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

(* This file follows middle_end/flambda2/simplify/apply_cont_rewrite.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. The compiler's
   file does not open [Simplify_import], so this one does not import its
   declarations. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter
  Bound_parameters Bound_var Code_size Continuation_extra_params_and_args
  Debuginfo Exn_continuation Flambda Flambda_arity Flambda_debug_uid
  Flambda_primitive Format List Name_mode Name_occurrences Or_invalid Simple
  Target_system.
Local Open Scope string_scope.
Local Open Scope Z_scope.
(* [@] on lists is [++]. *)
Local Open Scope list_scope.

(* 17-19 *)
From SimplifyPort.abbrev.apply_cont_rewrite Require Import Port_abbreviations.
(*OCAML
module EPA = Continuation_extra_params_and_args
module EA = EPA.Extra_arg
module Id = Apply_cont_rewrite_id
OCAML*)

(* 21-24 *)
Inductive used : Type :=
| Unused
| Used
| Used_as_invariant.

(* 26-32 *)
Record t : Type := {
  original_params_usage : list used;
  extra_params_usage : list used;
  extra_args : Id.Map.t (Or_invalid.t (list EA.t));
  original_params : Bound_parameters.t;
  extra_params : Bound_parameters.t
}.

(* 34-37 *)
Definition print_used (ppf : Format.formatter) (x : used) : M unit :=
  match x with
  | Unused => Format.fprintf0 ppf "unused"
  | Used => Format.fprintf0 ppf "used"
  | Used_as_invariant => Format.fprintf0 ppf "invariant"
  end.

(* 39-45 *)
Definition print_params_used (ppf : Format.formatter)
    '((params, usage) : Bound_parameters.t * list used) : M unit :=
  let! tmp1 := Bound_parameters.to_list params in
  let! tmp2 := List.combine tmp1 usage in
  (* PORT-GAP(papp): [Format.pp_print_list] is given its first two
     arguments only. *)
  let! tmp3 :=
    papp2 Format.pp_print_list (Some Format.pp_print_space)
      ((fun ppf '(param, used) =>
         Format.fprintf4 ppf "(%a:@ %a)" Bound_parameter.print param
           print_used used)
       : Format.formatter -> Bound_parameter.t * used -> M unit)
  in
  Format.fprintf2 ppf "(%a)" tmp3 tmp2.

(* 47-59 *)
(* PORT-GAP(loose): 47, the attribute [@ocamlformat "disable"] is not kept;
   50-54, the lines of the format are joined. *)
Definition print (ppf : Format.formatter)
    '({| original_params_usage := original_params_usage;
         extra_params_usage := extra_params_usage;
         extra_args := extra_args;
         original_params := original_params;
         extra_params := extra_params |} : t) : M unit :=
  (* PORT-GAP(papp): [Format.pp_print_list] is given its first two
     arguments only, [Or_invalid.print] and [Id.Map.print] their first. *)
  let! tmp1 :=
    papp2 Format.pp_print_list (Some Format.pp_print_space) EA.print
  in
  let! tmp2 := papp1 Or_invalid.print tmp1 in
  let! tmp3 := papp1 Id.Map.print tmp2 in
  Format.fprintf6 ppf
    "@[<hov 1>(@[<hov 1>(original_params@ (%a))@]@ @[<hov 1>(extra_params@ %a)@]@ @[<hov 1>(extra_args@ %a)@])@]"
    print_params_used (original_params, original_params_usage)
    print_params_used (extra_params, extra_params_usage)
    tmp3 extra_args.

(* 61-67 *)
Definition does_nothing (t : t) : M bool :=
  let! tmp1 :=
    List.for_all
      (fun x =>
        match x with
        | Used => ret true
        | Used_as_invariant | Unused => ret false
        end)
      t.(original_params_usage)
  in
  and_then tmp1
    (List.for_all
       (fun x =>
         match x with
         | Unused => ret true
         | Used | Used_as_invariant => ret false
         end)
       t.(extra_params_usage)).

(* 69-85 *)
Definition create (original_params : Bound_parameters.t)
    (extra_params_and_args : EPA.t)
    (decide_param_usage : Bound_parameter.t -> M used) : M t :=
  let* extra_params := EPA.extra_params extra_params_and_args in
  let* extra_args := EPA.extra_args extra_params_and_args in
  Bound_parameters.check_no_duplicates original_params ;;
  Bound_parameters.check_no_duplicates extra_params ;;
  let* original_params_usage :=
    let! tmp1 := Bound_parameters.to_list original_params in
    List.map decide_param_usage tmp1
  in
  let* extra_params_usage :=
    let! tmp1 := Bound_parameters.to_list extra_params in
    List.map decide_param_usage tmp1
  in
  ret
    {| original_params_usage := original_params_usage;
       extra_params_usage := extra_params_usage;
       extra_args := extra_args;
       original_params := original_params;
       extra_params := extra_params |}.

(* 87 *)
Definition original_params_arity (t : t) : M Flambda_arity.t :=
  Bound_parameters.arity t.(original_params).

(* 89-102 *)
Fixpoint partition_used {A : Type} (l : list A) (usage : list used)
    {struct l} : M (list A * list A) :=
  match l, usage with
  | [], [] => ret ([], [])
  | [], _ :: _ | _ :: _, [] =>
    fatal_error
      "Apply_cont_rewrite.partition_used: list and usage must have the same length"
  | _ :: l, Unused :: usage => partition_used l usage
  | x :: l, Used :: usage =>
    let* '(invariant, normal) := partition_used l usage in
    ret (invariant, x :: normal)
  | x :: l, Used_as_invariant :: usage =>
    let* '(invariant, normal) := partition_used l usage in
    ret (x :: invariant, normal)
  end.

(* 104-111 *)
Fixpoint get_unused {A : Type} (l : list A) (usage : list used) {struct l}
    : M (list A) :=
  match l, usage with
  | [], [] => ret []
  | [], _ :: _ | _ :: _, [] =>
    fatal_errorf0
      "Apply_cont_rewrite.get_unused: list and usage must have the same length"
  | x :: l, Unused :: usage =>
    let! tmp1 := get_unused l usage in
    ret (x :: tmp1)
  | _ :: l, (Used | Used_as_invariant) :: usage => get_unused l usage
  end.

(* 113-125 *)
Definition get_used_params (rewrite : t)
    : M (Bound_parameters.t * Bound_parameters.t) :=
  let* '(invariant_params, variant_params) :=
    let! tmp1 := Bound_parameters.to_list rewrite.(original_params) in
    partition_used tmp1 rewrite.(original_params_usage)
  in
  let* '(invariant_extra_params, variant_extra_params) :=
    let! tmp1 := Bound_parameters.to_list rewrite.(extra_params) in
    partition_used tmp1 rewrite.(extra_params_usage)
  in
  let! tmp1 :=
    Bound_parameters.create (variant_params ++ variant_extra_params)
  in
  let! tmp2 :=
    Bound_parameters.create (invariant_params ++ invariant_extra_params)
  in
  ret (tmp2, tmp1).

(* 127-138 *)
Definition get_unused_params (rewrite : t) : M Bound_parameters.t :=
  let* unused_params :=
    let! tmp1 := Bound_parameters.to_list rewrite.(original_params) in
    get_unused tmp1 rewrite.(original_params_usage)
  in
  let* unused_extra_params :=
    let! tmp1 := Bound_parameters.to_list rewrite.(extra_params) in
    get_unused tmp1 rewrite.(extra_params_usage)
  in
  Bound_parameters.create (unused_params ++ unused_extra_params).

(* 140-142 *)
Inductive rewrite_apply_cont_ctx : Type :=
| Apply_cont
| Apply_expr (_ : list Simple.t).

(* 144-153 *)
Definition extra_args_list (rewrite : t) (id : Id.t)
    : M (Or_invalid.t (list EA.t)) :=
  try_with
    (fun _ => Id.Map.find id rewrite.(extra_args))
    Not_found
    (fun _ =>
      match rewrite.(extra_params_usage) with
      | [] => ret (Or_invalid.Ok [])
      | _ :: _ =>
        fatal_errorf2
          "Apply_cont_rewrite.extra_args_list:@ Could not find extra args but extra params were not empty for id %a"
          Apply_cont_rewrite_id.print id
      end).

(* 155-240. In the compiler: [rewrite ~machine_width ~ctx id args]. *)
Definition make_rewrite (rewrite : t)
    (machine_width : Target_system.Machine_width.t)
    (ctx : rewrite_apply_cont_ctx) (id : Id.t) (args : list Simple.t)
    : M (Or_invalid.t
           (list (tuple3 Bound_var.t Code_size.t Flambda.Named.t)
            * list Simple.t)) :=
  let* '(invariant_args, args) :=
    partition_used args rewrite.(original_params_usage)
  in
  let! tmp1 := extra_args_list rewrite id in
  match tmp1 with
  | Or_invalid.Invalid => ret Or_invalid.Invalid
  | Or_invalid.Ok extra_args_list =>
    (* 162-235 *)
    let* '(T4 extra_invariant_args_rev extra_args_rev extra_lets _) :=
      List.fold_left2
        (fun '(T4 extra_invariant_args_rev extra_args_rev extra_lets
                 required_by_other_extra_args)
             (arg : EA.t) (used : used) =>
          (* Some extra_args computation can depend on other extra args. But
             those required extra args might not be needed as argument to the
             continuation. But we want to keep the let bindings.
             [required_by_other_extra_args] tracks that dependency. It is the
             set of free variables of [extra_args_rev] and
             [extra_invariant_args_rev] *)
          let* '(T4 extra_arg extra_let free_names defined_names) :=
            match arg with
            | EA.Already_in_scope simple =>
              let! tmp1 := Simple.free_names simple in
              ret (T4 simple [] tmp1 Name_occurrences.empty)
            | EA.New_let_binding temp prim =>
              let& temp_duid := Flambda_debug_uid.none in
              let* extra_let :=
                let! tmp1 := Flambda.Named.create_prim prim Debuginfo.none in
                let! tmp2 := Code_size.prim machine_width prim in
                let! tmp3 := Bound_var.create temp temp_duid Name_mode.normal in
                ret (T3 tmp3 tmp2 tmp1)
              in
              let! tmp1 :=
                Name_occurrences.singleton_variable temp Name_mode.normal
              in
              let! tmp2 := Flambda_primitive.free_names prim in
              let! tmp3 := Simple.var temp in
              ret (T4 tmp3 [extra_let] tmp2 tmp1)
            | EA.New_let_binding_with_named_args temp gen_prim =>
              let& temp_duid := Flambda_debug_uid.none in
              let* prim :=
                match ctx with
                | Apply_expr function_return_values =>
                  gen_prim function_return_values
                | Apply_cont =>
                  fatal_errorf0
                    "Apply_cont rewrites should not need to name arguments, since they are already named."
                end
              in
              let* extra_let :=
                let! tmp1 := Flambda.Named.create_prim prim Debuginfo.none in
                let! tmp2 := Code_size.prim machine_width prim in
                let! tmp3 := Bound_var.create temp temp_duid Name_mode.normal in
                ret (T3 tmp3 tmp2 tmp1)
              in
              let! tmp1 :=
                Name_occurrences.singleton_variable temp Name_mode.normal
              in
              let! tmp2 := Flambda_primitive.free_names prim in
              let! tmp3 := Simple.var temp in
              ret (T4 tmp3 [extra_let] tmp2 tmp1)
            end
          in
          (* 210-221 *)
          let* '(T3 required_let extra_invariant_args_rev extra_args_rev) :=
            match used with
            | Used =>
              ret (T3 true extra_invariant_args_rev (extra_arg :: extra_args_rev))
            | Used_as_invariant =>
              ret (T3 true (extra_arg :: extra_invariant_args_rev) extra_args_rev)
            | Unused =>
              let! tmp1 :=
                Name_occurrences.inter_domain_is_non_empty defined_names
                  required_by_other_extra_args
              in
              ret (T3 tmp1 extra_invariant_args_rev extra_args_rev)
            end
          in
          (* 222-232 *)
          if required_let
          then
            let! tmp1 :=
              Name_occurrences.union free_names required_by_other_extra_args
            in
            ret
              (T4 extra_invariant_args_rev extra_args_rev
                 (extra_let ++ extra_lets) tmp1)
          else
            ret
              (T4 extra_invariant_args_rev extra_args_rev extra_lets
                 required_by_other_extra_args))
        (T4 [] [] [] Name_occurrences.empty)
        extra_args_list rewrite.(extra_params_usage)
    in
    (* 236-240 *)
    let! tmp1 := List.rev extra_args_rev in
    let! tmp2 := List.rev_append extra_invariant_args_rev args in
    ret (Or_invalid.Ok (extra_lets, invariant_args ++ tmp2 ++ tmp1))
  end.

(* 242-307 *)
Definition rewrite_exn_continuation (rewrite : t) (id : Id.t)
    (exn_cont : Exn_continuation.t) : M Exn_continuation.t :=
  let* exn_cont_arity := Exn_continuation.arity exn_cont in
  (* 244-253 *)
  (let! tmp1 := original_params_arity rewrite in
   let! tmp2 :=
     Flambda_arity.equal_ignoring_subkinds exn_cont_arity tmp1
   in
   if negb tmp2
   then
     fatal_errorf4
       "Arity of exception continuation %a does not match@ [original_params] (%a)"
       Exn_continuation.print exn_cont Bound_parameters.print
       rewrite.(original_params)
   else ret tt) ;;
  (* 254 *)
  (let! tmp1 := Flambda_arity.cardinal_unarized exn_cont_arity in
   assert_ (tmp1 >=? 1)) ;;
  (* 255-261 *)
  (let! tmp1 := List.hd rewrite.(original_params_usage) in
   match tmp1 with
   | Used => ret tt
   | Unused | Used_as_invariant =>
     fatal_errorf2
       "The usage of the exn parameter of the continuation rewrite should be [Used]: %a"
       print rewrite
   end) ;;
  (* 262-270 *)
  (let! tmp1 :=
     List.exists_
       (fun x =>
         match x with
         | Used_as_invariant => ret true
         | Used | Unused => ret false
         end)
       (rewrite.(original_params_usage) ++ rewrite.(extra_params_usage))
   in
   if tmp1
   then
     fatal_errorf2
       "An exception continuation should never have invariant parameters: %a"
       print rewrite
   else ret tt) ;;
  (* 271-275 *)
  let* '(_, extra_args0) :=
    let! tmp1 := List.tl rewrite.(original_params_usage) in
    let! tmp2 := Exn_continuation.extra_args exn_cont in
    partition_used tmp2 tmp1
  in
  (* 276-303 *)
  let* '(_, extra_args1) :=
    let* extra_args_list :=
      let! tmp1 := extra_args_list rewrite id in
      match tmp1 with
      | Or_invalid.Invalid =>
        (* CR gbury: This is not supported for now, but adding support for it
           should be relatively easy and straight-forward *)
        fatal_error
          "[Invalid] extra args are currently not allowed for exn continuation rewrites"
      | Or_invalid.Ok extra_args_list =>
        let! tmp1 := Bound_parameters.to_list rewrite.(extra_params) in
        List.map2
          (fun (arg : EA.t) extra_param =>
            match arg with
            | EA.Already_in_scope simple =>
              let! tmp2 := Bound_parameter.kind extra_param in
              ret (simple, tmp2)
            | EA.New_let_binding _ _ | EA.New_let_binding_with_named_args _ _ =>
              (* Note: this is unsupported for now. If we choose to support it
                 in the future, we must take care of not introducing a wrapper
                 continuation, which would come with its own
                 pushtrap/poptrap. *)
              fatal_error
                "[New_let_binding] are currently forbidden for exn continuation rewrites"
            end)
          extra_args_list tmp1
      end
    in
    partition_used extra_args_list rewrite.(extra_params_usage)
  in
  (* 304-307 *)
  let& extra_args := extra_args0 ++ extra_args1 in
  let! tmp1 := Exn_continuation.exn_handler exn_cont in
  Exn_continuation.create tmp1 extra_args.
