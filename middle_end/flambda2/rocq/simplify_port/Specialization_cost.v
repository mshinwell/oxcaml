(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/specialization_cost.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the recursive function)
   is that of GUIDE.md; the Rocq declaration of the type [t], which has an
   inline record, is in the form of decl/Specialization_cost.v. The
   compiler's file does not open [Simplify_import], and neither does this
   one. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_var Code_size
  Continuation Cost_metrics Flambda Flambda2_types Flambda_features
  Flambda_primitive Format List Non_recursive_handler One_recursive_handler
  Or_unknown Original_handlers Removed_operations Set_of_closures Simple
  Switch_expr.
(* CONSTRUCTORS-WITHOUT-MODULE:
   Flambda2_types.Join_analysis.simple_refined_at_join_ Or_unknown.t
   Original_handlers.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16-20 *)
Inductive reason : Type :=
| Specialization_disabled
| At_toplevel
| Contains_static_consts
| Contains_set_of_closures.

(* 22-25 *)
Record cost : Type :=
  { primitives : list (Bound_var.t * Flambda_primitive.t);
    non_lifted_continuations : list Original_handlers.t
  }.

(* 27-29 *)
(* PORT-GAP(type): [t] has an inline record. As in
   decl/Specialization_cost.v, the Rocq variant, here [t_], takes the field
   of [Cannot_specialize] by place; [t] is its name in the rest of the
   file. *)
(* PORT-GAP(verbatim): the OCaml definition of [t] is the text of the
   directive of [t]: Rocq prints it where the type is defined. *)
Inductive t_ : Type :=
| Can_specialize : cost -> t_
| Cannot_specialize : reason -> t_.
Extract Inductive t_ => "t" [ "Can_specialize" "(fun x__1 -> (Cannot_specialize { reason = x__1 } : t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : t) with Can_specialize x__1 -> f__1 x__1 | Cannot_specialize { reason = x__1 } -> f__2 x__1)".
Definition t : Type := t_.
Extract Constant t =>
  "
  | Can_specialize of cost
  | Cannot_specialize of { reason : reason }".

(* 31-40 *)
Definition print_reason (ppf : Format.formatter) (reason : reason) : M unit :=
  match reason with
  | Specialization_disabled => Format.fprintf0 ppf "specialization_disabled"
  | At_toplevel => Format.fprintf0 ppf "at_top_level"
  | Contains_static_consts => Format.fprintf0 ppf "contains_static_consts"
  | Contains_set_of_closures =>
    Format.fprintf0 ppf "contains_set_of_closures"
  end.

(* 42-44 *)
Definition print_prim (ppf : Format.formatter)
    '((bound_var, prim) : Bound_var.t * Flambda_primitive.t) : M unit :=
  Format.fprintf4 ppf "@[<hov 1>(%a %a)@]" Bound_var.print bound_var
    Flambda_primitive.print prim.

(* 46-59 *)
Definition print (ppf : Format.formatter) (t : Specialization_cost.t)
    : M unit :=
  match t with
  | Can_specialize
      {| primitives := primitives;
         non_lifted_continuations := non_lifted_continuations
      |} =>
    let! tmp1 := papp2 Format.pp_print_list None Original_handlers.print in
    let! tmp2 := papp2 Format.pp_print_list None print_prim in
    Format.fprintf4 ppf
      "@[<hv>(can_specialize@ @[<hv 1>(primitives@ %a)@]@ @[<hv 1>(non_lifted_continuations@ %a)@])@]"
      tmp2 primitives tmp1 non_lifted_continuations
  | Cannot_specialize reason =>
    Format.fprintf2 ppf "@[<hv>(cannot_specialize@ @[<hv 1>(reason@ %a)@])@]"
      print_reason reason
  end.

(* Creations *)

(* 63 *)
Definition cannot_specialize (reason : reason) : M t :=
  ret (Cannot_specialize reason).

(* 65-68 *)
Definition can_specialize (_ : unit) : M t :=
  let! tmp1 := Flambda_features.match_in_match tt in
  if tmp1
  then
    ret (Can_specialize {| primitives := []; non_lifted_continuations := [] |})
  else cannot_specialize Specialization_disabled.

(* Updating costs *)

(* 72-74. In the compiler: [let update_cost ~f = function ..]; the second
   case is [Cannot_specialize _ as res -> res]. *)
Definition update_cost (f : cost -> M cost) (res : t) : M t :=
  match res with
  | Can_specialize cost =>
    let! tmp1 := f cost in
    ret (Can_specialize tmp1)
  | Cannot_specialize _ => ret res
  end.

(* 76-77 *)
Definition add_set_of_closures (_soc : Set_of_closures.t)
    (_t : Specialization_cost.t) : M t :=
  ret (Cannot_specialize Contains_set_of_closures).

(* 79-80 *)
Definition add_lifted_set_of_closures (_soc : Set_of_closures.t)
    (_t : Specialization_cost.t) : M t :=
  ret (Cannot_specialize Contains_set_of_closures).

(* 82-88. [update_cost t ~f]: the arguments are in the order of the
   definition. *)
Definition add_prim (bound_var : Bound_var.t) (prim : Flambda_primitive.t)
    (t : Specialization_cost.t) : M Specialization_cost.t :=
  update_cost
    (fun '({| primitives := primitives; non_lifted_continuations := _ |}
           as cost) =>
      (* CR gbury: we might want to limit the number of primitives we store,
         so that e.g. if there are more than <n> primitives, we stop storing
         them and decide that no specialization should take place *)
      let& primitives := (bound_var, prim) :: primitives in
      ret
        {| primitives := primitives;
           non_lifted_continuations := cost.(non_lifted_continuations)
        |})
    t.

(* 90-97 *)
Definition add_continuations (can_be_lifted : bool)
    (handlers : Original_handlers.t) (t : Specialization_cost.t)
    : M Specialization_cost.t :=
  if can_be_lifted
  then ret t
  else
    update_cost
      (fun '({| primitives := _;
                non_lifted_continuations := non_lifted_continuations
             |}
             as cost) =>
        let& non_lifted_continuations :=
          handlers :: non_lifted_continuations
        in
        ret
          {| primitives := cost.(primitives);
             non_lifted_continuations := non_lifted_continuations
          |})
      t.

(* Computing cost and benefits *)

(* 101. In the compiler: [repeat n acc ~f]. *)
Fixpoint repeat {A : Type} (fuel : fuel) (n : int) (acc : A) (f : A -> M A)
    {struct fuel} : M A :=
  recursive! fuel in
  if n <=? 0
  then ret acc
  else
    let! tmp1 := f acc in
    repeat fuel (n - 1) tmp1 f.

(* 103-193 *)
Definition cost_metrics (typing_env : Flambda2_types.Typing_env.t)
    (switch : Switch_expr.t)
    (join_analysis : Flambda2_types.Join_analysis.t Apply_cont_rewrite_id.t)
    (specialized generic : Apply_cont_rewrite_id.Set_.t) (cost : cost)
    : M Cost_metrics.t :=
  let* machine_width := Flambda2_types.Typing_env.machine_width typing_env in
  (* If there is exactly 1 "generic" call site, then that call site is the
     same as a specialized one. *)
  let* n_specialized := Apply_cont_rewrite_id.Set_.cardinal specialized in
  let* n_generic := Apply_cont_rewrite_id.Set_.cardinal generic in
  let& n_total := n_specialized + (if n_generic =? 0 then 0 else 1) in
  (* 111-131. Cost metrics for a generic call site *)
  let* metrics :=
    if n_generic =? 0
    then
      let* code_size :=
        let! tmp2 := Code_size.switch switch in
        List.fold_left
          (fun (acc : Code_size.t)
               '((_, primitive) : Bound_var.t * Flambda_primitive.t) =>
            let! tmp1 := Code_size.prim machine_width primitive in
            Code_size.op_plus acc tmp1)
          tmp2 cost.(primitives)
      in
      let! tmp1 := Code_size.op_minus Code_size.zero code_size in
      Cost_metrics.from_size tmp1
    else
      (* The regular case, where the generic continuation handler stays, and
         the code size is not changed (at least for the generic case *)
      ret Cost_metrics.zero
  in
  (* 133-137. Cost metrics for specialized call sites *)
  let* metrics :=
    (* Each specialized handler eliminates the switch *)
    let_fuel! fuel in
    let! tmp1 := papp1 Cost_metrics.notify_removed Removed_operations.branch in
    repeat fuel n_specialized metrics tmp1
  in
  (* 140-176. For each primitive, and each specialized call site: 1) notify
     it removed if its value is known, 2) else add the prim to the code
     size *)
  let* metrics :=
    List.fold_left
      (fun (metrics : Cost_metrics.t)
           '((bound_var, prim) : Bound_var.t * Flambda_primitive.t) =>
        let* simple :=
          let! tmp1 := Bound_var.var bound_var in
          Simple.var tmp1
        in
        (* 144-162 *)
        let* '(disappears, stays) :=
          let! tmp1 :=
            Flambda2_types.Join_analysis.simple_refined_at_join join_analysis
              typing_env simple
          in
          match tmp1 with
          | Flambda2_types.Join_analysis.Not_refined_at_join =>
            ret (0, n_total)
          | Flambda2_types.Join_analysis.Invariant_in_all_uses _ =>
            (* if the canonical is a simple already, then specialization does
               not change much *)
            ret (0, 0)
          | Flambda2_types.Join_analysis.Variable_refined_at_these_uses
              var_analysis =>
            Flambda2_types.Join_analysis.Variable_refined_at_join.fold_values_at_uses
              (fun id value '(disappears, stays) =>
                let! tmp1 := Apply_cont_rewrite_id.Set_.mem id specialized in
                if tmp1
                then
                  match value with
                  | Or_unknown.Known _ => ret (disappears + 1, stays)
                  | Or_unknown.Unknown => ret (disappears, stays + 1)
                  end
                else ret (disappears, stays + 1))
              var_analysis (0, 0)
          end
        in
        (* 163-168 *)
        let* metrics :=
          let_fuel! fuel in
          let! tmp1 := Removed_operations.prim prim in
          let! tmp2 := papp1 Cost_metrics.notify_removed tmp1 in
          repeat fuel disappears metrics tmp2
        in
        (* 169-174 *)
        let* metrics :=
          let_fuel! fuel in
          let! tmp1 := Code_size.prim machine_width prim in
          let! tmp2 := papp1 Cost_metrics.notify_added tmp1 in
          repeat fuel stays metrics tmp2
        in
        ret metrics)
      metrics cost.(primitives)
  in
  (* 178-185 *)
  (* Count the non lifted continuations. We currently cannot easily access the
     size of handlers, since we have not yet done a downwards traversal on them,
     so instead we just use an arbitrary size.

     CR gbury: find a way to get an estimate of the code size of
     handlers/exprs *)
  let& handler_metrics :=
    fun (_handler : Flambda.Expr.t) =>
    let! tmp1 := Code_size.of_int i5 in
    Cost_metrics.from_size tmp1
  in
  (* 186-200 *)
  let* metrics :=
    List.fold_left
      (fun (metrics : Cost_metrics.t) (handlers : Original_handlers.t) =>
        match handlers with
        | Original_handlers.Non_recursive
            {| Non_recursive_handler.handler := handler |} =>
          let! tmp1 := handler_metrics handler in
          Cost_metrics.op_plus metrics tmp1
        | Original_handlers.Recursive _ _ continuation_handlers _ =>
          Continuation.Lmap.fold
            (fun _cont one_rec_handler metrics =>
              let& handler :=
                one_rec_handler.(One_recursive_handler.handler)
              in
              let! tmp1 := handler_metrics handler in
              Cost_metrics.op_plus metrics tmp1)
            continuation_handlers metrics
        end)
      metrics cost.(non_lifted_continuations)
  in
  (* Return *)
  ret metrics.
