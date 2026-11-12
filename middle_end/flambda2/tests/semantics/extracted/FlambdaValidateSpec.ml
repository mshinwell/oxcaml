open Datatypes
open FlambdaAliasesSpec
open FlambdaBlockLoadSpec
open FlambdaCodeLetsSpec
open FlambdaCompareSpec
open FlambdaCseSpec
open FlambdaDeadParamsSpec
open FlambdaFloatCodeSpec
open FlambdaForwardSpec
open FlambdaHoistCodeSpec
open FlambdaIdentitiesSpec
open FlambdaInlineSiblingsSpec
open FlambdaInlineTailSpec
open FlambdaKnownClosuresSpec
open FlambdaKnownSymbolsSpec
open FlambdaLiftFromCodeSpec
open FlambdaLiftSpec
open FlambdaLoopAliasesSpec
open FlambdaLoopLetsSpec
open FlambdaLoopifySpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaParamAliasesSpec
open FlambdaRecHandlersSpec
open FlambdaRenameApartSpec
open FlambdaShortcutSpec
open FlambdaSinkContsSpec
open FlambdaStaticsOrderSpec
open FlambdaUnboxSpec
open FlambdaUnusedContsSpec
open FlambdaUnusedParamsSpec
open FlambdaUnusedProjectionsSpec
open FlambdaUnusedSlotsSpec
open FlambdaUnusedStaticsSpec
open FlambdaWellFormedSpec
open List

(** val iterate : nat -> (expr -> expr) -> expr -> expr **)

let rec iterate rounds f e =
  match rounds with O -> e | S rounds0 -> iterate rounds0 f (f e)

(** val normalise_expr_before : expr -> expr **)

let normalise_expr_before e =
  let e0 =
    shortcut_switches
      (thread_switches
         (inline_tail_conts
            (sink_let_conts
               (remove_unused_conts (collapse_switches (fold_constants e))))))
  in
  let e1 =
    apply_identities
      (follow_aliases_in_loops []
         (follow_aliases []
            (share_known_primitives
               (unbox_known_numbers (load_known_blocks e0)))))
  in
  drop_unused_params
    (remove_unused_defined_lets [] (remove_unused_lets (fold_constants e1)))

(** val normalise_code_before : expr -> expr **)

let normalise_code_before body =
  rewrite_rec_handlers normalise_expr_before (normalise_expr_before body)

(** val normalise_before_inlined : expr -> expr **)

let normalise_before_inlined e =
  rewrite_code normalise_code_before
    (merge_statics (drop_deleted_code (normalise_code_before e)))

(** val normalise_before_round_avoiding : continuation list -> code_id list ->
    expr -> expr **)

let normalise_before_round_avoiding avoid kept e =
  normalise_before_inlined
    (rename_apart_avoiding avoid
       (inline_sibling_calls kept (inline_calls kept [] e)))

(** val normalise_before_round : code_id list -> expr -> expr **)

let normalise_before_round kept e = normalise_before_round_avoiding [] kept e

(** val normalise_expr_params : expr -> expr **)

let normalise_expr_params e =
  let e0 =
    shortcut_switches
      (thread_switches
         (inline_tail_conts
            (sink_let_conts
               (remove_unused_conts (collapse_switches (fold_constants e))))))
  in
  let e1 = remove_unused_conts (forward_applications e0) in
  let e2 =
    follow_aliases_in_loops []
      (follow_aliases [] (unbox_known_numbers (load_known_blocks e1)))
  in
  drop_dead_params
    (bind_aliased_params
       (remove_unused_defined_lets [] (remove_unused_lets (fold_constants e2))))

(** val normalise_code_params : expr -> expr **)

let normalise_code_params body =
  normalise_expr_params (rewrite_rec_handlers normalise_expr_params body)

(** val normalise_params_round : expr -> expr **)

let normalise_params_round e =
  rewrite_code normalise_code_params (normalise_code_params e)

(** val normalise_before : nat -> code_id list -> expr -> expr **)

let normalise_before rounds kept e =
  iterate rounds
    (normalise_before_round kept)
    (iterate rounds normalise_params_round e)

(** val inline_once_applied_after : expr -> expr **)

let inline_once_applied_after e =
  inline_tail_conts_kinded (sink_let_conts (remove_unused_conts e))

(** val normalise_expr_after : expr -> expr **)

let normalise_expr_after e =
  remove_unused_defined_lets_in_loops []
    (remove_unused_projections
       (fold_constants
          (follow_aliases_in_loops []
             (follow_aliases [] (inline_once_applied_after e)))))

(** val normalise_code_after : expr -> expr **)

let normalise_code_after body =
  rewrite_rec_handlers normalise_expr_after (normalise_expr_after body)

(** val normalise_after_round : code_id list -> expr -> expr **)

let normalise_after_round kept e =
  remove_unused_defined_lets_in_code
    (rewrite_code normalise_code_after
       (merge_statics
          (drop_deleted_code
             (rewrite_rec_handlers normalise_expr_after
                (remove_unused_defined_lets_in_loops []
                   (remove_unused_projections
                      (fold_constants
                         (inline_known_calls kept [] []
                            (follow_aliases_in_loops []
                               (follow_aliases [] (inline_once_applied_after e)))))))))))

(** val normalise_after : nat -> code_id list -> expr -> expr **)

let normalise_after rounds kept e =
  iterate rounds (normalise_after_round kept) e

(** val without_statics : dropped -> expr -> expr **)

let without_statics d e =
  match drop_statics d e with
  | Some e' -> merge_statics (drop_deleted_code e')
  | None -> e

(** val with_lifting : lifting -> expr -> expr **)

let with_lifting l e =
  let e0 =
    match lift_from_code_unit l.lifting_unit l.lifted_out_of_code e with
    | Some e' -> e'
    | None -> e
  in
  match lift_unit l e0 with Some e' -> e' | None -> e0

(** val with_known : expr -> expr **)

let with_known e = match fold_known_unit e with Some e' -> e' | None -> e

(** val normalise_lifted_round : continuation list -> code_id list -> expr ->
    expr **)

let normalise_lifted_round avoid kept e =
  with_known (use_known_closures (normalise_before_round_avoiding avoid kept e))

(** val normalise_lifted : nat -> continuation list -> code_id list -> expr ->
    expr **)

let normalise_lifted rounds avoid kept e =
  iterate rounds
    (normalise_lifted_round avoid kept)
    (iterate rounds normalise_params_round e)

(** val unit_continuations : lifting list -> continuation list **)

let unit_continuations ls =
  flat_map (fun l -> [l.lifting_unit.unit_return; l.lifting_unit.unit_exn]) ls

(** val lifted_in_turn : nat -> continuation list -> lifting list -> code_id
    list -> expr -> expr **)

let rec lifted_in_turn rounds avoid ls kept e =
  match ls with
  | [] -> e
  | l :: ls0 ->
    lifted_in_turn rounds avoid ls0 kept
      (normalise_lifted rounds avoid kept (with_lifting l e))

(** val without_slots : value_slot list -> expr -> expr **)

let without_slots slots e =
  match drop_unused_slots slots e with Some e' -> e' | None -> e

(** val with_code_first : expr -> expr **)

let with_code_first e =
  match hoist_code e with
  | Some e' -> merge_statics (drop_deleted_code e')
  | None -> e

type validation =
  | Same_up_to_bound_names
  | Same_once_normalised
  | Same_once_unused_statics_removed
  | Same_once_lifted
  | Not_validated

(** val validate_unit : nat -> dropped -> value_slot list -> loopified ->
    lifting list -> code_id list -> expr -> expr -> validation **)

let validate_unit rounds unused slots g ls kept before after =
  if expr_eqb [] [] before after
  then Same_up_to_bound_names
  else
    let before0 = loopify_unit g before in
    let normalised = normalise_before rounds kept before0 in
    let after0 = normalise_after rounds kept after in
    if expr_eqb [] [] (order_statics_as after0 normalised) after0
    then Same_once_normalised
    else if
      expr_eqb [] []
        (order_statics_as after0 (without_statics unused normalised))
        after0
    then Same_once_unused_statics_removed
    else if
      expr_eqb [] []
        (order_statics_as
           (float_code (with_code_first after0))
           (float_code
              (without_statics unused
                 (without_slots slots
                    (lifted_in_turn rounds (unit_continuations ls) ls kept
                       before0)))))
        (float_code (with_code_first after0))
    then Same_once_lifted
    else Not_validated
