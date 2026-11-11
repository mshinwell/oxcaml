open Datatypes
open FlambdaAliasesSpec
open FlambdaBlockLoadSpec
open FlambdaCompareSpec
open FlambdaFloatCodeSpec
open FlambdaKnownClosuresSpec
open FlambdaKnownSymbolsSpec
open FlambdaLiftSpec
open FlambdaLoopAliasesSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaRecHandlersSpec
open FlambdaShortcutSpec
open FlambdaSinkContsSpec
open FlambdaUnboxSpec
open FlambdaUnusedContsSpec
open FlambdaUnusedParamsSpec
open FlambdaUnusedSlotsSpec
open FlambdaUnusedStaticsSpec

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
    follow_aliases_in_loops []
      (follow_aliases [] (unbox_known_numbers (load_known_blocks e0)))
  in
  drop_unused_params
    (remove_unused_defined_lets [] (remove_unused_lets (fold_constants e1)))

(** val normalise_code_before : expr -> expr **)

let normalise_code_before body =
  rewrite_rec_handlers normalise_expr_before (normalise_expr_before body)

(** val normalise_before_round : expr -> expr **)

let normalise_before_round e =
  rewrite_code normalise_code_before
    (merge_statics
       (drop_deleted_code (normalise_code_before (inline_calls [] e))))

(** val normalise_before : nat -> expr -> expr **)

let normalise_before rounds e = iterate rounds normalise_before_round e

(** val normalise_expr_after : expr -> expr **)

let normalise_expr_after e =
  remove_unused_defined_lets []
    (fold_constants (follow_aliases_in_loops [] (follow_aliases [] e)))

(** val normalise_code_after : expr -> expr **)

let normalise_code_after body =
  rewrite_rec_handlers normalise_expr_after (normalise_expr_after body)

(** val normalise_after_round : expr -> expr **)

let normalise_after_round e =
  rewrite_code normalise_code_after
    (merge_statics
       (drop_deleted_code
          (rewrite_rec_handlers normalise_expr_after
             (remove_unused_defined_lets []
                (fold_constants
                   (inline_known_calls [] []
                      (follow_aliases_in_loops [] (follow_aliases [] e))))))))

(** val normalise_after : nat -> expr -> expr **)

let normalise_after rounds e = iterate rounds normalise_after_round e

(** val without_statics : dropped -> expr -> expr **)

let without_statics d e =
  match drop_statics d e with
  | Some e' -> merge_statics (drop_deleted_code e')
  | None -> e

(** val with_lifting : lifting -> expr -> expr **)

let with_lifting l e = match lift_unit l e with Some e' -> e' | None -> e

(** val with_known : expr -> expr **)

let with_known e = match fold_known_unit e with Some e' -> e' | None -> e

(** val normalise_lifted_round : expr -> expr **)

let normalise_lifted_round e =
  with_known (use_known_closures (normalise_before_round e))

(** val normalise_lifted : nat -> expr -> expr **)

let normalise_lifted rounds e = iterate rounds normalise_lifted_round e

(** val lifted_in_turn : nat -> lifting list -> expr -> expr **)

let rec lifted_in_turn rounds ls e =
  match ls with
  | [] -> e
  | l :: ls0 ->
    lifted_in_turn rounds ls0 (normalise_lifted rounds (with_lifting l e))

(** val without_slots : value_slot list -> expr -> expr **)

let without_slots slots e =
  match drop_unused_slots slots e with Some e' -> e' | None -> e

type validation =
  | Same_up_to_bound_names
  | Same_once_normalised
  | Same_once_unused_statics_removed
  | Same_once_lifted
  | Not_validated

(** val validate_unit : nat -> dropped -> value_slot list -> lifting list ->
    expr -> expr -> validation **)

let validate_unit rounds unused slots ls before after =
  if expr_eqb [] [] before after
  then Same_up_to_bound_names
  else
    let normalised = normalise_before rounds before in
    let after0 = normalise_after rounds after in
    if expr_eqb [] [] normalised after0
    then Same_once_normalised
    else if expr_eqb [] [] (without_statics unused normalised) after0
    then Same_once_unused_statics_removed
    else if
      expr_eqb [] []
        (float_code
           (without_statics unused
              (without_slots slots (lifted_in_turn rounds ls before))))
        (float_code after0)
    then Same_once_lifted
    else Not_validated
