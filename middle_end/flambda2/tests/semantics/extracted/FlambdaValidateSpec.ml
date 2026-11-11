open Datatypes
open FlambdaAliasesSpec
open FlambdaCompareSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedStaticsSpec

(** val iterate : nat -> (expr -> expr) -> expr -> expr **)

let rec iterate rounds f e =
  match rounds with O -> e | S rounds0 -> iterate rounds0 f (f e)

(** val normalise_code_before : expr -> expr **)

let normalise_code_before body =
  remove_unused_defined_lets []
    (remove_unused_lets
       (fold_constants
          (follow_aliases []
             (thread_switches
                (inline_tail_conts (collapse_switches (fold_constants body)))))))

(** val normalise_before_round : expr -> expr **)

let normalise_before_round e =
  rewrite_code normalise_code_before
    (merge_statics
       (drop_deleted_code
          (remove_unused_defined_lets []
             (remove_unused_lets
                (fold_constants
                   (follow_aliases []
                      (thread_switches
                         (inline_tail_conts
                            (collapse_switches
                               (fold_constants (inline_calls [] e)))))))))))

(** val normalise_before : nat -> expr -> expr **)

let normalise_before rounds e = iterate rounds normalise_before_round e

(** val normalise_code_after : expr -> expr **)

let normalise_code_after body =
  remove_unused_defined_lets [] (fold_constants (follow_aliases [] body))

(** val normalise_after_round : expr -> expr **)

let normalise_after_round e =
  rewrite_code normalise_code_after
    (merge_statics
       (drop_deleted_code
          (remove_unused_defined_lets []
             (fold_constants (inline_known_calls [] [] (follow_aliases [] e))))))

(** val normalise_after : nat -> expr -> expr **)

let normalise_after rounds e = iterate rounds normalise_after_round e

(** val without_statics : dropped -> expr -> expr **)

let without_statics d e =
  match drop_statics d e with
  | Some e' -> merge_statics (drop_deleted_code e')
  | None -> e

type validation =
  | Same_up_to_bound_names
  | Same_once_normalised
  | Same_once_unused_statics_removed
  | Not_validated

(** val validate_unit : nat -> dropped -> expr -> expr -> validation **)

let validate_unit rounds unused before after =
  if expr_eqb [] [] before after
  then Same_up_to_bound_names
  else
    let before0 = normalise_before rounds before in
    let after0 = normalise_after rounds after in
    if expr_eqb [] [] before0 after0
    then Same_once_normalised
    else if expr_eqb [] [] (without_statics unused before0) after0
    then Same_once_unused_statics_removed
    else Not_validated
