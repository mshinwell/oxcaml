open Datatypes
open FlambdaEnvAliasesFollowSpec
open FlambdaLiftSpec
open FlambdaLoopifySpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedStaticsSpec
open FlambdaValidateSpec
open ListDef

(** val follow_aliases_knowing : expr -> expr **)

let follow_aliases_knowing e =
  rewrite_code (follow_aliases Known.empty) (follow_aliases Known.empty e)

(** val knowing_round : (expr -> expr) -> expr -> expr **)

let knowing_round round e = round (follow_aliases_knowing e)

(** val normalise_knowing : (expr -> expr) -> nat -> expr -> expr **)

let normalise_knowing round rounds e = iterate rounds (knowing_round round) e

(** val validate_unit_knowing : nat -> dropped -> value_slot list -> loopified
    -> lifting list -> code_id list -> expr -> expr -> validation **)

let validate_unit_knowing rounds unused slots g ls kept before after =
  validate_unit rounds unused slots g ls kept
    (normalise_knowing
       (normalise_before_round_avoiding
          (app (unit_continuations ls) (map snd g))
          kept)
       rounds before)
    (normalise_knowing (normalise_after_round kept) rounds after)
