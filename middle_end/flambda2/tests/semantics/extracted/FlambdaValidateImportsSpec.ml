open Datatypes
open FlambdaModel
open FlambdaUnusedHeadStaticsSpec
open FlambdaValidateSpec
open FlambdaValueSpec

(** val holds_from : static_env -> nat -> code_id list -> expr -> validation ->
    bool **)

let holds_from statics rounds kept after = function
  | Same_once_head_statics_removed ->
    head_free_in statics
      (tidied_after rounds (normalise_after rounds kept after))
  | Same_once_lifted -> false
  | Not_validated -> false
  | _ -> true
