(* A match on an integer whose arms are pairs of constants: the continuation of
   the arms takes the two parts of a pair. Simplify merges the four arms of the
   constants: each part follows no rule, and is loaded from a static array of
   its own at the scrutinee. The validation merges the arms of the term before
   in the same way, with a way for each argument
   (FlambdaMergeTablesSpec.merge_switch_by_table_ways), and the unit is
   validated. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

let[@inline never] describe code =
  let low, high =
    match code with
    | 0 -> 1, 10
    | 1 -> 5, 50
    | 2 -> 7, 70
    | 3 -> 2, 20
    | _ -> 0, 0
  in
  high - low

let result = describe (opaque 2) + describe (opaque 5)
