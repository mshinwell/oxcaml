(* A match from four constant constructors to four constant pairs. The arms give
   their continuation a pair, which it takes apart. Simplify gives the
   continuation the two parts instead and merges the arms: the first part, which
   follows no rule, is loaded from a static array at the scrutinee, and the
   second, which is the number of the arm plus 1, is computed from the
   scrutinee. The validation does the same to the term before, merging the arms
   with a way for each argument
   (FlambdaMergeTablesSpec.merge_switch_by_table_ways), and the unit is
   validated. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

type suit =
  | Clubs
  | Diamonds
  | Hearts
  | Spades

let[@inline never] colour_and_rank suit =
  match suit with
  | Clubs -> 0, 1
  | Diamonds -> 1, 2
  | Hearts -> 1, 3
  | Spades -> 0, 4

let result =
  let colour, rank = colour_and_rank (opaque Hearts) in
  (colour * 10) + rank
