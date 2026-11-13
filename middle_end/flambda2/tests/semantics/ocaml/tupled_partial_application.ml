(* A function whose first parameter is a pair and whose second is a number,
   given the pair alone and the number later; and one whose pair comes
   second. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] pair_first (a, b) c = (a * 100) + (b * 10) + c

let[@inline never] pair_second c (a, b) = (a * 100) + (b * 10) + c

let with_pair = pair_first (opaque (1, 2))

let pair_then_three = with_pair 3

let pair_then_four = with_pair 4

let with_number = pair_second 5

let number_then_pair = with_number (6, 7)

let number_then_unknown_pair = with_number (opaque (8, 9))

let both_at_once = pair_first (1, 2) 3 + pair_second 3 (1, 2)
