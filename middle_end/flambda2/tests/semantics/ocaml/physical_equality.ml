(* [==] and [!=] on constant constructors. *)

external ( == ) : 'a -> 'a -> bool = "%eq"

external ( != ) : 'a -> 'a -> bool = "%noteq"

external ( && ) : bool -> bool -> bool = "%sequand"

type colour =
  | Red
  | Green
  | Blue

let[@inline] same (x : colour) (y : colour) = x == y

let result = same Red Red && Green != Blue && same Blue Blue
