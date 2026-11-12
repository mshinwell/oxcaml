(* A variant that is a block on both paths of a test, with a tag for each path,
   matched where the paths meet by arms that give the same thing for the two
   tags. Simplify unboxes the variant there. The parameter that says whether the
   value is an immediate is given the same constant on both paths, so Simplify
   removes it and binds it at the head of the handler, and the [Switch] on it
   stays under that [Let]. The handler has no parameter left; it is applied by
   an arm of the test and by the handler of the path that computes something.
   The continuation that it goes on to is applied by the first branch of [f]
   too, with another value, so it stays and keeps its parameter. *)

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type t =
  | A
  | B of int
  | C of int * int

let f : int -> int -> int =
 fun p q ->
  if q > 0
  then q
  else
    match if 0 > p then B (opaque 6) else C (p, q) with
    | A -> 0
    | B _ -> p
    | C (_, _) -> p

let result = f (opaque 1) (opaque 4)
