(* [closure_uses_unit_function_only.ml] with an import: the unit exports a
   predefined exception too. A function returns a closure, which calls another
   function of the unit and captures nothing else. Neither function is inlined.
   The unit is validated at the second asking, once unused static bindings are
   removed from the head of the term after too, and no import is bound at that
   head. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] double x = x * 2

let[@inline never] doubler () = fun x -> double (x + 1)

let result =
  let f = doubler () in
  let g = doubler () in
  f (opaque 2) + g 4

let not_found = Not_found
