(* A [for] loop that sums into a reference, which the front end makes a variable
   of a recursive continuation. Simplify removes the tagging and untagging of
   the test and a continuation applied once, inside the handler of the recursive
   continuation, where the validator rewrites nothing. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let total = ref 0 in
  for i = 1 to opaque 10 do
    total := !total + i
  done;
  !total
