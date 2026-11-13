(* A flag kept in a reference that a while loop tests, and sets to a comparison:
   the loop goes on while the count is below the bound. The loop is given the
   tagging of the comparison where the source sets the flag; Simplify gives it
   the comparison itself. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] count_up_to (n : int) : int =
  let go = ref true in
  let i = ref 0 in
  while !go do
    i := !i + 1;
    go := !i < n
  done;
  !i

let result = count_up_to (opaque 7)
