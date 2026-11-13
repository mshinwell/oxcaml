(* A flag kept in a reference, set in a loop and tested after it. The flag is a
   parameter of the loop, of the continuation after the test in its body and of
   the continuation after the loop; Simplify makes it a naked immediate in all
   three, and the test after the loop reads it as it is. The function is
   exported, so that it stays a function. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] last_below (n : int) (limit : int) : int =
  let last = ref (-1) in
  let seen = ref false in
  for i = 0 to n do
    if i < limit
    then (
      last := i;
      seen := true)
  done;
  if !seen then !last else n

let result = last_below (opaque 5) 3
