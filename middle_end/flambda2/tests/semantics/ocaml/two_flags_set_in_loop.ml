(* Two flags kept in references, one set in each branch of the test in a loop,
   both tested after it. Simplify makes both naked immediates, in the loop, in
   the continuation after the test in its body and in the continuation after the
   loop; the two naked parameters come after the one that stays, the second flag
   before the first. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] two_flags (n : int) (limit : int) : int =
  let low = ref false in
  let high = ref false in
  let last = ref (-1) in
  for i = 0 to n do
    if i < limit
    then (
      last := i;
      low := true)
    else high := true
  done;
  if !low then if !high then !last else n else 0

let result = two_flags (opaque 5) 3
