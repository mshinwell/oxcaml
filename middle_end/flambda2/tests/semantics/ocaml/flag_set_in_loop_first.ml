(* As flag_set_in_loop, with the flag made before the other reference: the
   parameter that Simplify untags is the first of the two that the loop has, and
   the naked one comes after the one that stays. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] last_below (n : int) (limit : int) : int =
  let seen = ref false in
  let last = ref (-1) in
  for i = 0 to n do
    if i < limit
    then (
      last := i;
      seen := true)
  done;
  if !seen then !last else n

let result = last_below (opaque 5) 3
