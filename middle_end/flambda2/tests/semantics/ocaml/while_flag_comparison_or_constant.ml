(* A flag kept in a reference that a while loop tests: one branch of the body
   clears it, the other sets it to a comparison. The loop is given a constant in
   the first and the tagging of the comparison in the second. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] step_to (n : int) : int =
  let go = ref true in
  let i = ref 0 in
  while !go do
    i := !i + 2;
    if !i > 100 then go := false else go := !i < n
  done;
  !i

let result = step_to (opaque 7)
