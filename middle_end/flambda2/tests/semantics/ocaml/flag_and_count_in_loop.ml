(* A flag and a count kept in references, both changed under a test in a loop;
   the flag is tested after the loop and the count is the result. Simplify makes
   the flag a naked immediate; the count is read as a number in the loop and
   stays tagged. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] count_if_any (n : int) (limit : int) : int =
  let found = ref false in
  let count = ref 0 in
  for i = 0 to n do
    if i < limit
    then (
      found := true;
      count := !count + 1)
  done;
  if !found then !count else -1

let result = count_if_any (opaque 5) 3
