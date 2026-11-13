(* A flag kept in a reference that the loop tests before it sets it: the first
   index that passes a test is kept, and the flag says that there is one. Where
   the loop passes the flag on as it was read, Simplify passes the constant that
   the test of the flag found it to be. *)

external ( * ) : int -> int -> int = "%mulint"

external ( > ) : int -> int -> bool = "%greaterthan"

external not : bool -> bool = "%boolnot"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] first_above (n : int) (limit : int) : int =
  let seen = ref false in
  let first = ref 0 in
  for i = 0 to n do
    if not !seen
    then
      if i * 3 > limit
      then (
        seen := true;
        first := i)
  done;
  if !seen then !first else -1

let result = first_above (opaque 9) 7
