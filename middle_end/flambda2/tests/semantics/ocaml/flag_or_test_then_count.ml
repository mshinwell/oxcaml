(* A flag kept in a reference that a loop sets to itself or a test and then
   tests, to count the turns since it was set. The continuation where the arms
   of the disjunction meet has the count and the flag for parameters, and after
   Simplify the flag twice, as a value and as a number; the count is not a
   tagged immediate that is untagged, and stays as it is. *)

external ( + ) : int -> int -> int = "%addint"

external ( > ) : int -> int -> bool = "%greaterthan"

external ( || ) : bool -> bool -> bool = "%sequor"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] turns_since_above (n : int) (limit : int) : int =
  let any = ref false in
  let c = ref 0 in
  for i = 0 to n do
    any := !any || i > limit;
    if !any then c := !c + 1
  done;
  !c

let result = turns_since_above (opaque 9) 3
