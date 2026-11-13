(* A flag kept in a reference that a loop sets to itself or a test, and that the
   function returns. After Simplify the continuation where the arms of the
   disjunction meet has the flag twice: as a value, which goes round the loop
   and is returned, and as a number, which the next turn tests. *)

external ( * ) : int -> int -> int = "%mulint"

external ( > ) : int -> int -> bool = "%greaterthan"

external ( || ) : bool -> bool -> bool = "%sequor"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] some_square_above (n : int) (limit : int) : bool =
  let any = ref false in
  for i = 0 to n do
    any := !any || i * i > limit
  done;
  !any

let result = some_square_above (opaque 5) 3
