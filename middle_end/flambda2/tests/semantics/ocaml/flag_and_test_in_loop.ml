(* A flag kept in a reference that a loop sets to itself and a test, and that
   the function returns. After Simplify the continuation where the arms of the
   conjunction meet has the flag twice: as a value, which goes round the loop
   and is returned, and as a number, which the next turn tests. *)

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( && ) : bool -> bool -> bool = "%sequand"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] every_double_below (n : int) (limit : int) : bool =
  let all = ref true in
  for i = 0 to n do
    all := !all && i * 2 < limit
  done;
  !all

let result = every_double_below (opaque 5) 30
