(* A while loop that goes on while a flag is clear and two more tests hold.
   After Simplify the test of the flag gives the continuation where its arms
   meet the number of its arm, and so do the arms of the second test, which are
   in a handler that the first test applies. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external not : bool -> bool = "%boolnot"

external ( && ) : bool -> bool -> bool = "%sequand"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] first_square_above (n : int) (m : int) : int =
  let found = ref false in
  let i = ref 0 in
  while (not !found) && !i < n && !i < m do
    i := !i + 1;
    if !i * !i > 20 then found := true
  done;
  !i

let result = first_square_above (opaque 9) 7
