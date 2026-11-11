(* A while loop over two references. The front end makes the references
   variables and the loop a recursive continuation. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let sum_below n =
  let total = ref 0 in
  let i = ref 0 in
  while !i < n do
    total := !total + !i;
    i := !i + 1
  done;
  !total

let result = sum_below (opaque 5)
