(* A reference that the loop reads and does not assign, read again after the
   loop. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 4 in
  let k = ref 3 in
  let i = ref 0 in
  let s = ref 0 in
  while !i < n do
    s := !s + !k;
    i := !i + 1
  done;
  !s + !k
