(* A conditional in the body of a [while] loop. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 6 in
  let evens = ref 0 in
  let i = ref 0 in
  while !i < n do
    if !i - (!i - 1) > 0 then evens := !evens + !i;
    i := !i + 1
  done;
  !evens
