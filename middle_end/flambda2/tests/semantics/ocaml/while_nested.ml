(* A [while] loop in a [while] loop. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 3 in
  let total = ref 0 in
  let i = ref 0 in
  while !i < n do
    let j = ref 0 in
    while !j < n do
      total := !total + 1;
      j := !j + 1
    done;
    i := !i + 1
  done;
  !total
