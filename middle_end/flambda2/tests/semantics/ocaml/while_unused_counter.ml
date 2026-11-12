(* A [while] loop with a counter that is incremented and never read: Simplify
   removes it. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 5 in
  let i = ref 0 in
  let steps = ref 0 in
  while !i < n do
    i := !i + 1;
    steps := !steps + 2
  done;
  !i
