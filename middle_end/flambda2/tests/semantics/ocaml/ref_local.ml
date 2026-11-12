(* A function with a [while] loop over two references that do not escape: the
   front end makes them variables, so no block is read or written. Simplify
   makes the closure of [sum_while] a symbol, and rewrites inside the loop as in
   [for_sum.ml]. *)

external ( + ) : int -> int -> int = "%addint"

external ( <= ) : int -> int -> bool = "%lessequal"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let sum_while n =
  let acc = ref 0 in
  let i = ref 1 in
  while !i <= n do
    acc := !acc + !i;
    i := !i + 1
  done;
  !acc

let result = sum_while 10
