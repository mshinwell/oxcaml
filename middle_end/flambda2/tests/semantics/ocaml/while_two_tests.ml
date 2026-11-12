(* A [while] loop with two tests joined by [&&]. Where the tests meet, in the
   handler of the loop, Simplify untags the boolean: the first test gives the
   number 0 and the second gives its comparison, with nothing tagged. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( && ) : bool -> bool -> bool = "%sequand"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 10 in
  let i = ref 0 in
  let s = ref 0 in
  while !i < n && !s < 20 do
    s := !s + !i;
    i := !i + 1
  done;
  !s
