(* A reference that holds a pair, which every turn of a loop replaces by a new
   pair made of the fields of the one before. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] fib n =
  let p = ref (0, 1) in
  for _ = 1 to n do
    let a, b = !p in
    p := b, a + b
  done;
  fst !p

let result = fib (opaque 10)
