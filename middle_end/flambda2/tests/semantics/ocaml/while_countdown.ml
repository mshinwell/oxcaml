(* A [while] loop on one reference. As [for_sum.ml]. *)

external ( - ) : int -> int -> int = "%subint"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = ref (opaque 7) in
  while !n > 0 do
    n := !n - 2
  done;
  !n
