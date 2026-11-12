(* A conditional in the body of a [for] loop. *)

external ( + ) : int -> int -> int = "%addint"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 6 in
  let s = ref 0 in
  for i = 0 to n do
    if i > 2 then s := !s + i
  done;
  !s
