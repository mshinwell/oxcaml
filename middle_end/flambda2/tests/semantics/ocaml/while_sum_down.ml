(* A [while] loop that counts down and adds up. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 10 in
  let s = ref 0 in
  let i = ref n in
  while !i > 0 do
    s := !s + !i;
    i := !i - 1
  done;
  !s
