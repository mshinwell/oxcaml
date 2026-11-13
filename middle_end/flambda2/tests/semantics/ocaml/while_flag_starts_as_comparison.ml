(* A loop that counts down, written with a flag that says whether there is more
   to do: the flag starts as a comparison and is set to one at each turn. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] count_down (n : int) : int =
  let k = ref n in
  let steps = ref 0 in
  let more = ref (n > 0) in
  while !more do
    k := !k - 1;
    steps := !steps + 1;
    more := !k > 0
  done;
  !steps

let result = count_down (opaque 5)
