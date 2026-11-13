(* A flag kept in a reference that the body of a loop reads twice, each time to
   choose between two computations. After Simplify the second test is on a
   parameter that each arm of the first gives its number, from a continuation of
   its own. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] up_then_down (n : int) : int =
  let neg = ref false in
  let s = ref 0 in
  for i = 0 to n do
    let a = if !neg then !s - i else !s + (i * 2) in
    s := if !neg then a - 1 else a + 1;
    if a > 10 then neg := true
  done;
  !s

let result = up_then_down (opaque 9)
