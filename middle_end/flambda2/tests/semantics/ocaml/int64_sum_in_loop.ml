(* A loop whose accumulator is a boxed 64-bit integer kept in a reference: the
   loop is entered with the box of a constant and each turn makes a new box. *)

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

external add64 : int64 -> int64 -> int64 = "%int64_add"

external of_int64 : int -> int64 = "%int64_of_int"

external to_int64 : int64 -> int = "%int64_to_int"

let[@inline never] sum n =
  let acc = ref 0L in
  for i = 1 to n do
    acc := add64 !acc (of_int64 i)
  done;
  to_int64 !acc

let result = sum (opaque 10)
