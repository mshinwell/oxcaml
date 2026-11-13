(* A loop whose accumulator is a boxed 64-bit integer kept in a reference and
   set on some turns only: the loop and the join after the test in its body each
   pass the box to the other. *)

external ( land ) : int -> int -> int = "%andint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

external add64 : int64 -> int64 -> int64 = "%int64_add"

external of_int64 : int -> int64 = "%int64_of_int"

external to_int64 : int64 -> int = "%int64_to_int"

let[@inline never] sum_even n =
  let acc = ref 0L in
  for i = 1 to n do
    if i land 1 = 0 then acc := add64 !acc (of_int64 i)
  done;
  to_int64 !acc

let result = sum_even (opaque 10)
