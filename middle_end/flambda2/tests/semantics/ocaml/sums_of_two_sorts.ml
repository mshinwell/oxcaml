(* A loop with two accumulators, a boxed 64-bit integer and a boxed 32-bit
   integer, each set on some turns only. *)

external ( + ) : int -> int -> int = "%addint"

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

external add32 : int32 -> int32 -> int32 = "%int32_add"

external of_int32 : int -> int32 = "%int32_of_int"

external to_int32 : int32 -> int = "%int32_to_int"

let[@inline never] sums n =
  let evens = ref 0L in
  let odds = ref 0l in
  for i = 1 to n do
    if i land 1 = 0
    then evens := add64 !evens (of_int64 i)
    else odds := add32 !odds (of_int32 i)
  done;
  to_int64 !evens + to_int32 !odds

let result = sums (opaque 10)
