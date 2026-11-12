(* Arithmetic on boxed 32-bit integers. Simplify inlines [f] and removes every
   box but that of the result. *)

external opaque : 'a -> 'a = "%opaque"

external add : int32 -> int32 -> int32 = "%int32_add"

external mul : int32 -> int32 -> int32 = "%int32_mul"

external logand : int32 -> int32 -> int32 = "%int32_and"

let[@inline] f x y = logand (add (mul x y) 1l) 0xffl

let result = f (opaque 100l) 3l
