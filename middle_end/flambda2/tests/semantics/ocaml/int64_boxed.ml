(* Arithmetic on boxed 64-bit integers. Simplify inlines [scale] and removes
   every box: the multiplication and the addition are done on unboxed
   numbers. *)

external opaque : 'a -> 'a = "%opaque"

external add : int64 -> int64 -> int64 = "%int64_add"

external mul : int64 -> int64 -> int64 = "%int64_mul"

external less_than : int64 -> int64 -> bool = "%lessthan"

let scale x = add (mul x 3L) 1L

let result = less_than (scale (opaque 5L)) 20L
