(* A conversion between two boxed integers. *)

external to_int32 : int64 -> int32 = "%int64_to_int32"

external opaque : 'a -> 'a = "%opaque"

let result = to_int32 (opaque 5L)
