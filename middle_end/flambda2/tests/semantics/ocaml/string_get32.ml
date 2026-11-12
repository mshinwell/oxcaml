(* Four bytes of a string read as an int32, and the same with the bytes in the
   opposite order. *)

external get32 : string -> int -> int32 = "%caml_string_get32u"

external bswap32 : int32 -> int32 = "%bswap_int32"

external to_int : int32 -> int = "%int32_to_int"

external opaque : 'a -> 'a = "%opaque"

let s = opaque "hello"

let result = to_int (get32 s 1), to_int (bswap32 (get32 s 1))
