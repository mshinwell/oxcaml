(* Two bytes of a string read as one integer, the first being the more
   significant: [String.get_uint16_be] on a little-endian machine, which swaps
   the two bytes that it loads. *)

external get16 : string -> int -> int = "%caml_string_get16u"

external bswap16 : int -> int = "%bswap16"

external opaque : 'a -> 'a = "%opaque"

let[@inline] get_uint16_be s i = bswap16 (get16 s i)

let result = get_uint16_be (opaque "hello") 1
