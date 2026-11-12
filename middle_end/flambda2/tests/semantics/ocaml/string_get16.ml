(* Two bytes of a string read as one integer, the first being the less
   significant: what [String.get_uint16_le] does on a little-endian machine,
   without its test of the index. *)

external get16 : string -> int -> int = "%caml_string_get16u"

external opaque : 'a -> 'a = "%opaque"

let result = get16 (opaque "hello") 1
