(* The same load with the test of the index that [String.get_uint16_le]
   makes. *)

external get16 : string -> int -> int = "%caml_string_get16"

external opaque : 'a -> 'a = "%opaque"

let result = get16 (opaque "hello") 3
