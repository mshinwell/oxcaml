(* An array made and read. *)

external get : 'a array -> int -> 'a = "%array_unsafe_get"

let result = get [| 1; 2; 3 |] 1
