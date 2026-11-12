(* A match on characters is a switch on their codes. Simplify inlines [digit]
   three times and resolves each switch. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline] digit c = match c with '0' -> 0 | '1' -> 1 | '2' -> 2 | _ -> 9

let result = digit '1' + digit '2' + digit 'x'
