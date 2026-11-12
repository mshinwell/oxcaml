(* String constants passed around in pairs. Simplify inlines [first] and
   [second] and reads the fields of the static pairs. *)

let greeting = "hello"

let[@inline] first pair = match pair with a, _ -> a

let[@inline] second pair = match pair with _, b -> b

let result = first (second (1, (greeting, "world")))
