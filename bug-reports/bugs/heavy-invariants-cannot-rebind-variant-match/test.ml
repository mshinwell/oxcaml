type t = A | B | C of int | D of string

let[@inline never] f x =
  let y = match x with A -> 1 | B -> 2 | C n -> n | D s -> String.length s in
  y + 1

let () = Printf.printf "result %d\n" (f (D "abc"))
