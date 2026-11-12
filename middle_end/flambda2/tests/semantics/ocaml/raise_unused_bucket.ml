(* The same with an exception that is allocated where it is raised: nothing
   reads it, and Simplify does not allocate it. *)

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] f x = x

let result =
  try if opaque true then raise (Invalid_argument "no") else f 1 with _ -> 2
