(* The second of two units given to the driver in one process. It asks for
   [-O3], as what the first asked for stays for the units that come after it in
   the process: so Simplify runs on this one, and the driver must not compare
   the term that Simplify returns for it with the term of the first unit, which
   it still holds. *)

[@@@ocaml.flambda_o3]

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let result = opaque 3 + 4
