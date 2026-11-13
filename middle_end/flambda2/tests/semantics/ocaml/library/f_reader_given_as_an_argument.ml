(* A function that is kept makes an array and gives it to the function it is
   given. gives: p = 11 | q = 3 *)

let[@inline never] [@local never] apply (f : int iarray -> int) (x : int) =
  f [: x; x + 1; x + 2 :]

let[@inline never] [@local never] middle (a : int iarray) = Iarray.get a 1

let p : int = apply middle 10

let q : int = apply (fun a -> Iarray.length a) (Sys.opaque_identity 10)
