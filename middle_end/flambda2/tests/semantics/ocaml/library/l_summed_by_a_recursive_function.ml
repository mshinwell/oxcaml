(* A recursive function of the unit sums an array made by another function, with
   the index and the sum as parameters. gives: s = 12 | t = 23 *)

let rec sum (a : int iarray) (i : int) (acc : int) =
  if i = Iarray.length a then acc else sum a (i + 1) (acc + Iarray.get a i)

let[@inline never] [@local never] make (x : int) (y : int) : int iarray =
  [: x; y; x; y; x :]

let s : int = sum (make 2 3) 0 0

let t : int = sum (make (Sys.opaque_identity 1) 10) 0 0
