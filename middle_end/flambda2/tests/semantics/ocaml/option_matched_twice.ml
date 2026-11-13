(* An option made on the two arms of a test and matched twice after they meet:
   the test of the option and the load of its contents are each made in two
   places. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] twice c x =
  let o = if c then Some (x + 1) else None in
  let a = match o with None -> 0 | Some y -> y in
  let b = match o with None -> 10 | Some y -> y * 2 in
  a + b

let result = twice (opaque true) 4 + twice (opaque false) 4
