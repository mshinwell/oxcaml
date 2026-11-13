(* A pair, a triple and a closure, made at three times and all read at the
   end. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

(* Reads a local pair. Never inlined, so that the pair it is given exists. *)
let[@inline never] read2 (local_ p) =
  let a, b = p in
  (a * 3) + b

(* Reads a local triple. *)
let[@inline never] read3 (local_ t) =
  let a, b, c = t in
  (a * 5) + (b * 3) + c

(* Calls a local closure. *)
let[@inline never] call1 (local_ f) x = f x

(* Fills the free part of the local stack: two pairs, a triple and a closure
   made from [x], with numbers that no unit puts in a local value of its own.
   What a region gave back too early is written over here. *)
let[@inline never] noise x =
  let local_ a = x + 1000, x + 2001 in
  let local_ b = x + 3002, x + 4003, x + 5004 in
  let local_ c = x + 6005, x + 7006 in
  let local_ f = fun y -> y + x + 8007 in
  read2 a + read3 b + read2 c + call1 f 7

let[@inline never] body x =
  let local_ p = x, 1 in
  let n1 = noise x in
  let local_ q = n1, x, 2 in
  let n2 = noise n1 in
  let local_ f = fun y -> y + n2 in
  let n3 = noise n2 in
  n3 + read2 p + read3 q + call1 f 1

let result = body (opaque 3) + body 10
