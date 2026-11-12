(* A constructor with two arguments built at the call of an inlined function
   that matches it and gives the second. *)

external opaque : 'a -> 'a = "%opaque"

type shape =
  | Circle of int
  | Rect of int * int

let[@inline] height shape = match shape with Circle r -> r | Rect (_, h) -> h

let[@inline never] rect_height w h = height (Rect (w, h))

let result = rect_height (opaque 2) 7
