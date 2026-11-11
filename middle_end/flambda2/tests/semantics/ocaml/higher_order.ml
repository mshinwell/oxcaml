(* A function passed to a function. Simplify inlines [twice], then knows which
   closure [f] is, makes its two calls direct and inlines them. (For the type
   annotation, see [match_variant.ml].) *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] twice : (int -> int) -> int -> int = fun f x -> f (f x)

let result = twice (fun y -> y + 10) (opaque 2) + twice (fun y -> y + y) 3
