(* The composition of two functions. Simplify inlines [compose] and the three
   closures. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] compose f g = fun[@inline] x -> f (g x)

let result = (compose (fun x -> x + 1) (fun x -> x * 2)) (opaque 5)
