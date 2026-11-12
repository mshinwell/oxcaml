(* A functor applied to a structure. Simplify inlines the functor, which is a
   function, and then [next] twice. *)

external ( + ) : int -> int -> int = "%addint"

module type Step = sig
  val step : int
end

module Counter (S : Step) = struct
  let[@inline] next x = x + S.step
end

module By_two = Counter (struct
  let step = 2
end)

let result = By_two.next (By_two.next 1)
