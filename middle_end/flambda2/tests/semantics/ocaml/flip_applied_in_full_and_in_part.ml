(* A combinator that swaps the two arguments of a function, written with three
   parameters and written to return a function; each applied in full, to the
   function and one argument, and to the function alone. *)
external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let flip f x y = f y x

let flip_staged f = fun x y -> f y x

let[@inline never] weigh a b = (a * 10) - b

let a = opaque 7

let b = opaque 2

let in_full = flip weigh a b

let function_and_one =
  let waiting = flip weigh a in
  waiting b

let function_alone =
  let flipped = flip weigh in
  flipped a b

let staged_in_full = flip_staged weigh a b

let staged_function_alone =
  let flipped = flip_staged weigh in
  flipped a b

let flipped_twice = flip (flip weigh) a b
