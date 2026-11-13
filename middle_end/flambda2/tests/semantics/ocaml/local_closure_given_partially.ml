(* A function that takes a local function and two numbers, given the function
   alone: the function given captures a variable of the caller and is made on
   the caller's stack. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] apply_to_both (local_ f : int -> int) (a : int) (b : int) :
    int =
  let x = f a in
  let y = f b in
  (x * 100) + y

let[@inline never] with_offset (offset : int) : int =
  let local_ add_offset x = x + offset in
  let waiting = apply_to_both add_offset in
  let first = waiting 1 2 in
  let second = waiting 3 4 in
  first + second

let result = with_offset (opaque 10)
