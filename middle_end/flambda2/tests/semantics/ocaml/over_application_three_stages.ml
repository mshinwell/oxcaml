(* A function of one argument that returns a function of two that returns a
   function of one: given four arguments at once, three then one, one then
   three, and two then two. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] stage a =
  let a = a * 1000 in
  fun b c ->
    let bc = (b * 100) + (c * 10) in
    fun d -> a + bc + d

let w = opaque 1

let x = opaque 2

let y = opaque 3

let z = opaque 4

let all_at_once = stage w x y z

let three_then_one =
  let last = stage w x y in
  last z

let one_then_three =
  let rest = stage w in
  rest x y z

let two_then_two =
  let rest = stage w x in
  rest y z
