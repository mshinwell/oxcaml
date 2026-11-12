(* A function that calls itself in tail position, which is a loop once the call
   is a jump, and makes at each round a local recursive function that captures
   nothing. Simplify makes the local function a symbol bound beside the code,
   and the local function calls itself through that symbol. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( <= ) : int -> int -> bool = "%lessequal"

external opaque : 'a -> 'a = "%opaque"

let rec walk n acc =
  if n <= 0
  then acc
  else
    walk (n - 1)
      (let rec depth k = if k <= 0 then 0 else 1 + depth (k - 1) in
       acc + depth 2)

let result = walk (opaque 3) 0
