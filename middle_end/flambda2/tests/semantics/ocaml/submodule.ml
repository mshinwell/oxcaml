(* Two submodules, one using a value of the other. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

module Scale = struct
  let factor = 3

  let[@inline] apply x = x * factor
end

module Offset = struct
  let[@inline] apply x = x + Scale.factor
end

let result = Offset.apply (Scale.apply 5)
