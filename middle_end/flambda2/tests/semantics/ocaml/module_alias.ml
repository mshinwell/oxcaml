(* A module, an alias of it and an inclusion of it: fields of blocks that are
   known. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

module Base = struct
  let offset = 10

  let[@inline] shift x = x + offset
end

module Alias = Base

module Wider = struct
  include Base

  let[@inline] twice x = shift (shift x)
end

let result = Alias.shift (Wider.twice (opaque 1))
