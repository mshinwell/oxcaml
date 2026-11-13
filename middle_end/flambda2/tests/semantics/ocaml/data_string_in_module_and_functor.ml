(* A module with a string, given to a functor whose function reads it. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

module type Named = sig
  val name : string
end

module Describe (N : Named) = struct
  let size () = length N.name

  let initial () = code (unsafe_get N.name 0)
end

module D = Describe (struct
  let name = "module"
end)

let result = D.size () + D.initial ()
