external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

module type Named = sig
  val name : string
end

module Describe : functor (N : Named) -> sig
  val size : unit -> int

  val initial : unit -> int
end

module D : sig
  val size : unit -> int

  val initial : unit -> int
end

val result : int
