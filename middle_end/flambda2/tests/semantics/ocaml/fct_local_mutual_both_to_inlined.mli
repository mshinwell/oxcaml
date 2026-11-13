external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

val apply : ('a -> 'b) -> 'a -> 'b

module type Shift = sig
  val by : int
end

module Make : functor (S : Shift) -> sig
  val run : int -> int
end

module M : sig
  val run : int -> int
end

val result : int
