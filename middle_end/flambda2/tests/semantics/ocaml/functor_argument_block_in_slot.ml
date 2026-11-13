(* A functor is applied to a structure one of whose functions is a function of
   the unit given its first argument only. The closure of the function that the
   functor makes holds the block of that structure, and its code loads the
   function from the block. Simplify resolves the loads and keeps no such
   block. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

module type Unary = sig
  val f : int -> int
end

let plus a b = a + b

module Thrice (U : Unary) = struct
  let go x = U.f (U.f (U.f x))
end

module M = Thrice (struct
  let f = plus (opaque 2)
end)

let answer = M.go 1
