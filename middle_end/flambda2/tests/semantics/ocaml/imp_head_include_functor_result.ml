(* [include_functor_result.ml] with an import: the unit exports a predefined
   exception too. A module includes what a functor returns, and adds a function
   that calls a function included. The functor is marked to be inlined; the
   functions are never inlined. The unit is validated once unused static
   bindings are removed from the head of the term after too, and no import is
   bound at that head. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

module Times =
(functor [@inline]
  (N : sig
     val n : int
   end)
  ->
  struct
    let[@inline never] times x = x * N.n
  end)

module Three = struct
  include Times (struct
    let n = 3
  end)

  let[@inline never] times_plus_one x = times x + 1
end

let result = Three.times_plus_one (opaque 4) + Three.times 2

let not_found = Not_found
