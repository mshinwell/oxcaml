(* A functor that is never inlined, with a function that has two local functions
   that call each other, each given to an inlined function. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] apply f x = f x

module type Shift = sig
  val by : int
end

module Make =
(functor [@inline never]
  (S : Shift)
  ->
  struct
    let run n =
      let rec down k = if k = 0 then n + S.by else up (k - 1)
      and up k = if k = 0 then n else down (k - 1) in
      apply down 2 + apply up n
  end)

module M = Make (struct
  let by = opaque 2
end)

let result = M.run 3
