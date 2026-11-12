(* A recursive function that tests what a function given to it returns: [p] is
   not known where it is called. Simplify untags the boolean that the call
   returns: the call returns to a new continuation, bound at the call, that
   untags the result, and in the handler the untagging stands before the
   continuations of the two branches, where the term before has it after
   them. *)

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

let rec exists : (int -> bool) -> int list -> bool =
 fun p l ->
  match l with [] -> false | x :: t -> if p x then true else exists p t

let result = exists (fun x -> x > 2) (opaque [1; 2; 3])
