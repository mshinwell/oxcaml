(* Functions whose parameter is a pair pattern, given pairs that are not written
   out at the call. The front end makes them tupled functions: the code takes
   the two components, and a call of unknown arity gives it the pair, as every
   call of the model does. Simplify inlines both calls. *)

let[@inline] first (a, _) = a

let[@inline] second (_, b) = b

let result = first (second (1, ("hello", "world")))
