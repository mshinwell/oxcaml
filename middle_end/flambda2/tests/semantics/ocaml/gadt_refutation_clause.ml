(* A refutation case: the type says that the other constructor cannot come. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type zero = Zero

type 'n succ = Succ of 'n

type _ nat =
  | Z : zero nat
  | S : 'n nat -> 'n succ nat

let[@inline never] pred : type n. n succ nat -> n nat =
 fun n -> match n with S m -> m | _ -> .

let rec to_int : type n. n nat -> int =
 fun n -> match n with Z -> 0 | S m -> 1 + to_int m

let result = (to_int (pred (S (S (opaque (S Z))))) * 10) + to_int (pred (S Z))
