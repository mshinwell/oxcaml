(* A loop whose accumulator is a pair. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

let rec fib : int -> int * int -> int =
 fun n acc -> if n = 0 then fst acc else fib (n - 1) (snd acc, fst acc + snd acc)

let result = fib 10 (0, 1)
