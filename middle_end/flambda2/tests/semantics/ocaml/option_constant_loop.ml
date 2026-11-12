(* An option that one path gives as a constant block and the other as [None],
   matched after they meet, in the body of a loop of the unit itself: the
   function is applied once, and is no function in the term that Simplify is
   given. Simplify gives the continuation where they meet, in the loop, whether
   the value is an immediate and the field. The validation knows the block in
   the handler of the loop, as the symbol is bound above the loop. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( land ) : int -> int -> int = "%andint"

external ( = ) : int -> int -> bool = "%equal"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] f : int -> int =
 fun n ->
  let s = ref 0 in
  let i = ref 0 in
  while !i < n do
    let v = if !i land 1 = 0 then Some 8 else None in
    (match v with None -> s := !s + 1 | Some y -> s := !s + y);
    i := !i + 1
  done;
  !s

let result = f 5
