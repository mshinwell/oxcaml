type e = E0 | E1
type v = A | B of int | C of int * int | D of e

let f (x : v) (n : int) : int =
  let st =
    ref
      (match x with
       | A -> x
       | B _ -> (match n with 0 -> x | _ -> x)
       | C (_, _) -> C (4, n)
       | D _ -> D E1)
  in
  let acc = ref 0 in
  for i = 0 to n do
    st := !st;
    acc := !acc + (match x with A -> i | D _ -> i | B _ | C _ -> -2)
  done;
  !acc
