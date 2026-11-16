type t = A of int | B of int

let[@inline never] use (local_ (o : int option)) =
  match o with Some v -> v | None -> 0

let[@inline always] g x n =
  let r = stack_ (Some n) in
  match x with A a -> use r + a | B b -> use r + (2 * b)

let[@inline never] f n =
  let s = ref 0 in
  for i = 1 to n do
    let x = if i land 1 = 0 then A i else B i in
    s := !s + g x i
  done;
  !s

let () = Printf.printf "result %d\n" (f 20_000_000)
