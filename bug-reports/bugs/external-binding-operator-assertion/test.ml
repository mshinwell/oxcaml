external ( let& ) : 'a -> ('a -> 'b) -> 'b = "%revapply"

let f x =
  let& y = x + 1 in
  y * 2

let () = Printf.printf "result %d\n" (f 20)
