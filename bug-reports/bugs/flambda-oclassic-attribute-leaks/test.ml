let apply f x = f x

let[@zero_alloc] add3 x =
  let k = 3 in
  apply (fun y -> y + k) x
