type t = { mutable m : int }

let[@inline never] bump_and_raise q =
  q.m <- q.m + 100;
  raise Exit

let[@inline never] f q =
  let r = ref 0 in
  try
    r := q.m;
    bump_and_raise q;
    !r
  with Exit -> !r

let () = Printf.printf "result %d\n" (f { m = 5 })
