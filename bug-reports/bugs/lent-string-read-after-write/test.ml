let[@inline never] f b =
  let c = String.get (Bytes.unsafe_to_string b) 0 in
  Bytes.set b 0 'z';
  c

let () = Printf.printf "result %c\n" (f (Bytes.make 1 'a'))
