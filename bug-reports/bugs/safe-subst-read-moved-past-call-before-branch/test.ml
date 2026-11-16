let[@inline never] clear b = Bytes.fill b 0 (Bytes.length b) 'z'

let[@inline never] f b t =
  let c = String.get (Bytes.unsafe_to_string b) 0 in
  clear b;
  if t then c else '?'

let () = Printf.printf "result %c\n" (f (Bytes.make 1 'a') (Sys.opaque_identity true))
