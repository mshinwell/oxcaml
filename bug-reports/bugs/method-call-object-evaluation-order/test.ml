let[@inline never] say s v = print_string s; v

class packer = object method pack (a : int) (b : int) = (a * 10) + b end

let[@inline never] make () = say "o" (new packer)

let () =
  print_string "result ";
  let r = (make ())#pack (say "a" 1) (say "b" 2) in
  Printf.printf " %d\n" r
