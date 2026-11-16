let () =
  let a = Bigarray.(Array1.create float16 c_layout 1) in
  a.{0} <- 0x1.0020000001p+0;
  Printf.printf "result %h\n" a.{0}
