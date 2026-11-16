let () =
  let a = Bigarray.(Array1.create int c_layout 4) in
  match Bigarray.reshape_2 (Bigarray.genarray_of_array1 a) 5 3689348814741910324 with
  | _ -> print_endline "result no exception"
  | exception e -> Printf.printf "result %s\n" (Printexc.to_string e)
