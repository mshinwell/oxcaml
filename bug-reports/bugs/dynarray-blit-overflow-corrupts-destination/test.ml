let () =
  let src = Dynarray.of_list [ 1; 2; 3 ] in
  let dst = Dynarray.of_list [ 7; 8; 9 ] in
  (try Dynarray.blit ~src ~src_pos:max_int ~dst ~dst_pos:3 ~len:1 with Invalid_argument _ -> ());
  match Dynarray.to_list dst with
  | l -> Printf.printf "result %s\n" (String.concat " " (List.map string_of_int l))
  | exception Invalid_argument m -> Printf.printf "result Invalid_argument %S\n" m
