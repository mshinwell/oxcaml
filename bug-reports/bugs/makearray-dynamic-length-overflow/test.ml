external[@layout_poly] make : ('a : any mod separable). int -> 'a -> 'a array = "%makearray_dynamic"
external[@layout_poly] len : ('a : any mod separable). 'a array -> int = "%array_length"

let () =
  match make (Sys.opaque_identity (min_int + 1)) #(#1L, #2L, #3L, #4L) with
  | a -> Printf.printf "result length %d\n" (len a)
  | exception Invalid_argument _ -> print_endline "result Invalid_argument"
