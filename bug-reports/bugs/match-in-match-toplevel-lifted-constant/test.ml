type policy = Disabled | After of int | On_blur of int

let autosave = Array.length Sys.argv = 1
let on_blur = Array.length Sys.argv > 2
let delay_ms = 1500 * Array.length Sys.argv

let policy =
  let delay_s = (delay_ms + 999) / 1000 in
  if autosave && on_blur then On_blur delay_ms
  else if autosave then After delay_s
  else Disabled

let show = function
  | Disabled -> print_endline "result off"
  | After s -> Printf.printf "result %d\n" s
  | On_blur ms -> Printf.printf "result on blur %d\n" ms

let () = List.iter show [ policy ]
