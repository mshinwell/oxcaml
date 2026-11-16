module M : sig
  val run : int -> int
end = struct
  let[@inline never] call f x = f x

  let rec loop n acc = if n = 0 then acc else call step (n - 1) acc
  and step m acc = loop m (acc + 1)

  let run n = loop n 0
end

let () = Printf.printf "result %d\n" (M.run 10_000_000)
