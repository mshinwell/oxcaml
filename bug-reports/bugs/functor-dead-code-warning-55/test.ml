module type S = sig
  val step : int -> int
end

module Make (X : S) = struct
  let[@inline never] run x = (X.step [@inlined]) x
end

module M1 = Make (struct let step x = x + 1 end)
module M2 = Make (struct let step x = x + 2 end)

let () =
  Printf.printf "result %d\n" (M1.run (Sys.opaque_identity 20) + M2.run (Sys.opaque_identity 19))
