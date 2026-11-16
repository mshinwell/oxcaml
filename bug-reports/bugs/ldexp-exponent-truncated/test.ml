let () = Printf.printf "result %h\n" (ldexp 1.0 (Sys.opaque_identity (1 lsl 32)))
