type t = F of (unit -> t)
type 'a box = Box of 'a

module M (X : sig val x : int end) = struct
  let rec even () = ignore (Sys.opaque_identity X.x); F odd
  and odd () = ignore (Sys.opaque_identity X.x); F even
end
[@@inline never]

let[@inline never] use (_ : unit -> t) = ()

let[@inline never] test c d e g x1 x2 =
  let module A = M (struct let x = x1 end) in
  let module B = M (struct let x = x2 end) in
  let h = if c then A.even else B.even in
  let o = if d then A.odd else B.odd in
  let b =
    if g
    then (match (o [@unrolled 1]) () with F v -> Box (Box (Box (Box (Box v)))))
    else (
      ignore (Sys.opaque_identity 0);
      match (o [@unrolled 1]) () with F v -> Box (Box (Box (Box (Box v)))))
  in
  let w = match b with Box (Box (Box (Box (Box w)))) -> w in
  let p = if e then h else w in
  use p;
  p

let () =
  let (F _) = (test true false true false 1 2) () in
  print_endline "result done"
