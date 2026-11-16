external[@layout_poly] blit :
  ('a : any mod separable). 'a array -> int -> 'a array -> int -> int -> unit = "%arrayblit"

let[@inline never] copy (src : float array) (dst : float array) n = blit src 0 dst 0 n

let () =
  let n = 10_000_000 in
  let a = Array.make n 1.5 in
  let b = Array.make n 2.5 in
  copy a b n;
  Printf.printf "result %.1f\n" b.(n - 1)
