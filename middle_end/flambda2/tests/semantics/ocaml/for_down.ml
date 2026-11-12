(* A [for] loop counting down. As [for_sum.ml]. *)

external ( * ) : int -> int -> int = "%mulint"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let product = ref 1 in
  for i = 5 downto 1 do
    product := !product * i
  done;
  !product
