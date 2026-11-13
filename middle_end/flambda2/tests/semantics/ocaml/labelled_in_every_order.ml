(* A function of three labelled arguments, applied with the labels in each of
   the six orders, once where it may be inlined and once where it is kept. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let weigh ~hundreds ~tens ~units = (hundreds * 100) + (tens * 10) + units

let[@inline never] weigh_kept ~hundreds ~tens ~units =
  (hundreds * 100) + (tens * 10) + units

let h = opaque 1

let t = opaque 2

let u = opaque 3

let htu = weigh ~hundreds:h ~tens:t ~units:u

let hut = weigh ~hundreds:h ~units:u ~tens:t

let thu = weigh ~tens:t ~hundreds:h ~units:u

let tuh = weigh ~tens:t ~units:u ~hundreds:h

let uht = weigh ~units:u ~hundreds:h ~tens:t

let uth = weigh ~units:u ~tens:t ~hundreds:h

let kept_htu = weigh_kept ~hundreds:h ~tens:t ~units:u

let kept_hut = weigh_kept ~hundreds:h ~units:u ~tens:t

let kept_thu = weigh_kept ~tens:t ~hundreds:h ~units:u

let kept_tuh = weigh_kept ~tens:t ~units:u ~hundreds:h

let kept_uht = weigh_kept ~units:u ~hundreds:h ~tens:t

let kept_uth = weigh_kept ~units:u ~tens:t ~hundreds:h
