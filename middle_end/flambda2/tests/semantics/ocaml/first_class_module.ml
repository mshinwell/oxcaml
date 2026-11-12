(* A module packed as a value and unpacked: a block made and read. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

module type S = sig
  val base : int

  val step : int -> int
end

let packed =
  (module struct
    let base = 10

    let[@inline] step x = x + 1
  end : S)

let result =
  let module M = (val packed : S) in
  M.step (M.step (opaque M.base))
