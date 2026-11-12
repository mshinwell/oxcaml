(* A module inside the module, and a function that uses it. *)

external ( + ) : int -> int -> int = "%addint"

module Step = struct
  let size = 2

  let forward x = x + size
end

let twice x = Step.forward (Step.forward x)
