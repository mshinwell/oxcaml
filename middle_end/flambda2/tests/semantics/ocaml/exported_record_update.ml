(* A constant record, and an exported function that makes a record from
   another. *)

type t =
  { x : int;
    y : int
  }

let origin = { x = 0; y = 0 }

let move_x t dx = { t with x = dx }

let p = move_x origin 5
