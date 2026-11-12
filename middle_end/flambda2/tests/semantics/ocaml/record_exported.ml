(* A record type with a function that makes one and a function that reads a
   field, exported. *)

type r =
  { x : int;
    y : int
  }

let make x y = { x; y }

let get_x r = r.x
