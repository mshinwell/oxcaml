(* A record of records. Simplify inlines [width] and reads the fields of the
   records as they are built. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type point =
  { x : int;
    y : int
  }

type segment =
  { start : point;
    stop : point
  }

let[@inline] width segment = segment.stop.x + segment.start.x

let result =
  width { start = { x = opaque 1; y = 2 }; stop = { x = 30; y = 40 } }
