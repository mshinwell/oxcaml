(* The first unit of a pair: a record with a field of which the .cmx says what
   it holds, and one of which it says nothing. *)

external opaque : 'a -> 'a = "%opaque"

type t =
  { known : int;
    hidden : int
  }

let r = { known = 5; hidden = opaque 7 }
