(* A function with a parameter of no kind, called directly: from_ocaml.sh
   makes its text (void_argument_direct.says). A direct call has the
   parameters of its code, of which the text writes one, as it writes one
   argument. *)

external opaque : 'a -> 'a = "%opaque"

let[@inline never] h (c : int) #() = c

let result = h (opaque 5) #()
