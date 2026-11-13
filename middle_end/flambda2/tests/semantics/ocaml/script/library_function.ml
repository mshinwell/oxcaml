(* A unit that calls a function of the standard library, which from_ocaml.sh
   refuses where it is given the directory of the library
   (library_function.says): the term names a symbol of the unit of the library
   that defines the function. *)

let longer (l : int list) = List.length l + 1

let result = longer (Sys.opaque_identity [1; 2])
