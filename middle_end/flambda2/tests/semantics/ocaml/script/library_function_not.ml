(* The unit of library_function.ml with the length computed by a function of its
   own: what it takes from the standard library are primitives, the term names
   no symbol of another unit, and from_ocaml.sh makes its text
   (library_function_not.says). *)

let rec length (l : int list) = match l with [] -> 0 | _ :: t -> 1 + length t

let longer (l : int list) = length l + 1

let result = longer (Sys.opaque_identity [1; 2])
