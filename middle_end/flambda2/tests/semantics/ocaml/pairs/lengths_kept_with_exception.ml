(* [lengths_included.ml] with an import left: a toplevel that reads the fields
   of another unit and keeps them, and exports a predefined exception too. The
   .cmx of the other unit gives a prefix, and the exception stays an import. The
   unit is validated once unused static bindings are removed from the head of
   the term after too, and the import is not bound at that head. *)

include Lengths

let not_found = Not_found
