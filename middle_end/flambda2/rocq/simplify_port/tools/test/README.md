# Tests of tools/unmonad

Small OCaml files in the form that Rocq's extraction writes. They follow no
file of the compiler. `make tooltest` runs the tool on each:

- `reject_*.ml`: the tool must refuse the file (the first line says why
  the direct-style reading would not be the monadic one);
- `accept_*.ml`: the tool must write exactly `accept_*.expected`.
