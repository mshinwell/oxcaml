# Tests of tools/unmonad

Small OCaml files in the form that Rocq's extraction writes. They follow no
file of the compiler. `make tooltest` runs the tool on each:

- `reject_*.ml`: the tool must refuse the file (the first line says why
  the direct-style reading would not be the monadic one);
- `accept_*.ml`: the tool must write exactly `accept_*.expected` (each
  `.expected` file was written by the tool and then read by hand);
- `Kit_refuses.v`: Rocq must compile it; each `Fail` in it is a use of the
  kit that the types of `Port_monad.v` must refuse.
