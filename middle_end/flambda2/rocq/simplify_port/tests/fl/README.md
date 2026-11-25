# Tests in Flambda's text form

Six terms written in Flambda's text form (`.fl` files). Each has a shape
that the translation from Lambda never makes, so no OCaml source brings
Simplify to the code that treats it. The compiler's test tool `fexprc`
reads such a file and runs Simplify on the term. `run.sh` runs each test
through a copy of `fexprc` built with the compiler's own Simplify and a
copy built with the extracted files, and says whether the two give the
same.

    FEXPRC_BASE=.. FEXPRC_PORT=.. [FEXPRC_COV=..] tests/fl/run.sh

## The copies of fexprc

They are built in a SCRATCH work tree of the compiler. The scratch tree
and what is built in it are never committed.

- `FEXPRC_BASE`, with the compiler's own Simplify: in the scratch tree,
  `make boot-compiler`, then `make compiler`. The tool is
  `_build/main/middle_end/flambda2/tests/tools/fexprc.exe`; keep a copy.
- `FEXPRC_PORT`, with the extracted Simplify: `tools/linktest.sh swap TREE`
  (run in the folder of the port) puts the extracted files in the place of
  `middle_end/flambda2/simplify/` in the scratch tree; then `make compiler`
  there again. The tool is at the same path; keep a copy.
- `FEXPRC_COV`, which may be left out: as `FEXPRC_PORT`, from extracted
  files in which each function, when it is entered, records its name
  (`file.Module.function`); the program writes the names to the file that
  the variable `PORT_COV_FILE` names. The program that puts these calls in
  the extracted files is not committed. With this copy `run.sh` also says
  whether the functions that the head of each test names are entered.

## What "the same" compares

Each test is run three times: with no flag, with `-O3`, and with `-O3` and
the flags that turn on the lifting and the specialization of continuations.
Every run has `-dfexpr -dflambda`: the standard output is then the term
that Simplify gives, printed in the text form and in the full form.
Compared between the two copies: the exit status, the standard output, the
messages (the standard error). `fexprc` writes no file.

## The tests

| test | the shape | the functions of the extracted Simplify that it enters |
|---|---|---|
| `static_closures.fl` | sets of closures that are static constants | `rebuilt_static_const.Group.add`, `simplify_set_of_closures.simplify_lifted_set_of_closures0` |
| `static_arrays.fl` | static arrays of naked numbers | `simplify_static_const.rebuild_naked_number_array` |
| `num_conv_tagged.fl` | conversions of numbers with a tagged integer on one side | `number_adjuncts.For_tagged_immediates.Num.to_naked_float`, `.to_naked_float32`, `.to_immediate`, `number_adjuncts.For_naked_immediates.Num.to_immediate` |
| `extra_boxed_vectors.fl` | boxed vectors whose bits are known; `%reinterpret_boxed_vector` | `rebuilt_static_const.create_boxed_vec128`, `create_boxed_vec256`, `create_boxed_vec512`, `simplify_unary_primitive.simplify_reinterpret_boxed_vector` |
| `extra_recursive_handler.fl` | a recursive continuation around the Switch at which a continuation is specialized | `one_recursive_handler.with_handler`, with the expert flags only |
| `extra_boxed_var.fl` | a static boxed number whose content is a variable | none: see below |

`extra_boxed_var.fl` STOPS SIMPLIFY WITH A FATAL ERROR, with the compiler's
own Simplify as with the extracted one: `simplify_static_const.ml` looks up
the variable of a static boxed number with the kind of values, and here
the variable is a naked number ("Kind .. doesn't match expected kind").
Nothing is mended here: the two copies must stop in the same way with the
same message. The message prints the downwards accumulator, so the test
also compares what the printers of the two Simplifys write. It is kept as
a test of that sameness.

One function of this family is not entered by any test:
`rebuilt_static_const.create_boxed_mask`. The text form has no constant for
a mask and no static array of masks.

## To write more tests

- Take the syntax from the compiler: a compiler of stage 2 prints any OCaml
  file in the text form, with `-drawfexpr` (the term before Simplify) and
  `-dfexpr` (the term after it). A comment is `(* .. *)`.
- The symbol of the module must be `$caml` and the name of the file with a
  capital: `static_arrays.fl` ends with `let $camlStatic_arrays = Block 0
  (..) in cont done ($camlStatic_arrays)`. With another name Simplify stops
  ("Symbol .. not bound in typing environment").
- A keyword of the grammar is no name of a variable (`boxed`, `float`,
  `imm`, `int32`, ...). As a parameter of a primitive a keyword is written
  between backquotes: ``%array_load.`float` ``,
  ``%num_conv.[tagged_imm].[`float`]``.
- The handler of a continuation takes a `let` but no `where` of its own
  without parentheses: a `where` written after it belongs to the expression
  outside. Put the handler between parentheses if it has a `where`.
- A 32-bit float as a boxed number is `fnt32` (``%box_num.fnt32.region``),
  not `float32`.
- A vector is written only as an element of a static array:
  `Vec128_array [|vec128[1L:2L]|]`. What the printer writes for a vector
  (`vec128[0000000000000001:0000000000000002]`) is not read again.
- `fexprc` prints nothing without `-dfexpr` or `-dflambda`. It takes the
  options of the compiler. It refuses `-Oclassic`.
- At the head of a test, a line `ENTERS name` names a function that the
  test is meant to enter in every run, and `ENTERS-EXPERT name` one that it
  enters with the expert flags only.
