# The port of Simplify: where each file comes from

One line for each file or family of files of this folder. Kinds:
`transcribed` (follows a file of the compiler, named in the second column,
function by function; it carries that file's header), `generated` (made by a
program from files of this repository), `copy`, `original` (written for the
port; follows no file of the compiler; MIT header of
`middle_end/flambda2/rocq/`). The donor commit of every transcribed and
generated file is ecc5c0d968c892b4312065caef0f19ffffa042a9. ONE THING
HERE DOES NOT COME FROM THIS REPOSITORY: the types of the standard
library's values in 18 files of `decl/`. The last section says what is
read, what is taken and for how many declarations.

| file | donor or source | kind |
|---|---|---|
| `monad/real/Port_monad.v`, `monad/real/Kit_refuses.v`, `monad/id/Port_monad.v` | none | original |
| `runtime/port_monad.ml`, `runtime/port_abbreviations.ml` (empty) | none | original |
| `abbrev/FILE/Port_abbreviations.v` | the lines `module A = P` of the compiler's file that the ported file FILE follows (its abbreviations of modules), as Rocq's `Module A := P.` | transcribed |
| `Makefile`, `GUIDE.md`, `PROVENANCE.md`, `.gitignore` | none | original |
| `tools/assemble.sh`, `tools/progress.sh`, `tools/lint.py`, `tools/comments.py`, `tools/linktest.sh`, `tools/aliases.py`, `tools/samecode.sh`, `tools/papp.py`, `tools/given.py` | none | original |
| `tools/check.sh` | none; its list of include directories and `-open` flags is after `middle_end/flambda2/simplify/dune` | original |
| `tools/declgen/*` | none; it reads the compiled interfaces and typed trees of a build of the compiler, with the compiler's own library (`compiler-libs`); for the standard library it reads the compiled interfaces of the library of the OCaml that made the build (last section) | original |
| `decl/*.v` | written by `tools/declgen` from the compiled interface of the compiler's module of the same name; each begins with the header of that interface (`decl/README.md`). For the 18 files of modules of the standard library the compiled interface is NOT made from this tree (last section); the header is that of the tree's own `stdlib/NAME.mli` | generated |
| `decl/INDEX.tsv`, `decl/NOT-DECLARED.tsv`, `decl/FUNCTOR-ARGUMENTS.tsv`, `decl/VARIANTS.tsv` | written by `tools/declgen` with the `.v` files, from the compiled interfaces and the typed trees of the compiler (`decl/README.md` says what each holds) | generated |
| `decl/ARITIES.tsv` | written by `tools/declgen` from the typed trees of the implementations of the compiler's modules (`decl/README.md`, last section) | generated |
| `decl/UPDATES.tsv`, `decl/DONOR-TOKENS.tsv` | written by `tools/declgen` (`donors.ml`) about the 78 files of `middle_end/flambda2/simplify/`: the first from their typed trees (names and numbers of lines, no text), the second from their text as the compiler's lexer reads it (for each file a number and a digest, no text) (`decl/README.md`, the section before the last) | generated |
| `decl/README.md` | none | original |
| `extracted/.ocamlformat`, `runtime/.ocamlformat` | `middle_end/flambda2/.ocamlformat` | copy |
| `Simplify_import.v` | `middle_end/flambda2/simplify/simplify_import.ml` | transcribed |
| `Simplify_expr.v` | `middle_end/flambda2/simplify/simplify_expr.ml` | transcribed |
| `Simplify_apply_cont_expr.v` | `middle_end/flambda2/simplify/simplify_apply_cont_expr.ml` | transcribed |
| `extracted/DIR/foo.ml` | written by `make` from `DIR/Foo.v`: Rocq's extraction, then ocamlformat; the header is that of `middle_end/flambda2/simplify/DIR/foo.ml`; the text between `(*OCAML` lines of the `.v` file is copied as it is | generated |
| `PROGRESS.md` | written by `tools/progress.sh` | generated |
| `tests/fl/*.fl`, `tests/fl/run.sh`, `tests/fl/README.md` | none. The six terms were written for the port, by hand. Their syntax was learnt from the compiler's parser of the text form (`middle_end/flambda2/parser/`: the grammar and the names of the parameters of primitives) and from what a compiler prints with `-drawfexpr` and `-dfexpr` for three small OCaml files written for the purpose; the code of the tests follows the form of that printed text. Five `.fl` files of the compiler's tests were read (`middle_end/flambda2/tests/new_syntax*.fl`, `formatting_test.fl`); no line was taken from them, only the names `k` and `e` of the two continuations of a piece of code and the form of the last two lines. The other `.fl` files of the tests were not read before the terms were written. Two messages of the compiler are quoted in quotation marks ("Symbol .. not bound in typing environment", "Kind .. doesn't match expected kind"). | original |

A file `DIR/Foo.v` that is not in this table follows
`middle_end/flambda2/simplify/DIR/foo.ml` (`make list` prints the pairs) and
is `transcribed`: its first comment after the header says so.

## What is read that is not made from this tree's sources

`tools/declgen` finds compiled interfaces through the load path that the
build of the compiler recorded. For the compiler's own modules they are
compiled from this tree's sources. FOR THE STANDARD LIBRARY THEY ARE NOT.
The first stage of a build is compiled by the OCaml of the machine, and
reads and links THAT compiler's standard library (when `decl/` was made:
OCaml 5.4.1). The tree's own `stdlib/` is compiled by the tree's own
compiler at the second stage, in a format that the OCaml which builds
`tools/declgen` does not read.

WHAT IS TAKEN from those interfaces: the names and the TYPES of the values
and of the types of the standard library that `decl/` declares, written
as Rocq declarations. No body of a function, no text of an interface, no
comment. In such a file of `decl/` the header is that of the tree's own
`stdlib/NAME.mli`, and the comment before a declaration names that file,
without a line. The words of that comment are NOT that file's text: they
are the name and the type as the generator prints them from the compiled
interface (for a type, the name only). So a type there may be written as
the tree's file does not write it: without the kinds that the tree's
library gives its type variables, or with a name such as
`Stdlib__Format.formatter`.

HOW MANY: the rows of `decl/INDEX.tsv` whose place is under `stdlib/`.

    awk -F'\t' '$5 ~ /^stdlib\// {n[$3]++; u[$5]++}
      END {for (k in n) print n[k], k; c = 0; for (k in u) c++; print c, "files"}' decl/INDEX.tsv

prints `232 value`, `15 type` and `18 files`: 247 of the 8,892 rows, in
the files of `decl/` named after `Array`, `ArrayLabels`, `Bool`, `Float`,
`Format`, `Hashtbl`, `Int`, `Int32`, `Int64`, `List`, `ListLabels`,
`Option`, `Printexc`, `Printf`, `Queue`, `Seq`, `Stdlib` and `String`.

COULD THE TREE'S OWN INTERFACES BE READ INSTEAD? Not by this generator,
for the reason of the format; a second generator, built with the tree's
own compiler library, would be needed. What would differ, as far as
words tell: the declarations of the 232 values in the tree's
`stdlib/*.mli` and in the `.mli` files of that other library were
compared once, in scratch (the other library is not here, so `make` does
not repeat it). 91 have the same words. 140 more have the same words once
the modes, the kinds of type variables and the brackets that this
compiler's library adds are taken out; the Rocq declarations carry none
of these. 1 names a type otherwise (`String.length` takes `t` here and
`string` there; `t` is `string`). And the extracted files ARE compiled
against the tree's own standard library when the link test builds the
second stage (GUIDE.md, section 6): each use of these values there has a
type that the tree's library takes.

THE LIMIT: `decl/` is not made from the tree's standard library, and
`make` does not compare the two. No DEFINITION of either library is in
`decl/`; `make papp` reads two definitions of the tree's own `stdlib/` as
words (`tools/papp.py`).

Also read, with nothing of it in this folder: the OCaml of the PATH,
which type-checks the extracted files (`tools/check.sh`) with its own
standard library and builds `tools/declgen`; Rocq; `ocamlformat`.

