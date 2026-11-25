# The port of Simplify: where each file comes from

One line for each file or family of files of this folder. Kinds:
`transcribed` (follows a file of the compiler, named in the second column,
function by function; it carries that file's header), `generated` (made by a
program from files of this repository), `copy`, `original` (written for the
port; follows no file of the compiler; MIT header of
`middle_end/flambda2/rocq/`). The donor commit of the port as it stands is
ecc5c0d968c892b4312065caef0f19ffffa042a9: every transcribed file follows
its donor as it is at that commit, and its first comment says so. A file
of `decl/` names no commit: each names the text that it was made from, by
the name that Git gives that text, and the generator stops if the build
that it reads was not made from the texts of the tree (`decl/README.md`,
the section "What a file says that it was made from"). ONE THING
HERE DOES NOT COME FROM THIS REPOSITORY: the types of the standard
library's values in 20 files of `decl/`. The last section says what is
read, what is taken, for how many declarations and in which files.

| file | donor or source | kind |
|---|---|---|
| `monad/real/Port_monad.v`, `monad/real/Kit_refuses.v`, `monad/real/Kit_laws.v`, `monad/id/Port_monad.v` | none | original |
| `contracts/*.v`, `contracts/ported/*.v`, `contracts/ported/DIR/*.v`, `contracts/README.md` | none; they name functions, exceptions and files of the compiler and of the port | original |
| `proofs/*.v`, `proofs/DIR/*.v`, `proofs/README.md` | none; statements and proofs about ported files, written for the port. `proofs/env/Continuation_uses_handlers.v` holds two format strings of `env/Continuation_uses.v` (which has them from `middle_end/flambda2/simplify/env/continuation_uses.ml`): two of its premises name a call by its format | original |
| `runtime/port_monad.ml`, `runtime/port_abbreviations.ml` (empty) | none | original |
| `abbrev/FILE/Port_abbreviations.v` | the lines `module A = P` of the compiler's file that the ported file FILE follows (its abbreviations of modules), as Rocq's `Module A := P.` | transcribed |
| `Makefile`, `GUIDE.md`, `PROVENANCE.md`, `README.md`, `.gitignore` | none | original |
| `dune` | none; its one stanza, `(include_subdirs no)`, is a stanza of dune that dune files of the compiler also have (`middle_end/flambda2/tests/dune`) | original |
| `tools/assemble.sh`, `tools/progress.sh`, `tools/lint.py`, `tools/comments.py`, `tools/linktest.sh`, `tools/aliases.py`, `tools/samecode.sh`, `tools/papp.py`, `tools/given.py`, `tools/lines.py`, `tools/gate.sh`, `tools/shells.py`, `tools/exceptions.py` | none | original |
| `tools/check.sh` | none; its list of include directories and `-open` flags is after `middle_end/flambda2/simplify/dune` | original |
| `tools/declgen/*` | none; it reads the compiled interfaces and typed trees of a build of the compiler, with the compiler's own library (`compiler-libs`); for the standard library it reads the compiled interfaces of the library of the OCaml that made the build (last section) | original |
| `decl/*.v` | written by `tools/declgen` from the compiled interface of the compiler's module of the same name; each begins with the header of that interface and names the text of that interface by its Git blob (`decl/README.md`). For the 18 files of units of the standard library that declare something the compiled interface is NOT made from this tree (last section); the header is that of the tree's own `stdlib/NAME.mli` (also in `Lazy.v`, which declares nothing). Two files of the compiler's own modules (`Numeric_types.v`, `Rebuilt_expr__local.v`) also hold declarations whose types come from those interfaces, through what the module includes or applies of the library; they keep the header of the compiler's file | generated |
| `decl/INDEX.tsv`, `decl/NOT-DECLARED.tsv`, `decl/FUNCTOR-ARGUMENTS.tsv`, `decl/VARIANTS.tsv` | written by `tools/declgen` with the `.v` files, from the compiled interfaces and the typed trees of the compiler (`decl/README.md` says what each holds) | generated |
| `decl/ARITIES.tsv` | written by `tools/declgen` from the typed trees of the implementations of the compiler's modules (`decl/README.md`, last section) | generated |
| `decl/UPDATES.tsv`, `decl/DONOR-TOKENS.tsv`, `decl/DONOR-ITEMS.tsv` | written by `tools/declgen` (`donors.ml`) about the 78 files of `middle_end/flambda2/simplify/`: the first and the third from their typed trees (names and numbers of lines, no text), the second from their text as the compiler's lexer reads it (for each file a number and a digest, no text) (`decl/README.md`, the section before the last) | generated |
| `decl/README.md` | none | original |
| `extracted/.ocamlformat`, `runtime/.ocamlformat` | `middle_end/flambda2/.ocamlformat` | copy |
| `Simplify_import.v` | `middle_end/flambda2/simplify/simplify_import.ml` | transcribed |
| `Simplify_expr.v` | `middle_end/flambda2/simplify/simplify_expr.ml` | transcribed |
| `Simplify_apply_cont_expr.v` | `middle_end/flambda2/simplify/simplify_apply_cont_expr.ml` | transcribed |
| `extracted/DIR/foo.ml` | written by `make` from `DIR/Foo.v`: Rocq's extraction, then ocamlformat; the header is that of `middle_end/flambda2/simplify/DIR/foo.ml`; the text between `(*OCAML` lines of the `.v` file is copied as it is | generated |
| `PROGRESS.md` | written by `tools/progress.sh` | generated |
| `tests/fl/*.fl`, `tests/fl/run.sh`, `tests/fl/README.md` | none. The six terms were written for the port, by hand. Their syntax was learnt from the compiler's parser of the text form (`middle_end/flambda2/parser/`: the grammar and the names of the parameters of primitives) and from what a compiler prints with `-drawfexpr` and `-dfexpr` for three small OCaml files written for the purpose; the code of the tests follows the form of that printed text. Five `.fl` files of the compiler's tests were read (`middle_end/flambda2/tests/new_syntax*.fl`, `formatting_test.fl`); no line was taken from them, only the names `k` and `e` of the two continuations of a piece of code and the form of the last two lines. The other `.fl` files of the tests were not read before the terms were written. Two messages of the compiler are quoted in quotation marks ("Symbol .. not bound in typing environment", "Kind .. doesn't match expected kind"). | original |
| `tests/order/labels.ml`, `tests/order/pipe.ml`, `tests/order/run.sh`, `tests/order/README.md` | none; two small programs written for the port, in which each argument prints its name when it is evaluated | original |
| `tests/order/expected.oxcaml.txt`, `tests/order/expected.upstream.txt` | what the two programs print when they are compiled by the compiler of this tree and by upstream OCaml 5.4.1 (`tests/order/README.md`) | generated |
| `record_order/*.md` | none; written from a reading of the compiler's files (names of functions, modules and files, numbers of lines, and facts in the reader's words; no line of the compiler's code or comments) | original |

A file `DIR/Foo.v` that is not in this table follows
`middle_end/flambda2/simplify/DIR/foo.ml` (`make list` prints the pairs) and
is `transcribed`: its first comment after the header says so.

The header of a transcribed file, and of its extracted file, is the donor's
byte for byte: it is copied, not corrected. So `lifting/Reification.v` and
`extracted/lifting/reification.ml` have the misspelling `LICENSDE` that the
header of `middle_end/flambda2/simplify/lifting/reification.ml` has.

A QUESTION ABOUT A HEADER that a human must decide is written in the file
itself, under its header (or under the words that stand in its place), as
a comment that begins `CR mshinwell:`; the header is not changed on a
guess. Four files of `decl/` carry one, and the generator writes it
(`decl/README.md`): `Dwarf_flags.v` and `Target_system.v` (the interface
that they follow has no header: which header does the generated file
take?); `Numeric_types.v` and `Rebuilt_expr__local.v` (declarations whose
names and types come from the standard library stand under the header of
the compiler's file: are more credits owed? See the last section).

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
comment. In a file of `decl/` that is named after a unit of the standard
library the header is that of the tree's own `stdlib/NAME.mli`. The
comment before such a declaration, in whatever file it stands, names
that file, without a line (a family of a function of formats, such as
`Format.fprintf`, has one comment for its members: 165 comments for the
247 rows). The words of that comment are NOT that file's text: they
are the name and the type as the generator prints them from the compiled
interface (for a type, the name only). So a type there may be written as
the tree's file does not write it: without the kinds that the tree's
library gives its type variables, or with a name such as
`Stdlib__Format.formatter`.

THE HEADERS of the 19 files of `decl/` that are named after a unit of the
standard library (the 18 that have rows, and `Lazy.v`, which declares
nothing) are those of the tree's own `stdlib/NAME.mli`, though the names
and types were read from the other library; the comment under the header
of each file says so. Is the tree's header also the header of what was
read? The complete notice at the head of each of the 19 interfaces was
compared once, for the audit of the origin of the port at checkpoint 11:
in the tree's `stdlib/NAME.mli` and in the installed `.mli` file of that
name that was inspected for that audit, it is the same bytes for all 19
(14 lines; 15 for `Float`). That compares the two sets of files as they
were inspected then. Each of the 19 files now names the compiled
interface that `tools/declgen` read, by its digest (`decl/README.md`);
that does not show from which sources it was compiled. And `make` does
not repeat the comparison, since the other library is not here.

HOW MANY: the rows of `decl/INDEX.tsv` whose place is under `stdlib/`.

    awk -F'\t' '$5 ~ /^stdlib\// {n[$3]++; u[$5]++}
      END {for (k in n) print n[k], k; c = 0; for (k in u) c++; print c, "files"}' decl/INDEX.tsv

prints `232 value`, `15 type` and `18 files`: 247 of the 8,892 rows. The
18 are the interfaces `stdlib/NAME.mli` that the rows name as their
place, NOT the files of `decl/` that hold them. Those are 20:

    awk -F'\t' '$5 ~ /^stdlib\// {split($2, a, "."); n[a[1]]++}
      END {c = 0; for (k in n) {c++; print n[k], k}; print c, "files of decl/"}' decl/INDEX.tsv

- 200 rows in the 18 files of `decl/` named after a unit of the library:
  `Array`, `ArrayLabels`, `Bool`, `Float`, `Format`, `Hashtbl`, `Int`,
  `Int32`, `Int64`, `List`, `ListLabels`, `Option`, `Printexc`, `Printf`,
  `Queue`, `Seq`, `Stdlib_` (the library's `Stdlib`) and `String`. These
  carry the header of `stdlib/NAME.mli`; so does a nineteenth file,
  `Lazy.v`, which declares nothing (`Lazy.force` is in the kit) and has
  no row.
- 42 rows in `Numeric_types.v`: what the compiler's `Numeric_types.Int32`
  and `Numeric_types.Int64` include of the library's `Int32` and `Int64`
  (19 and 23 rows; places `stdlib/int32.mli` and `stdlib/int64.mli`).
- 5 rows in `Rebuilt_expr__local.v`: the module `HV` of
  `rebuilt_expr.ml`, which is `Hashtbl.Make` applied (place
  `stdlib/hashtbl.mli`).

The last two files are of the compiler's own modules and KEEP THEIR OWN
HEADERS (that of `numeric_types.mli` and of `rebuilt_expr.ml`); only the
comments before the 47 declarations name the library's files.

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

