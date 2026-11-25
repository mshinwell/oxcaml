# The port of Simplify: where each file comes from

One line for each file or family of files of this folder. Kinds:
`transcribed` (follows a file of the compiler, named in the second column,
function by function; it carries that file's header), `generated` (made by a
program from files of this repository), `copy`, `original` (written for the
port; follows no file of the compiler; MIT header of
`middle_end/flambda2/rocq/`). The donor commit of every transcribed and
generated file is ecc5c0d968c892b4312065caef0f19ffffa042a9. Nothing here
comes from outside this repository.

| file | donor or source | kind |
|---|---|---|
| `monad/real/Port_monad.v`, `monad/real/Kit_refuses.v`, `monad/id/Port_monad.v` | none | original |
| `runtime/port_monad.ml`, `runtime/port_abbreviations.ml` (empty) | none | original |
| `abbrev/FILE/Port_abbreviations.v` | the lines `module A = P` of the compiler's file that the ported file FILE follows (its abbreviations of modules), as Rocq's `Module A := P.` | transcribed |
| `Makefile`, `GUIDE.md`, `PROVENANCE.md`, `.gitignore` | none | original |
| `tools/assemble.sh`, `tools/progress.sh`, `tools/lint.py`, `tools/comments.py`, `tools/linktest.sh`, `tools/aliases.py`, `tools/samecode.sh`, `tools/papp.py` | none | original |
| `tools/check.sh` | none; its list of include directories and `-open` flags is after `middle_end/flambda2/simplify/dune` | original |
| `tools/declgen/*` | none; it reads the compiled interfaces and typed trees of a build of the compiler, with the compiler's own library (`compiler-libs`) | original |
| `decl/*.v` | written by `tools/declgen` from the compiled interface of the compiler's module of the same name; each begins with the header of that interface (`decl/README.md`) | generated |
| `decl/INDEX.tsv`, `decl/NOT-DECLARED.tsv`, `decl/FUNCTOR-ARGUMENTS.tsv`, `decl/VARIANTS.tsv` | written by `tools/declgen` with the `.v` files, from the compiled interfaces and the typed trees of the compiler (`decl/README.md` says what each holds) | generated |
| `decl/ARITIES.tsv` | written by `tools/declgen` from the typed trees of the implementations of the compiler's modules (`decl/README.md`, last section) | generated |
| `decl/README.md` | none | original |
| `extracted/.ocamlformat`, `runtime/.ocamlformat` | `middle_end/flambda2/.ocamlformat` | copy |
| `Simplify_import.v` | `middle_end/flambda2/simplify/simplify_import.ml` | transcribed |
| `Simplify_expr.v` | `middle_end/flambda2/simplify/simplify_expr.ml` | transcribed |
| `Simplify_apply_cont_expr.v` | `middle_end/flambda2/simplify/simplify_apply_cont_expr.ml` | transcribed |
| `extracted/DIR/foo.ml` | written by `make` from `DIR/Foo.v`: Rocq's extraction, then ocamlformat; the header is that of `middle_end/flambda2/simplify/DIR/foo.ml`; the text between `(*OCAML` lines of the `.v` file is copied as it is | generated |
| `PROGRESS.md` | written by `tools/progress.sh` | generated |

A file `DIR/Foo.v` that is not in this table follows
`middle_end/flambda2/simplify/DIR/foo.ml` (`make list` prints the pairs) and
is `transcribed`: its first comment after the header says so.
