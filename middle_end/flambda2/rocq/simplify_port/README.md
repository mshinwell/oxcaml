# The port of Simplify to Rocq

This folder holds a port to Rocq of the compiler's Simplify
(`middle_end/flambda2/simplify/`, 78 files). Each file `DIR/foo.ml` of the
compiler has here a Rocq file `DIR/Foo.v` that follows it definition by
definition, and the OCaml file that Rocq's extraction makes of that Rocq
file, `extracted/DIR/foo.ml`. Where to read on:

- `GUIDE.md`: how a file is ported and what the folder's checks ask;
- `PROGRESS.md`: where each of the 78 files stands (made by `make`);
- `PROVENANCE.md`: where each file of the folder comes from;
- `decl/README.md`: the declarations of what the port calls of the rest of
  the compiler, which a program makes from the compiler's interfaces;
- `record_order/README.md`: the 23 records with calls in more than one field,
  and whether the order of the fields can matter at each;
- `GUIDE.md`, section 8: what Rocq proves about the port, what a proof
  assumes, and what a reader has to trust. `monad/real/Kit_laws.v` has the
  laws of the monad that says what the port means; `contracts/README.md`,
  what a proof assumes of a declared function or exception;
  `proofs/README.md`, the first lemmas about ported files. They are not a
  specification of Simplify;
- `against_model/README.md`: statements about ported functions from the
  Spec files of the model (the other folders of `middle_end/flambda2/rocq/`),
  proved. `make against-model MODEL=ROOT` checks them against a built model;
  it is not a part of `make` or of the gate, which do not need the model.

## Who owns it

Every file under this folder belongs to one stream of the Rocq work, the
port of Simplify, and that stream alone edits it: for a change here, ask
that stream. The port edits no file outside this folder.

## How it is built

Not by `rocq/Makefile`. No `.v` file of this folder is in a list of that
file, `make -C rocq all` does not compile one, and its check of the layout
and of the licence heads does not look inside this folder (the comment
before the recipe `layout` there says so). The names and the heads of the
files here follow this folder's own rules (`GUIDE.md`, section 1): most
files follow a file of the compiler and begin with that file's header.

The folder has its own `Makefile`. In this folder:

    make -j1 CMI_ROOT=ROOT

where `ROOT` is the `_build/default` of a dune build of this repository
(the compiled interfaces of the compiler, which the check of the types
reads). `tools/typedtrees.sh` makes the part of such a build that the
tools of this folder read, without building the compiler.
It needs Rocq, OCaml, ocamlformat and Python on the path (`ROCQ`,
`OCAMLC`, `OCAMLFMT` and `PYTHON` name other programs). Use one
build job. It builds the port against both monads of `monad/` and extracts
OCaml from the identity-monad build. The build against the real monad also
compiles the laws, the contracts and the first lemmas. OCaml checks each
extracted file against the compiler's interfaces. The default target also
runs the text checks (`make shells`, `make given`, `make lines`, `make
follows`, `make exceptions`, `make papp` and `make names`), regenerates
`PROGRESS.md` and
checks the
comments. Build copies, compiled Rocq files
and type-checking outputs are under `_build/` here, and `make` leaves
nothing else in the folder. The head of the
`Makefile` lists the targets.

The extracted files are not compiled by the build of the compiler, nor is
any other `.ml` file of this folder. The file `dune` here has one stanza,
`(include_subdirs no)`: it takes the folder and its subdirectories out of
the group of modules that `middle_end/flambda2/dune` makes of its
subdirectories. The folder is not excluded from `dune build @fmt`;
formatting remains enabled for its extracted files and runtime.
`tools/linktest.sh` says how a compiler is built with the extracted files
in the place of its own Simplify, in a scratch tree (`GUIDE.md`, section
6).

## The gate

One command asks what a commit of the port must hold. In a work tree
that has only its tracked files (a new `git worktree`), from any
directory:

    middle_end/flambda2/rocq/simplify_port/tools/gate.sh ROOT

`ROOT` is as for `make`, and must be a build of the compiler from the
sources of that tree. The command makes `decl/` again from `ROOT` and
compares it with the tree's; asks that the files under `extracted/` and
`runtime/` are the ones that `make` makes and the kit, and no other; that
the folder's `dune` file is the one stanza that the section above names,
and the only file of dune in the folder; that the names of the tracked
files have only letters, digits and the characters `_ . / + -`; that
ocamlformat leaves every `.ml` and `.mli` file as it is; that every shell
script begins with `set -eu`; then runs `make` from nothing and asks
that `git status --porcelain` is empty after it and that the make left
nothing in the folder but `_build/`. It prints each thing
that it asks with the answer, one line each, and exits 0 only if every
answer is yes. The make is the long part (about 25 minutes, one process).
The head of `tools/gate.sh` has the whole list, and what the gate does
not ask; `GUIDE.md`, section 6, says when it is run.
