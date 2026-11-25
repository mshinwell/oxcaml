# Tests of the order of evaluation

Two small OCaml programs in which each argument prints its name when it is
evaluated, and what they print with two compilers. The guide's rules for
the order of `let!` (GUIDE.md, section 2) rest on these facts. Not part of
`make`: the port's `make` has no compiler of OxCaml.

    tests/order/run.sh oxcaml COMPILER [ARGUMENT ...]
    tests/order/run.sh upstream COMPILER [ARGUMENT ...]

`COMPILER` is a native compiler (`ocamlopt.opt`); the first word says which
answer is expected of it. An installed compiler needs no argument. The
compiler that `make boot-compiler` builds in a tree of OxCaml is not
installed, and is told where the standard library of the tree is:

    tests/order/run.sh oxcaml TREE/_build/_bootinstall/bin/ocamlopt.opt \
      -nostdlib -I TREE/_build/default/stdlib/build -I TREE/_build/default/runtime

## The facts

| | OxCaml | upstream OCaml |
|---|---|---|
| a total application, the labelled arguments written in any order (`labels.ml`) | from the last PARAMETER to the first | the same |
| `x \|> f ~l:e`, the piped value is the parameter BEFORE `l` | `e`, then `x`: it is the one application `f x ~l:e` | `x`, then `e` |
| `f ~l:e @@ x`, the same `f` | `e`, then `x` | `x`, then `e` |
| `x \|> f ~l:a \|> f ~l:b`, the same `f` | `b`, `a`, `x` | `x`, `a`, `b` |
| `x \|> g a`, the piped value is the LAST parameter | `x`, then `a` | the same |
| `x \|> g a \|> g b`, the same `g` | `x`, `a`, `b` | the same |

So the two compilers differ only where the right side of a pipe gives an
argument for a parameter that comes AFTER the piped one. OxCaml types a
pipe whose right side is an application as one application, and evaluates
its arguments from the last parameter to the first, as it does for every
application. The port follows OxCaml: it is the compiler that compiles
Simplify.

## With which compilers this was seen

- `expected.oxcaml.txt`: the compiler that `make boot-compiler` builds from
  the sources of this tree (`ocamlopt.opt -config`: version 5.4.1,
  `flambda2: true`), native code, on x86-64 Linux.
- `expected.upstream.txt`: upstream OCaml 5.4.1 (`flambda: false`), native
  code, on x86-64 Linux. `labels.ml` gave the same with its bytecode
  compiler.

`run.sh` given the other compiler's name exits 1 and shows the three lines
that differ.
