# Pairs of units

A unit that uses another unit reaches it, before Simplify, by loading
a field of the module block of that unit. The compiler's Simplify
reads the `.cmx` of the other unit and uses what it says: it puts the
symbol of a closure in the place of the load, makes the call direct,
and inlines the body where the `.cmx` has it. The units of the
directory above use no other unit. Here the second unit of each pair
uses the first, and the test tool is given the directory that has the
`.cmx` of the first, so that its Simplify does what the compiler's
does.

This is the first step of
`middle_end/flambda2/rocq/requests/C5-imports-with-contents.md`
(section 6, item 1): the option of the tool and the pairs. It claims
nothing that the directory above does not claim; see "What is
claimed".

## The files

`F.ml` is a first unit and `F_more.ml` a second unit that uses it: a
unit is the second unit of a pair if its name is the name of another
unit of this directory followed by an underscore and more (the
longest such name, if several fit). As in the directory above,
`X.fl` is the term that the compiler makes of `X.ml` for Simplify
and `X.expected` is what the tool prints of that term; both are kept.
A unit that has no `X.expected` is compiled, for the unit that uses
it, and its term is compared with `X.fl`; the tool is not run on it.
There are no interface files: a unit exports everything.

## How a pair is made and checked

    sh from_ocaml.sh <ocamlopt> F.ml F
    sh from_ocaml.sh <ocamlopt> F_more.ml F_more F

Each is, in a directory of its own, to which `F.cmi` and `F.cmx` are
copied first for the second unit,

    ocamlopt -nopervasives -nostdlib -stop-after middle_end -c \
      X.ml -drawfexpr-to X.fl

which writes `X.cmi` and `X.cmx` beside `X.fl`; the three are kept in
the directory of the build. Then, in that directory,

    flsemantics.exe -I . X.fl

The dune rules of this directory do so for every unit, compare the
term made with `X.fl` and what the tool prints with `X.expected`, and
fail on a difference:

    dune build --root=. --workspace=duneconf/main.ws \
      @middle_end/flambda2/tests/semantics/ocaml/pairs/runtest

The alias of `tests/semantics/` runs these rules with the others.

- As in the directory above, a unit is compiled with no standard
  library and no initially opened module, and declares the
  primitives it uses.
- The compiler finds `F.cmi` and `F.cmx` in the directory it is run
  in. The tool's Simplify looks for a `.cmx` in the directories given
  with `-I` and in no other: neither the standard library nor the
  directory it is run in. The rules of the directory above give it
  none, so what the tool prints of a unit there does not depend on
  any `.cmx`.
- The `.cmx` of a first unit is made by the build, with the compiler
  that builds the tool. What the tool prints of a second unit depends
  on that file, which is not kept: like `X.fl`, it moves with the
  compiler.

## What is claimed

Where its Simplify read a `.cmx`, the tool prints one line more,
after the name of the term:

    the tool's Simplify read the .cmx of: F

Every other line is a line of the directory above, and means what it
means there (`../README.md`, "What the verdicts mean"). Nothing is
said of the first unit, and nothing rests on what its `.cmx` says:

- The model is told nothing of what a `.cmx` says. A symbol of the
  first unit is an import whose contents are unknown, the symbol of
  its module block and the symbols of its closures alike, and a code
  id of the first unit is bound to nothing. So a load of a field of
  the first unit has no value, a call of one of its functions is
  undefined when it runs, and a second unit that does either as it
  is initialised is undefined in the model.
- A unit that has an import is run from its imports, and its verdict
  is one of the three labels of such a unit: "validated with its
  imports", which is the theorem from the imports
  (`FlambdaValidateImportsSpec.v`), whatever the imports are;
  "validated with nothing imported", followed by "not validated with
  its imports"; or "not validated". No line begins "validated:".
  That the term after is the one that the compiler makes with the
  `.cmx` at hand adds nothing to these and takes nothing from them:
  the validator is given the two terms and no `.cmx`.
- Where Simplify used what the `.cmx` says, the two terms differ by
  it, and the validator, which does not know it, does not accept the
  pair; where the unit is undefined before Simplify there is nothing
  to validate. That is what the pairs show today.

What the request goes on to, and is not here: a prefix of static
bindings, in front of both terms, that says of the symbols and the
code of the first unit what its `.cmx` says, with an entry of the
trust ledger for it; a verdict that rests on a prefix says so and is
counted apart.

The units of this directory are in none of the tables and counts of
`../README.md` and of `../census/README.md`, which are of units that
use no other unit.

## The pairs

| Second unit | First unit | What the second unit does | What the tool says of it |
|-------------|------------|---------------------------|--------------------------|
| `lengths_called_in_function.ml` | `lengths.ml` | a function calls a function of the first unit | both runs return the module block; the same; not validated |
| `lengths_called_at_toplevel.ml` | `lengths.ml` | a toplevel calls one | undefined before and after; nothing to validate |
| `lengths_included.ml` | `lengths.ml` | a toplevel reads the fields of the first unit and keeps them (`include`) | undefined before; after, returns a block of two imports; nothing to validate |
| `never_called.ml` | `never.ml` | calls a function that is never inlined, whose code has no body in the `.cmx`, in a function and at toplevel | undefined before and after; nothing to validate |
| `hidden_read.ml` | `hidden.ml` | a toplevel reads a field of which the `.cmx` says nothing, beside one that it knows | undefined before and after; nothing to validate |
| `parity_called.ml` | `parity.ml` | calls a function that is one of a set of two, in a function and at toplevel | undefined before and after; nothing to validate |
| `cycle_read.ml` | `cycle.ml` | a toplevel reads a block that the first unit made by calls of the runtime | undefined before and after; validated with its imports, with the line that says the validation says nothing of a unit whose term before is undefined |

In `lengths_called_in_function.ml` the unit only makes its closure, so
both runs are defined. The term before loads `length` from the module
block of the first unit and calls what it loaded. In the term after,
Simplify has inlined `length`, whose body the `.cmx` has, and left a
direct call of the code of `length_from`, which is recursive and has
no body there, with the symbol of its closure as the callee. The
validator sees a load and an indirect call on one side and a direct
call of code that nothing binds on the other.

The five units that have nothing to validate load from the module
block of the first unit, or call a function of it, as they are
initialised: the load has no value on an import. In
`lengths_included.ml` Simplify has put the symbols of the two
closures in the place of the loads, so the term after is defined and
returns them; in the four others the term after still loads a field
or calls code that nothing binds.

Of `cycle.ml` the `.cmx` says nothing that Simplify can use, so the
term after of `cycle_read.ml` is the term before simplified as a unit
of the directory above is, and the validator accepts the pair; the
unit is undefined all the same, as it loads from an import.

The first units `lengths.ml`, `never.ml`, `hidden.ml` and
`parity.ml` use no other unit; the tool says of each what it says of
a unit of the directory above, and each is validated.

`cycle.ml` is compiled and the tool is not run on it. Its two blocks
name each other, and the compiler makes them by four calls of C
functions of the runtime (`caml_alloc_dummy`, `caml_update_dummy`).
The model has no call of a C function, and the tool cannot read the
term at all: `-drawfexpr` prints such a call as `apply ccall (...)`
with no region, and the parser asks for one after `ccall`
(`middle_end/flambda2/parser/print_fexpr.ml`, at `C_call`;
`middle_end/flambda2/parser/flambda_parser.mly`, rule `call_kind`).
So the `.cmx` of that unit says nothing of its two fields, which
hold what the calls returned.
