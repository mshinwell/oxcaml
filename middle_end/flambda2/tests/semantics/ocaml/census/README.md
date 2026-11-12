# A count over generated units

The examples of the directory above are written by hand, and most are
written to validate. This is the other measure: units made at random,
with what the test tool says of each.

    sh census/run.sh <ocamlopt> <flsemantics.exe> 1 150 census-output

run from the directory above, makes for each seed from 1 to 150 one
unit of each profile (`gen.py`), makes its term (`from_ocaml.sh`), runs
the tool on it and prints the counts. Nothing here is run by the tests.

## What a generated unit is

One to three inlined functions of two integers and a boolean, each
returning an integer, a boolean, an option, a pair, a variant or a
record; then one to three values that call each of them and compute
with the results. The expressions are arithmetic and comparisons on
integers, boolean operators, conditionals, constructors and matches on
the variant, on options and on pairs, record fields, `let`, and
closures applied at once. There is no recursion, no loop, nothing
mutable, no float, no string and no exception, but in the two
profiles of the last section.

The profiles: `known` (every input is a constant), `unknown` (about a
quarter of the integer constants are behind `opaque`), `functions`
(as `unknown`, and the unit keeps one or two functions that are not
inlined). With `_scalar` the values of the unit are integers and
booleans only; without it, about four in ten are an option, a pair or
a variant, that is, a block that the unit keeps.

## The counts of 2026-11-12

Seeds 1 to 100 for the first three profiles, 1 to 150 for the two
scalar ones: 600 units. No unit on which the two runs differ, none
undefined before Simplify, none on which the tool gave no answer, none
that the conversion refused.

| Profile | Units | Validated | Not validated |
|---------|-------|-----------|---------------|
| `known_scalar` | 150 | 150 | 0 |
| `unknown_scalar` | 150 | 146 | 4 |
| `known` | 100 | 98 | 2 |
| `unknown` | 100 | 98 | 2 |
| `functions` | 100 | 96 | 4 |

588 of the 600 are validated. On the same 600 terms, earlier the
same day: 509 before the term after lost the continuations that are
applied once (`FlambdaValidateSpec.inline_once_applied_after`); 555
with that, and still 555 with the unused `Let`s of the parameters of
code removed from the term after; 577 with the tool guessing again
what was lifted where its first guess gave a symbol to a block that
nothing uses, and with the lifting out of the code of functions; 578
with the second asking (`unknown`, seed 30); and four more with the
constants lifted to the head of the unit and the parameters of
continuations unboxed where branches meet (`functions`, seeds 1, 55
and 69; `unknown_scalar`, seed 122). Sharing the loads marked
immutable changes none, and nor does the demotion of exception
handlers, which the generated units have not got; with the rounds
gone through again after it, the two units that were validated at the
second asking are validated at the first. Two more with two arms of
a `Switch` that give one continuation 0 and 1 made the tagging of
what is tested (`FlambdaMergeSwitchesSpec.merge_switches`;
`functions`, seed 5, and `unknown_scalar`, seed 38), and four more
with the applications of a continuation of no parameters whose
handler is one jump forwarded in the term after
(`FlambdaForwardJumpsSpec.forward_jumps`; `functions`, seeds 14, 27
and 72, the last at the second asking, and `unknown_scalar`, seed
100). Sharing the projections of value slots changes none, and nor
does the unboxing of parameters giving, for an untagging under a
test, the number that was tagged. No unit that was validated at one
of these points is not at a later one. The day before, 336 were
validated, 256 were not and 8 were not checked; of the units that
keep a function, none was.

What the 12 units that are not validated lack, read off the two
terms that the tool shows of each:

| What is missing | `unknown_scalar` (4) | The other three (8) |
|-----------------|----------------------|---------------------|
| A block that Simplify makes a symbol and the term before still makes with a `Let`: the block is made in a handler and Simplify binds the symbol outside it, or the guess of the tool does not find it | 0 | 7 |
| A `Switch` that Simplify removes with what it knows of the variable tested | 4 | 0 |
| A `Let` on the other side of the binding of a continuation whose handler does not use it | 0 | 1 |

The second row is two things, and a unit may have both. A `Switch`
on a variable that a `Switch` around it has tested is resolved
(seeds 57, 61 and 144). A match on a variant that was made where two
branches meet loses its tests where one branch gives a symbol of a
static block, which the unboxing of the validator does not read
under a test (seeds 1 and 144).

Five of the 600 have the constant `poison` after Simplify, which
unboxes a variant where two branches meet and gives the fields that a
branch has not got that constant. The conversion makes it the poison
of the model, so they are run and compared; three are validated
(`functions`, seeds 27 and 55; `unknown_scalar`, seed 100), and the
other two are in the second row.

In eight of the 12 the term before keeps a continuation that the
term after has not: the four of the second row, and four where a
handler only makes a block and goes on (Simplify makes the block a
symbol and has no use for the handler).

The first row is in the tool only: nothing is believed of its
guesses, and a better one needs no proof.

So, for units of this kind: when every input is known and the result
is a number, all are validated; with unknown inputs and numbers, 146
of 150; of the units that keep a function, 96 of 100.

## Two more profiles: exceptions, loops

`exceptions` is `unknown` with handlers: `try ... with _ ->`, `raise
Not_found`, `raise_notrace`, and `/` and `mod`, which raise where the
divisor is zero, under a handler; an inlined function may raise, and
is then called under a handler. `loops` is `unknown` with `for` loops
(up and down) and `while` loops on references, local recursive
functions (whose recursive call is a tail call or not), and one
recursive function that the unit keeps and exports. With `_scalar`
the values of the unit are integers and booleans, as above. A loop
goes round seven times at most, and loops are nested twice at most.

    sh census/run.sh <ocamlopt> <flsemantics.exe> 1 60 census-output \
      exceptions exceptions_scalar loops loops_scalar

Seeds 1 to 60 of each, 240 units, on 2026-11-12. No unit on which the
two runs differ, none undefined before Simplify, none on which the
tool gave no answer.

| Profile | Units | Validated | Not validated | Not checked |
|---------|-------|-----------|---------------|-------------|
| `exceptions` | 60 | 60 | 0 | 0 |
| `exceptions_scalar` | 60 | 57 | 3 | 0 |
| `loops` | 60 | 6 | 52 | 2 |
| `loops_scalar` | 60 | 10 | 50 | 0 |

The two that are not checked have a reference that a local function
captures: it stays a block with a field that is written
(`Block_set`).

What the 102 units with loops that are not validated lack. One unit
of each kind was read; the counts are of the units whose two terms,
as the tool shows them, differ by the same kinds of line, and a unit
may lack several.

- A `Let` on the other side of the binding of a continuation. In 57
  units the two terms have, once the names are erased, the same
  lines in another order, and most of the other 45 have this
  difference too. The common case is the return continuation of a
  call that does not use its parameter, as in

      let rec f n acc =
        if n <= 0 then acc else (let _ = f (n - 1) acc in n)

  The term before binds the continuation and then has the `Let` of
  `n - 1`; the term after has the `Let` first. Simplify cannot remove
  the parameter of a return continuation, so it makes a wrapper of
  the continuation at the call, below the `Let`s of the arguments,
  and the handler, which is then applied once, ends up there. Where
  the handler uses its parameter the two terms have the same order,
  and such a unit is validated.
- Code that the term after has twice (10 units). An inlined function
  with a local recursive function that captures one of its
  parameters, called twice. Simplify copies the code at each
  inlining, makes each closure a symbol and puts the constant of its
  value slot in its copy of the code; the term before has one piece
  of code and two closures.
- A closure with a value slot that is a variable, which Simplify
  makes a symbol in the handler where the variable is bound (4
  units), and a closure of no value slot that is not lifted under a
  handler in the code of a function (6 units).
- Static bindings on the other side of the binding of a
  continuation.
- A continuation that only applies another, as the return
  continuation of a call, which the term before keeps (7 units).

Of the three units with exceptions that are not validated, one has
the first difference. One has it too, with a comparison in the term
after whose result nothing uses, which the term before has lost. One
has, in the term after, a record that Simplify made a symbol and a
load of a field of that symbol, where the validator has the field:
the record is the result of a `try` whose handler gives another
record, and the handler turns out not to be reached.
