# Units made from OCaml sources

Each `X.ml` here is a small OCaml program. `X.fl` is the Flambda 2 term
that the compiler makes of it for Simplify, and `X.expected` is what the
test tool (`../../tools/flsemantics.ml`) says of that term: it runs
Simplify on it, runs the term before and the term after on the machine
extracted from the Rocq semantics, and asks the extracted validator
whether the term after refines the term before
(`rocq/HACKING.md`, "Testing Simplify against the semantics").

## How a term is made

    sh from_ocaml.sh <ocamlopt> X.ml X.fl

which is, in a directory of its own,

    ocamlopt -nopervasives -nostdlib -stop-after middle_end -c \
      [X.mli] X.ml -drawfexpr-to X.fl

and then

    flsemantics.exe X.fl

The dune rules of this directory do both for every `X.ml` (with the
compiler that builds the tool, which is built from the same sources),
compare the term made with `X.fl` and what the tool prints with
`X.expected`, and fail on a difference:

    dune build --root=. --workspace=duneconf/main.ws \
      @middle_end/flambda2/tests/semantics/runtest

- `-drawfexpr` prints the unit after the conversion from Lambda (closure
  conversion) and before Simplify. The tool runs Simplify itself, with
  the default flags, on what the parser reads back.
- `-nopervasives -nostdlib`: the unit refers to no other unit, so each
  source declares the primitives it uses (`external ( + ) : int -> int ->
  int = "%addint"`). This changes nothing in what the front end makes of
  an expression.
- `X.mli` exports `result` only. A function that the unit exports is a
  field of the module block, and Simplify makes its closure a symbol.
  The validator follows that by making the closure a symbol in the term
  before (`exported_function.ml`, which has no interface file).
- A function whose inlining an example is about has `[@inline]`: with
  the default flags Simplify inlines only the smallest functions.
- A type annotation on a function (`let area : shape -> int = fun ...`)
  keeps its argument on the heap. Without it the compiler allocates an
  argument that does not escape on the stack, in a region, which the
  model has not got (`match_variant_local.ml`).

## What the verdicts mean

- **validated**: the extracted `validate_unit` accepted the pair. By
  `FlambdaValidateSpec.validate_unit_sound`, the unit after Simplify
  refines the unit before, run on its own from empty environments. This
  is a theorem about this compilation. It rests on what
  `rocq/TRUST-LEDGER.md` lists (the conversion of the compiler's terms
  to the model's) and, for a unit made from OCaml, on the printing of
  `-drawfexpr` and the fexpr parser: what is validated is the term the
  parser reads back, which is the term the compiler simplifies only as
  far as printing and parsing lose nothing.
  What the theorem observes at the exit is the continuation and its
  arguments, here the symbol of the unit; the contents of the module
  block are not part of the statement.
- **the same, not validated**: the two runs came to the same result,
  which is a test of one run and no proof. The validator could not make
  the two terms the same; the table says what it is missing.
- **not checked**: the conversion refused the unit, as it has something
  the model has not got.

## The examples

Steps are those of the machine, before and after Simplify.

| Source | What Simplify does | Steps | Verdict |
|--------|--------------------|-------|---------|
| `inline_function.ml` | inlines two calls of `square` | 20, 4 | validated |
| `constant_folding.ml` | inlines two functions, folds the arithmetic and two comparisons to 100 | 31, 1 | validated |
| `tuple_swap.ml` | a pair built, swapped and taken apart: no block is left | 19, 4 | validated |
| `closure_capture.ml` | inlines `make_adder` twice, makes the calls of the two closures direct, inlines them, reads the captured variable | 31, 4 | validated |
| `higher_order.ml` | inlines `twice`, then the function passed to it, twice | 32, 5 | validated |
| `match_variant.ml` | inlines `cells` three times and resolves the three matches: no test and no block is left | 66, 7 | validated |
| `option_default.ml` | the `Some` built and matched goes | 32, 3 | validated |
| `record_project.ml` | two records built by a function inlined twice, and read: none is left | 37, 8 | validated |
| `int64_boxed.ml` | removes every box around 64-bit integer arithmetic | 22, 8 | validated |
| `add_zero.ml` | makes `x + 0` into `x` | 8, 2 | the same, not validated: the validator folds a primitive applied to constants only, and knows no identity of arithmetic |
| `while_loop.ml` | a loop over two references, which the front end has made a recursive continuation; Simplify removes a tagging and untagging of the test, a continuation applied once and two parameters that are not used | 78, 45 | the same, not validated: the validator rewrites nothing inside the handler of a recursive continuation, and does not remove a parameter of a continuation |
| `tail_loop.ml` | makes the tail call of `sum` a jump, and the closure of `sum` a symbol | 128, 83 | the same, not validated: lifting to a symbol, and the loop |
| `factorial.ml` | makes the closure of `factorial` a symbol | 70, 46 | the same, not validated: lifting to a symbol |
| `mutual_recursion.ml` | makes the set of two closures static | 130, 70 | the same, not validated: lifting to symbols |
| `exported_function.ml` | inlines the call; the exported closure becomes a symbol | 14, 6 | validated, the closure lifted to a symbol in the term before |
| `exported_two_functions.ml` | two exported functions, the second calling the first: inlines the calls, makes both closures symbols, and removes from the second the value slot that held the first | 22, 10 | validated, the closures lifted to symbols and the unused value slot removed in the term before |
| `exported_table.ml` | an exported function that reads a field of a constant pair of the module, the field being a function: the code of the function, which stays, returns the symbol of that function, and the value slot that held the pair is removed | 13, 8 | validated, the closures and the pair lifted to symbols, the projection of the pair from the closure and the load from the pair folded in the code, and the unused value slot removed |
| `exported_capture.ml` | an exported function that uses a value of the module computed when the module runs: its closure becomes a symbol that holds the value in a value slot, its code is bound after the value is computed, and where the function is inlined the slot is read as the variable | 16, 5 | validated, the closure lifted to a symbol, the value slot read from the static closure, and the bindings of code moved up in both terms |
| `exported_apply.ml` | an exported function given to another exported function: inlines both calls; the call of the argument, once the first is inlined, is a call of the symbol of the function | 18, 9 | validated, the closures lifted to symbols and the indirect call of the symbol made a direct call of its code, which is then inlined |
| `exported_made.ml` | a pair made by an exported function that is called when the module runs: inlines the call, and makes the pair that the inlined call makes a symbol | 14, 6 | validated, in two liftings: the closure of the function in the term before as given, then the pair in the term that this gives once normalised |
| `exported_record.ml` | a record made by one exported function and read by another, both called when the module runs with an argument that is not known; the closures of the two functions become symbols | 23, 9 | validated, closures and blocks lifted to symbols in the term before |
| `exported_variant.ml` | a value of a variant type made when the module runs, with an argument that is not known, and an exported function that tests it, called on that value; the block and the closure become symbols | 17, 6 | validated, closures and blocks lifted to symbols in the term before |
| `exported_list.ml` | a list of three elements whose head is not known until the module runs; its cells become symbols | 9, 5 | validated, closures and blocks lifted to symbols in the term before |
| `exported_local_fun.ml` | an exported function with a function of its own inside, which it calls; its closure becomes a symbol | 8, 4 | validated, closures and blocks lifted to symbols in the term before |
| `exported_curried.ml` | an exported function of two arguments, called with both when the module runs | 14, 6 | validated, closures and blocks lifted to symbols in the term before |
| `exported_nested_pair.ml` | a constant pair of pairs, and an exported function that reads a field of a field of it | 10, 7 | validated, closures and blocks lifted to symbols in the term before, and the loads from the constants of the module folded in the code of the function |
| `exported_funs_in_pair.ml` | two functions in a pair, and an exported function that calls the first | 14, 11 | validated, closures and blocks lifted to symbols in the term before, and unused value slots removed |
| `exported_chain.ml` | three exported functions, each calling the one before twice | 14, 10 | validated, closures and blocks lifted to symbols in the term before, and unused value slots removed |
| `exported_string_length.ml` | a constant string of the module, and an exported function that returns its length | 8, 5 | validated, closures and blocks lifted to symbols in the term before, and the length of the constant computed in the code of the function |
| `exported_record_update.ml` | a constant record, an exported function that makes a record from another with one field changed, and a call of it on the constant when the module runs | 14, 6 | validated, closures and blocks lifted to symbols in the term before |
| `exported_bool.ml` | an exported predicate, and an exported function that uses it on each of its two arguments with `&&` | 11, 7 | validated, closures and blocks lifted to symbols in the term before, and unused value slots removed |
| `exported_after_effect.ml` | a value that is not known until the module runs, then an exported function, then a call of the function on the value | 15, 6 | validated, closures and blocks lifted to symbols in the term before |
| `exported_twice_kept.ml` | a function that takes a function and is always inlined, given an exported function that is never inlined: the two calls of the argument, in the code of the function that gives it, stay, as direct calls | 14, 10 | the same, not validated: in the term before the indirect calls of the symbol of the argument are made direct in the code, as Simplify leaves them; the validator then inlines them in the term after, where the code called is bound around the code of the caller, and not in the term before, where the two are in one group. To be validated with a list of code not to inline, which leaves the calls on both sides (on a trial of that list over this series it is, and it is not there without the calls made direct). Inlining between the code of one group makes the two sides inline the same calls and is not enough alone: the term after is left with a continuation applied once and an alias that nothing uses |
| `exported_compose_kept.ml` | the composition of two exported functions that are never inlined, by a function that is always inlined: the two calls stay, in the code of the composition, as direct calls | 17, 13 | the same, not validated: as `exported_twice_kept.ml` |
| `exported_branch_then_fun.ml` | a value chosen by a test that is not resolved when the module runs, then an exported function that uses it: the closure of the function becomes a symbol that holds the value in a value slot, and the symbol and its code are bound in the handler of the continuation that the test goes to | 14, 8 | validated, the closure lifted to a symbol in the term before and all the code of the term after bound first |
| `exported_match_then_fun.ml` | a value taken out of an option that is not known, then a predicate that uses it: as the one before, after a match | 21, 12 | validated, as the one before |
| `exported_branch_two_funs.ml` | a value chosen by a test, then two functions, the second calling the first: inlines the call; both closures become symbols, bound with their code in the handler | 17, 11 | validated, the closures lifted to symbols, the unused value slot removed and the code of the term after bound first |
| `exported_fun_branch_fun.ml` | a function, then a value chosen by a test, then a function that uses both: the code of the second function, with the call of the first inlined, is bound in the handler | 17, 11 | validated, as the one before |
| `exported_two_branches.ml` | two values, each chosen by a test, with a function after each, the second function calling the first: the code of each function is bound in the handler of its test, the second handler inside the first | 23, 15 | validated, as the one before |
| `exported_branch_pair.ml` | one of two constant pairs chosen by a test, then a function that reads it: the pairs become symbols, and the closure a symbol that holds the one chosen | 15, 10 | validated, the closure lifted to a symbol in the term before and the code of the term after bound first |
| `exported_branch_calls_twice.ml` | as `exported_branch_two_funs.ml`, the second function calling the first twice: inlines both calls, and reads the value slot of the first closure once | 17, 11 | the same, not validated: with the two calls inlined in the term before the validator reads the value slot twice, and it shares no primitive |
| `match_variant_local.ml` | | | not checked: `Begin_region`, `End_region` and a local allocation |
