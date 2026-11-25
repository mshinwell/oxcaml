# The port of Simplify: first lemmas

This folder holds statements that Rocq proves about the ported files as the
real monad reads them (`monad/real/Port_monad.v`). THEY ARE FIRST LEMMAS,
NOT A SPECIFICATION. No file here says what Simplify computes. Most of the
lemmas say what one handler of one ported function does with one end of its
body. They show that the ported text can be reasoned about with the laws of
`monad/real/Kit_laws.v`, and what such a proof has to assume.

## What a lemma here says, and what it does not

- It is a statement about the Rocq definition that `make real` compiles.
  That OCaml's run of the extracted file ends as the Rocq run does is NOT
  proved (`GUIDE.md`, section 8).
- It is for every fuel, and it says nothing of a run that is out of fuel: a
  statement of the form `spec` or `wp` holds of such a run whatever it
  says.
- What it assumes of a parameter is a CONTRACT (`contracts/README.md`): a
  premise of the lemma, which the head of the file names. No file here has
  an `Axiom` or a `Parameter`. `Print Assumptions NAME.` after a lemma
  lists the parameters that it rests on: those of the kit and of the
  declarations that the ported function calls.

No tool checks these three sentences against a file; `make real` checks
that Rocq accepts each proof.

## The files

A file `proofs/DIR/Foo_WHAT.v` holds lemmas about the ported file
`DIR/Foo.v`. It requires the ported file itself (never a declaration in
its place), the laws, and the contracts that it needs. It is compiled by
`make real` only; nothing of it is extracted, and no ported file requires
one.

| file | about | assumes |
|---|---|---|
| `Simplify_simple_handlers.v` | the three handlers of `Simplify_simple.v`: which end of the body each takes, which it lets pass | two lemmas: the name of the file's exception. The others: nothing |
| `unboxing/Unboxing_epa_exceptions.v` | `Invalid_apply_cont`, declared in `decl/Unboxing_epa.v` and again in `unboxing/Unboxing_epa.v`: a handler for the one takes what a raise of the other raises | the names of the exceptions |
| `env/Continuation_uses_handlers.v` | `add_use` of `env/Continuation_uses.v`, whose handler prints a context and raises the fatal error again: what it returns; and that it returns or ends in a fatal error | the first: the contract of `Printexc.raise_with_backtrace`. The second: that, the contract of `Printexc.get_raw_backtrace`, and six premises about the calls of `add_use` |
| `unboxing/Is_unboxing_beneficial_recursion.v` | `filter_non_beneficial_decisions` of `unboxing/Is_unboxing_beneficial.v`, a function with a fuel: the one case that makes no call | nothing |

## How to write one

1. Unfold the function. For a statement about one run, rewrite with the
   equations of `Kit_laws.v`, section 3 (`run_bind`, `run_try_with`,
   `run_match_exn`). For a statement about every run, state it with `spec`
   and apply the rules of section 5 (`wp_bind`, `wp_try_with`,
   `wp_match_exn`, ..): each takes the next operation from the goal.
2. A call of a declared function is a parameter. Without a contract, only
   `wp_any` applies to it: whatever it returns, whatever it raises. With
   `returns_or_fatal` of the call, `wp_returns_or_fatal`.
3. An exception: `exn_match_make` when the handler's exception is the one
   that is raised; `exn_other` or `fatal_passes` when it is another, from
   the names (a contract for each declared exception).
4. A function with a fuel: the statement is for every fuel of the
   function. Where the fuel is out there is nothing to prove
   (`wp_out_of_fuel`, `wp_recursive`); a statement about the recursive
   calls is by induction on the fuel (`fuel_induction`). No lemma here
   uses the induction yet: the recursive calls of
   `filter_non_beneficial_decisions` stand inside functions that it gives
   to declared functions (`List.fold_left_map`, `List.map`, the maps), and
   a statement about those cases needs contracts of them.
