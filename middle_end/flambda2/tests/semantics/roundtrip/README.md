# The conversion of the test tool, through fexpr and back

`../../tools/flsemantics.exe -round-trip X.fl` converts the unit of
`X.fl` to a term of the Rocq model, prints that term as fexpr
(`../../tools/flmodel_to_fexpr.ml`), reads the text again with the
compiler's parser, converts what it read, and compares the two terms of
the model with the model's comparison (`../../tools/flroundtrip.ml`). It
does the same of the unit that Simplify makes of the one in the file.
The rules of this directory run it on every example of the directory
above and of `../ocaml`; `dune` says how the answers are checked.

The conversion is trusted (`rocq/TRUST-LEDGER.md`). What this adds is a
second reading of each of its cases, in the other direction, and a
check that the two agree on every example: a case that the conversion
gets wrong in a way that is not the same both times is found. It does
not find what the conversion drops and the printer does not put back.

## Answers that are not "round trip the same"

Each has a file here with what the tool prints, and its reason below.

- `kinds_direct_naked.expected`, the unit after Simplify. Simplify
  makes the call of `$Add_naked` a direct call of its code, at the
  arity of two naked immediates. The printer writes that arity; the
  parser of fexpr gives a direct call the arity of as many values as
  it has arguments, whatever is written
  (`middle_end/flambda2/parser/fexpr_to_flambda.ml`, the case of
  `Function (Direct ...)`; discrepancies C2-5 and R2-12). So the unit
  read back is not the unit printed. A limit of fexpr, not of the
  conversion: the example is there to show it.

## What cannot be printed

`flmodel_to_fexpr.ml` lists at its head what it refuses, with the
reason for each. No example meets one today.

## The constant `poison`

Simplify unboxes a variant where two branches meet, and gives the
fields that a branch has not got the constant `poison`; eight examples
of `../ocaml` that the tool converts have it after Simplify
(`option_join.fl` and seven whose names end in `_heap.fl`). The
conversion makes that constant of the model, which keeps its kind and
no name. The printer writes it as
`poison.KIND."poison"`, with the quotes in the name that it gives the
printer of fexpr: that printer writes the name of a poison constant as
it is (`middle_end/flambda2/parser/print_fexpr.ml`), and the parser
reads a string there (`middle_end/flambda2/parser/flambda_parser.mly`,
the rule `const`), so a poison constant printed with the name that the
compiler gave it is not read back (discrepancy C2-14).

A poison constant whose kind is a naked `int8`, a naked `int16` or
`mask` is printed all the same and is not read back today: the
printer of fexpr writes those three kinds and the parser has no rule
for them (`flambda_parser.mly`, the rule `naked_number_kind`;
discrepancy R6-1). No example has one.
