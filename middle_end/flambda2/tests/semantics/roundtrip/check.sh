#!/bin/sh

# What the tool printed for an example that has no expected file here (see
# dune): two lines, the first for the unit of the file and the second for
# the unit after Simplify, each saying that the round trip is the same, or
# that the unit is not converted, which says why itself. Anything else, a
# line that is missing included, is to be recorded with its reason.

set -eu

ok=true
lines=0
# The second test of the loop is for a last line that does not end in a
# newline, which [read] gives and answers false for.
while IFS= read -r line || [ -n "$line" ]; do
  lines=$((lines + 1))
  case "$lines" in
  1)
    case "$line" in
    *", after Simplify: "*) ok=false ;;
    *": round trip the same") ;;
    *": not converted: "*) ;;
    *) ok=false ;;
    esac
    ;;
  2)
    case "$line" in
    *", after Simplify: round trip the same") ;;
    *", after Simplify: not converted: "*) ;;
    *) ok=false ;;
    esac
    ;;
  *) ok=false ;;
  esac
done <"$1"
if [ "$lines" -ne 2 ]; then
  ok=false
fi

if ! $ok; then
  name=$(basename "$1" .output)
  cat "$1"
  echo "The round trip of this example is not the same, before and after"
  echo "Simplify. If that is a limit that is known, record what is printed"
  echo "above in"
  echo "middle_end/flambda2/tests/semantics/roundtrip/$name.expected, and the"
  echo "reason in README.md beside it."
  exit 1
fi
