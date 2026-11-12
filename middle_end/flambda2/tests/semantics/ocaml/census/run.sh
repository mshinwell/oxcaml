#!/bin/sh

# Makes random units (gen.py), has the test tool check each, and counts what
# it says:
#
#   run.sh <ocamlopt> <flsemantics.exe> <first seed> <count> <directory> \
#     [profile ...]
#
# from the directory above this one. The units, their terms and what the tool
# printed are left in the directory given. See README.md.

set -eu

ocamlopt=$1
tool=$2
first=$3
count=$4
out=$5
shift 5
profiles=${*:-known unknown functions known_scalar unknown_scalar}

here=$(dirname "$0")
mkdir -p "$out"
: >"$out/verdicts.txt"
seed=$first
while [ "$seed" -lt $((first + count)) ]; do
  for profile in $profiles; do
    python3 "$here/gen.py" "$seed" "$profile" "$out"
    unit=$out/c_${profile}_$(printf %04d "$seed")
    if sh "$here/../from_ocaml.sh" "$ocamlopt" "$unit.ml" "$unit.fl" \
      >"$unit.log" 2>&1; then
      code=0
      timeout 60 "$tool" "$unit.fl" >"$unit.out" 2>&1 || code=$?
      if [ "$code" = 124 ]; then
        verdict="no answer in 60 seconds"
      elif grep -q "DIFFERENT" "$unit.out"; then
        verdict="THE RUNS DIFFER"
      elif grep -q "not checked" "$unit.out"; then
        verdict="not checked: $(sed -n \
          's/.*not checked: the model has not got \([a-z ]*[A-Za-z_]*\).*/\1/p' \
          "$unit.out" | head -1)"
      elif grep -q "undefined" "$unit.out"; then
        verdict="undefined before Simplify"
      elif grep -q "not decided" "$unit.out"; then
        verdict="not decided"
      else
        verdict=$(tail -1 "$unit.out" | sed 's/^ *//')
      fi
    else
      verdict="does not compile"
    fi
    echo "$profile | $verdict" >>"$out/verdicts.txt"
  done
  seed=$((seed + 1))
done
sort "$out/verdicts.txt" | uniq -c | sort -k2,2 -k1,1nr
