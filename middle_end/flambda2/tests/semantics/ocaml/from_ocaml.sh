#!/bin/sh

# Makes of an OCaml source the term that the compiler gives to Simplify, in
# the syntax that the test tool reads (see README.md):
#
#   from_ocaml.sh <ocamlopt> <X.ml> <target>
#
# The unit is compiled with no standard library and no initially opened
# module, so that it needs nothing but itself, and with X.mli if that is
# beside it. The compilation stops after the middle end: what is printed is
# what -drawfexpr prints, the unit as it is after the conversion from Lambda
# and before Simplify.
#
# A unit is refused if the text loses of its term something that the tool
# cannot give back (see below): the test of being an integer that is for any
# value, unless generic_is_int.txt names the unit; a call that is a probe.

set -eu

ocamlopt=$1
source=$2
target=$3

case "$ocamlopt" in
/*) ;;
*) ocamlopt="$PWD/$ocamlopt" ;;
esac

dir=$(dirname "$source")
name=$(basename "$source" .ml)

# In a directory of its own, as the compiler writes X.cmi and X.cmx too, and
# under the name X.ml, as the names of anonymous functions have the name of
# the file as it is given.
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp "$source" "$work/$name.ml"
interface=
if [ -f "$dir/$name.mli" ]; then
  cp "$dir/$name.mli" "$work/$name.mli"
  interface="$name.mli"
fi
(cd "$work" &&
  "$ocamlopt" -nopervasives -nostdlib -stop-after middle_end -c \
    $interface "$name.ml" -drawfexpr-to "$name.fl")

# The text writes the two tests of being an integer alike, and its reader
# gives the one that is for variants (label C2-26). So the unit is compiled
# once more, for what -drawflambda prints of the term before Simplify, which
# is kept in a file; and a unit whose term has the other test, printed as
# Is_int_generic, is refused unless generic_is_int.txt, beside the source,
# names it. Nothing is given back of a unit that is refused, or whose second
# compilation fails or prints no term.
if ! (cd "$work" &&
  "$ocamlopt" -nopervasives -nostdlib -stop-after middle_end -c \
    $interface "$name.ml" -drawflambda >"$name.raw" 2>&1); then
  cat "$work/$name.raw" >&2
  echo "$name.ml: the compilation that prints the term failed" >&2
  exit 1
fi
if ! grep -q 'module_symbol' "$work/$name.raw"; then
  echo "$name.ml: -drawflambda printed no term" >&2
  exit 1
fi
if grep -q 'Is_int_generic' "$work/$name.raw"; then
  if ! grep -qx "$name" "$dir/generic_is_int.txt"; then
    echo "$name.ml: the term that the compiler gives to Simplify has" >&2
    echo "Is_int_generic, the test of being an integer that is for any" >&2
    echo "value. The text writes it as the test that is for variants, and" >&2
    echo "it is read as that one: the unit read is not the compiler's." >&2
    echo "generic_is_int.txt says how such a unit may be kept." >&2
    exit 1
  fi
fi

# What the compiler printed, as one line with single spaces: it cuts what it
# prints into lines by their width.
tr '\n' ' ' <"$work/$name.raw" | tr -s ' ' >"$work/$name.line"

# The text does not say that a call is a probe, and the call is read as a
# plain one (label C2-17); the program runs the handler of a probe only while
# the probe is enabled. The compiler prints "(probe NAME)" in a call that is
# one and "(probe ())" in any other. A unit whose term has one is refused.
if grep -q '(probe [^(]' "$work/$name.line"; then
  echo "$name.ml: the term that the compiler gives to Simplify has a call" >&2
  echo "that is a probe. The text does not say so, and the call is read" >&2
  echo "as a plain call, which is always made: the unit read is not the" >&2
  echo "compiler's." >&2
  exit 1
fi

cp "$work/$name.fl" "$target"
