#!/bin/sh

# Compiles a unit of a pair as far as the middle end, and keeps what a second
# unit and the test tool need of it (see README.md):
#
#   from_ocaml.sh <ocamlopt> <X.ml> <X> [<F>]
#
# Made in the current directory: X.fl.made, the term that the compiler gives
# to Simplify, as -drawfexpr prints it; and X.cmi and X.cmx, which the
# compiler writes. With <F>, the unit is compiled against F.cmi and F.cmx,
# which are in the current directory.
#
# As in the directory above, the unit is compiled with no standard library
# and no initially opened module, and the compilation stops after the middle
# end.

set -eu

ocamlopt=$1
source=$2
name=$3
first=${4:-}

case "$ocamlopt" in
/*) ;;
*) ocamlopt="$PWD/$ocamlopt" ;;
esac

# In a directory of its own, and under the name X.ml, as the names of
# anonymous functions have the name of the file as it is given. The compiler
# looks for the .cmi and the .cmx of the first unit in the directory it is
# run in.
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp "$source" "$work/$name.ml"
if [ -n "$first" ]; then
  cp "$first.cmi" "$first.cmx" "$work/"
fi
(cd "$work" &&
  "$ocamlopt" -nopervasives -nostdlib -stop-after middle_end -c \
    "$name.ml" -drawfexpr-to "$name.fl")
cp "$work/$name.fl" "$name.fl.made"
cp "$work/$name.cmi" "$work/$name.cmx" .
