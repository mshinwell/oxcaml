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
cp "$work/$name.fl" "$target"
