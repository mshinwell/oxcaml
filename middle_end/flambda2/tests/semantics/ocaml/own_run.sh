#!/bin/sh

# Compiles OCaml sources with the driver that checks the compiler's own run
# (../../tools/ownrun/flsemantics_ownrun.ml) and prints what the check says:
#
#   own_run.sh <flsemantics_ownrun.exe> X.ml
#
# As from_ocaml.sh compiles X.ml: with X.mli if it is beside X.ml, and as far
# as the middle end. See README.md, "The compiler's own run".
#
# Given more sources, it gives them all to one run of the driver, which
# checks one unit in a process and says so of the others (a control of
# ../own_run/ does that).

set -eu

if [ $# -lt 2 ]; then
  echo "usage: $0 <flsemantics_ownrun.exe> X.ml" >&2
  exit 2
fi

driver=$1
shift

case "$driver" in
/*) ;;
*) driver="$PWD/$driver" ;;
esac

# In a directory of its own, as the compiler writes X.cmi and X.cmx too, and
# under the name X.ml, as the names of anonymous functions have the name of
# the file as it is given. The driver is given -nostdlib and no -I. So,
# given one source, and where nothing else adds to the load path of the
# compiler (OCAMLPARAM), the compilation finds no .cmx file of another unit.
# Given more sources, the files written for one are there for the next.
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
files=
for source in "$@"; do
  dir=$(dirname "$source")
  name=$(basename "$source" .ml)
  cp "$source" "$work/$name.ml"
  if [ -f "$dir/$name.mli" ]; then
    cp "$dir/$name.mli" "$work/$name.mli"
    files="$files $name.mli"
  fi
  files="$files $name.ml"
done
cd "$work"
"$driver" -nopervasives -nostdlib -stop-after middle_end -c $files
