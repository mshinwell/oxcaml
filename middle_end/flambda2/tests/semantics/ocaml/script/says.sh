#!/bin/sh

# What from_ocaml.sh says of a source:
#
#   says.sh <from_ocaml.sh> <ocamlopt> <X.ml> [<directory>]
#
# prints "made" if the script makes the text of the unit, and otherwise what
# the script printed, then "refused". The directory, if there is one, is that
# of the standard library, which the script is then given.

set -u

script=$1
ocamlopt=$2
source=$3
library=${4-}

made=$(mktemp)
said=$(mktemp)
trap 'rm -f "$made" "$said"' EXIT
# The directory is passed on as one argument, and not at all if there is none.
if sh "$script" "$ocamlopt" "$source" "$made" ${library:+"$library"} \
  2>"$said"; then
  echo made
else
  cat "$said"
  echo refused
fi
