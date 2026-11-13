#!/bin/sh

# What from_ocaml.sh says of a source:
#
#   says.sh <from_ocaml.sh> <ocamlopt> <X.ml>
#
# prints "made" if the script makes the text of the unit, and otherwise what
# the script printed, then "refused".

set -u

script=$1
ocamlopt=$2
source=$3

made=$(mktemp)
said=$(mktemp)
trap 'rm -f "$made" "$said"' EXIT
if sh "$script" "$ocamlopt" "$source" "$made" 2>"$said"; then
  echo made
else
  cat "$said"
  echo refused
fi
