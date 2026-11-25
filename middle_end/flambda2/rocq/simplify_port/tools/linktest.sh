#!/bin/bash
#******************************************************************************
#*                                  OxCaml                                    *
#* -------------------------------------------------------------------------- *
#*                               MIT License                                  *
#*                                                                            *
#* Copyright (c) 2026 Jane Street Group LLC                                   *
#* opensource-contacts@janestreet.com                                         *
#*                                                                            *
#* Permission is hereby granted, free of charge, to any person obtaining a    *
#* copy of this software and associated documentation files (the "Software"), *
#* to deal in the Software without restriction, including without limitation  *
#* the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
#* and/or sell copies of the Software, and to permit persons to whom the      *
#* Software is furnished to do so, subject to the following conditions:       *
#*                                                                            *
#* The above copyright notice and this permission notice shall be included    *
#* in all copies or substantial portions of the Software.                     *
#*                                                                            *
#* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
#* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
#* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
#* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
#* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
#* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
#* DEALINGS IN THE SOFTWARE.                                                  *
#******************************************************************************

# linktest.sh swap TREE | sums TREE CONTEXT | differ SUMS1 SUMS2
#
# The link test of the port: the compiler built with the extracted files in
# the place of middle_end/flambda2/simplify/. It follows no file of the
# compiler. Run in the folder of the port. TREE is a SCRATCH work tree of
# the compiler (never commit it): this script changes files of the compiler
# there.
#
#   swap TREE      in TREE/middle_end/flambda2/simplify: each DIR/foo.ml is
#                  replaced by extracted/DIR/foo.ml of this folder (the .mli
#                  files stay); runtime/port_monad.ml and the empty
#                  runtime/port_abbreviations.ml are added; in the dune
#                  file the library gets -nolabels (the extracted text has
#                  no labels) and -w -a (no warning is an error).
#   sums TREE CTX  the MD5 of every object file under TREE/_build/CTX that
#                  is not of the library flambda2_simplify, sorted by path.
#   differ A B     the paths whose sums differ between two such lists, and
#                  the paths that only one of the lists has.
#
# The test: build the compiler in TREE (make boot-compiler; make compiler),
# keep `sums TREE main`; then swap, build again, and take the sums again.
# After the swap the compiler of stage 1 holds the extracted Simplify, and
# it compiles every file of stage 2: an object file of stage 2 that differs
# is a file that the two Simplifys do not treat alike.
#
# A command whose output is used here stands alone, with its output in a
# variable or in a file, and not in a pipe, in <( ) or in the list of a
# for: there its failure would be lost, and a list that could not be made
# would be an empty list (two lists that are not there differ in nothing).
# An empty list is refused.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
case "${1:-}" in
swap)
  tree=${2:-}; s=$tree/middle_end/flambda2/simplify
  [ -d "$s" ] || { echo "no $s"; exit 2; }
  n=0
  files=$(cd "$here/extracted" && find . -name '*.ml')
  [ -n "$files" ] || { echo "no file .ml under $here/extracted"; exit 1; }
  for f in $files; do
    f=${f#./}
    [ -e "$s/$f" ] || { echo "no file $s/$f"; exit 1; }
    cp "$here/extracted/$f" "$s/$f"; n=$((n+1))
  done
  cp "$here/runtime/port_monad.ml" "$s/port_monad.ml"
  cp "$here/runtime/port_abbreviations.ml" "$s/port_abbreviations.ml"
  grep -q -- '-nolabels' "$s/dune" || \
    sed -i '0,/^  (:standard$/s//  (:standard\n   -nolabels\n   -w\n   -a/' "$s/dune"
  grep -q -- '-nolabels' "$s/dune" || { echo "the dune file was not changed"; exit 1; }
  echo "swapped $n files in $s; port_monad.ml and port_abbreviations.ml added; dune file: -nolabels -w -a"
  ;;
sums)
  tree=$2; ctx=$3
  cd "$tree/_build/$ctx"
  find . -name '*.o' ! -path '*flambda2_simplify*' ! -path './.sandbox/*' > "$tmp/paths"
  [ -s "$tmp/paths" ] || { echo "no object file under $tree/_build/$ctx" >&2; exit 1; }
  LC_ALL=C sort "$tmp/paths" > "$tmp/sorted"
  xargs md5sum < "$tmp/sorted"
  ;;
differ)
  # every path of either list: its two sums, "-" where a list has no such path
  a=$2; b=$3
  sort -k2 "$a" > "$tmp/a"
  sort -k2 "$b" > "$tmp/b"
  [ -s "$tmp/a" ] || { echo "the list $a is empty" >&2; exit 1; }
  [ -s "$tmp/b" ] || { echo "the list $b is empty" >&2; exit 1; }
  join -j 2 -a 1 -a 2 -e - -o 0,1.1,2.1 "$tmp/a" "$tmp/b" > "$tmp/both"
  awk '$2!=$3{ if ($2=="-") print $1 " (only in the second list)";
               else if ($3=="-") print $1 " (only in the first list)";
               else print $1 }' "$tmp/both"
  ;;
*) echo "usage: linktest.sh swap TREE | sums TREE CONTEXT | differ SUMS1 SUMS2"; exit 2;;
esac
