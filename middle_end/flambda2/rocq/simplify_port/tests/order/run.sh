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

# run.sh WHICH COMPILER [ARGUMENT ...] : the tests of the order of
# evaluation. It follows no file of the compiler.
#
# WHICH is oxcaml or upstream: which answer is expected. COMPILER is a
# native compiler of OCaml (ocamlopt, ocamlopt.opt), by its name on the PATH
# or by its path; the ARGUMENTs are given to it before the name of the file
# (a compiler that is not installed needs to be told where its standard
# library is: -nostdlib -I DIR ...).
#
# labels.ml and pipe.ml are compiled with it in a new temporary directory,
# and run. What they print is compared with expected.WHICH.txt. Prints what
# they printed, and one line that says whether it is what is expected. Exit
# status 0 if it is; 1 if it is not, or a file was not compiled, or a
# program failed; 2 if the arguments are not right. Nothing is written in
# the folder of the port.
#
# WHAT THE TWO ANSWERS SAY. An application evaluates its arguments from the
# last PARAMETER to the first, whatever order the call writes them in: both
# compilers. A pipe whose right side is an application (x |> f ~l:e, and
# f ~l:e @@ x) is, for OxCaml, the ONE application f x ~l:e: an argument of
# the right side that is for a parameter AFTER the piped one is evaluated
# BEFORE the piped value. Upstream OCaml evaluates the piped value first.
# README.md of this folder says with which compilers this was seen.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
if [ $# -lt 2 ] || [ ! -f "$here/expected.$1.txt" ]; then
  echo "usage: tests/order/run.sh oxcaml|upstream COMPILER [ARGUMENT ...]"; exit 2
fi
which=$1; shift
if ! command -v "$1" > /dev/null; then echo "run.sh: $1 is not a program"; exit 2; fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp "$here/labels.ml" "$here/pipe.ml" "$work"
cd "$work"
failed=0
for t in labels pipe; do
  echo "== $t.ml" >> got.txt
  if "$@" "$t.ml" -o "$t.exe" > "$t.log" 2>&1 && "./$t.exe" >> got.txt 2>> "$t.log"; then :
  else echo "run.sh: $t.ml was not compiled, or its program failed:"; cat "$t.log"; failed=1; fi
done
cat got.txt
if [ $failed = 0 ] && cmp -s got.txt "$here/expected.$which.txt"; then
  echo "run.sh: this is what is expected of $which (expected.$which.txt)"
else
  echo "run.sh: this is NOT what is expected of $which:"
  diff "$here/expected.$which.txt" got.txt || true
  exit 1
fi
