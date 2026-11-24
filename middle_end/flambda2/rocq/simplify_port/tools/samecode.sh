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

# samecode.sh REV : run in the folder of the port, with CMI_ROOT set as for
# make. Compares the extracted files of this folder with those of the commit
# REV: each file of both is compiled as tools/check.sh compiles it, and the
# bytecode instructions that ocamlc makes of it (-dinstr) are compared. The
# instructions hold no name of a variable and no spelling of a module, so a
# change that only writes names otherwise (an abbreviation of a module, a
# constructor without its module, a variable without its number) gives the
# same instructions; a change of what a function does gives others. The
# places of assertions (file, line) are made blank. Prints the count, and the
# files whose instructions differ; exit status 1 if any does. It follows no
# file of the compiler.
set -e
rev=$1
[ -n "$rev" ] || { echo "usage: tools/samecode.sh REV"; exit 2; }
[ -n "$CMI_ROOT" ] || { echo "CMI_ROOT is not set"; exit 2; }
OCAMLC=${OCAMLC:-ocamlc.opt}; export OCAMLC CMI_ROOT
here=$(pwd); simplify=../../simplify
tmp=$here/_build/samecode; rm -rf "$tmp"; mkdir -p "$tmp/old" "$tmp/new"
prefix=$(git rev-parse --show-prefix)
(cd "$(git rev-parse --show-toplevel)" && git archive "$rev:${prefix%/}" extracted runtime) \
  | tar -x -C "$tmp/old"
mkdir -p "$tmp/new/src"; cp -r extracted runtime "$tmp/new/src/"
mkdir -p "$tmp/old/src"; mv "$tmp/old/extracted" "$tmp/old/runtime" "$tmp/old/src/"
for side in old new; do
  for r in "$tmp/$side/src/runtime"/port_*.ml; do
    RUNTIME="$tmp/$side/rt" tools/check.sh --runtime "$r" > /dev/null
  done
  for f in $(cd "$tmp/$side/src/extracted" && find . -name '*.ml' | sed 's|^\./||' | sort); do
    mkdir -p "$tmp/$side/instr/$(dirname "$f")"
    RUNTIME="$tmp/$side/rt" tools/check.sh --instr "$tmp/$side/src/extracted/$f" $simplify \
      "$tmp/$side/instr/${f%.ml}.instr" || { echo "samecode: $side: $f does not compile"; exit 1; }
  done
done
n=0; d=0
for f in $(cd "$tmp/new/instr" && find . -name '*.instr' | sed 's|^\./||' | sort); do
  n=$((n+1))
  if [ ! -e "$tmp/old/instr/$f" ]; then d=$((d+1)); echo "samecode: only now: ${f%.instr}.ml"
  elif ! cmp -s "$tmp/old/instr/$f" "$tmp/new/instr/$f"; then
    d=$((d+1))
    echo "samecode: OTHER INSTRUCTIONS: extracted/${f%.instr}.ml ($(diff "$tmp/old/instr/$f" "$tmp/new/instr/$f" | grep -c '^[<>]') lines differ)"
  fi
done
echo "samecode: $n extracted files against $rev: $((n-d)) with the same instructions, $d with others"
[ $d = 0 ]
