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
# make. Compares the extracted files and the runtime of this folder with
# those of the commit REV: each file of either is compiled as tools/check.sh
# compiles it, and the bytecode instructions that ocamlc makes of it (-dinstr)
# are compared. The instructions hold no name of a variable and no spelling
# of a module, so a change that only writes names otherwise (an abbreviation
# of a module, a constructor without its module, a variable without its
# number) gives the same instructions. Prints the counts, and the files whose
# instructions differ or that only one side has; exit status 1 if there is
# any.
#
# WHAT THE SAME INSTRUCTIONS SAY, and what they do not. They say that ocamlc,
# with the flags of tools/check.sh, makes the same bytecode of the two texts
# of a file. BOTH sides are compiled now, by this folder's tools/check.sh,
# against the same compiled interfaces (CMI_ROOT) and the same .mli files of
# this tree: not against the compiler as it was at REV. They do NOT say that
# a constructor written without its module is the constructor of the same
# type as before: constructors of two types can have the same instructions.
# They say nothing of native code, and they are not a proof about the
# program. Two kinds of places are made blank before the comparison, and
# nothing else (tools/check.sh --instr): the places of failed assertions and
# the texts of `__LOC__`, which change when lines move; the last line says
# how many. Not part of make.
#
# Of the compiler it reads what tools/check.sh reads: the compiled interfaces
# under CMI_ROOT and the .mli files of ../../simplify. It follows no file of
# the compiler.
set -e
rev=$1
[ -n "$rev" ] || { echo "usage: tools/samecode.sh REV"; exit 2; }
[ -n "$CMI_ROOT" ] || { echo "CMI_ROOT is not set"; exit 2; }
[ -d "$CMI_ROOT/middle_end/flambda2/simplify/.flambda2_simplify.objs/byte" ] \
  || { echo "samecode: no compiled interfaces under CMI_ROOT=$CMI_ROOT"; exit 2; }
OCAMLC=${OCAMLC:-ocamlc.opt}; export OCAMLC CMI_ROOT
here=$(pwd); simplify=../../simplify
tmp=$here/_build/samecode; rm -rf "$tmp"; mkdir -p "$tmp/old" "$tmp/new"
prefix=$(git rev-parse --show-prefix)
(cd "$(git rev-parse --show-toplevel)" && git archive "$rev:${prefix%/}" extracted runtime) \
  | tar -x -C "$tmp/old"
mkdir -p "$tmp/new/src"; cp -r extracted runtime "$tmp/new/src/"
mkdir -p "$tmp/old/src"; mv "$tmp/old/extracted" "$tmp/old/runtime" "$tmp/old/src/"
# has_instr FILE : the instructions are there (not empty, not the word of a
# check that was skipped).
has_instr() { [ -s "$1" ] && ! grep -qx skipped "$1" && [ -s "$1.places" ]; }
for side in old new; do
  mkdir -p "$tmp/$side/instr/runtime" "$tmp/$side/instr/extracted"
  for r in "$tmp/$side/src/runtime"/port_*.ml; do
    RUNTIME="$tmp/$side/rt" tools/check.sh --runtime "$r" > /dev/null
    o="$tmp/$side/instr/runtime/$(basename "$r" .ml).instr"
    tools/check.sh --runtime-instr "$r" "$o" && has_instr "$o" \
      || { echo "samecode: $side: runtime/$(basename "$r"): no instructions"; exit 1; }
  done
  for f in $(cd "$tmp/$side/src/extracted" && find . -name '*.ml' | sed 's|^\./||' | sort); do
    mkdir -p "$tmp/$side/instr/extracted/$(dirname "$f")"
    o="$tmp/$side/instr/extracted/${f%.ml}.instr"
    RUNTIME="$tmp/$side/rt" tools/check.sh --instr "$tmp/$side/src/extracted/$f" $simplify "$o" \
      && has_instr "$o" \
      || { echo "samecode: $side: extracted/$f does not compile, or gives no instructions"; exit 1; }
  done
done
# compare KIND : the files of both sides (the union), one by one; sets n, d.
compare() {
  n=0; d=0
  for f in $( { (cd "$tmp/old/instr/$1" && find . -name '*.instr')
                (cd "$tmp/new/instr/$1" && find . -name '*.instr'); } | sed 's|^\./||' | sort -u); do
    n=$((n+1)); a="$tmp/old/instr/$1/$f"; b="$tmp/new/instr/$1/$f"; name=$1/${f%.instr}.ml
    if [ ! -e "$a" ]; then d=$((d+1)); echo "samecode: only now: $name"
    elif [ ! -e "$b" ]; then d=$((d+1)); echo "samecode: only at $rev: $name"
    elif ! cmp -s "$a" "$b"; then
      d=$((d+1))
      echo "samecode: OTHER INSTRUCTIONS: $name" \
        "($(diff "$a" "$b" | grep -c '^[<>]') lines differ)"
    elif ! cmp -s "$a.places" "$b.places"; then
      d=$((d+1))
      echo "samecode: OTHER COUNTS OF PLACES MADE BLANK: $name" \
        "($(cat "$b.places") now, $(cat "$a.places") at $rev)"
    fi
  done
}
# places SIDE : the three counts of tools/check.sh --instr, summed.
places() {
  find "$tmp/$1/instr" -name '*.places' -exec cat {} + \
    | awk '{a+=$1; l+=$2; r+=$3} END {print a+0, l+0, r+0}'
}
compare extracted; ne=$n; de=$d
echo "samecode: $ne extracted files against $rev: $((ne-de)) with the same instructions, $de with others"
compare runtime; nr=$n; dr=$d
echo "samecode: $nr files of the runtime against $rev: $((nr-dr)) with the same instructions, $dr with others"
set -- $(places new) $(places old)
echo "samecode: made blank before the comparison, and nothing else:" \
  "the places of $1 assertions and $2 __LOC__ texts (at $rev: $4 and $5)"
left="elsewhere in its instructions (left as it is: the file is among the others)"
[ "$3" = 0 ] || echo "samecode: now: the name of a compiled file stands $3 times $left"
[ "$6" = 0 ] || echo "samecode: at $rev: the name of a compiled file stands $6 times $left"
[ $de = 0 ] && [ $dr = 0 ]
