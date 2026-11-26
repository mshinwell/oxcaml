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
#
# EACH COMMAND ON WHOSE OUTPUT THE COMPARISON IS DECIDED STANDS ALONE (git,
# tar, find, sed, sort, diff, grep, cat, awk), with its output in a file of
# _build/samecode or in a variable, and its status is read: by `set -e`,
# which stops the script, or by the script (diff, grep and cmp, whose
# status 1 is an answer and no failure). No list comes through a pipe or
# through the list of a `for`: there the shell does not read the status of
# the command that makes the list, and a list of files that was made in
# part would be compared as if it were whole. The functions compare and
# places are called as commands of the script, not inside `$( )`, where
# `set -e` would not hold in them. If the script stops before its last
# lines, it says so (the shell says nothing when `set -e` stops it): the
# lines above that one are then no result.
set -eu
compared=no
trap 'if [ $compared = no ]; then echo "samecode: STOPPED before the comparison was whole: a command failed, or a file has no instructions"; fi' EXIT
rev=${1:-}
[ -n "$rev" ] || { echo "usage: tools/samecode.sh REV"; exit 2; }
[ -n "${CMI_ROOT:-}" ] || { echo "CMI_ROOT is not set"; exit 2; }
[ -d "$CMI_ROOT/middle_end/flambda2/simplify/.flambda2_simplify.objs/byte" ] \
  || { echo "samecode: no compiled interfaces under CMI_ROOT=$CMI_ROOT"; exit 2; }
OCAMLC=${OCAMLC:-ocamlc.opt}; export OCAMLC CMI_ROOT
here=$(pwd); simplify=../../simplify
tmp=$here/_build/samecode; rm -rf "$tmp"; mkdir -p "$tmp/old" "$tmp/new"
prefix=$(git rev-parse --show-prefix)
top=$(git rev-parse --show-toplevel)
git -C "$top" archive -o "$tmp/old.tar" "$rev:${prefix%/}" extracted runtime
tar -x -f "$tmp/old.tar" -C "$tmp/old"
mkdir -p "$tmp/new/src"; cp -r extracted runtime "$tmp/new/src/"
mkdir -p "$tmp/old/src"; mv "$tmp/old/extracted" "$tmp/old/runtime" "$tmp/old/src/"
# has_instr FILE : the instructions are there (not empty, not the word of a
# check that was skipped). grep exits 0 if the word is the file's line, 1
# if not; any other status is a failure, and the answer is then no.
has_instr() {
  local rc=0
  [ -s "$1" ] || return 1
  grep -qx skipped "$1" || rc=$?
  [ $rc = 1 ] || return 1
  [ -s "$1.places" ]
}
for side in old new; do
  mkdir -p "$tmp/$side/instr/runtime" "$tmp/$side/instr/extracted"
  for r in "$tmp/$side/src/runtime"/port_*.ml; do
    RUNTIME="$tmp/$side/rt" tools/check.sh --runtime "$r" > /dev/null
    o="$tmp/$side/instr/runtime/$(basename "$r" .ml).instr"
    tools/check.sh --runtime-instr "$r" "$o" && has_instr "$o" \
      || { echo "samecode: $side: runtime/$(basename "$r"): no instructions"; exit 1; }
  done
  files=$(cd "$tmp/$side/src/extracted" && find . -name '*.ml')
  files=$(sed 's|^\./||' <<< "$files")
  files=$(sort <<< "$files")
  [ -n "$files" ] || { echo "samecode: $side: no .ml file under extracted/"; exit 1; }
  for f in $files; do
    mkdir -p "$tmp/$side/instr/extracted/$(dirname "$f")"
    o="$tmp/$side/instr/extracted/${f%.ml}.instr"
    RUNTIME="$tmp/$side/rt" tools/check.sh --instr "$tmp/$side/src/extracted/$f" $simplify "$o" \
      && has_instr "$o" \
      || { echo "samecode: $side: extracted/$f does not compile, or gives no instructions"; exit 1; }
  done
done
# compare KIND : the files of both sides (the union), one by one; sets n, d.
compare() {
  local of_old of_new both rc lines now before
  n=0; d=0
  of_old=$(cd "$tmp/old/instr/$1" && find . -name '*.instr')
  of_new=$(cd "$tmp/new/instr/$1" && find . -name '*.instr')
  both=$(printf '%s\n%s\n' "$of_old" "$of_new")
  both=$(sed 's|^\./||' <<< "$both")
  both=$(sort -u <<< "$both")
  for f in $both; do
    n=$((n+1)); a="$tmp/old/instr/$1/$f"; b="$tmp/new/instr/$1/$f"; name=$1/${f%.instr}.ml
    if [ ! -e "$a" ]; then d=$((d+1)); echo "samecode: only now: $name"
    elif [ ! -e "$b" ]; then d=$((d+1)); echo "samecode: only at $rev: $name"
    elif ! cmp -s "$a" "$b"; then
      # (a status of cmp above 1 is counted as a difference too)
      d=$((d+1))
      rc=0
      diff "$a" "$b" > "$tmp/diff.out" || rc=$?
      if [ $rc -gt 1 ]; then echo "samecode: diff exits $rc on $name"; exit 2; fi
      rc=0
      lines=$(grep -c '^[<>]' "$tmp/diff.out") || rc=$?
      if [ $rc -gt 1 ]; then echo "samecode: grep exits $rc on the difference of $name"; exit 2; fi
      echo "samecode: OTHER INSTRUCTIONS: $name ($lines lines differ)"
    elif ! cmp -s "$a.places" "$b.places"; then
      d=$((d+1))
      now=$(cat "$b.places")
      before=$(cat "$a.places")
      echo "samecode: OTHER COUNTS OF PLACES MADE BLANK: $name ($now now, $before at $rev)"
    fi
  done
}
# places SIDE : the three counts of tools/check.sh --instr, summed, into
# the variable sums.
places() {
  find "$tmp/$1/instr" -name '*.places' -exec cat {} + > "$tmp/$1.places"
  sums=$(awk '{a+=$1; l+=$2; r+=$3} END {print a+0, l+0, r+0}' "$tmp/$1.places")
}
compare extracted; ne=$n; de=$d
echo "samecode: $ne extracted files against $rev: $((ne-de)) with the same instructions, $de with others"
compare runtime; nr=$n; dr=$d
echo "samecode: $nr files of the runtime against $rev: $((nr-dr)) with the same instructions, $dr with others"
places new; of_now=$sums
places old; of_then=$sums
set -- $of_now $of_then
echo "samecode: made blank before the comparison, and nothing else:" \
  "the places of $1 assertions and $2 __LOC__ texts (at $rev: $4 and $5)"
left="elsewhere in its instructions (left as it is: the file is among the others)"
[ "$3" = 0 ] || echo "samecode: now: the name of a compiled file stands $3 times $left"
[ "$6" = 0 ] || echo "samecode: at $rev: the name of a compiled file stands $6 times $left"
compared=yes
[ $de = 0 ] && [ $dr = 0 ]
