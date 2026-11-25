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

# run.sh [TEST.fl ...] : the tests of this folder (all of them if none is
# named). Each is a term in Flambda's text form that the translation from
# Lambda does not make where Simplify runs on x86-64 (README.md names the
# two shapes that are made elsewhere). It follows no file of the compiler.
#
# The compiler's test tool fexprc reads such a file and runs Simplify on the
# term. This script runs each test through two copies of fexprc, one built
# with the compiler's own Simplify and one built with the extracted files in
# the place of middle_end/flambda2/simplify/ (README.md says how to build
# them), and compares what they give. The copies are named by the
# environment:
#   FEXPRC_BASE  fexprc.exe with the compiler's own Simplify
#   FEXPRC_PORT  fexprc.exe with the extracted Simplify
#   FEXPRC_COV   (may be left out) fexprc.exe with the extracted Simplify in
#                which each function writes its name when it is entered, to
#                the file that the variable PORT_COV_FILE names
#   FL_OUT       (may be left out) a folder in which the outputs are kept
#
# Each test is run three times: with no flag, with -O3, and with -O3 and
# the flags that turn on the lifting and the specialization of
# continuations. Every run has -dfexpr -dflambda, so that the standard
# output is the term that Simplify gives, in the text form and in the full
# form. COMPARED, between the two copies: the exit status, the standard
# output, the messages (the standard error).
#
# With FEXPRC_COV the third copy is compared with the second in the same
# way, and the names that the head of a test gives after ENTERS (and after
# ENTERS-EXPERT, for the run with the expert flags) are looked for among
# the names entered.
#
# A RUN IN WHICH A COPY DOES NOT COME TO AN END OF ITS OWN is never "the
# same": the program is not found or cannot be run (status 126, 127), the
# limit of time (124, 125), a signal (above 128), or the work folder cannot
# be made. Such a run is counted apart. An exit status 1 or 2 of fexprc
# itself (a text that is not read, a fatal error) is a result and is
# compared.
#
# Prints one line a run, then the counts. Exit status 1 if a run differs,
# if a copy did not come to its end in a run, or if a name that a test is
# meant to enter is not entered; 2 if a copy of fexprc is not given or the
# program timeout is not found.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
# what may be left out is empty
FEXPRC_COV=${FEXPRC_COV:-}; FL_OUT=${FL_OUT:-}
for v in FEXPRC_BASE FEXPRC_PORT; do
  if [ ! -x "${!v:-}" ]; then
    echo "run.sh: set $v to a copy of fexprc.exe (see README.md)"; exit 2
  fi
done
if [ -n "$FEXPRC_COV" ] && [ ! -x "$FEXPRC_COV" ]; then
  echo "run.sh: FEXPRC_COV is not a program"; exit 2
fi
command -v timeout > /dev/null \
  || { echo "run.sh: the program timeout is not found"; exit 2; }
expert="-flambda2-expert-cont-lifting-budget 200"
expert="$expert -flambda2-expert-cont-specialization-threshold 200"
expert="$expert -flambda2-match-in-match"
expert="$expert -flambda2-expert-can-inline-recursive-functions"
expert="$expert -flambda2-inline-max-rec-depth 1"
flags_of() {
  case $1 in
    none) echo "";;
    O3) echo "-O3";;
    expert) echo "-O3 $expert";;
  esac
}
if [ -n "$FL_OUT" ]; then
  mkdir -p "$FL_OUT" || exit 2; out=$(cd "$FL_OUT" && pwd)
else
  out=$(mktemp -d) || exit 2; trap 'rm -rf "$out"' EXIT
fi
# one_run COPY PROGRAM TEST MODE : runs the program on a copy of the test
# in a folder of its own; leaves TEST.MODE.COPY.{status,out,err} in $out
one_run() {
  local copy=$1 prog=$2 t=$3 m=$4 w=$out/work rc=0
  rm -f "$out/$t.$m.$copy.status" "$out/$t.$m.$copy.out" "$out/$t.$m.$copy.err"
  if ! { rm -rf "$w" && mkdir -p "$w" && cp "$here/$t.fl" "$w/"; }; then
    echo "no work folder" > "$out/$t.$m.$copy.status"; return
  fi
  # the exit status of the copy is a result, whatever it is
  ( cd "$w" && timeout 300 "$prog" $(flags_of $m) -dfexpr -dflambda "$t.fl" \
      > "$out/$t.$m.$copy.out" 2> "$out/$t.$m.$copy.err" ) || rc=$?
  echo $rc > "$out/$t.$m.$copy.status"
  rm -rf "$w"
}
# ended COPY TEST MODE : did the copy come to an end of its own (any exit
# status below 124)
ended() {
  local s; s=$(cat "$out/$2.$3.$1.status" 2> /dev/null) || s=""
  case $s in
    ''|*[!0-9]*) return 1;;
  esac
  [ "$s" -lt 124 ]
}
# same TEST MODE COPY1 COPY2 : are the status, the output and the messages
# of the two copies the same
same() {
  cmp -s "$out/$1.$2.$3.status" "$out/$1.$2.$4.status" \
    && cmp -s "$out/$1.$2.$3.out" "$out/$1.$2.$4.out" \
    && cmp -s "$out/$1.$2.$3.err" "$out/$1.$2.$4.err"
}
if [ $# = 0 ]; then
  set -- $(cd "$here" && ls *.fl | LC_ALL=C sort)
fi
runs=0; differ=0; cov_differ=0; wanted=0; entered=0; notrun=0
for f in "$@"; do
  t=$(basename "$f" .fl)
  [ -e "$here/$t.fl" ] || { echo "run.sh: no test $t.fl"; exit 2; }
  for m in none O3 expert; do
    runs=$((runs+1))
    one_run base "$FEXPRC_BASE" $t $m
    one_run port "$FEXPRC_PORT" $t $m
    if ! ended base $t $m || ! ended port $t $m; then
      notrun=$((notrun+1))
      echo "$t, $m: A COPY DID NOT COME TO ITS END (base:" \
        "$(cat "$out/$t.$m.base.status" 2> /dev/null); port:" \
        "$(cat "$out/$t.$m.port.status" 2> /dev/null)): not compared"
      continue
    fi
    line="$t, $m: exit status $(cat "$out/$t.$m.port.status"); base and port:"
    if same $t $m base port; then line="$line the same"
    else line="$line DIFFER"; differ=$((differ+1)); fi
    if [ -n "$FEXPRC_COV" ]; then
      hits=$out/$t.$m.hits; rm -f "$hits"
      PORT_COV_FILE=$hits one_run cov "$FEXPRC_COV" $t $m
      if ! ended cov $t $m; then
        line="$line; cov: DID NOT COME TO ITS END"; cov_differ=$((cov_differ+1))
      elif same $t $m cov port; then line="$line; cov and port: the same"
      else line="$line; cov and port: DIFFER"; cov_differ=$((cov_differ+1)); fi
      names=$(sed -n 's/^ *ENTERS \([^ ]*\).*$/\1/p' "$here/$t.fl")
      if [ $m = expert ]; then
        names="$names $(sed -n 's/^ *ENTERS-EXPERT \([^ ]*\).*$/\1/p' "$here/$t.fl")"
      fi
      n=0; e=0; missing=""
      for name in $names; do
        n=$((n+1))
        if [ -e "$hits" ] && grep -q -x -F -- "$name" "$hits"; then e=$((e+1))
        else missing="$missing $name"; fi
      done
      wanted=$((wanted+n)); entered=$((entered+e))
      line="$line; entered $e of $n"
      if [ -n "$missing" ]; then line="$line (NOT ENTERED:$missing)"; fi
    fi
    echo "$line"
  done
done
last="$runs runs; base and port the same: $((runs-differ-notrun)); differ: $differ"
last="$last; a copy did not come to its end: $notrun"
if [ -n "$FEXPRC_COV" ]; then
  last="$last; cov and port differ: $cov_differ; names entered: $entered of $wanted"
fi
echo "$last"
[ $differ = 0 ] && [ $cov_differ = 0 ] && [ $entered = $wanted ] && [ $notrun = 0 ]
