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

# progress.sh SIMPLIFY_DIR BUILD_DIR : writes PROGRESS.md on standard output:
# one line for each file of middle_end/flambda2/simplify/. It follows no
# file of the compiler.
#   lines    the lines of the compiler's file
#   defs     its definitions at the left margin (let, and its and), by name
#   ported   those of them that the .v file defines (Definition, Fixpoint,
#            with, or a field of a Record of the file: Rocq makes the
#            function that reads it) and does not leave as a parameter
#   gaps     the marks of the .v file, by kind: the comments that BEGIN
#            with "PORT-GAP(kind)"
# After the table: the marks of the ported files by kind (the sums of the
# rows), and then THE MARKS OF THE OTHER .v FILES of the folder, which the
# table does not have: those of decl/, which tools/declgen writes, and of
# the kit (monad/). There a mark is counted wherever it stands in a
# comment, as "PORT-GAP(kind):" with its colon (the kit has one that does
# not begin its comment); "PORT-GAP(kind)" without a colon is a mention.
#   Rocq     whether the .v file is compiled against both implementations
#            of the monad
#   OCaml    how the extracted file type-checks (tools/check.sh)
#
# EACH COMMAND ON WHOSE OUTPUT THE TABLE IS MADE STANDS ALONE (find, awk,
# sed, sort, comm, wc, grep, cat), with its output in a file of
# BUILD_DIR/progress or in a variable, and its status is read: by `set -e`,
# which stops the script, or by the script (grep, which exits 1 when it
# finds nothing). No list comes through a pipe, through the list of a
# `for` or through `<( )`: there the shell does not read the status of the
# command that makes the list, and a list that was made in part would be
# taken for the whole. The functions are called as commands of the script
# and not inside `$( )`, where `set -e` would not hold in them. If the
# script stops, it says so on the standard error (the shell says nothing
# when `set -e` stops it), and make deletes what it has written of
# PROGRESS.md.
set -eu
whole=no
trap 'if [ $whole = no ]; then echo "progress.sh: STOPPED: a command failed; the table is not whole" >&2; fi' EXIT
simplify=$1; B=$2
kinds="unported partial loose type verbatim init order decl papp record-order update"
work=$B/progress
rm -rf "$work"
mkdir -p "$work"
# names_ml FILE OUT : the names that the compiler's file defines at its left
# margin, sorted, one on a line, into OUT
names_ml() {
  # an [and] at the left margin counts only after a [let] (not after a [type])
  awk '/^type /{m=0} /^let[ []/{m=1} /^let[ []/||(m&&/^and[ []/){print}' "$1" > "$work/ml.lines"
  sed -n -E 's/^(let|and)( rec)?( ?\[@[^]]*\])* +([a-z_][A-Za-z0-9_'"'"']*).*/\4/p' \
    "$work/ml.lines" > "$work/ml.names"
  awk '$0 != "_"' "$work/ml.names" > "$work/ml.kept"
  LC_ALL=C sort -u "$work/ml.kept" > "$2"
}
# names_v FILE OUT : the names that the .v file defines, sorted, into OUT
names_v() {
  local rc=0
  # a name that is a word of Rocq has one _ after it in the .v file
  sed -n -E 's/^(Definition|Fixpoint|with) +([a-z_][A-Za-z0-9_'"'"']*).*/\2/p' "$1" > "$work/v.defs"
  sed -E 'p; s/_$//' "$work/v.defs" > "$work/v.names"
  # the fields of the file's records: Rocq makes one function for each
  awk '/^ *Record /{r=1} r{print} r&&/}\./{r=0}' "$1" > "$work/v.records"
  tr '\n' ' ' < "$work/v.records" > "$work/v.line"
  # (grep exits 1 for a file that has no record: only a status above 1 is
  # a failure)
  grep -o -E '[{;] *[a-z_][A-Za-z0-9_'"'"']* *:' "$work/v.line" > "$work/v.fields" || rc=$?
  if [ $rc -gt 1 ]; then echo "progress.sh: grep exits $rc on the records of $1" >&2; exit 2; fi
  sed -E 's/[{;: ]//g' "$work/v.fields" >> "$work/v.names"
  LC_ALL=C sort -u "$work/v.names" > "$2"
}
echo "# The port of Simplify: progress"
echo
echo "Made by \`make table\` (tools/progress.sh); do not edit. One line for each"
echo "file of \`middle_end/flambda2/simplify/\`. \`defs\`: the compiler's definitions"
echo "at the left margin; \`ported\`: those that the Rocq file defines; \`gaps\`:"
echo "the marks PORT-GAP by kind; \`OCaml\`: how the extracted file type-checks"
echo "(strict: against the whole interface; overlay: in the place of the"
echo "compiler's own definitions; alone: no interface)."
echo
echo "| file | lines | defs | ported | gaps | Rocq | OCaml |"
echo "|---|---:|---:|---:|---|---|---|"
tl=0; td=0; tp=0; tf=0; tr=0; to=0; tg=0
declare -A by_kind
ported_files=" "
# three assignments: if SIMPLIFY_DIR is not there, or find fails, the
# script stops, and does not write a table of no file or of some files
files=$(cd "$simplify" && find . -name '*.ml')
files=$(sed 's|^\./||' <<< "$files")
files=$(LC_ALL=C sort <<< "$files")
if [ -z "$files" ]; then echo "progress.sh: no .ml file under $simplify" >&2; exit 2; fi
for ml in $files; do
  dir=$(dirname "$ml"); base=$(basename "$ml" .ml)
  if [ "$dir" = . ]; then d=""; else d="$dir/"; fi
  v="$d${base^}.v"
  lines=$(wc -l < "$simplify/$ml")
  names_ml "$simplify/$ml" "$work/ml.sorted"
  defs=$(wc -l < "$work/ml.sorted")
  ported=0; gaps="-"; rocq="-"; ocaml="-"
  if [ -e "$v" ]; then
    tf=$((tf+1))
    ported_files="$ported_files$v "
    names_v "$v" "$work/v.sorted"
    LC_ALL=C comm -12 "$work/ml.sorted" "$work/v.sorted" > "$work/both"
    ported=$(wc -l < "$work/both")
    gaps=""
    for k in $kinds; do
      # how many times the mark of the kind begins a comment (one awk, and
      # no grep whose status 1 would have to be told from a failure)
      n=$(awk -v k="$k" 'BEGIN { mark = "\\(\\* PORT-GAP\\(" k "\\)" }
                         { n += gsub(mark, "&") } END { print n + 0 }' "$v")
      if [ "$n" -gt 0 ]; then gaps="$gaps $k:$n"; tg=$((tg+n)); fi
      by_kind[$k]=$(( ${by_kind[$k]:-0} + n ))
    done
    if [ -z "$gaps" ]; then gaps="none"; fi
    if [ -e "$B/real/${v%.v}.vo" ] && [ -e "$B/id/${v%.v}.vo" ] \
       && [ ! "$v" -nt "$B/real/${v%.v}.vo" ] && [ ! "$v" -nt "$B/id/${v%.v}.vo" ]; then
      rocq=yes; tr=$((tr+1))
    else rocq=NO; fi
    s="$B/check/$d$base.status"
    if [ -e "$s" ]; then ocaml=$(cat "$s"); else ocaml=NO; fi
    case "$ocaml" in strict|overlay|alone) to=$((to+1));; esac
  fi
  tl=$((tl+lines)); td=$((td+defs)); tp=$((tp+ported))
  echo "| \`$ml\` | $lines | $defs | $ported | ${gaps# } | $rocq | $ocaml |"
done
echo "| **total: $tf files of 78** | $tl | $td | $tp | $tg marks | $tr | $to |"
echo
echo "Gaps by kind, the ported files:"
echo
for k in $kinds; do
  echo "- $k: ${by_kind[$k]:-0}"
done
echo
echo "The marks of the other \`.v\` files of the folder (\`decl/\`, which"
echo "\`tools/declgen\` writes; the kit, \`monad/\`). They are not in the table"
echo "and not in the numbers above:"
echo
all=$(find . -name '*.v' -not -path './_build/*')
all=$(LC_ALL=C sort <<< "$all")
others=""
for f in $all; do
  f=${f#./}
  case "$ported_files" in *" $f "*) ;; *) others="$others $f";; esac
done
if [ -z "$others" ]; then
  found=""
else
  # DIRECTORY kind NUMBER, for each first directory of a file and each kind
  found=$(awk '
    { line = $0
      while (match(line, /PORT-GAP\([a-z-]+\):/)) {
        kind = substr(line, RSTART + 9, RLENGTH - 11)
        n = split(FILENAME, part, "/")
        where = (n > 1) ? part[1] "/" : FILENAME
        count[where " " kind]++
        line = substr(line, RSTART + RLENGTH)
      } }
    END { for (x in count) print x, count[x] }' $others)
  found=$(LC_ALL=C sort <<< "$found")
fi
if [ -z "$found" ]; then
  echo "- none"
else
  while read -r where kind n; do
    echo "- \`$where\`: $kind: $n"
  done <<< "$found"
fi
whole=yes
