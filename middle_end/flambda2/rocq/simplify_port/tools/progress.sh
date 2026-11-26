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
set -eu
simplify=$1; B=$2
kinds="unported partial loose type verbatim init order decl papp record-order update"
names_ml() {
  # an [and] at the left margin counts only after a [let] (not after a [type])
  awk '/^type /{m=0} /^let[ []/{m=1} /^let[ []/||(m&&/^and[ []/){print}' "$1" \
    | sed -n -E 's/^(let|and)( rec)?( ?\[@[^]]*\])* +([a-z_][A-Za-z0-9_'"'"']*).*/\4/p' \
    | grep -v '^_$' | sort -u
}
names_v() {
  { # a name that is a word of Rocq has one _ after it in the .v file
    sed -n -E 's/^(Definition|Fixpoint|with) +([a-z_][A-Za-z0-9_'"'"']*).*/\2/p' "$1" \
      | sed -E 'p; s/_$//'
    # the fields of the file's records: Rocq makes one function for each
    awk '/^ *Record /{r=1} r{print} r&&/}\./{r=0}' "$1" | tr '\n' ' ' \
      | grep -o -E '[{;] *[a-z_][A-Za-z0-9_'"'"']* *:' | sed -E 's/[{;: ]//g'
  } | sort -u
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
# as an assignment: if SIMPLIFY_DIR is not there the script stops, and does
# not write a table of no file
files=$(cd "$simplify" && find . -name '*.ml' | sed 's|^\./||' | LC_ALL=C sort)
for ml in $files; do
  dir=$(dirname "$ml"); base=$(basename "$ml" .ml)
  if [ "$dir" = . ]; then d=""; else d="$dir/"; fi
  v="$d${base^}.v"
  lines=$(wc -l < "$simplify/$ml")
  defs=$(names_ml "$simplify/$ml" | wc -l)
  ported=0; gaps="-"; rocq="-"; ocaml="-"
  if [ -e "$v" ]; then
    tf=$((tf+1))
    ported_files="$ported_files$v "
    ported=$(comm -12 <(names_ml "$simplify/$ml") <(names_v "$v") | wc -l)
    gaps=""
    for k in $kinds; do
      n=$(grep -o "(\* PORT-GAP($k)" "$v" | wc -l)
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
# each command stands alone, and its status is read: a list that could not
# be made stops the script
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
