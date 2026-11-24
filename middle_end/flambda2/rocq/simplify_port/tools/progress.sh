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
#   defs     its definitions at the left margin (let, and), by name
#   ported   those of them that the .v file defines (Definition, Fixpoint,
#            with, or a field of a Record of the file: Rocq makes the
#            function that reads it) and does not leave as a parameter
#   gaps     the marks of the .v file, by kind: the comments that BEGIN
#            with "PORT-GAP(kind)"
#   Rocq     whether the .v file is compiled against both implementations
#            of the monad
#   OCaml    how the extracted file type-checks (tools/check.sh)
simplify=$1; B=$2
kinds="unported partial loose type verbatim init order decl papp"
names_ml() {
  sed -n -E 's/^(let|and)( rec)?( ?\[@[^]]*\])* +([a-z_][A-Za-z0-9_'"'"']*).*/\4/p' "$1" \
    | grep -v '^_$' | sort -u
}
names_v() {
  { sed -n -E 's/^(Definition|Fixpoint|with) +([a-z_][A-Za-z0-9_'"'"']*).*/\2/p' "$1"
    # the fields of the file's records: Rocq makes one function for each
    awk '/^Record /{r=1} r{print} r&&/}\./{r=0}' "$1" \
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
for ml in $(cd "$simplify" && find . -name '*.ml' | sed 's|^\./||' | LC_ALL=C sort); do
  dir=$(dirname "$ml"); base=$(basename "$ml" .ml)
  [ "$dir" = . ] && d="" || d="$dir/"
  v="$d${base^}.v"
  lines=$(wc -l < "$simplify/$ml")
  defs=$(names_ml "$simplify/$ml" | wc -l)
  ported=0; gaps="-"; rocq="-"; ocaml="-"
  if [ -e "$v" ]; then
    tf=$((tf+1))
    ported=$(comm -12 <(names_ml "$simplify/$ml") <(names_v "$v") | wc -l)
    gaps=""
    for k in $kinds; do
      n=$(grep -o "(\* PORT-GAP($k)" "$v" | wc -l)
      [ "$n" -gt 0 ] && gaps="$gaps $k:$n" && tg=$((tg+n))
    done
    [ -z "$gaps" ] && gaps="none"
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
echo "Gaps by kind, all files:"
echo
for k in $kinds; do
  n=$(cat $(find . -name '*.v' -not -path './_build/*' -not -path './decl/*') 2>/dev/null | grep -o "(\* PORT-GAP($k)" | wc -l)
  echo "- $k: $n"
done
