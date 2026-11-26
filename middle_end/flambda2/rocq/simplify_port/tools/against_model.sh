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

# against_model.sh MODEL BUILD : what `make against-model MODEL=ROOT` runs. It
# compiles the files of against_model/ (against_model/README.md), which say of
# ported functions what a Spec file of the model says must hold, and prints of
# each theorem its statement and what it rests on. It follows no file of the
# compiler.
#
# MODEL is the root of a tree of this repository in which `make -C rocq all`
# has run: the model's compiled files are read there, beside its .v files.
# Nothing is written there, and nothing of the model is compiled. BUILD is
# the port's directory of builds (_build): the port's real build is read in
# BUILD/real (the Makefile makes it first), and everything that this script
# writes is under BUILD/against_model, which it makes anew. ROCQ in the
# environment names another program than rocq.
#
# WHAT IT DOES, in this order:
#  1. It reads the flags of the model from the model's own list,
#     MODEL/middle_end/flambda2/rocq/_CoqProject (the model's make stops if
#     that list is not the flags that it gives to Rocq): each line `-Q DIR
#     NAME`, with DIR taken from that folder. A line that is neither blank,
#     nor a comment, nor of that form stops the script.
#  2. It prints the commit of the model's tree and of the port's tree, and
#     for each how many files have a change that is not committed (in the
#     port: of the port's folder). IT DOES NOT STOP AT A CHANGE: a record of
#     a run says these lines.
#  3. It refuses a file of against_model/ with a sentence that begins
#     `Axiom`, `Parameter`, `Conjecture` or `Admitted` (or their plurals),
#     or with the word `admit`. (It reads lines, and does not know a
#     comment: write none that begins so.)
#  4. It copies the .v files of against_model/ to BUILD/against_model and
#     Rocq compiles them there, in the order of their dependencies, with the
#     model's flags, the port's real build as the library SimplifyPort, and
#     that directory as the library SimplifyPortAgainstModel.
#  5. For each file FooProofs.v, each line that begins `Theorem` must be
#     `Theorem NAME : STATEMENT.`, where STATEMENT is a name that
#     FooSpec.v defines. Of each it prints, by Rocq: the theorem with its
#     statement's name (Check); THE WHOLE STATEMENT, with every definition
#     of a proposition of the Spec files of this folder unfolded (a
#     definition whose type is written Prop before its `:=`), so that the
#     contracts stand in it as the premises that they are; and what the
#     theorem rests on
#     (Print Assumptions). The contracts are premises: Print Assumptions
#     does not list them. It lists parameters. THE SCRIPT DOES NOT JUDGE
#     THAT LIST: the reader sees whether each name is a parameter of the
#     port or of its kit. The same text is kept in
#     BUILD/against_model/THEOREMS.txt.
set -eu
if [ $# != 2 ] || [ -z "$1" ]; then
  echo "against-model: say where the built model is: make against-model MODEL=ROOT" >&2
  echo "  (ROOT: a tree of this repository in which make -C rocq all has run)" >&2
  exit 2
fi
model=$1; B=$2
ROCQ=${ROCQ:-rocq}
model_rocq=$model/middle_end/flambda2/rocq
project=$model_rocq/_CoqProject
if [ ! -f "$project" ]; then
  echo "against-model: $project is not there: MODEL is not the root of a tree of this repository" >&2
  exit 2
fi
if [ ! -f "$B/real/Kit_laws.vo" ]; then
  echo "against-model: the port's real build is not in $B/real: make real" >&2
  exit 2
fi

# 1. The flags of the model.
flags=()
while IFS= read -r line; do
  case "$line" in
  ''|'#'*) ;;
  '-Q '*)
    set -- $line
    if [ $# != 3 ]; then
      echo "against-model: a line of $project that is not -Q DIR NAME: $line" >&2
      exit 2
    fi
    flags+=(-Q "$model_rocq/$2" "$3")
    ;;
  *)
    echo "against-model: a line of $project that is not -Q DIR NAME: $line" >&2
    exit 2
    ;;
  esac
done < "$project"

# 2. The two inputs. (Each command of git stands alone: in a pipe, one
# that fails would be a tree without a change.)
lines_of() {
  if [ -z "$1" ]; then echo 0; else printf '%s\n' "$1" | wc -l; fi
}
model_commit=$(git -C "$model" rev-parse HEAD)
model_status=$(git -C "$model" status --porcelain)
port_commit=$(git rev-parse HEAD)
port_status=$(git status --porcelain .)
echo "against-model: the model: commit $model_commit; files with a change that is not committed: $(lines_of "$model_status")"
echo "against-model: the port: commit $port_commit; files of the port's folder with a change that is not committed: $(lines_of "$port_status")"

# 3. Nothing is taken without a proof.
sources=$(ls against_model/*.v)
if grep -n -E '^[[:space:]]*(Axioms?|Parameters?|Conjectures?|Admitted)([[:space:].]|$)|(^|[^A-Za-z0-9_])admit([^A-Za-z0-9_]|$)' $sources; then
  echo "against-model: the lines above take something without a proof" >&2
  exit 1
fi

# 4. The files, compiled.
out=$B/against_model
rm -rf "$out"
mkdir -p "$out"
cp $sources "$out"/
cd "$out"
libraries=("${flags[@]}" -Q ../real SimplifyPort -Q . SimplifyPortAgainstModel)
sorted=$("$ROCQ" dep -sort "${libraries[@]}" *.v)
for v in $sorted; do
  # [rocq dep -sort] names the .v files in an order in which each comes
  # after what it requires, those of the libraries too, with their
  # directories. Only the files of this directory are compiled.
  v=${v#./}
  case "$v" in */*) continue ;; esac
  [ -f "$v" ] || continue
  echo "$ROCQ compile -q (the model's flags) -Q ../real SimplifyPort -Q . SimplifyPortAgainstModel $v"
  "$ROCQ" compile -q "${libraries[@]}" "$v"
done
for v in *.v; do
  if [ ! -f "${v%.v}.vo" ]; then
    echo "against-model: $v was not compiled" >&2
    exit 1
  fi
done

# 5. The theorems.
specs=$(ls *Spec.v)
# The definitions of propositions: from `Definition NAME` to the first
# `:=`, the text ends `: Prop :=`.
awk '
  /^[[:space:]]*Definition[[:space:]]/ { name = $2; head = ""; collecting = 1 }
  collecting {
    head = head " " $0
    if (index($0, ":=")) {
      collecting = 0
      if (head ~ /: Prop :=/) print name
    }
  }' $specs > propositions.tmp
definitions=$(tr '\n' ' ' < propositions.tmp)
rm -f propositions.tmp
: > THEOREMS.txt
for proofs in *Proofs.v; do
  name=${proofs%Proofs.v}
  if [ ! -f "${name}Spec.v" ]; then
    echo "against-model: $proofs has no ${name}Spec.v" >&2
    exit 1
  fi
  check=${name}Theorems.v
  {
    echo "From SimplifyPortAgainstModel Require Import ${name}Spec ${name}Proofs."
    echo "Set Printing Width 78."
  } > "$check"
  grep -E '^[[:space:]]*Theorem([[:space:]]|$)' "$proofs" > theorems.tmp || true
  if [ ! -s theorems.tmp ]; then
    echo "against-model: $proofs has no theorem" >&2
    exit 1
  fi
  while IFS= read -r line; do
    theorem=$(printf '%s\n' "$line" | sed -n -E 's/^Theorem ([A-Za-z_][A-Za-z0-9_'"'"']*) : ([A-Za-z_][A-Za-z0-9_'"'"']*)\.$/\1/p')
    statement=$(printf '%s\n' "$line" | sed -n -E 's/^Theorem ([A-Za-z_][A-Za-z0-9_'"'"']*) : ([A-Za-z_][A-Za-z0-9_'"'"']*)\.$/\2/p')
    if [ -z "$theorem" ] || [ -z "$statement" ]; then
      echo "against-model: $proofs: a theorem is one line, Theorem NAME : STATEMENT. ; this is not: $line" >&2
      exit 1
    fi
    if ! grep -q -E "^Definition $statement([[:space:]]|$)" "${name}Spec.v"; then
      echo "against-model: $proofs: the statement $statement of the theorem $theorem is not a definition of ${name}Spec.v" >&2
      exit 1
    fi
    {
      echo "Check $theorem."
      echo "Eval cbv beta delta [$definitions] in $statement."
      echo "Print Assumptions $theorem."
    } >> "$check"
  done < theorems.tmp
  rm -f theorems.tmp
  {
    echo "==== the theorems of $proofs: each with its statement's name, then its whole statement, then what it rests on ===="
    "$ROCQ" compile -q "${libraries[@]}" "$check"
  } > theorems.out
  cat theorems.out
  cat theorems.out >> THEOREMS.txt
  rm -f theorems.out
done
echo "against-model: the files of against_model/ are compiled, and the text above is in $out/THEOREMS.txt"
