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
# Nothing is written there, and nothing of the model is compiled. MODEL may
# be a name from the port's folder (../model): the script makes ONE ABSOLUTE
# NAME of it before it reads anything, and the model's list of flags, the
# commit that is printed and the directories that Rocq is given are all of
# that name. BUILD is the port's directory of builds (_build): the port's
# real build is read in BUILD/real (the Makefile makes it first), and
# everything that this script writes is under BUILD/against_model, which it
# makes anew. ROCQ in the environment names another program than rocq.
#
# WHAT IT DOES, in this order:
#  0. It makes MODEL absolute (cd, then pwd -P). It stops if MODEL is not a
#     directory, if the model's list of flags is not in it, or if git says
#     that the root of MODEL's tree is another directory (the commit of
#     step 2 would be of that other tree).
#  1. It reads the flags of the model from the model's own list,
#     MODEL/middle_end/flambda2/rocq/_CoqProject (the model's make stops if
#     that list is not the flags that it gives to Rocq): each line `-Q DIR
#     NAME`, with DIR taken from that folder. A line that is neither blank,
#     nor a comment, nor of that form stops the script.
#  2. It prints MODEL as it made it, the commit of the model's tree and of
#     the port's tree, and for each how many files have a change that is
#     not committed (in the port: of the port's folder). IT DOES NOT STOP
#     AT A CHANGE: a record of a run says these lines. IT DOES NOT KNOW
#     whether the model's compiled files are of the model's .v files.
#  3. It refuses a file of against_model/ with a sentence that begins
#     `Axiom`, `Parameter`, `Conjecture` or `Admitted` (or their plurals),
#     or with the word `admit`. (It reads lines, and does not know a
#     comment: write none that begins so.) THIS IS A RULE OF LINES AND
#     WORDS. It does not show that a file takes nothing without a proof:
#     the reader of the files does, with the list of step 5.
#  4. It copies the .v files of against_model/ to BUILD/against_model and
#     Rocq compiles them there, in the order of their dependencies, with the
#     model's flags, the port's real build as the library SimplifyPort, and
#     that directory as the library SimplifyPortAgainstModel.
#  5. For each file FooProofs.v, each line that begins `Theorem` must be
#     `Theorem NAME : STATEMENT.`, where STATEMENT is a name that
#     FooSpec.v defines. For each, the script writes sentences of Rocq in
#     a file FooTheorems.v, and Rocq compiles that file. Every name in
#     them is written with its file (FooProofs.NAME, FooSpec.STATEMENT):
#     the folder may have several pairs of files, and a name of one is
#     not taken for the same name of another, or of the Proofs file. The
#     sentences:
#     - Rocq CHECKS that the theorem of the Proofs file proves the
#       statement of the Spec file (a goal FooSpec.STATEMENT, closed by
#       FooProofs.NAME). This prints nothing; if it fails, the script
#       stops.
#     - the theorem with its statement's name (Check);
#     - THE WHOLE STATEMENT, with every definition of a proposition of
#       the Spec files of this folder unfolded (a definition whose type
#       is written Prop before its `:=`), so that the contracts stand in
#       it as the premises that they are. For this a Spec file has no
#       module of its own (`Module X.` .. `End X.`): the script stops at
#       one. A short name for a module (`Module X := Y.`) is none;
#     - what the theorem rests on (Print Assumptions). The contracts are
#       premises: Print Assumptions does not list them. It lists
#       parameters. THE SCRIPT DOES NOT JUDGE THAT LIST: the reader sees
#       whether each name is a parameter of the port or of its kit.
#     The same text is kept in BUILD/against_model/THEOREMS.txt.
#
# THE STATUSES THAT DECIDE. The script ends with 0 at its last line only.
# It ends with 1 when it refuses the files of against_model/; with 2 when
# it could not do its work (an argument, a tree, a grep that failed); with
# the status of a command of its own that failed, Rocq among them.
#  - grep, in three places: the lines that take something without a proof
#    (step 3), the lines that begin `Theorem` (step 5), the definition of a
#    statement in the Spec file (step 5). grep ends with 0 when a line has
#    the pattern, with 1 when no line has it, and with another status when
#    it failed. The script reads the status each time. At 0, step 3
#    refuses the files, and step 5 goes on. At 1, step 3 goes on, and step
#    5 refuses the files (a Proofs file without a theorem; a statement that
#    the Spec file does not define). AT ANY OTHER STATUS THE SCRIPT STOPS,
#    whatever grep printed before it failed.
#  - Every other command of which a failure would change an answer is a
#    command that stands alone, or one that gives a variable its text
#    ($(..)), and `set -e` ends the script when it fails: cd, git, ls, cp,
#    Rocq, awk, tr. Two of them fail ON PURPOSE in step 5: awk ends with 3
#    at a module of a Spec file; Rocq ends with an error at the file of
#    the theorems when a theorem does not prove the statement of the Spec
#    file.
#  - Two places are pipes, and the shell reads the last command of a pipe
#    only. The counts of step 2 (wc after printf, in the text of an echo):
#    a count that fails leaves its place empty on the printed line, and
#    decides nothing. The two names of a theorem's line (sed after
#    printf): a name that is empty stops the script, as a line that has
#    not the form does.
set -eu
if [ $# != 2 ] || [ -z "$1" ]; then
  echo "against-model: say where the built model is: make against-model MODEL=ROOT" >&2
  echo "  (ROOT: a tree of this repository in which make -C rocq all has run)" >&2
  exit 2
fi
B=$2
ROCQ=${ROCQ:-rocq}

# 0. MODEL, as one absolute name. Every later line reads the model by it:
# the script changes its directory in step 4, and a name from the port's
# folder would be another place there.
if [ ! -d "$1" ]; then
  echo "against-model: MODEL is not a directory: $1" >&2
  exit 2
fi
model=$(CDPATH= cd -- "$1" && pwd -P)
model_rocq=$model/middle_end/flambda2/rocq
project=$model_rocq/_CoqProject
if [ ! -f "$project" ]; then
  echo "against-model: $project is not there: MODEL is not the root of a tree of this repository" >&2
  exit 2
fi
model_top=$(git -C "$model" rev-parse --show-toplevel)
model_top=$(CDPATH= cd -- "$model_top" && pwd -P)
if [ "$model_top" != "$model" ]; then
  echo "against-model: MODEL is $model, and git says that the root of its tree is $model_top: the commit that would be printed is not MODEL's" >&2
  exit 2
fi
if [ ! -f "$B/real/Kit_laws.vo" ]; then
  echo "against-model: the port's real build is not in $B/real: make real" >&2
  exit 2
fi

# 1. The flags of the model. (A last line without a newline at its end is
# read too.)
flags=()
while IFS= read -r line || [ -n "$line" ]; do
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
echo "against-model: the model: $model"
echo "against-model: the model: commit $model_commit; files with a change that is not committed: $(lines_of "$model_status")"
echo "against-model: the port: commit $port_commit; files of the port's folder with a change that is not committed: $(lines_of "$port_status")"

# 3. Nothing is taken without a proof. grep's status is read: 0, a line
# was found; 1, none; any other, grep failed and nothing is known.
sources=$(ls against_model/*.v)
status=0
grep -n -E '^[[:space:]]*(Axioms?|Parameters?|Conjectures?|Admitted)([[:space:].]|$)|(^|[^A-Za-z0-9_])admit([^A-Za-z0-9_]|$)' $sources || status=$?
case $status in
0)
  echo "against-model: the lines above take something without a proof" >&2
  exit 1
  ;;
1) ;;
*)
  echo "against-model: grep failed (status $status) on the files of against_model/: it is not known whether one takes something without a proof" >&2
  exit 2
  ;;
esac

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
# `:=`, the text ends `: Prop :=`. Each is written with its file,
# FooSpec.NAME. That is its name only if no module of the file is around
# it: awk ends with the status 3 at a line `Module X` without `:=`, and
# `set -e` ends the script.
awk '
  FNR == 1 { file = FILENAME; sub(/\.v$/, "", file) }
  /^[[:space:]]*Module[[:space:]]/ && !index($0, ":=") {
    printf "against-model: %s, line %d: a Spec file has no module of its own\n", FILENAME, FNR > "/dev/stderr"
    exit 3
  }
  /^[[:space:]]*Definition[[:space:]]/ { name = $2; head = ""; collecting = 1 }
  collecting {
    head = head " " $0
    if (index($0, ":=")) {
      collecting = 0
      if (head ~ /: Prop :=/) print file "." name
    }
  }' $specs > propositions.tmp
definitions=$(tr '\n' ' ' < propositions.tmp)
rm -f propositions.tmp
spec_modules=
for spec in $specs; do spec_modules="$spec_modules ${spec%.v}"; done
: > THEOREMS.txt
for proofs in *Proofs.v; do
  name=${proofs%Proofs.v}
  if [ ! -f "${name}Spec.v" ]; then
    echo "against-model: $proofs has no ${name}Spec.v" >&2
    exit 1
  fi
  check=${name}Theorems.v
  {
    # Every Spec file of the folder is required, for the definitions that
    # are unfolded. This pair's two files are imported, so that Rocq
    # prints their names short.
    echo "From SimplifyPortAgainstModel Require$spec_modules."
    echo "From SimplifyPortAgainstModel Require Import ${name}Spec ${name}Proofs."
    echo "Set Printing Width 78."
  } > "$check"
  # The lines that begin Theorem. grep's status is read: 0, the list is
  # whole; 1, the file has no theorem; any other, grep failed, and what it
  # wrote before is not the list.
  status=0
  grep -E '^[[:space:]]*Theorem([[:space:]]|$)' "$proofs" > theorems.tmp || status=$?
  case $status in
  0) ;;
  1)
    echo "against-model: $proofs has no theorem" >&2
    exit 1
    ;;
  *)
    echo "against-model: grep failed (status $status) on $proofs: its theorems are not known" >&2
    exit 2
    ;;
  esac
  while IFS= read -r line; do
    theorem=$(printf '%s\n' "$line" | sed -n -E 's/^Theorem ([A-Za-z_][A-Za-z0-9_'"'"']*) : ([A-Za-z_][A-Za-z0-9_'"'"']*)\.$/\1/p')
    statement=$(printf '%s\n' "$line" | sed -n -E 's/^Theorem ([A-Za-z_][A-Za-z0-9_'"'"']*) : ([A-Za-z_][A-Za-z0-9_'"'"']*)\.$/\2/p')
    if [ -z "$theorem" ] || [ -z "$statement" ]; then
      echo "against-model: $proofs: a theorem is one line, Theorem NAME : STATEMENT. ; this is not: $line" >&2
      exit 1
    fi
    # The statement is a definition of the Spec file. grep's status is
    # read: 0, it is; 1, it is not; any other, grep failed.
    status=0
    grep -q -E "^Definition $statement([[:space:]]|$)" "${name}Spec.v" || status=$?
    case $status in
    0) ;;
    1)
      echo "against-model: $proofs: the statement $statement of the theorem $theorem is not a definition of ${name}Spec.v" >&2
      exit 1
      ;;
    *)
      echo "against-model: grep failed (status $status) on ${name}Spec.v: it is not known whether it defines $statement" >&2
      exit 2
      ;;
    esac
    {
      echo "Goal ${name}Spec.$statement. Proof. exact ${name}Proofs.$theorem. Qed."
      echo "Check ${name}Proofs.$theorem."
      echo "Eval cbv beta delta [$definitions] in ${name}Spec.$statement."
      echo "Print Assumptions ${name}Proofs.$theorem."
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
