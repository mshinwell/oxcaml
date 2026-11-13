#!/bin/sh

# Compiles a unit of a pair as far as the middle end, and keeps what a second
# unit and the test tool need of it (see README.md):
#
#   from_ocaml.sh <ocamlopt> <X.ml> <X> [<F>]
#
# Made in the current directory: X.fl.made, the term that the compiler gives
# to Simplify, as -drawfexpr prints it; and X.cmi and X.cmx, which the
# compiler writes. With <F>, the unit is compiled against F.cmi and F.cmx,
# which are in the current directory.
#
# As in the directory above, the unit is compiled with no standard library
# and no initially opened module, and the compilation stops after the middle
# end. A source may give more flags for its own compilation, on a line of its
# own:
#
#   (* flags: -g *)
#
# As in the directory above, a unit is refused if the text loses of its term
# something that the tool cannot give back (see below). Two of the three
# refusals are of a unit that the tool is run on, one that has X.expected
# beside its source: a unit that has none is compiled for the unit that uses
# it, and no verdict is given of its text.

set -eu

ocamlopt=$1
source=$2
name=$3
first=${4:-}

case "$ocamlopt" in
/*) ;;
*) ocamlopt="$PWD/$ocamlopt" ;;
esac

dir=$(dirname "$source")

flags=$(sed -n 's/^(\* flags: \(.*\) \*)$/\1/p' "$source" | head -n 1)

# In a directory of its own, and under the name X.ml, as the names of
# anonymous functions have the name of the file as it is given. The compiler
# looks for the .cmi and the .cmx of the first unit in the directory it is
# run in.
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp "$source" "$work/$name.ml"
if [ -n "$first" ]; then
  cp "$first.cmi" "$first.cmx" "$work/"
fi
(cd "$work" &&
  "$ocamlopt" -nopervasives -nostdlib $flags -stop-after middle_end -c \
    "$name.ml" -drawfexpr-to "$name.fl")

# The text writes the two tests of being an integer alike, and its reader
# gives the one that is for variants (label C2-26). So the unit is compiled
# once more, for what -drawflambda prints of the term before Simplify, which
# is kept in a file; and a unit whose term has the other test, printed as
# Is_int_generic, is refused unless generic_is_int.txt, beside the source,
# names it. Nothing is given back of a unit that is refused, or whose second
# compilation fails or prints no term.
if ! (cd "$work" &&
  "$ocamlopt" -nopervasives -nostdlib $flags -stop-after middle_end -c \
    "$name.ml" -color never -drawflambda >"$name.raw" 2>&1); then
  cat "$work/$name.raw" >&2
  echo "$name.ml: the compilation that prints the term failed" >&2
  exit 1
fi
if ! grep -q 'module_symbol' "$work/$name.raw"; then
  echo "$name.ml: -drawflambda printed no term" >&2
  exit 1
fi
if grep -q 'Is_int_generic' "$work/$name.raw"; then
  if ! grep -qx "$name" "$dir/generic_is_int.txt"; then
    echo "$name.ml: the term that the compiler gives to Simplify has" >&2
    echo "Is_int_generic, the test of being an integer that is for any" >&2
    echo "value. The text writes it as the test that is for variants, and" >&2
    echo "it is read as that one: the unit read is not the compiler's." >&2
    echo "generic_is_int.txt says how such a unit may be kept." >&2
    exit 1
  fi
fi

# What the compiler printed, as one line with single spaces: it cuts what it
# prints into lines by their width.
tr '\n' ' ' <"$work/$name.raw" | tr -s ' ' >"$work/$name.line"

# The text does not say that a call is a probe, and the call is read as a
# plain one (label C2-17); the program runs the handler of a probe only while
# the probe is enabled. The compiler prints "(probe NAME)" in a call that is
# one and "(probe ())" in any other. A unit whose term has one is refused if
# the tool is run on it.
if [ -f "$dir/$name.expected" ] &&
  grep -q '(probe [^(]' "$work/$name.line"; then
  echo "$name.ml: the term that the compiler gives to Simplify has a call" >&2
  echo "that is a probe. The text does not say so, and the call is read" >&2
  echo "as a plain call, which is always made: the unit read is not the" >&2
  echo "compiler's." >&2
  exit 1
fi

# The text does not give the arity of the arguments of a call of unknown
# arity. Such a call is read with one value for each argument, and the tool
# then gives it one kind for each argument (label C2-5): one component for
# each argument that the text writes, either way. In the compiler's arity the
# arguments may be grouped. An argument that is an unboxed product is one
# component, printed "#(...)"; the product of nothing is printed "void", and
# the text does not write such an argument at all. An application counts the
# components against the parameters of the code, to tell a full application
# from a partial application or an over-application, and the text writes the
# parameters of code with no grouping either, and none for a parameter that
# is the product of nothing. So a call of unknown arity is read as the
# compiler has it, as far as the grouping goes, if neither it nor the code
# that it reaches has a group, and may not be if one of them has; and of what
# is read from the text it can reach the code of the unit. A unit that has a
# call of unknown arity is therefore refused, where the tool is run on it, if
# such a call has a group among its arguments, or if code that the unit binds
# has one among its parameters (labels C2-5 and C2-30). A unit that has only
# direct calls is not: a direct call has the parameters of its code.
#
# What is printed of a call begins with the arity of its arguments, then that
# of its result, then its kind; of code, the arity of its parameters is
# followed by their modes; the kinds of an arity are separated by " ⨯ ". A
# unit of which that is not found is refused too.
calls=0
sed 's/(args_arity /\
(args_arity /g; s/(params_arity /\
(params_arity /g' "$work/$name.line" | awk '
  function grouped(arity,    n, kinds, i) {
    if (index(arity, "#(") > 0) return 1
    n = split(arity, kinds, " ⨯ ")
    for (i = 1; i <= n; i++) if (kinds[i] == "void") return 1
    return 0
  }
  /^\(params_arity / {
    j = index($0, ") (param_modes ")
    if (j == 0) { bad = 1; next }
    if (grouped(substr($0, 15, j - 15))) code_grouped = 1
  }
  /^\(args_arity / {
    j = index($0, ") (return_arity ")
    k = index($0, "(call_kind ")
    if (j == 0 || k == 0) { bad = 1; next }
    unknown = "(call_kind (Function (function_call Indirect_unknown_arity"
    if (index(substr($0, k), unknown) == 1) {
      call_of_unknown_arity = 1
      if (grouped(substr($0, 13, j - 13))) call_grouped = 1
    }
  }
  END {
    if (bad) exit 12
    if (call_grouped) exit 10
    if (call_of_unknown_arity && code_grouped) exit 11
  }' || calls=$?
# No verdict is given of the text of a unit that the tool is not run on.
if [ ! -f "$dir/$name.expected" ]; then
  calls=0
fi
case "$calls" in
0) ;;
10)
  echo "$name.ml: the term that the compiler gives to Simplify has a call" >&2
  echo "of unknown arity with an unboxed product among its arguments, which" >&2
  echo "may be the product of nothing. The text does not group the" >&2
  echo "arguments of such a call, nor write an argument that has no kind" >&2
  echo "in it: the unit read is not the compiler's." >&2
  exit 1
  ;;
11)
  echo "$name.ml: the term that the compiler gives to Simplify has a call" >&2
  echo "of unknown arity, and code with an unboxed product among its" >&2
  echo "parameters, which may be the product of nothing. The text does not" >&2
  echo "group the parameters of code, nor write one that has no kind in" >&2
  echo "it, and nothing in it says that the call does not reach that code:" >&2
  echo "the unit read may not be the compiler's." >&2
  exit 1
  ;;
*)
  echo "$name.ml: what -drawflambda printed of a call or of code is not" >&2
  echo "what this script expects, so it cannot tell whether the unit has" >&2
  echo "a call of unknown arity that it refuses." >&2
  exit 1
  ;;
esac

cp "$work/$name.fl" "$name.fl.made"
cp "$work/$name.cmi" "$work/$name.cmx" .
