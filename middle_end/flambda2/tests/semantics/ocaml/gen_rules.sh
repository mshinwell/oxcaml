#!/bin/sh

# Writes the dune rules for the OCaml examples of this directory, for
# run/dune to include (see dune). The arguments are the .ml, .mli, .fl and
# .expected files that are here. The rules are for run/, so they name the
# files here with ../ .

set -eu

examples=" "
interfaces=" "
for file in "$@"; do
  case "$file" in
  *.mli) interfaces="$interfaces$(basename "$file" .mli) " ;;
  *.ml) examples="$examples$(basename "$file" .ml) " ;;
  esac
done

for name in $examples; do
  interface=
  case "$interfaces" in
  *" $name "*) interface=" %{dep:../$name.mli}" ;;
  esac
  cat <<RULES
(rule
 (targets $name.fl.made)
 (deps$interface)
 (action
  (run sh %{dep:../from_ocaml.sh} %{ocamlopt} %{dep:../$name.ml}
   $name.fl.made)))

(rule
 (alias runtest)
 (action
  (diff ../$name.fl $name.fl.made)))

(rule
 (with-stdout-to
  $name.output
  (run ../../../tools/flsemantics.exe %{dep:../$name.fl})))

(rule
 (alias runtest)
 (action
  (diff ../$name.expected $name.output)))

RULES
done

# A term or an expected file whose source is gone would never be looked at.
for file in "$@"; do
  case "$file" in
  *.fl | *.expected | *.mli)
    name=$(basename "$file")
    name=${name%.*}
    case "$examples" in
    *" $name "*) ;;
    *)
      cat <<RULES
(rule
 (alias runtest)
 (action
  (progn
   (echo "$(basename "$file") has no $name.ml beside it\n")
   (run false))))

RULES
      ;;
    esac
    ;;
  esac
done
