(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* The compiler, with the check of the test tool (../flsemantics.ml) made of the
   two terms of its own run. It is the driver of the compiler
   (driver/oxcaml_main.ml) with two hooks registered (driver/compiler_hooks.mli)
   and nothing else: it takes the command line of the compiler and compiles as
   the compiler does.

   The first mode of the tool (../flsemantics_main.ml) checks a pair that the
   tool makes: it reads the text that [-drawfexpr] prints of the term given to
   Simplify, and runs Simplify on what the reader made of the text. The text has
   not got all that the term has, and Simplify reads some of what is lost
   (../../semantics/ocaml/README.md, "What a validation does not say"). Here
   there is no text, no reader and no second Simplify.

   The hook [Raw_flambda2] is given the term that the compiler gives to Simplify
   (middle_end/flambda2/flambda2.ml, [flambda_to_flambda0], before anything else
   is done with the term). As the tool does of the term it has read, the driver
   asks whether it is well-formed, before Simplify runs.

   The hook [Flambda2] is given the term that the compiler's own Simplify
   returned (the same function, after [Simplify.run]). The two terms, as they
   are in memory, are given to [Flsemantics.check]: both are converted to the
   model, both are run, what the runs come to is compared, and the validator is
   asked. Nothing is done to either term before that: what the tool does to a
   term that it has read from a text ([Flsemantics.as_read_from_text]) is for
   what the text has lost, and is not done here.

   What is printed is what the tool prints, under the name <unit>.fl, so that
   the two modes can be compared line by line. The conversion is the tool's, as
   it is: it sees in these terms what the text does not write (the kinds of the
   fields of a [Make_block], for one), and says "not checked" of what the model
   has not got.

   What is trusted here and not in the first mode: that the two hooks are given
   the terms that the compiler goes on with. What is not checked: the term after
   the reaper, where it is enabled (the hook [Reaped_flambda2]), and a unit on
   which the compiler does not run Simplify ([-Oclassic], or an attribute of the
   unit that asks for it), of which the driver says so.

   The units asked about are those whose .cmx file the compilation has read when
   Simplify returns ([Flsemantics.units_read]): the check must load no other, as
   [Compilenv] would record it among the imports of the unit being compiled.
   Which files the compilation finds is for the compiler's load path
   ([Compmisc.init_path]): the current directory unless [-nocwd] is given, the
   directories of [-I] and [-H], and the standard library unless [-nostdlib] is
   given. The first mode looks only in the directories of [-I]
   ([Flsemantics.init_load_path]).

   One unit is checked in a process, as in the first mode. Given a second unit,
   the driver says so of it, checks nothing from then on, and exits with 2 where
   the compiler exits 0.

   The driver exits with the status of the compiler; with 1 if the compiler
   exits 0 and the check failed (as the first mode does: the term after is not
   well-formed, or the two runs differ); and with 2 if the check raised an
   exception, which is printed, or a second unit was given. *)

(* Eta-expansion gives [create_process] and [waitpid] the unannotated types
   required by [Compiler_owee.Unix_intf.S] (as in driver/oxcaml_main.ml). *)
module Unix_for_owee = struct
  include Unix

  let create_process prog args stdin stdout stderr =
    Unix.create_process prog args stdin stdout stderr

  let waitpid flags pid = Unix.waitpid flags pid
end

(* The name under which the unit being compiled is shown: that of the file that
   the first mode would be given. *)
let shown () =
  match Env.get_current_unit () with
  | Some unit_info ->
    String.uncapitalize_ascii
      (Compilation_unit.name_as_string (Unit_info.modname unit_info))
    ^ ".fl"
  | None -> "(no unit).fl"

type state =
  | No_unit_yet
  | Given_to_simplify of
      { unit : Flambda2_terms.Flambda_unit.t;
        well_formed : bool;
        shown : string
      }
  | Checked
  | Refused

(* Where the run is. [Given_to_simplify] holds the term given to Simplify until
   Simplify has returned. [Refused] is for good: a second unit has come in this
   process, and nothing is checked from then on. *)
let state = ref No_unit_yet

(* The status of the check: 0, 1 where it failed, 2 where it raised or was
   refused. *)
let status = ref 0

let guarded ~shown what f =
  try f ()
  with exn ->
    Format.printf "%s: the check stopped (%s): %s@." shown what
      (Printexc.to_string exn);
    status := max !status 2

let simplify_not_run shown =
  Format.printf
    "%s: not checked: the compiler did not run Simplify on the unit@." shown

let on_raw_flambda (unit : Flambda2_terms.Flambda_unit.t) =
  let shown = shown () in
  match !state with
  | No_unit_yet ->
    state := Given_to_simplify { unit; well_formed = false; shown };
    guarded ~shown "the term given to Simplify" (fun () ->
        let well_formed = Flsemantics.well_formed_before ~filename:shown unit in
        state := Given_to_simplify { unit; well_formed; shown })
  | (Given_to_simplify _ | Checked | Refused) as earlier ->
    (* One unit to a process, as in the first mode: the conversion keeps what it
       has noted of a unit. Where Simplify was not run on the first unit its
       term is still held: it is let go here, before anything is printed, so
       that it is not compared with the term that Simplify returns for this
       unit. *)
    state := Refused;
    status := max !status 2;
    (match earlier with
    | Given_to_simplify { shown = first; well_formed = true; _ } ->
      simplify_not_run first
    | No_unit_yet | Given_to_simplify _ | Checked | Refused -> ());
    Format.printf
      "%s: not checked: a second unit in one process; run the driver once for \
       each unit@."
      shown

let on_flambda (after : Flambda2_terms.Flambda_unit.t) =
  match !state with
  | No_unit_yet | Checked | Refused -> ()
  | Given_to_simplify { well_formed = false; _ } -> state := Checked
  | Given_to_simplify { unit; well_formed = true; shown } ->
    state := Checked;
    guarded ~shown "the two terms" (fun () ->
        match
          Flsemantics.check ~filename:shown
            ~units:(Flsemantics.units_read ())
            unit after
        with
        | Failed -> status := max !status 1
        | Not_checked | Compared _ -> ())

let () =
  Compiler_hooks.register Raw_flambda2 on_raw_flambda;
  Compiler_hooks.register Flambda2 on_flambda;
  let compiler =
    Optmaindriver.main
      (module Unix_for_owee : Compiler_owee.Unix_intf.S)
      Sys.argv Format.err_formatter
      ~flambda2:(module Flambda2)
  in
  (match !state with
  | Given_to_simplify { shown; well_formed = true; _ } when compiler = 0 ->
    simplify_not_run shown
  | No_unit_yet | Given_to_simplify _ | Checked | Refused -> ());
  exit (if compiler <> 0 then compiler else !status)
