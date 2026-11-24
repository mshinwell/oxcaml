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

(* What the extracted files of the port of Simplify call where Rocq's extraction
   has no OCaml syntax to print: handlers of exceptions and [while]. It also
   gives the type names that Rocq prints in the comments of the extracted files.
   Written for the port; it follows no file of the compiler. The extracted files
   begin with [open Port_monad]. *)

type 'a coq_M = 'a

(* Two modules of the compiler have a name that Rocq reserves, and Rocq prints
   the name that the declarations give them. *)
module Variable_ = Flambda2_identifiers.Variable
module Stdlib_ = Stdlib

type 'a box = 'a

type ('a, 'b, 'c) tuple3 = 'a * 'b * 'c

type ('a, 'b, 'c, 'd) tuple4 = 'a * 'b * 'c * 'd

type ('a, 'b, 'c, 'd, 'e) tuple5 = 'a * 'b * 'c * 'd * 'e

type ('a, 'b, 'c, 'd, 'e, 'f) tuple6 = 'a * 'b * 'c * 'd * 'e * 'f

(* A declared exception whose argument has type ['p]: how to make its value and
   how to know it. *)
type 'p exception_ = ('p -> exn) * (exn -> 'p option)

let not_found : unit exception_ =
  (fun () -> Not_found), function Not_found -> Some () | _ -> None

let fatal_error_exception : unit exception_ =
  ( (fun () -> Misc.Fatal_error),
    function Misc.Fatal_error -> Some () | _ -> None )

(* [raise (E p)] *)
let raise_ ((make, _) : 'p exception_) (p : 'p) = raise (make p)

(* [try body () with E p -> handler p] *)
let try_with body ((_, select) : 'p exception_) handler =
  try body ()
  with e -> (
    let bt = Printexc.get_raw_backtrace () in
    match select e with
    | Some p -> handler p
    | None -> Printexc.raise_with_backtrace e bt)

(* [try body () with e -> handler e] *)
let try_with_any body handler = try body () with e -> handler e

(* [match body () with exception E p -> handler p | x -> k x] *)
let match_exn body ((_, select) : 'p exception_) handler k =
  match body () with
  | exception e -> (
    let bt = Printexc.get_raw_backtrace () in
    match select e with
    | Some p -> handler p
    | None -> Printexc.raise_with_backtrace e bt)
  | x -> k x

(* [while cond () do body () done] *)
let while_ cond body =
  while cond () do
    body ()
  done
