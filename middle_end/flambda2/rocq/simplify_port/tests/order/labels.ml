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

(* The order in which the arguments of a total application are evaluated when
   its labelled arguments are written in another order than the parameters of
   the function. Each argument prints its name when it is evaluated. It follows
   no file of the compiler. *)
let f ~a ~b ~c d = a + b + c + d

let say name v =
  print_string name;
  print_char ' ';
  v

let () =
  print_string "parameters a b c d; the call writes d, c, a, b: evaluated ";
  let r = f (say "d" 4) ~c:(say "c" 3) ~a:(say "a" 1) ~b:(say "b" 2) in
  print_newline ();
  print_string "parameters a b c d; the call writes b, a, d, c: evaluated ";
  let r' = f ~b:(say "b" 2) ~a:(say "a" 1) (say "d" 4) ~c:(say "c" 3) in
  print_newline ();
  assert (r = 10 && r' = 10)
