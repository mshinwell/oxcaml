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

(* The order in which the two sides of a pipe ([x |> f ..], [f .. @@ x]) are
   evaluated. [f] takes the piped value BEFORE its labelled parameter, [g] takes
   it AFTER its other parameter. Each argument prints its name when it is
   evaluated. It follows no file of the compiler. *)
let say name v =
  print_string name;
  print_char ' ';
  v

let f x ~without = x + without

let g a x = a + x

let () =
  print_string "x |> f ~without:l, f's parameters x without: evaluated ";
  let r1 = say "x" 1 |> f ~without:(say "l" 2) in
  print_newline ();
  print_string "f x ~without:l: evaluated ";
  let r2 = f (say "x" 1) ~without:(say "l" 2) in
  print_newline ();
  print_string "f ~without:l @@ x: evaluated ";
  let r3 = f ~without:(say "l" 2) @@ say "x" 1 in
  print_newline ();
  print_string "x |> f ~without:a |> f ~without:b: evaluated ";
  let r4 = say "x" 1 |> f ~without:(say "a" 2) |> f ~without:(say "b" 3) in
  print_newline ();
  print_string "x |> g a, g's parameters a x: evaluated ";
  let r5 = say "x" 1 |> g (say "a" 2) in
  print_newline ();
  print_string "g a x: evaluated ";
  let r6 = g (say "a" 2) (say "x" 1) in
  print_newline ();
  print_string "x |> g a |> g b: evaluated ";
  let r7 = say "x" 1 |> g (say "a" 2) |> g (say "b" 3) in
  print_newline ();
  assert (r1 = 3 && r2 = 3 && r3 = 3 && r4 = 6 && r5 = 3 && r6 = 3 && r7 = 6)
