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

(* The name that Git gives the content of a file. With it a file of decl/ says
   which text it follows by the text itself, and not by a commit: two commits in
   which the file has the same bytes give it the same name. This file follows no
   file of the compiler.

   The name is the SHA-1 of the word [blob], a space, the number of the bytes in
   decimal, a byte zero, and then the bytes: what [git hash-object FILE] prints,
   and what [git rev-parse COMMIT:PATH] prints of a file of a commit. Git is not
   called, and OCaml's library has no SHA-1, so it is computed here. *)

let mask = 0xFFFFFFFF

let rotate x n = (x lsl n) lor (x lsr (32 - n)) land mask

(* The SHA-1 of a string, as 40 digits. The numbers are of 32 bits, held in
   OCaml's integers of 63. *)
let sha1 s =
  let len = String.length s in
  (* the text, a byte 0x80, zeros, and the number of bits in 8 bytes: a whole
     number of blocks of 64 bytes *)
  let total = (((len + 8) / 64) + 1) * 64 in
  let padded = Bytes.make total '\000' in
  Bytes.blit_string s 0 padded 0 len;
  Bytes.set padded len '\x80';
  let bits = len * 8 in
  for i = 0 to 7 do
    Bytes.set padded (total - 1 - i) (Char.chr ((bits lsr (8 * i)) land 0xFF))
  done;
  let h = [| 0x67452301; 0xEFCDAB89; 0x98BADCFE; 0x10325476; 0xC3D2E1F0 |] in
  let w = Array.make 80 0 in
  for block = 0 to (total / 64) - 1 do
    for t = 0 to 15 do
      let byte k = Char.code (Bytes.get padded ((block * 64) + (t * 4) + k)) in
      w.(t) <- (byte 0 lsl 24) lor (byte 1 lsl 16) lor (byte 2 lsl 8) lor byte 3
    done;
    for t = 16 to 79 do
      w.(t)
        <- rotate (w.(t - 3) lxor w.(t - 8) lxor w.(t - 14) lxor w.(t - 16)) 1
    done;
    let a = ref h.(0) in
    let b = ref h.(1) in
    let c = ref h.(2) in
    let d = ref h.(3) in
    let e = ref h.(4) in
    for t = 0 to 79 do
      let f, k =
        if t < 20
        then !b land !c lor (lnot !b land mask land !d), 0x5A827999
        else if t < 40
        then !b lxor !c lxor !d, 0x6ED9EBA1
        else if t < 60
        then !b land !c lor (!b land !d) lor (!c land !d), 0x8F1BBCDC
        else !b lxor !c lxor !d, 0xCA62C1D6
      in
      let next = (rotate !a 5 + f + !e + k + w.(t)) land mask in
      e := !d;
      d := !c;
      c := rotate !b 30;
      b := !a;
      a := next
    done;
    h.(0) <- (h.(0) + !a) land mask;
    h.(1) <- (h.(1) + !b) land mask;
    h.(2) <- (h.(2) + !c) land mask;
    h.(3) <- (h.(3) + !d) land mask;
    h.(4) <- (h.(4) + !e) land mask
  done;
  Printf.sprintf "%08x%08x%08x%08x%08x" h.(0) h.(1) h.(2) h.(3) h.(4)

let of_text text =
  sha1 (Printf.sprintf "blob %d\000" (String.length text) ^ text)
