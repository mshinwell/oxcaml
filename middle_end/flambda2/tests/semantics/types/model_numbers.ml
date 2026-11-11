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

(* The numbers of the Rocq model, and OCaml's.

   The model's numbers are extracted as they are, binary: [positive], [Z] and
   [nat] (middle_end/flambda2/rocq/FlambdaExtract.v). This is the conversion
   between them and the numbers of the compiler. It is trusted, like the
   converter of types that uses it (type_converter.ml), and is meant to be read:
   every conversion goes through the bits of a number, least significant first.

   An integer of the compiler (an immediate, an [int8] to a [nativeint], a tag,
   a size) is the [Z] of its signed value. A bit pattern (a float, a vector, a
   mask) is the [Z] of its bits read as a number that is not negative: the 64
   bits of a float, and for a vector its words, [word0] the least significant.
   Back from the model, a number that is outside the range of what it is to
   become has no conversion: the functions answer [None], and never reduce a
   number modulo anything. *)

module Numbers = Flambda2_rocq_semantics.BinNums
module Datatypes = Flambda2_rocq_semantics.Datatypes

type positive = Numbers.positive

type z = Numbers.coq_Z

type nat = Datatypes.nat

(* ---- Bits ------------------------------------------------------------- *)

(* The 64 bits of a word, least significant first. *)
let bits_of_word (word : int64) : bool list =
  List.init 64 (fun i ->
      Int64.equal (Int64.logand (Int64.shift_right_logical word i) 1L) 1L)

(* The number whose bits are given, least significant first; [None] if it is
   zero. Zeros at the top are allowed. *)
let rec positive_of_bits (bits : bool list) : positive option =
  match bits with
  | [] -> None
  | bit :: bits -> (
    match positive_of_bits bits, bit with
    | None, false -> None
    | None, true -> Some Coq_xH
    | Some p, false -> Some (Coq_xO p)
    | Some p, true -> Some (Coq_xI p))

(* The bits of a number, least significant first, the last one set. *)
let rec bits_of_positive (p : positive) : bool list =
  match p with
  | Coq_xH -> [true]
  | Coq_xO p -> false :: bits_of_positive p
  | Coq_xI p -> true :: bits_of_positive p

(* The word whose bits are given, least significant first; [None] if there are
   more than 64. *)
let word_of_bits (bits : bool list) : int64 option =
  if List.compare_length_with bits 64 > 0
  then None
  else
    Some
      (List.fold_right
         (fun bit word ->
           Int64.logor (Int64.shift_left word 1) (if bit then 1L else 0L))
         bits 0L)

(* ---- Bit patterns: numbers that are not negative ---------------------- *)

(* The number whose 64-bit words are given, the least significant first. *)
let z_of_words (words : int64 list) : z =
  match positive_of_bits (List.concat_map bits_of_word words) with
  | None -> Z0
  | Some p -> Zpos p

(* The [count] 64-bit words of a number, the least significant first; [None] if
   it is negative or does not fit. *)
let words_of_z ~count (z : z) : int64 list option =
  let rec split count bits =
    if count = 0
    then match bits with [] -> Some [] | _ :: _ -> None
    else
      let word = List.filteri (fun i _ -> i < 64) bits in
      let rest = List.filteri (fun i _ -> i >= 64) bits in
      match word_of_bits word, split (count - 1) rest with
      | Some word, Some words -> Some (word :: words)
      | None, _ | _, None -> None
  in
  match z with
  | Zneg _ -> None
  | Z0 -> split count []
  | Zpos p -> split count (bits_of_positive p)

(* ---- Signed integers --------------------------------------------------- *)

let z_of_int64 (n : int64) : z =
  if Int64.compare n 0L >= 0
  then z_of_words [n]
  else
    (* [Int64.neg n] read without a sign is the magnitude of [n], also for the
       least [int64], whose magnitude is 2^63. *)
    match positive_of_bits (bits_of_word (Int64.neg n)) with
    | None -> Z0
    | Some p -> Zneg p

let int64_of_z (z : z) : int64 option =
  match z with
  | Z0 -> Some 0L
  | Zpos p -> (
    match word_of_bits (bits_of_positive p) with
    | Some n when Int64.compare n 0L >= 0 -> Some n
    | Some _ | None -> None)
  | Zneg p -> (
    match word_of_bits (bits_of_positive p) with
    | Some magnitude
      when Int64.compare magnitude 0L > 0 || Int64.equal magnitude Int64.min_int
      ->
      Some (Int64.neg magnitude)
    | Some _ | None -> None)

let z_of_int (n : int) : z = z_of_int64 (Int64.of_int n)

let int_of_z (z : z) : int option =
  match int64_of_z z with
  | Some n when Int64.equal (Int64.of_int (Int64.to_int n)) n ->
    Some (Int64.to_int n)
  | Some _ | None -> None

(* A number from 1 up: a name of the model. *)
let positive_of_int (n : int) : positive =
  match z_of_int n with
  | Zpos p -> p
  | Z0 | Zneg _ ->
    invalid_arg "Model_numbers.positive_of_int: not a positive number"

let int_of_positive (p : positive) : int option = int_of_z (Zpos p)

let rec nat_of_int (n : int) : nat =
  if n <= 0 then O else S (nat_of_int (n - 1))

let rec int_of_nat (n : nat) : int =
  match n with O -> 0 | S n -> 1 + int_of_nat n

(* ---- Order and printing ------------------------------------------------ *)

let compare_positive (p : positive) (q : positive) : int =
  let rec compare_bits p q =
    (* Most significant first, of equal lengths. *)
    match p, q with
    | [], [] -> 0
    | bit :: p, bit' :: q ->
      let c = Bool.compare bit bit' in
      if c <> 0 then c else compare_bits p q
    | [], _ :: _ -> -1
    | _ :: _, [] -> 1
  in
  let p = bits_of_positive p and q = bits_of_positive q in
  let c = List.compare_lengths p q in
  if c <> 0 then c else compare_bits (List.rev p) (List.rev q)

let compare_z (a : z) (b : z) : int =
  match a, b with
  | Z0, Z0 -> 0
  | Zpos p, Zpos q -> compare_positive p q
  | Zneg p, Zneg q -> compare_positive q p
  | Zneg _, (Z0 | Zpos _) | Z0, Zpos _ -> -1
  | (Z0 | Zpos _), Zneg _ | Zpos _, Z0 -> 1

(* In decimal where the number fits an [int], and by its bits where not. *)
let print_positive ppf (p : positive) =
  match int_of_positive p with
  | Some n -> Format.pp_print_int ppf n
  | None ->
    Format.pp_print_string ppf "0b";
    List.iter
      (fun bit -> Format.pp_print_char ppf (if bit then '1' else '0'))
      (List.rev (bits_of_positive p))

let print_z ppf (z : z) =
  match z with
  | Z0 -> Format.pp_print_string ppf "0"
  | Zpos p -> print_positive ppf p
  | Zneg p -> Format.fprintf ppf "-%a" print_positive p

let print_nat ppf (n : nat) = Format.pp_print_int ppf (int_of_nat n)
