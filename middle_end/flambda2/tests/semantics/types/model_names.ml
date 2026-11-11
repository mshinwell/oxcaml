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

(* The names of the compiler as the numbers that names are in the Rocq model.

   In the model a variable, a symbol, a code id, a value slot and a function
   slot are each a [positive] (FlambdaModel.v, FlambdaTypeGrammar.v), and a
   variable and a symbol may be the same number. The converter of types
   (type_converter.ml) is given a numbering: for each sort of name, the number
   of a name of the compiler and the name that has a number.

   What is trusted of a numbering, whoever gives it: that for each sort it is
   one-to-one, so that two names of the compiler are one number only if they are
   one name, and that it is the same wherever the types and the terms of one
   test are converted. [create] makes such a numbering: each sort is numbered
   from 1 in the order in which its names are first asked for, which is how the
   test tool of the semantics numbers the names of terms
   (../../tools/flsemantics.ml, [Numbering]). Nothing is assumed of the order of
   the numbers: no function of the model compares two names but for equality.

   A number that no name has been given has no name: the conversion from the
   model fails on it, and does not make a name up. *)

open Flambda2_identifiers

type positive = Model_numbers.positive

type 'name sort =
  { number : 'name -> positive;
    named : positive -> 'name option
  }

type t =
  { variables : Variable.t sort;
    symbols : Symbol.t sort;
    code_ids : Code_id.t sort;
    value_slots : Value_slot.t sort;
    function_slots : Function_slot.t sort
  }

module Numbering (Id : sig
  type t

  val compare : t -> t -> int
end) =
struct
  module Numbers_of_names = Map.Make (Id)
  module Names_of_numbers = Map.Make (Int)

  let create () : Id.t sort =
    let numbers = ref Numbers_of_names.empty in
    let names = ref Names_of_numbers.empty in
    let number id =
      match Numbers_of_names.find_opt id !numbers with
      | Some n -> Model_numbers.positive_of_int n
      | None ->
        let n = Numbers_of_names.cardinal !numbers + 1 in
        numbers := Numbers_of_names.add id n !numbers;
        names := Names_of_numbers.add n id !names;
        Model_numbers.positive_of_int n
    in
    let named p =
      Option.bind (Model_numbers.int_of_positive p) (fun n ->
          Names_of_numbers.find_opt n !names)
    in
    { number; named }
end

module Variables = Numbering (Variable)
module Symbols = Numbering (Symbol)
module Code_ids = Numbering (Code_id)
module Value_slots = Numbering (Value_slot)
module Function_slots = Numbering (Function_slot)

let create () : t =
  { variables = Variables.create ();
    symbols = Symbols.create ();
    code_ids = Code_ids.create ();
    value_slots = Value_slots.create ();
    function_slots = Function_slots.create ()
  }
