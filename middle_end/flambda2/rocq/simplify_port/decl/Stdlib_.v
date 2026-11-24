(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Stdlib], after its interface
   stdlib/stdlib.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* the type [char] that OCaml defines before any module *)
Parameter char : Type.
Extract Inlined Constant char => "char".
(* the type [float] that OCaml defines before any module *)
Parameter float_ : Type.
Extract Inlined Constant float_ => "float".
(* the type [int32] that OCaml defines before any module *)
Parameter int32 : Type.
Extract Inlined Constant int32 => "int32".
(* the type [int64] that OCaml defines before any module *)
Parameter int64 : Type.
Extract Inlined Constant int64 => "int64".
(* raise: in the kit (Port_monad.v). *)
(* raise_notrace: in the kit (Port_monad.v). *)
(* stdlib/stdlib.mli  val invalid_arg : string -> 'a *)
Parameter invalid_arg : forall {A : Type}, string -> M A.
Extract Inlined Constant invalid_arg => "invalid_arg".
(* _none_  exception Invalid_argument *)
Parameter Invalid_argument : exception string.
Extract Inlined Constant Invalid_argument => "((fun x__1 -> Invalid_argument x__1), (function Invalid_argument x__1 -> Some x__1 | _ -> None))".
(* Not_found: in the kit (Port_monad.v). *)
(* NOT DECLARED: ( = ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( <> ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( < ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( > ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( <= ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( >= ): an operator of Stdlib: the kit and Rocq have their own. *)
(* max: in the kit (Port_monad.v). *)
(* NOT DECLARED: ( == ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( != ): an operator of Stdlib: the kit and Rocq have their own. *)
(* not: in the kit (Port_monad.v). *)
(* NOT DECLARED: ( && ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( || ): an operator of Stdlib: the kit and Rocq have their own. *)
(* stdlib/stdlib.mli  val __LOC__ : string *)
Parameter __LOC__ : string.
Extract Inlined Constant __LOC__ => "__LOC__".
(* NOT DECLARED: ( |> ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( ~- ): an operator of Stdlib: the kit and Rocq have their own. *)
(* succ: in the kit (Port_monad.v). *)
(* NOT DECLARED: ( + ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( - ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( / ): an operator of Stdlib: the kit and Rocq have their own. *)
(* stdlib/stdlib.mli  val mod : int -> int -> int *)
Parameter mod_ : int -> int -> M int.
Extract Inlined Constant mod_ => "( mod )".
(* stdlib/stdlib.mli  val max_int : int *)
Parameter max_int : int.
Extract Inlined Constant max_int => "max_int".
(* stdlib/stdlib.mli  val land : int -> int -> int *)
Parameter land : int -> int -> M int.
Extract Inlined Constant land => "( land )".
(* stdlib/stdlib.mli  val lor : int -> int -> int *)
Parameter lor : int -> int -> M int.
Extract Inlined Constant lor => "( lor )".
(* stdlib/stdlib.mli  val lsl : int -> int -> int *)
Parameter lsl : int -> int -> M int.
Extract Inlined Constant lsl => "( lsl )".
(* stdlib/stdlib.mli  val lsr : int -> int -> int *)
Parameter lsr : int -> int -> M int.
Extract Inlined Constant lsr => "( lsr )".
(* NOT DECLARED: ( ^ ): an operator of Stdlib: the kit and Rocq have their own. *)
(* ignore: in the kit (Port_monad.v). *)
(* stdlib/stdlib.mli  val string_of_int : int -> string *)
Parameter string_of_int : int -> M string.
Extract Inlined Constant string_of_int => "string_of_int".
(* stdlib/stdlib.mli  val fst : 'a * 'b -> 'a *)
Parameter fst : forall {A B : Type}, (A * B) -> M A.
Extract Inlined Constant fst => "fst".
(* stdlib/stdlib.mli  val snd : 'a * 'b -> 'b *)
Parameter snd : forall {A B : Type}, (A * B) -> M B.
Extract Inlined Constant snd => "snd".
(* NOT DECLARED: ( @ ): an operator of Stdlib: the kit and Rocq have their own. *)
(* stdlib/stdlib.mli  type out_channel *)
Parameter out_channel : Type.
Extract Inlined Constant out_channel => "out_channel".
(* stdlib/stdlib.mli  val open_out : string -> out_channel *)
Parameter open_out : string -> M out_channel.
Extract Inlined Constant open_out => "open_out".
(* stdlib/stdlib.mli  val close_out : out_channel -> unit *)
Parameter close_out : out_channel -> M unit.
Extract Inlined Constant close_out => "close_out".
(* ref: in the kit (Port_monad.v). *)
(* NOT DECLARED: ( ! ): an operator of Stdlib: the kit and Rocq have their own. *)
(* NOT DECLARED: ( := ): an operator of Stdlib: the kit and Rocq have their own. *)
(* stdlib/stdlib.mli  val incr : int ref -> unit *)
Parameter incr : ref int -> M unit.
Extract Inlined Constant incr => "incr".
(* stdlib/stdlib.mli  val at_exit : (unit -> unit) -> unit *)
Parameter at_exit : (unit -> M unit) -> M unit.
Extract Inlined Constant at_exit => "at_exit".
