(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of the modules that
   middle_end/flambda2/simplify/number_adjuncts.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9 makes for itself by applying a functor of another
   part of the compiler, and of what the file uses of them. The port keeps
   the definitions of these modules as they are in the file, and the
   realisations name them as the file does. Made by tools/declgen (see
   decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Numeric_types.

Module For_int8s.
  Module Num.
    (* module Pair, lines 609-613 of the file *)
    Module Pair.
      Module Set_.
        (* container_types.mli:47  include S with type t := T1.t * T2.t *)
        (* abstract here: it is the type Flambda2_algorithms__Container_types.Make_pair(Flambda2_numbers__Numeric_types.Int8)(Flambda2_numbers__Numeric_types.Int8).Set.t is not a global name. *)
        Parameter t : Type.
        Extract Inlined Constant t => "Pair.Set.t".
      End Set_.
      (* container_types.mli:49  val create_from_cross_product : T1.Set.t -> T2.Set.t -> Set.t *)
      Parameter create_from_cross_product : Numeric_types.Int8.Set_.t -> Numeric_types.Int8.Set_.t -> M Number_adjuncts__local.For_int8s.Num.Pair.Set_.t.
      Extract Inlined Constant create_from_cross_product => "Pair.create_from_cross_product".
    End Pair.
  End Num.
End For_int8s.
Module For_int16s.
  Module Num.
    (* module Pair, lines 735-739 of the file *)
    Module Pair.
      Module Set_.
        (* container_types.mli:47  include S with type t := T1.t * T2.t *)
        (* abstract here: it is the type Flambda2_algorithms__Container_types.Make_pair(Flambda2_numbers__Numeric_types.Int16)(Flambda2_numbers__Numeric_types.Int16).Set.t is not a global name. *)
        Parameter t : Type.
        Extract Inlined Constant t => "Pair.Set.t".
      End Set_.
      (* container_types.mli:49  val create_from_cross_product : T1.Set.t -> T2.Set.t -> Set.t *)
      Parameter create_from_cross_product : Numeric_types.Int16.Set_.t -> Numeric_types.Int16.Set_.t -> M Number_adjuncts__local.For_int16s.Num.Pair.Set_.t.
      Extract Inlined Constant create_from_cross_product => "Pair.create_from_cross_product".
    End Pair.
  End Num.
End For_int16s.

(* Not in the file of Simplify: an empty module with the name of this file.
   With it Rocq's extraction writes no [open] of this file, which is not a
   module of OCaml, and prints each of its names in full. *)
Module Number_adjuncts__local. End Number_adjuncts__local.
