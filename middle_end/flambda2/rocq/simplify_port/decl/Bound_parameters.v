(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Bound_parameters], after its interface
   middle_end/flambda2/bound_identifiers/bound_parameters.mli
   (Git blob 8a1178e6a19e64b99ea6920fe3a2fdb7b8236cd4). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameter Flambda_arity Format Int_ids Name_occurrences Renaming Variable_.

(* bound_parameters.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Bound_parameters.t".
(* bound_parameters.mli:19  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Bound_parameters.empty".
(* bound_parameters.mli:21  val create : Bound_parameter.t list -> t *)
Parameter create : list Bound_parameter.t -> M t.
Extract Inlined Constant create => "Bound_parameters.create".
(* bound_parameters.mli:23  val cons : Bound_parameter.t -> t -> t *)
Parameter cons : Bound_parameter.t -> t -> M t.
Extract Inlined Constant cons => "Bound_parameters.cons".
(* bound_parameters.mli:25  val append : t -> t -> t *)
Parameter append : t -> t -> M t.
Extract Inlined Constant append => "Bound_parameters.append".
(* bound_parameters.mli:27  val to_list : t -> Bound_parameter.t list *)
Parameter to_list : t -> M (list Bound_parameter.t).
Extract Inlined Constant to_list => "Bound_parameters.to_list".
(* bound_parameters.mli:29  val is_empty : t -> bool *)
Parameter is_empty : t -> M bool.
Extract Inlined Constant is_empty => "Bound_parameters.is_empty".
(* bound_parameters.mli:31  val same_number : t -> t -> bool *)
Parameter same_number : t -> t -> M bool.
Extract Inlined Constant same_number => "Bound_parameters.same_number".
(* bound_parameters.mli:33  val equal : t -> t -> bool *)
Parameter equal : t -> t -> M bool.
Extract Inlined Constant equal => "Bound_parameters.equal".
(* bound_parameters.mli:35  val arity : t -> [> ] Flambda_arity.t *)
Parameter arity : t -> M Flambda_arity.t.
Extract Inlined Constant arity => "Bound_parameters.arity".
(* bound_parameters.mli:37  val check_no_duplicates : t -> unit *)
Parameter check_no_duplicates : t -> M unit.
Extract Inlined Constant check_no_duplicates => "Bound_parameters.check_no_duplicates".
(* bound_parameters.mli:39  val cardinal : t -> int *)
Parameter cardinal : t -> M int.
Extract Inlined Constant cardinal => "Bound_parameters.cardinal".
(* bound_parameters.mli:41  val simples : t -> Int_ids.Simple.t list *)
Parameter simples : t -> M (list Int_ids.Simple.t).
Extract Inlined Constant simples => "Bound_parameters.simples".
(* bound_parameters.mli:43  val to_set : t -> Bound_parameter.Set.t *)
Parameter to_set : t -> M Bound_parameter.Set_.t.
Extract Inlined Constant to_set => "Bound_parameters.to_set".
(* bound_parameters.mli:45  val vars : t -> Variable.t list *)
Parameter vars : t -> M (list Variable_.t).
Extract Inlined Constant vars => "Bound_parameters.vars".
(* bound_parameters.mli:49  val var_set : t -> Variable.Set.t *)
Parameter var_set : t -> M Variable_.Set_.t.
Extract Inlined Constant var_set => "Bound_parameters.var_set".
(* bound_parameters.mli:53  val filter : (Bound_parameter.t -> bool) -> t -> t *)
Parameter filter : (Bound_parameter.t -> M bool) -> t -> M t.
Extract Inlined Constant filter => "Bound_parameters.filter".
(* bound_parameters.mli:57  include Bindable.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Bound_parameters.free_names".
(* bound_parameters.mli:57  include Bindable.S with type t := t *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Bound_parameters.print".
(* bound_parameters.mli:57  include Bindable.S with type t := t *)
Parameter rename : t -> M t.
Extract Inlined Constant rename => "Bound_parameters.rename".
(* bound_parameters.mli:57  include Bindable.S with type t := t *)
Parameter renaming : t -> t -> M Renaming.t.
Extract Inlined Constant renaming => "Bound_parameters.renaming".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Bound_parameters. End Bound_parameters.
