(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simple], after its interface
   middle_end/flambda2/term_basics/simple.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Coercion Debuginfo Flambda_kind Format Int_ids Name_occurrences Or_null Reg_width_const Symbol Target_ocaml_int Target_system Variable_.

(* int_ids.mli:200  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Simple.t.
Extract Inlined Constant t => "Simple.t".
(* module T = Int_ids.Simple.T: declared again here under this name. *)
Module T.
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Simple.T.t.
  Extract Inlined Constant t => "Simple.T.t".
End T.
(* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
Parameter equal : Simple.T.t -> Simple.T.t -> M bool.
Extract Inlined Constant equal => "Simple.equal".
(* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
Parameter compare : Simple.T.t -> Simple.T.t -> M int.
Extract Inlined Constant compare => "Simple.compare".
(* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
Parameter print : Format.formatter -> Simple.T.t -> M unit.
Extract Inlined Constant print => "Simple.print".
(* module Set = Int_ids.Simple.Set: declared again here under this name. *)
Module Set_.
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Definition elt : Type := Int_ids.Simple.Set_.elt.
  Extract Inlined Constant elt => "Simple.Set.elt".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Simple.Set_.t.
  Extract Inlined Constant t => "Simple.Set.t".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Simple.Set.empty".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter is_empty : t -> M bool.
  Extract Inlined Constant is_empty => "Simple.Set.is_empty".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Simple.Set.mem".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Simple.Set.add".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter singleton : elt -> M t.
  Extract Inlined Constant singleton => "Simple.Set.singleton".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Simple.Set.union".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter inter : t -> t -> M t.
  Extract Inlined Constant inter => "Simple.Set.inter".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Simple.Set.diff".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Simple.Set.equal".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  Extract Inlined Constant iter => "Simple.Set.iter".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter map : (elt -> M elt) -> t -> M t.
  Extract Inlined Constant map => "Simple.Set.map".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Simple.Set.fold".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter cardinal : t -> M int.
  Extract Inlined Constant cardinal => "Simple.Set.cardinal".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter choose : t -> M elt.
  Extract Inlined Constant choose => "Simple.Set.choose".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter of_list : list elt -> M t.
  Extract Inlined Constant of_list => "Simple.Set.of_list".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Simple.Set.print".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter get_singleton : t -> M (option elt).
  Extract Inlined Constant get_singleton => "Simple.Set.get_singleton".
End Set_.
(* module Map = Int_ids.Simple.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Definition key : Type := Int_ids.Simple.Map.key.
  Extract Inlined Constant key => "Simple.Map.key".
  (* module Set = Int_ids.Simple.Map.Set: declared again here under this name. *)
  Module Set_.
    (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
    Definition t : Type := Int_ids.Simple.Map.Set_.t.
    Extract Inlined Constant t => "Simple.Map.Set.t".
  End Set_.
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Simple.Map.t A.
  Extract Constant t "'a1" => "('a1) Simple.Map.t".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Simple.Map.empty".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter is_empty : forall {A : Type}, t A -> M bool.
  Extract Inlined Constant is_empty => "Simple.Map.is_empty".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  Extract Inlined Constant mem => "Simple.Map.mem".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Simple.Map.add".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Simple.Map.update".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
  Extract Inlined Constant equal => "Simple.Map.equal".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
  Extract Inlined Constant iter => "Simple.Map.iter".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Simple.Map.fold".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Simple.Map.exists".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Simple.Map.find".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Simple.Map.find_opt".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Simple.Map.find_or_null".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter keys : forall {A : Type}, t A -> M Simple.Map.Set_.t.
  Extract Inlined Constant keys => "Simple.Map.keys".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter of_set : forall {A : Type}, (key -> M A) -> Simple.Map.Set_.t -> M (t A).
  Extract Inlined Constant of_set => "Simple.Map.of_set".
  (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Simple.Map.print".
End Map.
(* int_ids.mli:206  val name : Name.t -> t *)
Parameter name : Int_ids.Name.t -> M t.
Extract Inlined Constant name => "Simple.name".
(* int_ids.mli:208  val var : Variable.t -> t *)
Parameter var : Int_ids.Variable_.t -> M t.
Extract Inlined Constant var => "Simple.var".
(* int_ids.mli:212  val symbol : Symbol.t -> t *)
Parameter symbol : Int_ids.Symbol.t -> M t.
Extract Inlined Constant symbol => "Simple.symbol".
(* int_ids.mli:214  val const : Const.t -> t *)
Parameter const : Int_ids.Const.t -> M t.
Extract Inlined Constant const => "Simple.const".
(* int_ids.mli:216  val coercion : t -> Coercion.t *)
Parameter coercion : t -> M Int_ids.Coercion.t.
Extract Inlined Constant coercion => "Simple.coercion".
(* int_ids.mli:218  val with_coercion : t -> Coercion.t -> t *)
Parameter with_coercion : t -> Int_ids.Coercion.t -> M t.
Extract Inlined Constant with_coercion => "Simple.with_coercion".
(* int_ids.mli:225  val pattern_match : t -> name:(Name.t -> coercion:Coercion.t -> 'a) -> const:(Const.t -> 'a) -> 'a *)
Parameter pattern_match : forall {A : Type}, t -> (Int_ids.Name.t -> Int_ids.Coercion.t -> M A) -> (Int_ids.Const.t -> M A) -> M A.
Extract Inlined Constant pattern_match => "Simple.pattern_match".
(* simple.mli:24  include Contains_names.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Simple.free_names".
(* simple.mli:30  val apply_coercion_exn : t -> Coercion.t -> t *)
Parameter apply_coercion_exn : t -> Coercion.t -> M t.
Extract Inlined Constant apply_coercion_exn => "Simple.apply_coercion_exn".
(* simple.mli:32  val without_coercion : t -> t *)
Parameter without_coercion : t -> M t.
Extract Inlined Constant without_coercion => "Simple.without_coercion".
(* simple.mli:34  val must_be_var : t -> (Variable.t * Coercion.t) option *)
Parameter must_be_var : t -> M (option (Variable_.t * Coercion.t)).
Extract Inlined Constant must_be_var => "Simple.must_be_var".
(* simple.mli:40  val must_be_const : t -> Reg_width_const.t option *)
Parameter must_be_const : t -> M (option Reg_width_const.t).
Extract Inlined Constant must_be_const => "Simple.must_be_const".
(* simple.mli:43  val const_int : Target_ocaml_int.t -> t *)
Parameter const_int : Target_ocaml_int.t -> M t.
Extract Inlined Constant const_int => "Simple.const_int".
(* simple.mli:49  val untagged_const_bool : Target_system.Machine_width.t -> bool -> t *)
Parameter untagged_const_bool : Target_system.Machine_width.t -> bool -> M t.
Extract Inlined Constant untagged_const_bool => "Simple.untagged_const_bool".
(* simple.mli:54  val untagged_const_true : Target_system.Machine_width.t -> t *)
Parameter untagged_const_true : Target_system.Machine_width.t -> M t.
Extract Inlined Constant untagged_const_true => "Simple.untagged_const_true".
(* simple.mli:59  val untagged_const_false : Target_system.Machine_width.t -> t *)
Parameter untagged_const_false : Target_system.Machine_width.t -> M t.
Extract Inlined Constant untagged_const_false => "Simple.untagged_const_false".
(* simple.mli:62  val const_zero : Target_system.Machine_width.t -> t *)
Parameter const_zero : Target_system.Machine_width.t -> M t.
Extract Inlined Constant const_zero => "Simple.const_zero".
(* simple.mli:66  val untagged_const_int : Target_ocaml_int.t -> t *)
Parameter untagged_const_int : Target_ocaml_int.t -> M t.
Extract Inlined Constant untagged_const_int => "Simple.untagged_const_int".
(* simple.mli:71  val const_unit : Target_system.Machine_width.t -> t *)
Parameter const_unit : Target_system.Machine_width.t -> M t.
Extract Inlined Constant const_unit => "Simple.const_unit".
(* simple.mli:75  val const_int_of_kind : machine_width:Target_system.Machine_width.t -> Flambda_kind.t -> int -> t *)
Parameter const_int_of_kind : Target_system.Machine_width.t -> Flambda_kind.t -> int -> M t.
Extract Inlined Constant const_int_of_kind => "Simple.const_int_of_kind".
(* simple.mli:78  val is_const : t -> bool *)
Parameter is_const : t -> M bool.
Extract Inlined Constant is_const => "Simple.is_const".
(* simple.mli:88  val pattern_match' : t -> var:(Variable.t -> coercion:Coercion.t -> 'a) -> symbol:(Symbol.t -> coercion:Coercion.t -> 'a) -> const:(Reg_width_const.t -> 'a) -> 'a *)
Parameter pattern_match' : forall {A : Type}, t -> (Variable_.t -> Coercion.t -> M A) -> (Symbol.t -> Coercion.t -> M A) -> (Reg_width_const.t -> M A) -> M A.
Extract Inlined Constant pattern_match' => "Simple.pattern_match'".
(* simple.mli:95  val kind : t -> Flambda_kind.t *)
Parameter kind : t -> M Flambda_kind.t.
Extract Inlined Constant kind => "Simple.kind".
Module List.
  (* simple.mli:98  type nonrec t = t list *)
  Definition t : Type := list Simple.t.
  Extract Inlined Constant t => "Simple.List.t".
  (* simple.mli:100  include Contains_names.S with type t := t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Simple.List.free_names".
  Module T.
    (* simple.mli:102  include Container_types.S with type t := t *)
    Definition t : Type := Simple.List.t.
    Extract Inlined Constant t => "Simple.List.T.t".
  End T.
  (* simple.mli:102  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> Simple.List.T.t -> M unit.
  Extract Inlined Constant print => "Simple.List.print".
End List.
Module With_debuginfo.
  (* simple.mli:114  type nonrec t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Simple.With_debuginfo.t".
  (* simple.mli:116  val create : Int_ids.Simple.t -> Debuginfo.t -> t *)
  Parameter create : Int_ids.Simple.t -> Debuginfo.t -> M t.
  Extract Inlined Constant create => "Simple.With_debuginfo.create".
  (* simple.mli:118  val simple : t -> Int_ids.Simple.t *)
  Parameter simple : t -> M Int_ids.Simple.t.
  Extract Inlined Constant simple => "Simple.With_debuginfo.simple".
  (* simple.mli:120  val dbg : t -> Debuginfo.t *)
  Parameter dbg : t -> M Debuginfo.t.
  Extract Inlined Constant dbg => "Simple.With_debuginfo.dbg".
  (* simple.mli:122  include Contains_names.S with type t := t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Simple.With_debuginfo.free_names".
End With_debuginfo.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simple. End Simple.
