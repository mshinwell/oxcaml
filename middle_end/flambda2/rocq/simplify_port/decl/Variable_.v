(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Variable], after its interface
   middle_end/flambda2/identifiers/variable.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_kind Format Int_ids Or_null.

(* int_ids.mli:110  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Variable_.t.
Extract Inlined Constant t => "Variable.t".
(* module T = Int_ids.Variable.T: declared again here under this name. *)
Module T.
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Variable_.T.t.
  Extract Inlined Constant t => "Variable.T.t".
End T.
(* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
Parameter equal : Variable_.T.t -> Variable_.T.t -> M bool.
Extract Inlined Constant equal => "Variable.equal".
(* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
Parameter hash : Variable_.T.t -> M int.
Extract Inlined Constant hash => "Variable.hash".
(* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
Parameter print : Format.formatter -> Variable_.T.t -> M unit.
Extract Inlined Constant print => "Variable.print".
(* module Set = Int_ids.Variable.Set: declared again here under this name. *)
Module Set_.
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Definition elt : Type := Int_ids.Variable_.Set_.elt.
  Extract Inlined Constant elt => "Variable.Set.elt".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Variable_.Set_.t.
  Extract Inlined Constant t => "Variable.Set.t".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Variable.Set.empty".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter is_empty : t -> M bool.
  Extract Inlined Constant is_empty => "Variable.Set.is_empty".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Variable.Set.mem".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Variable.Set.add".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter remove : elt -> t -> M t.
  Extract Inlined Constant remove => "Variable.Set.remove".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Variable.Set.union".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Variable.Set.diff".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Variable.Set.equal".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Variable.Set.fold".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Variable.Set.print".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_list : list t -> M t.
  Extract Inlined Constant union_list => "Variable.Set.union_list".
End Set_.
(* module Map = Int_ids.Variable.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Definition key : Type := Int_ids.Variable_.Map.key.
  Extract Inlined Constant key => "Variable.Map.key".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Variable_.Map.t A.
  Extract Constant t "'a1" => "('a1) Variable.Map.t".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Variable.Map.empty".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  Extract Inlined Constant mem => "Variable.Map.mem".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Variable.Map.add".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Variable.Map.update".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
  Extract Inlined Constant iter => "Variable.Map.iter".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Variable.Map.fold".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Variable.Map.find".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Variable.Map.find_opt".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Variable.Map.find_or_null".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
  Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Variable.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
  (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Variable.Map.print".
End Map.
(* module Lmap = Int_ids.Variable.Lmap: declared again here under this name. *)
Module Lmap.
  (* int_ids.mli:116  module Lmap : Lmap.S with type key := t *)
  Definition t (A : Type) : Type := Int_ids.Variable_.Lmap.t A.
  Extract Constant t "'a1" => "('a1) Variable.Lmap.t".
  (* int_ids.mli:116  module Lmap : Lmap.S with type key := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Variable.Lmap.empty".
  (* int_ids.mli:116  module Lmap : Lmap.S with type key := t *)
  Parameter add : forall {A : Type}, Int_ids.Variable_.t -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Variable.Lmap.add".
  (* int_ids.mli:116  module Lmap : Lmap.S with type key := t *)
  Parameter singleton : forall {A : Type}, Int_ids.Variable_.t -> A -> M (t A).
  Extract Inlined Constant singleton => "Variable.Lmap.singleton".
  (* int_ids.mli:116  module Lmap : Lmap.S with type key := t *)
  Parameter fold : forall {A B : Type}, (Int_ids.Variable_.t -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Variable.Lmap.fold".
  (* int_ids.mli:116  module Lmap : Lmap.S with type key := t *)
  Parameter exists_ : forall {A : Type}, (Int_ids.Variable_.t -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Variable.Lmap.exists".
  (* int_ids.mli:116  module Lmap : Lmap.S with type key := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Variable.Lmap.print".
End Lmap.
(* int_ids.mli:118  val create : ?user_visible:unit -> string -> Flambda_kind.t -> t *)
Parameter create : option unit -> string -> Flambda_kind.t -> M t.
Extract Inlined Constant create => "(fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)".
(* int_ids.mli:131  val name_stamp : t -> int *)
Parameter name_stamp : t -> M int.
Extract Inlined Constant name_stamp => "Variable.name_stamp".
(* int_ids.mli:133  val kind : t -> Flambda_kind.t *)
Parameter kind : t -> M Flambda_kind.t.
Extract Inlined Constant kind => "Variable.kind".
(* int_ids.mli:135  val user_visible : t -> bool *)
Parameter user_visible : t -> M bool.
Extract Inlined Constant user_visible => "Variable.user_visible".
(* variable.mli:28  val is_renamed_version_of : t -> t -> bool *)
Parameter is_renamed_version_of : t -> t -> M bool.
Extract Inlined Constant is_renamed_version_of => "Variable.is_renamed_version_of".
(* variable.mli:34  val canonical_name : t -> string *)
Parameter canonical_name : t -> M string.
Extract Inlined Constant canonical_name => "Variable.canonical_name".
