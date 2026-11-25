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
   Simplify uses of the compiler's module [Continuation], after its interface
   middle_end/flambda2/identifiers/continuation.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Or_null Seq.

(* continuation.mli:19  type t = private Table_by_int_id.Id.t *)
Parameter t : Type.
Extract Inlined Constant t => "Continuation.t".
(* continuation.mli:19  the coercion (x :> int) of this private type *)
Parameter coerce_t_to_int : t -> int.
Extract Inlined Constant coerce_t_to_int => "(fun (x__1 : Continuation.t) -> (x__1 :> int))".
Module T.
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Definition t : Type := Continuation.t.
  Extract Inlined Constant t => "Continuation.T.t".
End T.
(* continuation.mli:23  include Container_types.S with type t := t *)
Parameter equal : Continuation.T.t -> Continuation.T.t -> M bool.
Extract Inlined Constant equal => "Continuation.equal".
(* continuation.mli:23  include Container_types.S with type t := t *)
Parameter hash : Continuation.T.t -> M int.
Extract Inlined Constant hash => "Continuation.hash".
(* continuation.mli:23  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Continuation.T.t -> M unit.
Extract Inlined Constant print => "Continuation.print".
Module Set_.
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Definition elt : Type := Continuation.t.
  Extract Inlined Constant elt => "Continuation.Set.elt".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Continuation.Set.t".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Continuation.Set.empty".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Continuation.Set.mem".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Continuation.Set.add".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter singleton : elt -> M t.
  Extract Inlined Constant singleton => "Continuation.Set.singleton".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter remove : elt -> t -> M t.
  Extract Inlined Constant remove => "Continuation.Set.remove".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Continuation.Set.union".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter inter : t -> t -> M t.
  Extract Inlined Constant inter => "Continuation.Set.inter".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Continuation.Set.diff".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter subset : t -> t -> M bool.
  Extract Inlined Constant subset => "Continuation.Set.subset".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  Extract Inlined Constant iter => "Continuation.Set.iter".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Continuation.Set.fold".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter elements : t -> M (list elt).
  Extract Inlined Constant elements => "Continuation.Set.elements".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter min_elt_opt : t -> M (option elt).
  Extract Inlined Constant min_elt_opt => "Continuation.Set.min_elt_opt".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter of_list : list elt -> M t.
  Extract Inlined Constant of_list => "Continuation.Set.of_list".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Continuation.Set.print".
End Set_.
Module Map.
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Definition key : Type := Continuation.t.
  Extract Inlined Constant key => "Continuation.Map.key".
  Module Set_.
    (* continuation.mli:23  include Container_types.S with type t := t *)
    Definition t : Type := Continuation.Set_.t.
    Extract Inlined Constant t => "Continuation.Map.Set.t".
  End Set_.
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Continuation.Map.t".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Continuation.Map.empty".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  Extract Inlined Constant mem => "Continuation.Map.mem".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Continuation.Map.add".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Continuation.Map.update".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Continuation.Map.singleton".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter remove : forall {A : Type}, key -> t A -> M (t A).
  Extract Inlined Constant remove => "Continuation.Map.remove".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
  Extract Inlined Constant merge => "Continuation.Map.merge".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total => "Continuation.Map.union_total".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total_shared => "Continuation.Map.union_total_shared".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant update_many => "Continuation.Map.update_many".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
  Extract Inlined Constant iter => "Continuation.Map.iter".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Continuation.Map.fold".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
  Extract Inlined Constant filter_map => "Continuation.Map.filter_map".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant min_binding_opt => "Continuation.Map.min_binding_opt".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Continuation.Map.find".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Continuation.Map.find_opt".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Continuation.Map.find_or_null".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Continuation.Map.map".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Continuation.Map.mapi".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
  Extract Inlined Constant to_seq => "Continuation.Map.to_seq".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
  Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Continuation.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter keys : forall {A : Type}, t A -> M Continuation.Map.Set_.t.
  Extract Inlined Constant keys => "Continuation.Map.keys".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Continuation.Map.print".
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant get_singleton => "Continuation.Map.get_singleton".
End Map.
Module Lmap.
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Continuation.Lmap.t".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Continuation.Lmap.empty".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter add : forall {A : Type}, Continuation.t -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Continuation.Lmap.add".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter singleton : forall {A : Type}, Continuation.t -> A -> M (t A).
  Extract Inlined Constant singleton => "Continuation.Lmap.singleton".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter fold : forall {A B : Type}, (Continuation.t -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Continuation.Lmap.fold".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter keys : forall {A : Type}, t A -> M (list Continuation.t).
  Extract Inlined Constant keys => "Continuation.Lmap.keys".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter find : forall {A : Type}, Continuation.t -> t A -> M A.
  Extract Inlined Constant find => "Continuation.Lmap.find".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Continuation.Lmap.map".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter mapi : forall {A B : Type}, (Continuation.t -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Continuation.Lmap.mapi".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Continuation.Lmap.print".
End Lmap.
Module Sort.
  (* continuation.mli:28  type t = | Normal_or_exn | Return | Define_root_symbol | Toplevel_return *)
  Inductive t : Type :=
  | Normal_or_exn : t
  | Return : t
  | Define_root_symbol : t
  | Toplevel_return : t.
  Extract Inductive t => "Continuation.Sort.t" [ "Continuation.Sort.Normal_or_exn" "Continuation.Sort.Return" "Continuation.Sort.Define_root_symbol" "Continuation.Sort.Toplevel_return" ].
End Sort.
(* continuation.mli:39  val create : ?sort:Sort.t -> ?name:string -> unit -> t *)
Parameter create : option Continuation.Sort.t -> option string -> unit -> M t.
Extract Inlined Constant create => "(fun x__1 x__2 x__3 -> Continuation.create ?sort:x__1 ?name:x__2 x__3)".
(* continuation.mli:41  val rename : t -> t *)
Parameter rename : t -> M t.
Extract Inlined Constant rename => "Continuation.rename".
(* continuation.mli:43  val is_renamed_version_of : t -> t -> bool *)
Parameter is_renamed_version_of : t -> t -> M bool.
Extract Inlined Constant is_renamed_version_of => "Continuation.is_renamed_version_of".
(* continuation.mli:45  val name : t -> string *)
Parameter name : t -> M string.
Extract Inlined Constant name => "Continuation.name".
(* continuation.mli:49  val sort : t -> Sort.t *)
Parameter sort : t -> M Continuation.Sort.t.
Extract Inlined Constant sort => "Continuation.sort".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Continuation. End Continuation.
