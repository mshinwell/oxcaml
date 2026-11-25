(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Container_types], after its interface
   middle_end/flambda2/algorithms/container_types.mli
   (Git blob 9e8a0ef5464fe59da5c58db54f81d9bc0983f63c). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Or_null Seq.

(* The module type Container_types.Set: all that it names. No directive: in a functor, Rocq prints what the parameter has by its name here. *)
Module Type Set_.
  (* container_types_intf.ml:36  type elt *)
  Parameter elt : Type.
  (* container_types_intf.ml:38  type t *)
  Parameter t : Type.
  (* container_types_intf.ml:40  val empty : t *)
  Parameter empty : t.
  (* container_types_intf.ml:42  val is_empty : t -> bool *)
  Parameter is_empty : t -> M bool.
  (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
  Parameter mem : elt -> t -> M bool.
  (* container_types_intf.ml:46  val add : elt -> t -> t *)
  Parameter add : elt -> t -> M t.
  (* container_types_intf.ml:48  val singleton : elt -> t *)
  Parameter singleton : elt -> M t.
  (* container_types_intf.ml:50  val remove : elt -> t -> t *)
  Parameter remove : elt -> t -> M t.
  (* container_types_intf.ml:52  val union : t -> t -> t *)
  Parameter union : t -> t -> M t.
  (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
  Parameter union_sharing : t -> t -> M t.
  (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
  Parameter union_shared : t -> t -> M t.
  (* container_types_intf.ml:62  val inter : t -> t -> t *)
  Parameter inter : t -> t -> M t.
  (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
  Parameter disjoint : t -> t -> M bool.
  (* container_types_intf.ml:66  val diff : t -> t -> t *)
  Parameter diff : t -> t -> M t.
  (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
  Parameter diff_sharing : t -> t -> M t.
  (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
  Parameter diff_shared : t -> t -> M t.
  (* container_types_intf.ml:76  val compare : t -> t -> int *)
  Parameter compare : t -> t -> M int.
  (* container_types_intf.ml:78  val equal : t -> t -> bool *)
  Parameter equal : t -> t -> M bool.
  (* container_types_intf.ml:80  val subset : t -> t -> bool *)
  Parameter subset : t -> t -> M bool.
  (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
  Parameter map : (elt -> M elt) -> t -> M t.
  (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
  Parameter for_all : (elt -> M bool) -> t -> M bool.
  (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
  Parameter exists_ : (elt -> M bool) -> t -> M bool.
  (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
  Parameter filter : (elt -> M bool) -> t -> M t.
  (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
  Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
  (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
  Parameter partition : (elt -> M bool) -> t -> M (t * t).
  (* container_types_intf.ml:98  val cardinal : t -> int *)
  Parameter cardinal : t -> M int.
  (* container_types_intf.ml:100  val elements : t -> elt list *)
  Parameter elements : t -> M (list elt).
  (* container_types_intf.ml:102  val min_elt : t -> elt *)
  Parameter min_elt : t -> M elt.
  (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
  Parameter min_elt_opt : t -> M (option elt).
  (* container_types_intf.ml:106  val max_elt : t -> elt *)
  Parameter max_elt : t -> M elt.
  (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
  Parameter max_elt_opt : t -> M (option elt).
  (* container_types_intf.ml:110  val choose : t -> elt *)
  Parameter choose : t -> M elt.
  (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
  Parameter choose_opt : t -> M (option elt).
  (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
  Parameter split : elt -> t -> M (tuple3 t bool t).
  (* container_types_intf.ml:116  val find : elt -> t -> elt *)
  Parameter find : elt -> t -> M elt.
  (* container_types_intf.ml:118  val of_list : elt list -> t *)
  Parameter of_list : list elt -> M t.
  (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
  Parameter to_seq : t -> Seq.t elt.
  (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  (* container_types_intf.ml:124  val to_string : t -> string *)
  Parameter to_string : t -> M string.
  (* container_types_intf.ml:126  val union_list : t list -> t *)
  Parameter union_list : list t -> M t.
  (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
  Parameter get_singleton : t -> M (option elt).
End Set_.
(* The module type Container_types.Map: all that it names. No directive: in a functor, Rocq prints what the parameter has by its name here. *)
Module Type Map.
  (* container_types_intf.ml:132  type key *)
  Parameter key : Type.
  Module Set_.
    (* container_types_intf.ml:134  module Set : Set with type elt = key *)
    Definition elt : Type := Container_types.Map.key.
    (* container_types_intf.ml:38  type t *)
    Parameter t : Type.
    (* container_types_intf.ml:40  val empty : t *)
    Parameter empty : t.
    (* container_types_intf.ml:42  val is_empty : t -> bool *)
    Parameter is_empty : t -> M bool.
    (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
    Parameter mem : elt -> t -> M bool.
    (* container_types_intf.ml:46  val add : elt -> t -> t *)
    Parameter add : elt -> t -> M t.
    (* container_types_intf.ml:48  val singleton : elt -> t *)
    Parameter singleton : elt -> M t.
    (* container_types_intf.ml:50  val remove : elt -> t -> t *)
    Parameter remove : elt -> t -> M t.
    (* container_types_intf.ml:52  val union : t -> t -> t *)
    Parameter union : t -> t -> M t.
    (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
    Parameter union_sharing : t -> t -> M t.
    (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
    Parameter union_shared : t -> t -> M t.
    (* container_types_intf.ml:62  val inter : t -> t -> t *)
    Parameter inter : t -> t -> M t.
    (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
    Parameter disjoint : t -> t -> M bool.
    (* container_types_intf.ml:66  val diff : t -> t -> t *)
    Parameter diff : t -> t -> M t.
    (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
    Parameter diff_sharing : t -> t -> M t.
    (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
    Parameter diff_shared : t -> t -> M t.
    (* container_types_intf.ml:76  val compare : t -> t -> int *)
    Parameter compare : t -> t -> M int.
    (* container_types_intf.ml:78  val equal : t -> t -> bool *)
    Parameter equal : t -> t -> M bool.
    (* container_types_intf.ml:80  val subset : t -> t -> bool *)
    Parameter subset : t -> t -> M bool.
    (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    (* container_types_intf.ml:98  val cardinal : t -> int *)
    Parameter cardinal : t -> M int.
    (* container_types_intf.ml:100  val elements : t -> elt list *)
    Parameter elements : t -> M (list elt).
    (* container_types_intf.ml:102  val min_elt : t -> elt *)
    Parameter min_elt : t -> M elt.
    (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
    Parameter min_elt_opt : t -> M (option elt).
    (* container_types_intf.ml:106  val max_elt : t -> elt *)
    Parameter max_elt : t -> M elt.
    (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
    Parameter max_elt_opt : t -> M (option elt).
    (* container_types_intf.ml:110  val choose : t -> elt *)
    Parameter choose : t -> M elt.
    (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
    Parameter choose_opt : t -> M (option elt).
    (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    (* container_types_intf.ml:116  val find : elt -> t -> elt *)
    Parameter find : elt -> t -> M elt.
    (* container_types_intf.ml:118  val of_list : elt list -> t *)
    Parameter of_list : list elt -> M t.
    (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
    Parameter to_seq : t -> Seq.t elt.
    (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    (* container_types_intf.ml:124  val to_string : t -> string *)
    Parameter to_string : t -> M string.
    (* container_types_intf.ml:126  val union_list : t list -> t *)
    Parameter union_list : list t -> M t.
    (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
    Parameter get_singleton : t -> M (option elt).
  End Set_.
  (* container_types_intf.ml:136  type +!'a t *)
  Parameter t : Type -> Type.
  (* container_types_intf.ml:138  val empty : 'a t *)
  Parameter empty : forall {A : Type}, t A.
  (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
  Parameter is_empty : forall {A : Type}, t A -> M bool.
  (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
  Parameter remove : forall {A : Type}, key -> t A -> M (t A).
  (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
  Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
  (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
  Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
  Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
  Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
  Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
  Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
  Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
  (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
  Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
  (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
  Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
  (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
  Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
  (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
  Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
  (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
  Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
  (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
  Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
  Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
  (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
  Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
  (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
  Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
  (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
  Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
  (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
  Parameter cardinal : forall {A : Type}, t A -> M int.
  (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
  Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
  (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
  Parameter min_binding : forall {A : Type}, t A -> M (key * A).
  (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
  Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
  Parameter max_binding : forall {A : Type}, t A -> M (key * A).
  (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
  Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
  Parameter choose : forall {A : Type}, t A -> M (key * A).
  (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
  Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
  (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
  Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
  (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
  Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
  (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
  Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
  Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
  (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
  Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
  (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
  Parameter keys : forall {A : Type}, t A -> M Container_types.Map.Set_.t.
  (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
  Parameter data : forall {A : Type}, t A -> M (list A).
  (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
  Parameter of_set : forall {A : Type}, (key -> M A) -> Container_types.Map.Set_.t -> M (t A).
  (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
  Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
  (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
  Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
  (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
  Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
  (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
  Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
  Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
  Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
  Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
  (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
  Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
  (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
  Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
  (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
  Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
End Map.
(* The module type Container_types.S: all that it names. No directive: in a functor, Rocq prints what the parameter has by its name here. *)
Module Type S.
  (* container_types_intf.ml:297  type t *)
  Parameter t : Type.
  Module T.
    (* container_types_intf.ml:299  module T : Thing with type t = t *)
    Definition t : Type := Container_types.S.t.
    (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
    Parameter equal : t -> t -> M bool.
    (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
    Parameter hash : t -> M int.
    (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
    Parameter compare : t -> t -> M int.
    (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
  End T.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter equal : Container_types.S.T.t -> Container_types.S.T.t -> M bool.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter hash : Container_types.S.T.t -> M int.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter compare : Container_types.S.T.t -> Container_types.S.T.t -> M int.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter print : Format.formatter -> Container_types.S.T.t -> M unit.
  Module Set_.
    (* container_types_intf.ml:303  module Set : Set with type elt = t *)
    Definition elt : Type := Container_types.S.t.
    (* container_types_intf.ml:38  type t *)
    Parameter t : Type.
    (* container_types_intf.ml:40  val empty : t *)
    Parameter empty : t.
    (* container_types_intf.ml:42  val is_empty : t -> bool *)
    Parameter is_empty : t -> M bool.
    (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
    Parameter mem : elt -> t -> M bool.
    (* container_types_intf.ml:46  val add : elt -> t -> t *)
    Parameter add : elt -> t -> M t.
    (* container_types_intf.ml:48  val singleton : elt -> t *)
    Parameter singleton : elt -> M t.
    (* container_types_intf.ml:50  val remove : elt -> t -> t *)
    Parameter remove : elt -> t -> M t.
    (* container_types_intf.ml:52  val union : t -> t -> t *)
    Parameter union : t -> t -> M t.
    (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
    Parameter union_sharing : t -> t -> M t.
    (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
    Parameter union_shared : t -> t -> M t.
    (* container_types_intf.ml:62  val inter : t -> t -> t *)
    Parameter inter : t -> t -> M t.
    (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
    Parameter disjoint : t -> t -> M bool.
    (* container_types_intf.ml:66  val diff : t -> t -> t *)
    Parameter diff : t -> t -> M t.
    (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
    Parameter diff_sharing : t -> t -> M t.
    (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
    Parameter diff_shared : t -> t -> M t.
    (* container_types_intf.ml:76  val compare : t -> t -> int *)
    Parameter compare : t -> t -> M int.
    (* container_types_intf.ml:78  val equal : t -> t -> bool *)
    Parameter equal : t -> t -> M bool.
    (* container_types_intf.ml:80  val subset : t -> t -> bool *)
    Parameter subset : t -> t -> M bool.
    (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    (* container_types_intf.ml:98  val cardinal : t -> int *)
    Parameter cardinal : t -> M int.
    (* container_types_intf.ml:100  val elements : t -> elt list *)
    Parameter elements : t -> M (list elt).
    (* container_types_intf.ml:102  val min_elt : t -> elt *)
    Parameter min_elt : t -> M elt.
    (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
    Parameter min_elt_opt : t -> M (option elt).
    (* container_types_intf.ml:106  val max_elt : t -> elt *)
    Parameter max_elt : t -> M elt.
    (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
    Parameter max_elt_opt : t -> M (option elt).
    (* container_types_intf.ml:110  val choose : t -> elt *)
    Parameter choose : t -> M elt.
    (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
    Parameter choose_opt : t -> M (option elt).
    (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    (* container_types_intf.ml:116  val find : elt -> t -> elt *)
    Parameter find : elt -> t -> M elt.
    (* container_types_intf.ml:118  val of_list : elt list -> t *)
    Parameter of_list : list elt -> M t.
    (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
    Parameter to_seq : t -> Seq.t elt.
    (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    (* container_types_intf.ml:124  val to_string : t -> string *)
    Parameter to_string : t -> M string.
    (* container_types_intf.ml:126  val union_list : t list -> t *)
    Parameter union_list : list t -> M t.
    (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
    Parameter get_singleton : t -> M (option elt).
  End Set_.
  Module Map.
    (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
    Definition key : Type := Container_types.S.t.
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Container_types.S.t.
      (* container_types_intf.ml:38  type t *)
      Definition t : Type := Container_types.S.Set_.t.
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
    End Set_.
    (* container_types_intf.ml:136  type +!'a t *)
    Parameter t : Type -> Type.
    (* container_types_intf.ml:138  val empty : 'a t *)
    Parameter empty : forall {A : Type}, t A.
    (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
    Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
    (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
    Parameter remove : forall {A : Type}, key -> t A -> M (t A).
    (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
    Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
    (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
    Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
    Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
    Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
    (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
    Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
    (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
    (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
    Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
    (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
    Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
    (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
    Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
    (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
    Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
    Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
    Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
    (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
    Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
    (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
    Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
    (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
    Parameter cardinal : forall {A : Type}, t A -> M int.
    (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
    Parameter min_binding : forall {A : Type}, t A -> M (key * A).
    (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
    Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
    Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
    Parameter choose : forall {A : Type}, t A -> M (key * A).
    (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
    Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
    (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
    Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
    (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
    Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
    (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
    Parameter keys : forall {A : Type}, t A -> M Container_types.S.Map.Set_.t.
    (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Container_types.S.Map.Set_.t -> M (t A).
    (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
    Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
    (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
    Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
    (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
    Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
    (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
    Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
    (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
    Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
    (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
    Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
  End Map.
End S.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Container_types. End Container_types.
