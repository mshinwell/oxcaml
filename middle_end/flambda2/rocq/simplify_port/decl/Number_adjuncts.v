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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Number_adjuncts], after its interface
   middle_end/flambda2/simplify/number_adjuncts.mli
   (Git blob 55de0362a9c8c80e72df1e219ea8828b3022aa5c). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Flambda Flambda2_types Flambda_kind Format Numeric_types Or_null Reg_width_const Seq Target_ocaml_int Target_system Targetint_32_64.

(* The module type Number_adjuncts.Num_common: all that it names. No directive: in a functor, Rocq prints what the parameter has by its name here. *)
Module Type Num_common.
  (* container_types_intf.ml:297  type t *)
  Parameter t : Type.
  Module T.
    (* container_types_intf.ml:299  module T : Thing with type t = t *)
    Definition t : Type := Number_adjuncts.Num_common.t.
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
  Parameter equal : Number_adjuncts.Num_common.T.t -> Number_adjuncts.Num_common.T.t -> M bool.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter hash : Number_adjuncts.Num_common.T.t -> M int.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter compare : Number_adjuncts.Num_common.T.t -> Number_adjuncts.Num_common.T.t -> M int.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter print : Format.formatter -> Number_adjuncts.Num_common.T.t -> M unit.
  Module Set_.
    (* container_types_intf.ml:303  module Set : Set with type elt = t *)
    Definition elt : Type := Number_adjuncts.Num_common.t.
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
    Definition key : Type := Number_adjuncts.Num_common.t.
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.Num_common.t.
      (* container_types_intf.ml:38  type t *)
      Definition t : Type := Number_adjuncts.Num_common.Set_.t.
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
    Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.Num_common.Map.Set_.t.
    (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.Num_common.Map.Set_.t -> M (t A).
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
  Module Pair.
    (* number_adjuncts.mli:25  type nonrec t = t * t *)
    Definition t : Type := (Number_adjuncts.Num_common.t * Number_adjuncts.Num_common.t).
    Module T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Definition t : Type := Number_adjuncts.Num_common.Pair.t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : t -> t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : t -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : t -> t -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> t -> M unit.
    End T.
    (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
    Parameter equal : Number_adjuncts.Num_common.Pair.T.t -> Number_adjuncts.Num_common.Pair.T.t -> M bool.
    (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
    Parameter hash : Number_adjuncts.Num_common.Pair.T.t -> M int.
    (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
    Parameter compare : Number_adjuncts.Num_common.Pair.T.t -> Number_adjuncts.Num_common.Pair.T.t -> M int.
    (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
    Parameter print : Format.formatter -> Number_adjuncts.Num_common.Pair.T.t -> M unit.
    Module Set_.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Definition elt : Type := Number_adjuncts.Num_common.Pair.t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter t : Type.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter empty : t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter is_empty : t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter mem : elt -> t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter add : elt -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter singleton : elt -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter remove : elt -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union : t -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_sharing : t -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_shared : t -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter inter : t -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter disjoint : t -> t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter diff : t -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter diff_sharing : t -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter diff_shared : t -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : t -> t -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : t -> t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter subset : t -> t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter cardinal : t -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter elements : t -> M (list elt).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter min_elt : t -> M elt.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter min_elt_opt : t -> M (option elt).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter max_elt : t -> M elt.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter max_elt_opt : t -> M (option elt).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter choose : t -> M elt.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter choose_opt : t -> M (option elt).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter find : elt -> t -> M elt.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter of_list : list elt -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter to_seq : t -> Seq.t elt.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> t -> M unit.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter to_string : t -> M string.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_list : list t -> M t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter get_singleton : t -> M (option elt).
    End Set_.
    Module Map.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Definition key : Type := Number_adjuncts.Num_common.Pair.t.
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.Num_common.Pair.t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.Num_common.Pair.Set_.t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
      End Set_.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter t : Type -> Type.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter empty : forall {A : Type}, t A.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.Num_common.Pair.Map.Set_.t.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.Num_common.Pair.Map.Set_.t -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
    End Map.
  End Pair.
  (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
  Parameter cross_product : Number_adjuncts.Num_common.Set_.t -> Number_adjuncts.Num_common.Set_.t -> M Number_adjuncts.Num_common.Pair.Set_.t.
  (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
  Parameter zero : Target_system.Machine_width.t -> M t.
  (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
  Parameter one : Target_system.Machine_width.t -> M t.
  (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
  Parameter minus_one : Target_system.Machine_width.t -> M t.
  (* number_adjuncts.mli:38  val add : t -> t -> t *)
  Parameter add : t -> t -> M t.
  (* number_adjuncts.mli:40  val sub : t -> t -> t *)
  Parameter sub : t -> t -> M t.
  (* number_adjuncts.mli:42  val mul : t -> t -> t *)
  Parameter mul : t -> t -> M t.
  (* number_adjuncts.mli:44  val div : t -> t -> t option *)
  Parameter div : t -> t -> M (option t).
  (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
  Parameter mod_ : t -> t -> M (option t).
  (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
  Parameter to_const : t -> M Reg_width_const.t.
  (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
  Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
  (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
  Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
  (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
  Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
  (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
  Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
  (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
  Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
  (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
  Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
  (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
  Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
  (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
  Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
End Num_common.
(* NOT DECLARED: Number_adjuncts.Number_kind_common: a module type that no file of Simplify names from outside the file that defines it. *)
(* The module type Number_adjuncts.Number_kind: all that it names. No directive: in a functor, Rocq prints what the parameter has by its name here. *)
Module Type Number_kind.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.Number_kind.Num.t.
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
    Parameter equal : Number_adjuncts.Number_kind.Num.T.t -> Number_adjuncts.Number_kind.Num.T.t -> M bool.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.Number_kind.Num.T.t -> M int.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.Number_kind.Num.T.t -> Number_adjuncts.Number_kind.Num.T.t -> M int.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.Number_kind.Num.T.t -> M unit.
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.Number_kind.Num.t.
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
      Definition key : Type := Number_adjuncts.Number_kind.Num.t.
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.Number_kind.Num.t.
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.Number_kind.Num.Set_.t.
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
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.Number_kind.Num.Map.Set_.t.
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.Number_kind.Num.Map.Set_.t -> M (t A).
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
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.Number_kind.Num.t * Number_adjuncts.Number_kind.Num.t).
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.Number_kind.Num.Pair.t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.Number_kind.Num.Pair.T.t -> Number_adjuncts.Number_kind.Num.Pair.T.t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.Number_kind.Num.Pair.T.t -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.Number_kind.Num.Pair.T.t -> Number_adjuncts.Number_kind.Num.Pair.T.t -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.Number_kind.Num.Pair.T.t -> M unit.
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.Number_kind.Num.Pair.t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.Number_kind.Num.Pair.t.
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.Number_kind.Num.Pair.t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.Number_kind.Num.Pair.Set_.t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.Number_kind.Num.Pair.Map.Set_.t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.Number_kind.Num.Pair.Map.Set_.t -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.Number_kind.Num.Set_.t -> Number_adjuncts.Number_kind.Num.Set_.t -> M Number_adjuncts.Number_kind.Num.Pair.Set_.t.
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
  End Num.
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.Number_kind.Num.Set_.t).
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.Number_kind.Num.t -> M Flambda2_types.t.
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.Number_kind.Num.Set_.t -> M Flambda2_types.t.
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.Number_kind.Num.t -> M Flambda.Named.t.
End Number_kind.
(* The module type Number_adjuncts.Int_number_kind: all that it names. No directive: in a functor, Rocq prints what the parameter has by its name here. *)
Module Type Int_number_kind.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.Int_number_kind.Num.t.
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
    Parameter equal : Number_adjuncts.Int_number_kind.Num.T.t -> Number_adjuncts.Int_number_kind.Num.T.t -> M bool.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.Int_number_kind.Num.T.t -> M int.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.Int_number_kind.Num.T.t -> Number_adjuncts.Int_number_kind.Num.T.t -> M int.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.Int_number_kind.Num.T.t -> M unit.
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.Int_number_kind.Num.t.
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
      Definition key : Type := Number_adjuncts.Int_number_kind.Num.t.
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.Int_number_kind.Num.t.
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.Int_number_kind.Num.Set_.t.
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
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.Int_number_kind.Num.Map.Set_.t.
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.Int_number_kind.Num.Map.Set_.t -> M (t A).
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
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.Int_number_kind.Num.t * Number_adjuncts.Int_number_kind.Num.t).
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.Int_number_kind.Num.Pair.t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.Int_number_kind.Num.Pair.T.t -> Number_adjuncts.Int_number_kind.Num.Pair.T.t -> M bool.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.Int_number_kind.Num.Pair.T.t -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.Int_number_kind.Num.Pair.T.t -> Number_adjuncts.Int_number_kind.Num.Pair.T.t -> M int.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.Int_number_kind.Num.Pair.T.t -> M unit.
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.Int_number_kind.Num.Pair.t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.Int_number_kind.Num.Pair.t.
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.Int_number_kind.Num.Pair.t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.Int_number_kind.Num.Pair.Set_.t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.Int_number_kind.Num.Pair.Map.Set_.t.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.Int_number_kind.Num.Pair.Map.Set_.t -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.Int_number_kind.Num.Set_.t -> Number_adjuncts.Int_number_kind.Num.Set_.t -> M Number_adjuncts.Int_number_kind.Num.Pair.Set_.t.
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    (* number_adjuncts.mli:95  val and_ : t -> t -> t *)
    Parameter and_ : t -> t -> M t.
    (* number_adjuncts.mli:97  val or_ : t -> t -> t *)
    Parameter or_ : t -> t -> M t.
    (* number_adjuncts.mli:99  val xor : t -> t -> t *)
    Parameter xor : t -> t -> M t.
    (* number_adjuncts.mli:101  val not_ : t -> t *)
    Parameter not_ : t -> M t.
    (* number_adjuncts.mli:103  val unsigned_div : t -> t -> t option *)
    Parameter unsigned_div : t -> t -> M (option t).
    (* number_adjuncts.mli:105  val unsigned_mod : t -> t -> t option *)
    Parameter unsigned_mod : t -> t -> M (option t).
    (* number_adjuncts.mli:107  val shift_left : t -> Target_ocaml_int.t -> t *)
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    (* number_adjuncts.mli:111  val shift_right : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    (* number_adjuncts.mli:113  val shift_right_logical : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    (* number_adjuncts.mli:115  val swap_byte_endianness : t -> t *)
    Parameter swap_byte_endianness : t -> M t.
    (* number_adjuncts.mli:117  val neg : t -> t *)
    Parameter neg : t -> M t.
    (* number_adjuncts.mli:119  val compare_unsigned : t -> t -> int *)
    Parameter compare_unsigned : t -> t -> M int.
  End Num.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.Int_number_kind.Num.Set_.t).
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.Int_number_kind.Num.t -> M Flambda2_types.t.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.Int_number_kind.Num.Set_.t -> M Flambda2_types.t.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.Int_number_kind.Num.t -> M Flambda.Named.t.
  (* number_adjuncts.mli:124  val standard_int_kind : Flambda_kind.Standard_int.t *)
  Parameter standard_int_kind : Flambda_kind.Standard_int.t.
End Int_number_kind.
(* NOT DECLARED: Number_adjuncts.Boxable: a module type that no file of Simplify names from outside the file that defines it. *)
(* NOT DECLARED: Number_adjuncts.Boxable_number_kind: a module type that no file of Simplify names from outside the file that defines it. *)
(* NOT DECLARED: Number_adjuncts.Boxable_int_number_kind: a module type that no file of Simplify names from outside the file that defines it. *)
Module For_tagged_immediates.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_tagged_immediates.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_tagged_immediates.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_tagged_immediates.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_tagged_immediates.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_tagged_immediates.Num.T.t -> Number_adjuncts.For_tagged_immediates.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_tagged_immediates.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_tagged_immediates.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_tagged_immediates.Num.T.t -> Number_adjuncts.For_tagged_immediates.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_tagged_immediates.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_tagged_immediates.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_tagged_immediates.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_tagged_immediates.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_tagged_immediates.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_tagged_immediates.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_tagged_immediates.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_tagged_immediates.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_tagged_immediates.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_tagged_immediates.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_tagged_immediates.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_tagged_immediates.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_tagged_immediates.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_tagged_immediates.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_tagged_immediates.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_tagged_immediates.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_tagged_immediates.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_tagged_immediates.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_tagged_immediates.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_tagged_immediates.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_tagged_immediates.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_tagged_immediates.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_tagged_immediates.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_tagged_immediates.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_tagged_immediates.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_tagged_immediates.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_tagged_immediates.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_tagged_immediates.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_tagged_immediates.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_tagged_immediates.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_tagged_immediates.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_tagged_immediates.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_tagged_immediates.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_tagged_immediates.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_tagged_immediates.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_tagged_immediates.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_tagged_immediates.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_tagged_immediates.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_tagged_immediates.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_tagged_immediates.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_tagged_immediates.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_tagged_immediates.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_tagged_immediates.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_tagged_immediates.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_tagged_immediates.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_tagged_immediates.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_tagged_immediates.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_tagged_immediates.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_tagged_immediates.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_tagged_immediates.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_tagged_immediates.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_tagged_immediates.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_tagged_immediates.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_tagged_immediates.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_tagged_immediates.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_tagged_immediates.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_tagged_immediates.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_tagged_immediates.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_tagged_immediates.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_tagged_immediates.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_tagged_immediates.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_tagged_immediates.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_tagged_immediates.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_tagged_immediates.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_tagged_immediates.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_tagged_immediates.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_tagged_immediates.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_tagged_immediates.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_tagged_immediates.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_tagged_immediates.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_tagged_immediates.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_tagged_immediates.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_tagged_immediates.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_tagged_immediates.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_tagged_immediates.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_tagged_immediates.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_tagged_immediates.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_tagged_immediates.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_tagged_immediates.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_tagged_immediates.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_tagged_immediates.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_tagged_immediates.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_tagged_immediates.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_tagged_immediates.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_tagged_immediates.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_tagged_immediates.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_tagged_immediates.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_tagged_immediates.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_tagged_immediates.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_tagged_immediates.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_tagged_immediates.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_tagged_immediates.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_tagged_immediates.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_tagged_immediates.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_tagged_immediates.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_tagged_immediates.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_tagged_immediates.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_tagged_immediates.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_tagged_immediates.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_tagged_immediates.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_tagged_immediates.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_tagged_immediates.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_tagged_immediates.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_tagged_immediates.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_tagged_immediates.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_tagged_immediates.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_tagged_immediates.Num.t * Number_adjuncts.For_tagged_immediates.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_tagged_immediates.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_tagged_immediates.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_tagged_immediates.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_tagged_immediates.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_tagged_immediates.Num.Pair.T.t -> Number_adjuncts.For_tagged_immediates.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_tagged_immediates.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_tagged_immediates.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_tagged_immediates.Num.Pair.T.t -> Number_adjuncts.For_tagged_immediates.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_tagged_immediates.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_tagged_immediates.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_tagged_immediates.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_tagged_immediates.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_tagged_immediates.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_tagged_immediates.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_tagged_immediates.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_tagged_immediates.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_tagged_immediates.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_tagged_immediates.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_tagged_immediates.Num.Set_.t -> Number_adjuncts.For_tagged_immediates.Num.Set_.t -> M Number_adjuncts.For_tagged_immediates.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_tagged_immediates.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_tagged_immediates.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_tagged_immediates.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_tagged_immediates.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_tagged_immediates.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_tagged_immediates.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_tagged_immediates.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_tagged_immediates.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_tagged_immediates.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_tagged_immediates.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_tagged_immediates.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_tagged_immediates.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_tagged_immediates.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_tagged_immediates.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_tagged_immediates.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_tagged_immediates.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_tagged_immediates.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_tagged_immediates.Num.to_naked_nativeint".
    (* number_adjuncts.mli:95  val and_ : t -> t -> t *)
    Parameter and_ : t -> t -> M t.
    Extract Inlined Constant and_ => "Number_adjuncts.For_tagged_immediates.Num.and_".
    (* number_adjuncts.mli:97  val or_ : t -> t -> t *)
    Parameter or_ : t -> t -> M t.
    Extract Inlined Constant or_ => "Number_adjuncts.For_tagged_immediates.Num.or_".
    (* number_adjuncts.mli:99  val xor : t -> t -> t *)
    Parameter xor : t -> t -> M t.
    Extract Inlined Constant xor => "Number_adjuncts.For_tagged_immediates.Num.xor".
    (* number_adjuncts.mli:101  val not_ : t -> t *)
    Parameter not_ : t -> M t.
    Extract Inlined Constant not_ => "Number_adjuncts.For_tagged_immediates.Num.not_".
    (* number_adjuncts.mli:103  val unsigned_div : t -> t -> t option *)
    Parameter unsigned_div : t -> t -> M (option t).
    Extract Inlined Constant unsigned_div => "Number_adjuncts.For_tagged_immediates.Num.unsigned_div".
    (* number_adjuncts.mli:105  val unsigned_mod : t -> t -> t option *)
    Parameter unsigned_mod : t -> t -> M (option t).
    Extract Inlined Constant unsigned_mod => "Number_adjuncts.For_tagged_immediates.Num.unsigned_mod".
    (* number_adjuncts.mli:107  val shift_left : t -> Target_ocaml_int.t -> t *)
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_left => "Number_adjuncts.For_tagged_immediates.Num.shift_left".
    (* number_adjuncts.mli:111  val shift_right : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right => "Number_adjuncts.For_tagged_immediates.Num.shift_right".
    (* number_adjuncts.mli:113  val shift_right_logical : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right_logical => "Number_adjuncts.For_tagged_immediates.Num.shift_right_logical".
    (* number_adjuncts.mli:115  val swap_byte_endianness : t -> t *)
    Parameter swap_byte_endianness : t -> M t.
    Extract Inlined Constant swap_byte_endianness => "Number_adjuncts.For_tagged_immediates.Num.swap_byte_endianness".
    (* number_adjuncts.mli:117  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Number_adjuncts.For_tagged_immediates.Num.neg".
    (* number_adjuncts.mli:119  val compare_unsigned : t -> t -> int *)
    Parameter compare_unsigned : t -> t -> M int.
    Extract Inlined Constant compare_unsigned => "Number_adjuncts.For_tagged_immediates.Num.compare_unsigned".
  End Num.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_tagged_immediates.standard_int_or_float_kind".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_tagged_immediates.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_tagged_immediates.unboxed_prover".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_tagged_immediates.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_tagged_immediates.this_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_tagged_immediates.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_tagged_immediates.these_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_tagged_immediates.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_tagged_immediates.term_unboxed".
  (* number_adjuncts.mli:124  val standard_int_kind : Flambda_kind.Standard_int.t *)
  Parameter standard_int_kind : Flambda_kind.Standard_int.t.
  Extract Inlined Constant standard_int_kind => "Number_adjuncts.For_tagged_immediates.standard_int_kind".
End For_tagged_immediates.
Module For_naked_immediates.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_naked_immediates.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_naked_immediates.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_naked_immediates.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_naked_immediates.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_naked_immediates.Num.T.t -> Number_adjuncts.For_naked_immediates.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_naked_immediates.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_naked_immediates.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_naked_immediates.Num.T.t -> Number_adjuncts.For_naked_immediates.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_naked_immediates.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_naked_immediates.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_naked_immediates.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_naked_immediates.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_naked_immediates.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_naked_immediates.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_naked_immediates.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_naked_immediates.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_naked_immediates.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_naked_immediates.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_naked_immediates.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_naked_immediates.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_naked_immediates.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_naked_immediates.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_naked_immediates.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_naked_immediates.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_naked_immediates.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_naked_immediates.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_naked_immediates.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_naked_immediates.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_naked_immediates.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_naked_immediates.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_naked_immediates.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_naked_immediates.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_naked_immediates.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_naked_immediates.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_naked_immediates.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_naked_immediates.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_naked_immediates.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_naked_immediates.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_naked_immediates.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_naked_immediates.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_naked_immediates.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_naked_immediates.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_naked_immediates.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_naked_immediates.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_naked_immediates.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_naked_immediates.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_naked_immediates.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_naked_immediates.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_naked_immediates.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_naked_immediates.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_naked_immediates.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_naked_immediates.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_naked_immediates.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_naked_immediates.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_naked_immediates.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_naked_immediates.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_naked_immediates.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_naked_immediates.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_naked_immediates.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_naked_immediates.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_naked_immediates.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_naked_immediates.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_naked_immediates.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_naked_immediates.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_naked_immediates.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_naked_immediates.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_naked_immediates.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_naked_immediates.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_naked_immediates.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_naked_immediates.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_naked_immediates.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_naked_immediates.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_naked_immediates.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_naked_immediates.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_naked_immediates.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_naked_immediates.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_naked_immediates.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_naked_immediates.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_naked_immediates.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_naked_immediates.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_naked_immediates.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_naked_immediates.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_naked_immediates.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_naked_immediates.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_naked_immediates.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_naked_immediates.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_naked_immediates.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_naked_immediates.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_naked_immediates.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_naked_immediates.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_naked_immediates.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_naked_immediates.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_naked_immediates.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_naked_immediates.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_naked_immediates.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_naked_immediates.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_naked_immediates.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_naked_immediates.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_naked_immediates.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_naked_immediates.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_naked_immediates.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_naked_immediates.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_naked_immediates.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_naked_immediates.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_naked_immediates.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_naked_immediates.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_naked_immediates.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_naked_immediates.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_naked_immediates.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_naked_immediates.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_naked_immediates.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_naked_immediates.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_naked_immediates.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_naked_immediates.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_naked_immediates.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_naked_immediates.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_naked_immediates.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_naked_immediates.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_naked_immediates.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_naked_immediates.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_naked_immediates.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_naked_immediates.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_naked_immediates.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_naked_immediates.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_naked_immediates.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_naked_immediates.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_naked_immediates.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_naked_immediates.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_naked_immediates.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_naked_immediates.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_naked_immediates.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_naked_immediates.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_naked_immediates.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_naked_immediates.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_naked_immediates.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_naked_immediates.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_naked_immediates.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_naked_immediates.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_naked_immediates.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_naked_immediates.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_naked_immediates.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_naked_immediates.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_naked_immediates.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_naked_immediates.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_naked_immediates.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_naked_immediates.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_naked_immediates.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_naked_immediates.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_naked_immediates.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_naked_immediates.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_naked_immediates.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_naked_immediates.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_naked_immediates.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_naked_immediates.Num.t * Number_adjuncts.For_naked_immediates.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_naked_immediates.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_naked_immediates.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_naked_immediates.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_naked_immediates.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_naked_immediates.Num.Pair.T.t -> Number_adjuncts.For_naked_immediates.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_naked_immediates.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_naked_immediates.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_naked_immediates.Num.Pair.T.t -> Number_adjuncts.For_naked_immediates.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_naked_immediates.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_naked_immediates.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_naked_immediates.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_naked_immediates.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_naked_immediates.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_naked_immediates.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_naked_immediates.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_naked_immediates.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_naked_immediates.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_naked_immediates.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_naked_immediates.Num.Set_.t -> Number_adjuncts.For_naked_immediates.Num.Set_.t -> M Number_adjuncts.For_naked_immediates.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_naked_immediates.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_naked_immediates.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_naked_immediates.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_naked_immediates.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_naked_immediates.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_naked_immediates.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_naked_immediates.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_naked_immediates.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_naked_immediates.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_naked_immediates.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_naked_immediates.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_naked_immediates.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_naked_immediates.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_naked_immediates.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_naked_immediates.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_naked_immediates.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_naked_immediates.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_naked_immediates.Num.to_naked_nativeint".
    (* number_adjuncts.mli:95  val and_ : t -> t -> t *)
    Parameter and_ : t -> t -> M t.
    Extract Inlined Constant and_ => "Number_adjuncts.For_naked_immediates.Num.and_".
    (* number_adjuncts.mli:97  val or_ : t -> t -> t *)
    Parameter or_ : t -> t -> M t.
    Extract Inlined Constant or_ => "Number_adjuncts.For_naked_immediates.Num.or_".
    (* number_adjuncts.mli:99  val xor : t -> t -> t *)
    Parameter xor : t -> t -> M t.
    Extract Inlined Constant xor => "Number_adjuncts.For_naked_immediates.Num.xor".
    (* number_adjuncts.mli:101  val not_ : t -> t *)
    Parameter not_ : t -> M t.
    Extract Inlined Constant not_ => "Number_adjuncts.For_naked_immediates.Num.not_".
    (* number_adjuncts.mli:103  val unsigned_div : t -> t -> t option *)
    Parameter unsigned_div : t -> t -> M (option t).
    Extract Inlined Constant unsigned_div => "Number_adjuncts.For_naked_immediates.Num.unsigned_div".
    (* number_adjuncts.mli:105  val unsigned_mod : t -> t -> t option *)
    Parameter unsigned_mod : t -> t -> M (option t).
    Extract Inlined Constant unsigned_mod => "Number_adjuncts.For_naked_immediates.Num.unsigned_mod".
    (* number_adjuncts.mli:107  val shift_left : t -> Target_ocaml_int.t -> t *)
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_left => "Number_adjuncts.For_naked_immediates.Num.shift_left".
    (* number_adjuncts.mli:111  val shift_right : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right => "Number_adjuncts.For_naked_immediates.Num.shift_right".
    (* number_adjuncts.mli:113  val shift_right_logical : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right_logical => "Number_adjuncts.For_naked_immediates.Num.shift_right_logical".
    (* number_adjuncts.mli:115  val swap_byte_endianness : t -> t *)
    Parameter swap_byte_endianness : t -> M t.
    Extract Inlined Constant swap_byte_endianness => "Number_adjuncts.For_naked_immediates.Num.swap_byte_endianness".
    (* number_adjuncts.mli:117  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Number_adjuncts.For_naked_immediates.Num.neg".
    (* number_adjuncts.mli:119  val compare_unsigned : t -> t -> int *)
    Parameter compare_unsigned : t -> t -> M int.
    Extract Inlined Constant compare_unsigned => "Number_adjuncts.For_naked_immediates.Num.compare_unsigned".
  End Num.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_naked_immediates.standard_int_or_float_kind".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_naked_immediates.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_naked_immediates.unboxed_prover".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_naked_immediates.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_naked_immediates.this_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_naked_immediates.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_naked_immediates.these_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_naked_immediates.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_naked_immediates.term_unboxed".
  (* number_adjuncts.mli:124  val standard_int_kind : Flambda_kind.Standard_int.t *)
  Parameter standard_int_kind : Flambda_kind.Standard_int.t.
  Extract Inlined Constant standard_int_kind => "Number_adjuncts.For_naked_immediates.standard_int_kind".
End For_naked_immediates.
Module For_float32s.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_float32s.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_float32s.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_float32s.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_float32s.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_float32s.Num.T.t -> Number_adjuncts.For_float32s.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_float32s.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_float32s.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_float32s.Num.T.t -> Number_adjuncts.For_float32s.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_float32s.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_float32s.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_float32s.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_float32s.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_float32s.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_float32s.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_float32s.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_float32s.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_float32s.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_float32s.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_float32s.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_float32s.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_float32s.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_float32s.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_float32s.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_float32s.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_float32s.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_float32s.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_float32s.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_float32s.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_float32s.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_float32s.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_float32s.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_float32s.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_float32s.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_float32s.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_float32s.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_float32s.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_float32s.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_float32s.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_float32s.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_float32s.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_float32s.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_float32s.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_float32s.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_float32s.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_float32s.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_float32s.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_float32s.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_float32s.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_float32s.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_float32s.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_float32s.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_float32s.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_float32s.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_float32s.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_float32s.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_float32s.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_float32s.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_float32s.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_float32s.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_float32s.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_float32s.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_float32s.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_float32s.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_float32s.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_float32s.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_float32s.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_float32s.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_float32s.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_float32s.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_float32s.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_float32s.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_float32s.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_float32s.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_float32s.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_float32s.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_float32s.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_float32s.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_float32s.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_float32s.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_float32s.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_float32s.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_float32s.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_float32s.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_float32s.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_float32s.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_float32s.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_float32s.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_float32s.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_float32s.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_float32s.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_float32s.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_float32s.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_float32s.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_float32s.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_float32s.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_float32s.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_float32s.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_float32s.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_float32s.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_float32s.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_float32s.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_float32s.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_float32s.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_float32s.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_float32s.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_float32s.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_float32s.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_float32s.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_float32s.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_float32s.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_float32s.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_float32s.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_float32s.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_float32s.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_float32s.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_float32s.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_float32s.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_float32s.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_float32s.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_float32s.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_float32s.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_float32s.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_float32s.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_float32s.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_float32s.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_float32s.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_float32s.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_float32s.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_float32s.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_float32s.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_float32s.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_float32s.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_float32s.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_float32s.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_float32s.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_float32s.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_float32s.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_float32s.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_float32s.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_float32s.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_float32s.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_float32s.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_float32s.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_float32s.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_float32s.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_float32s.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_float32s.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_float32s.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_float32s.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_float32s.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_float32s.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_float32s.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_float32s.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_float32s.Num.t * Number_adjuncts.For_float32s.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_float32s.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_float32s.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_float32s.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_float32s.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_float32s.Num.Pair.T.t -> Number_adjuncts.For_float32s.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_float32s.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_float32s.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_float32s.Num.Pair.T.t -> Number_adjuncts.For_float32s.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_float32s.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_float32s.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_float32s.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_float32s.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_float32s.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_float32s.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_float32s.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_float32s.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_float32s.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_float32s.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_float32s.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_float32s.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_float32s.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_float32s.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_float32s.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_float32s.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_float32s.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_float32s.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_float32s.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_float32s.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_float32s.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_float32s.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_float32s.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_float32s.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_float32s.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_float32s.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_float32s.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_float32s.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_float32s.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_float32s.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_float32s.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_float32s.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_float32s.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_float32s.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_float32s.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_float32s.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_float32s.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_float32s.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_float32s.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_float32s.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_float32s.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_float32s.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_float32s.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_float32s.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_float32s.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_float32s.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_float32s.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_float32s.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_float32s.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_float32s.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_float32s.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_float32s.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_float32s.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_float32s.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_float32s.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_float32s.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_float32s.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_float32s.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_float32s.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_float32s.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_float32s.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_float32s.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_float32s.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_float32s.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_float32s.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_float32s.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_float32s.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_float32s.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_float32s.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_float32s.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_float32s.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_float32s.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_float32s.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_float32s.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_float32s.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_float32s.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_float32s.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_float32s.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_float32s.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_float32s.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_float32s.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_float32s.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_float32s.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_float32s.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_float32s.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_float32s.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_float32s.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_float32s.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_float32s.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_float32s.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_float32s.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_float32s.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_float32s.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_float32s.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_float32s.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_float32s.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_float32s.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_float32s.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_float32s.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_float32s.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_float32s.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_float32s.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_float32s.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_float32s.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_float32s.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_float32s.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_float32s.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_float32s.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_float32s.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_float32s.Num.Set_.t -> Number_adjuncts.For_float32s.Num.Set_.t -> M Number_adjuncts.For_float32s.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_float32s.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_float32s.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_float32s.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_float32s.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_float32s.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_float32s.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_float32s.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_float32s.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_float32s.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_float32s.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_float32s.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_float32s.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_float32s.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_float32s.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_float32s.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_float32s.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_float32s.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_float32s.Num.to_naked_nativeint".
  End Num.
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_float32s.standard_int_or_float_kind".
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_float32s.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_float32s.unboxed_prover".
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_float32s.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_float32s.this_unboxed".
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_float32s.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_float32s.these_unboxed".
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_float32s.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_float32s.term_unboxed".
  (* number_adjuncts.mli:142  include Boxable with module Num := Num *)
  Parameter boxable_number_kind : Flambda_kind.Boxable_number.t.
  Extract Inlined Constant boxable_number_kind => "Number_adjuncts.For_float32s.boxable_number_kind".
  (* number_adjuncts.mli:142  include Boxable with module Num := Num *)
  Parameter this_boxed : Number_adjuncts.For_float32s.Num.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant this_boxed => "Number_adjuncts.For_float32s.this_boxed".
  (* number_adjuncts.mli:142  include Boxable with module Num := Num *)
  Parameter these_boxed : Number_adjuncts.For_float32s.Num.Set_.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant these_boxed => "Number_adjuncts.For_float32s.these_boxed".
  (* number_adjuncts.mli:142  include Boxable with module Num := Num *)
  Parameter box : Flambda2_types.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant box => "Number_adjuncts.For_float32s.box".
End For_float32s.
Module For_floats.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_floats.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_floats.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_floats.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_floats.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_floats.Num.T.t -> Number_adjuncts.For_floats.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_floats.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_floats.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_floats.Num.T.t -> Number_adjuncts.For_floats.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_floats.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_floats.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_floats.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_floats.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_floats.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_floats.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_floats.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_floats.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_floats.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_floats.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_floats.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_floats.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_floats.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_floats.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_floats.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_floats.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_floats.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_floats.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_floats.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_floats.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_floats.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_floats.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_floats.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_floats.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_floats.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_floats.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_floats.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_floats.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_floats.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_floats.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_floats.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_floats.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_floats.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_floats.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_floats.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_floats.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_floats.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_floats.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_floats.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_floats.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_floats.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_floats.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_floats.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_floats.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_floats.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_floats.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_floats.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_floats.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_floats.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_floats.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_floats.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_floats.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_floats.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_floats.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_floats.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_floats.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_floats.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_floats.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_floats.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_floats.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_floats.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_floats.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_floats.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_floats.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_floats.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_floats.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_floats.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_floats.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_floats.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_floats.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_floats.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_floats.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_floats.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_floats.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_floats.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_floats.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_floats.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_floats.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_floats.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_floats.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_floats.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_floats.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_floats.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_floats.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_floats.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_floats.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_floats.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_floats.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_floats.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_floats.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_floats.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_floats.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_floats.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_floats.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_floats.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_floats.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_floats.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_floats.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_floats.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_floats.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_floats.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_floats.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_floats.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_floats.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_floats.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_floats.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_floats.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_floats.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_floats.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_floats.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_floats.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_floats.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_floats.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_floats.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_floats.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_floats.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_floats.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_floats.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_floats.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_floats.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_floats.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_floats.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_floats.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_floats.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_floats.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_floats.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_floats.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_floats.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_floats.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_floats.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_floats.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_floats.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_floats.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_floats.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_floats.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_floats.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_floats.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_floats.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_floats.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_floats.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_floats.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_floats.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_floats.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_floats.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_floats.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_floats.Num.t * Number_adjuncts.For_floats.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_floats.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_floats.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_floats.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_floats.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_floats.Num.Pair.T.t -> Number_adjuncts.For_floats.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_floats.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_floats.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_floats.Num.Pair.T.t -> Number_adjuncts.For_floats.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_floats.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_floats.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_floats.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_floats.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_floats.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_floats.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_floats.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_floats.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_floats.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_floats.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_floats.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_floats.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_floats.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_floats.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_floats.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_floats.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_floats.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_floats.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_floats.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_floats.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_floats.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_floats.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_floats.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_floats.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_floats.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_floats.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_floats.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_floats.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_floats.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_floats.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_floats.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_floats.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_floats.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_floats.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_floats.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_floats.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_floats.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_floats.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_floats.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_floats.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_floats.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_floats.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_floats.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_floats.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_floats.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_floats.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_floats.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_floats.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_floats.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_floats.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_floats.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_floats.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_floats.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_floats.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_floats.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_floats.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_floats.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_floats.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_floats.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_floats.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_floats.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_floats.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_floats.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_floats.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_floats.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_floats.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_floats.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_floats.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_floats.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_floats.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_floats.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_floats.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_floats.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_floats.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_floats.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_floats.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_floats.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_floats.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_floats.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_floats.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_floats.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_floats.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_floats.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_floats.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_floats.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_floats.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_floats.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_floats.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_floats.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_floats.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_floats.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_floats.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_floats.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_floats.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_floats.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_floats.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_floats.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_floats.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_floats.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_floats.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_floats.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_floats.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_floats.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_floats.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_floats.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_floats.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_floats.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_floats.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_floats.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_floats.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_floats.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_floats.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_floats.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_floats.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_floats.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_floats.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_floats.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_floats.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_floats.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_floats.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_floats.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_floats.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_floats.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_floats.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_floats.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_floats.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_floats.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_floats.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_floats.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_floats.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_floats.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_floats.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_floats.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_floats.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_floats.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_floats.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_floats.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_floats.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_floats.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_floats.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_floats.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_floats.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_floats.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_floats.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_floats.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_floats.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_floats.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_floats.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_floats.Num.Set_.t -> Number_adjuncts.For_floats.Num.Set_.t -> M Number_adjuncts.For_floats.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_floats.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_floats.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_floats.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_floats.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_floats.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_floats.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_floats.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_floats.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_floats.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_floats.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_floats.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_floats.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_floats.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_floats.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_floats.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_floats.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_floats.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_floats.Num.to_naked_nativeint".
  End Num.
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_floats.standard_int_or_float_kind".
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_floats.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_floats.unboxed_prover".
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_floats.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_floats.this_unboxed".
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_floats.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_floats.these_unboxed".
  (* number_adjuncts.mli:88  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_floats.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_floats.term_unboxed".
  (* number_adjuncts.mli:142  include Boxable with module Num := Num *)
  Parameter boxable_number_kind : Flambda_kind.Boxable_number.t.
  Extract Inlined Constant boxable_number_kind => "Number_adjuncts.For_floats.boxable_number_kind".
  (* number_adjuncts.mli:142  include Boxable with module Num := Num *)
  Parameter this_boxed : Number_adjuncts.For_floats.Num.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant this_boxed => "Number_adjuncts.For_floats.this_boxed".
  (* number_adjuncts.mli:142  include Boxable with module Num := Num *)
  Parameter these_boxed : Number_adjuncts.For_floats.Num.Set_.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant these_boxed => "Number_adjuncts.For_floats.these_boxed".
  (* number_adjuncts.mli:142  include Boxable with module Num := Num *)
  Parameter box : Flambda2_types.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant box => "Number_adjuncts.For_floats.box".
End For_floats.
Module For_int8s.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_int8s.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_int8s.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_int8s.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_int8s.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_int8s.Num.T.t -> Number_adjuncts.For_int8s.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_int8s.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_int8s.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_int8s.Num.T.t -> Number_adjuncts.For_int8s.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_int8s.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_int8s.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_int8s.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_int8s.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_int8s.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_int8s.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_int8s.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_int8s.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_int8s.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_int8s.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_int8s.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_int8s.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_int8s.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_int8s.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_int8s.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_int8s.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int8s.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_int8s.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_int8s.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_int8s.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_int8s.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_int8s.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_int8s.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_int8s.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_int8s.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_int8s.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_int8s.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_int8s.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_int8s.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_int8s.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int8s.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_int8s.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int8s.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_int8s.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_int8s.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_int8s.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_int8s.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_int8s.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_int8s.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_int8s.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_int8s.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_int8s.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_int8s.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_int8s.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_int8s.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_int8s.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_int8s.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_int8s.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_int8s.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int8s.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int8s.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_int8s.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_int8s.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_int8s.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_int8s.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int8s.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int8s.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_int8s.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_int8s.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_int8s.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int8s.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int8s.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_int8s.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int8s.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_int8s.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_int8s.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int8s.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int8s.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_int8s.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int8s.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_int8s.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int8s.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_int8s.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_int8s.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int8s.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_int8s.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int8s.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_int8s.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int8s.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_int8s.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_int8s.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_int8s.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int8s.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_int8s.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_int8s.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int8s.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_int8s.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_int8s.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_int8s.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_int8s.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_int8s.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_int8s.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_int8s.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_int8s.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_int8s.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_int8s.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_int8s.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_int8s.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_int8s.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_int8s.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_int8s.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_int8s.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_int8s.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_int8s.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_int8s.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_int8s.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_int8s.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_int8s.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_int8s.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_int8s.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_int8s.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_int8s.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_int8s.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_int8s.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_int8s.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_int8s.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_int8s.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_int8s.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_int8s.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_int8s.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_int8s.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_int8s.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_int8s.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_int8s.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_int8s.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_int8s.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_int8s.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_int8s.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_int8s.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_int8s.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_int8s.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_int8s.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_int8s.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_int8s.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_int8s.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_int8s.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_int8s.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_int8s.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_int8s.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int8s.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_int8s.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_int8s.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_int8s.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_int8s.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_int8s.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_int8s.Num.t * Number_adjuncts.For_int8s.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_int8s.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_int8s.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_int8s.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_int8s.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_int8s.Num.Pair.T.t -> Number_adjuncts.For_int8s.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_int8s.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_int8s.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_int8s.Num.Pair.T.t -> Number_adjuncts.For_int8s.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_int8s.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_int8s.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_int8s.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_int8s.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_int8s.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int8s.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int8s.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_int8s.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_int8s.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_int8s.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_int8s.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int8s.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int8s.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_int8s.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_int8s.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_int8s.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int8s.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int8s.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_int8s.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int8s.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_int8s.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_int8s.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int8s.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int8s.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_int8s.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int8s.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_int8s.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int8s.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_int8s.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_int8s.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int8s.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_int8s.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int8s.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_int8s.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int8s.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_int8s.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_int8s.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_int8s.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int8s.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_int8s.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_int8s.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int8s.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_int8s.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_int8s.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_int8s.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_int8s.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_int8s.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_int8s.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_int8s.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int8s.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int8s.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_int8s.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_int8s.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_int8s.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_int8s.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_int8s.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_int8s.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int8s.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int8s.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_int8s.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_int8s.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_int8s.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_int8s.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_int8s.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int8s.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int8s.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int8s.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_int8s.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int8s.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int8s.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_int8s.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int8s.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_int8s.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_int8s.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int8s.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_int8s.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_int8s.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_int8s.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_int8s.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_int8s.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_int8s.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int8s.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_int8s.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_int8s.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_int8s.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_int8s.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_int8s.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_int8s.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int8s.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_int8s.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_int8s.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_int8s.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_int8s.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_int8s.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_int8s.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_int8s.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_int8s.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_int8s.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int8s.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_int8s.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_int8s.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_int8s.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_int8s.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int8s.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int8s.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_int8s.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int8s.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_int8s.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_int8s.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_int8s.Num.Set_.t -> Number_adjuncts.For_int8s.Num.Set_.t -> M Number_adjuncts.For_int8s.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_int8s.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_int8s.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_int8s.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_int8s.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_int8s.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_int8s.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_int8s.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_int8s.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_int8s.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_int8s.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_int8s.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_int8s.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_int8s.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_int8s.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_int8s.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_int8s.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_int8s.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_int8s.Num.to_naked_nativeint".
    (* number_adjuncts.mli:95  val and_ : t -> t -> t *)
    Parameter and_ : t -> t -> M t.
    Extract Inlined Constant and_ => "Number_adjuncts.For_int8s.Num.and_".
    (* number_adjuncts.mli:97  val or_ : t -> t -> t *)
    Parameter or_ : t -> t -> M t.
    Extract Inlined Constant or_ => "Number_adjuncts.For_int8s.Num.or_".
    (* number_adjuncts.mli:99  val xor : t -> t -> t *)
    Parameter xor : t -> t -> M t.
    Extract Inlined Constant xor => "Number_adjuncts.For_int8s.Num.xor".
    (* number_adjuncts.mli:101  val not_ : t -> t *)
    Parameter not_ : t -> M t.
    Extract Inlined Constant not_ => "Number_adjuncts.For_int8s.Num.not_".
    (* number_adjuncts.mli:103  val unsigned_div : t -> t -> t option *)
    Parameter unsigned_div : t -> t -> M (option t).
    Extract Inlined Constant unsigned_div => "Number_adjuncts.For_int8s.Num.unsigned_div".
    (* number_adjuncts.mli:105  val unsigned_mod : t -> t -> t option *)
    Parameter unsigned_mod : t -> t -> M (option t).
    Extract Inlined Constant unsigned_mod => "Number_adjuncts.For_int8s.Num.unsigned_mod".
    (* number_adjuncts.mli:107  val shift_left : t -> Target_ocaml_int.t -> t *)
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_left => "Number_adjuncts.For_int8s.Num.shift_left".
    (* number_adjuncts.mli:111  val shift_right : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right => "Number_adjuncts.For_int8s.Num.shift_right".
    (* number_adjuncts.mli:113  val shift_right_logical : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right_logical => "Number_adjuncts.For_int8s.Num.shift_right_logical".
    (* number_adjuncts.mli:115  val swap_byte_endianness : t -> t *)
    Parameter swap_byte_endianness : t -> M t.
    Extract Inlined Constant swap_byte_endianness => "Number_adjuncts.For_int8s.Num.swap_byte_endianness".
    (* number_adjuncts.mli:117  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Number_adjuncts.For_int8s.Num.neg".
    (* number_adjuncts.mli:119  val compare_unsigned : t -> t -> int *)
    Parameter compare_unsigned : t -> t -> M int.
    Extract Inlined Constant compare_unsigned => "Number_adjuncts.For_int8s.Num.compare_unsigned".
  End Num.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_int8s.standard_int_or_float_kind".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_int8s.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_int8s.unboxed_prover".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_int8s.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_int8s.this_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_int8s.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_int8s.these_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_int8s.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_int8s.term_unboxed".
  (* number_adjuncts.mli:124  val standard_int_kind : Flambda_kind.Standard_int.t *)
  Parameter standard_int_kind : Flambda_kind.Standard_int.t.
  Extract Inlined Constant standard_int_kind => "Number_adjuncts.For_int8s.standard_int_kind".
End For_int8s.
Module For_int16s.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_int16s.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_int16s.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_int16s.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_int16s.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_int16s.Num.T.t -> Number_adjuncts.For_int16s.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_int16s.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_int16s.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_int16s.Num.T.t -> Number_adjuncts.For_int16s.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_int16s.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_int16s.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_int16s.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_int16s.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_int16s.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_int16s.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_int16s.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_int16s.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_int16s.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_int16s.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_int16s.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_int16s.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_int16s.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_int16s.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_int16s.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_int16s.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int16s.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_int16s.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_int16s.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_int16s.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_int16s.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_int16s.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_int16s.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_int16s.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_int16s.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_int16s.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_int16s.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_int16s.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_int16s.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_int16s.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int16s.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_int16s.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int16s.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_int16s.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_int16s.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_int16s.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_int16s.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_int16s.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_int16s.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_int16s.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_int16s.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_int16s.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_int16s.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_int16s.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_int16s.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_int16s.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_int16s.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_int16s.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_int16s.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int16s.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int16s.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_int16s.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_int16s.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_int16s.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_int16s.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int16s.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int16s.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_int16s.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_int16s.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_int16s.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int16s.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int16s.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_int16s.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int16s.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_int16s.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_int16s.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int16s.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int16s.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_int16s.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int16s.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_int16s.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int16s.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_int16s.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_int16s.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int16s.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_int16s.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int16s.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_int16s.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int16s.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_int16s.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_int16s.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_int16s.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int16s.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_int16s.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_int16s.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int16s.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_int16s.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_int16s.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_int16s.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_int16s.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_int16s.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_int16s.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_int16s.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_int16s.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_int16s.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_int16s.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_int16s.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_int16s.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_int16s.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_int16s.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_int16s.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_int16s.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_int16s.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_int16s.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_int16s.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_int16s.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_int16s.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_int16s.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_int16s.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_int16s.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_int16s.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_int16s.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_int16s.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_int16s.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_int16s.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_int16s.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_int16s.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_int16s.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_int16s.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_int16s.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_int16s.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_int16s.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_int16s.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_int16s.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_int16s.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_int16s.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_int16s.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_int16s.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_int16s.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_int16s.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_int16s.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_int16s.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_int16s.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_int16s.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_int16s.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_int16s.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_int16s.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_int16s.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_int16s.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int16s.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_int16s.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_int16s.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_int16s.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_int16s.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_int16s.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_int16s.Num.t * Number_adjuncts.For_int16s.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_int16s.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_int16s.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_int16s.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_int16s.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_int16s.Num.Pair.T.t -> Number_adjuncts.For_int16s.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_int16s.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_int16s.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_int16s.Num.Pair.T.t -> Number_adjuncts.For_int16s.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_int16s.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_int16s.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_int16s.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_int16s.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_int16s.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int16s.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int16s.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_int16s.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_int16s.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_int16s.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_int16s.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int16s.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int16s.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_int16s.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_int16s.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_int16s.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int16s.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int16s.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_int16s.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int16s.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_int16s.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_int16s.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int16s.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int16s.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_int16s.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int16s.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_int16s.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int16s.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_int16s.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_int16s.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int16s.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_int16s.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int16s.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_int16s.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int16s.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_int16s.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_int16s.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_int16s.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int16s.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_int16s.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_int16s.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int16s.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_int16s.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_int16s.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_int16s.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_int16s.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_int16s.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_int16s.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_int16s.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int16s.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int16s.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_int16s.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_int16s.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_int16s.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_int16s.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_int16s.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_int16s.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int16s.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int16s.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_int16s.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_int16s.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_int16s.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_int16s.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_int16s.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int16s.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int16s.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int16s.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_int16s.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int16s.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int16s.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_int16s.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int16s.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_int16s.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_int16s.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int16s.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_int16s.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_int16s.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_int16s.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_int16s.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_int16s.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_int16s.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int16s.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_int16s.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_int16s.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_int16s.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_int16s.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_int16s.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_int16s.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int16s.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_int16s.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_int16s.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_int16s.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_int16s.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_int16s.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_int16s.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_int16s.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_int16s.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_int16s.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int16s.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_int16s.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_int16s.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_int16s.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_int16s.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int16s.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int16s.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_int16s.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int16s.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_int16s.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_int16s.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_int16s.Num.Set_.t -> Number_adjuncts.For_int16s.Num.Set_.t -> M Number_adjuncts.For_int16s.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_int16s.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_int16s.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_int16s.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_int16s.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_int16s.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_int16s.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_int16s.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_int16s.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_int16s.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_int16s.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_int16s.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_int16s.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_int16s.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_int16s.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_int16s.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_int16s.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_int16s.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_int16s.Num.to_naked_nativeint".
    (* number_adjuncts.mli:95  val and_ : t -> t -> t *)
    Parameter and_ : t -> t -> M t.
    Extract Inlined Constant and_ => "Number_adjuncts.For_int16s.Num.and_".
    (* number_adjuncts.mli:97  val or_ : t -> t -> t *)
    Parameter or_ : t -> t -> M t.
    Extract Inlined Constant or_ => "Number_adjuncts.For_int16s.Num.or_".
    (* number_adjuncts.mli:99  val xor : t -> t -> t *)
    Parameter xor : t -> t -> M t.
    Extract Inlined Constant xor => "Number_adjuncts.For_int16s.Num.xor".
    (* number_adjuncts.mli:101  val not_ : t -> t *)
    Parameter not_ : t -> M t.
    Extract Inlined Constant not_ => "Number_adjuncts.For_int16s.Num.not_".
    (* number_adjuncts.mli:103  val unsigned_div : t -> t -> t option *)
    Parameter unsigned_div : t -> t -> M (option t).
    Extract Inlined Constant unsigned_div => "Number_adjuncts.For_int16s.Num.unsigned_div".
    (* number_adjuncts.mli:105  val unsigned_mod : t -> t -> t option *)
    Parameter unsigned_mod : t -> t -> M (option t).
    Extract Inlined Constant unsigned_mod => "Number_adjuncts.For_int16s.Num.unsigned_mod".
    (* number_adjuncts.mli:107  val shift_left : t -> Target_ocaml_int.t -> t *)
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_left => "Number_adjuncts.For_int16s.Num.shift_left".
    (* number_adjuncts.mli:111  val shift_right : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right => "Number_adjuncts.For_int16s.Num.shift_right".
    (* number_adjuncts.mli:113  val shift_right_logical : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right_logical => "Number_adjuncts.For_int16s.Num.shift_right_logical".
    (* number_adjuncts.mli:115  val swap_byte_endianness : t -> t *)
    Parameter swap_byte_endianness : t -> M t.
    Extract Inlined Constant swap_byte_endianness => "Number_adjuncts.For_int16s.Num.swap_byte_endianness".
    (* number_adjuncts.mli:117  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Number_adjuncts.For_int16s.Num.neg".
    (* number_adjuncts.mli:119  val compare_unsigned : t -> t -> int *)
    Parameter compare_unsigned : t -> t -> M int.
    Extract Inlined Constant compare_unsigned => "Number_adjuncts.For_int16s.Num.compare_unsigned".
  End Num.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_int16s.standard_int_or_float_kind".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_int16s.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_int16s.unboxed_prover".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_int16s.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_int16s.this_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_int16s.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_int16s.these_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_int16s.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_int16s.term_unboxed".
  (* number_adjuncts.mli:124  val standard_int_kind : Flambda_kind.Standard_int.t *)
  Parameter standard_int_kind : Flambda_kind.Standard_int.t.
  Extract Inlined Constant standard_int_kind => "Number_adjuncts.For_int16s.standard_int_kind".
End For_int16s.
Module For_int32s.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_int32s.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_int32s.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_int32s.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_int32s.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_int32s.Num.T.t -> Number_adjuncts.For_int32s.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_int32s.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_int32s.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_int32s.Num.T.t -> Number_adjuncts.For_int32s.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_int32s.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_int32s.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_int32s.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_int32s.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_int32s.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_int32s.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_int32s.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_int32s.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_int32s.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_int32s.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_int32s.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_int32s.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_int32s.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_int32s.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_int32s.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_int32s.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int32s.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_int32s.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_int32s.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_int32s.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_int32s.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_int32s.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_int32s.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_int32s.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_int32s.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_int32s.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_int32s.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_int32s.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_int32s.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_int32s.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int32s.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_int32s.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int32s.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_int32s.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_int32s.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_int32s.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_int32s.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_int32s.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_int32s.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_int32s.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_int32s.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_int32s.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_int32s.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_int32s.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_int32s.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_int32s.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_int32s.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_int32s.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_int32s.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int32s.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int32s.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_int32s.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_int32s.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_int32s.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_int32s.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int32s.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int32s.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_int32s.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_int32s.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_int32s.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int32s.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int32s.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_int32s.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int32s.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_int32s.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_int32s.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int32s.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int32s.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_int32s.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int32s.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_int32s.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int32s.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_int32s.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_int32s.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int32s.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_int32s.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int32s.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_int32s.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int32s.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_int32s.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_int32s.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_int32s.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int32s.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_int32s.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_int32s.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int32s.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_int32s.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_int32s.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_int32s.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_int32s.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_int32s.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_int32s.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_int32s.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_int32s.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_int32s.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_int32s.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_int32s.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_int32s.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_int32s.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_int32s.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_int32s.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_int32s.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_int32s.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_int32s.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_int32s.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_int32s.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_int32s.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_int32s.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_int32s.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_int32s.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_int32s.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_int32s.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_int32s.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_int32s.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_int32s.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_int32s.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_int32s.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_int32s.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_int32s.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_int32s.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_int32s.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_int32s.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_int32s.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_int32s.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_int32s.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_int32s.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_int32s.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_int32s.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_int32s.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_int32s.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_int32s.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_int32s.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_int32s.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_int32s.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_int32s.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_int32s.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_int32s.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_int32s.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_int32s.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int32s.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_int32s.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_int32s.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_int32s.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_int32s.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_int32s.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_int32s.Num.t * Number_adjuncts.For_int32s.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_int32s.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_int32s.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_int32s.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_int32s.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_int32s.Num.Pair.T.t -> Number_adjuncts.For_int32s.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_int32s.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_int32s.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_int32s.Num.Pair.T.t -> Number_adjuncts.For_int32s.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_int32s.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_int32s.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_int32s.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_int32s.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_int32s.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int32s.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int32s.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_int32s.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_int32s.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_int32s.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_int32s.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int32s.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int32s.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_int32s.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_int32s.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_int32s.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int32s.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int32s.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_int32s.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int32s.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_int32s.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_int32s.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int32s.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int32s.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_int32s.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int32s.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_int32s.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int32s.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_int32s.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_int32s.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int32s.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_int32s.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int32s.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_int32s.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int32s.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_int32s.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_int32s.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_int32s.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int32s.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_int32s.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_int32s.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int32s.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_int32s.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_int32s.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_int32s.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_int32s.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_int32s.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_int32s.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_int32s.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int32s.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int32s.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_int32s.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_int32s.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_int32s.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_int32s.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_int32s.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_int32s.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int32s.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int32s.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_int32s.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_int32s.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_int32s.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_int32s.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_int32s.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int32s.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int32s.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int32s.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_int32s.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int32s.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int32s.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_int32s.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int32s.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_int32s.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_int32s.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int32s.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_int32s.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_int32s.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_int32s.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_int32s.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_int32s.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_int32s.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int32s.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_int32s.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_int32s.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_int32s.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_int32s.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_int32s.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_int32s.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int32s.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_int32s.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_int32s.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_int32s.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_int32s.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_int32s.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_int32s.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_int32s.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_int32s.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_int32s.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int32s.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_int32s.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_int32s.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_int32s.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_int32s.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int32s.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int32s.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_int32s.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int32s.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_int32s.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_int32s.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_int32s.Num.Set_.t -> Number_adjuncts.For_int32s.Num.Set_.t -> M Number_adjuncts.For_int32s.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_int32s.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_int32s.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_int32s.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_int32s.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_int32s.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_int32s.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_int32s.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_int32s.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_int32s.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_int32s.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_int32s.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_int32s.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_int32s.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_int32s.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_int32s.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_int32s.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_int32s.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_int32s.Num.to_naked_nativeint".
    (* number_adjuncts.mli:95  val and_ : t -> t -> t *)
    Parameter and_ : t -> t -> M t.
    Extract Inlined Constant and_ => "Number_adjuncts.For_int32s.Num.and_".
    (* number_adjuncts.mli:97  val or_ : t -> t -> t *)
    Parameter or_ : t -> t -> M t.
    Extract Inlined Constant or_ => "Number_adjuncts.For_int32s.Num.or_".
    (* number_adjuncts.mli:99  val xor : t -> t -> t *)
    Parameter xor : t -> t -> M t.
    Extract Inlined Constant xor => "Number_adjuncts.For_int32s.Num.xor".
    (* number_adjuncts.mli:101  val not_ : t -> t *)
    Parameter not_ : t -> M t.
    Extract Inlined Constant not_ => "Number_adjuncts.For_int32s.Num.not_".
    (* number_adjuncts.mli:103  val unsigned_div : t -> t -> t option *)
    Parameter unsigned_div : t -> t -> M (option t).
    Extract Inlined Constant unsigned_div => "Number_adjuncts.For_int32s.Num.unsigned_div".
    (* number_adjuncts.mli:105  val unsigned_mod : t -> t -> t option *)
    Parameter unsigned_mod : t -> t -> M (option t).
    Extract Inlined Constant unsigned_mod => "Number_adjuncts.For_int32s.Num.unsigned_mod".
    (* number_adjuncts.mli:107  val shift_left : t -> Target_ocaml_int.t -> t *)
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_left => "Number_adjuncts.For_int32s.Num.shift_left".
    (* number_adjuncts.mli:111  val shift_right : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right => "Number_adjuncts.For_int32s.Num.shift_right".
    (* number_adjuncts.mli:113  val shift_right_logical : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right_logical => "Number_adjuncts.For_int32s.Num.shift_right_logical".
    (* number_adjuncts.mli:115  val swap_byte_endianness : t -> t *)
    Parameter swap_byte_endianness : t -> M t.
    Extract Inlined Constant swap_byte_endianness => "Number_adjuncts.For_int32s.Num.swap_byte_endianness".
    (* number_adjuncts.mli:117  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Number_adjuncts.For_int32s.Num.neg".
    (* number_adjuncts.mli:119  val compare_unsigned : t -> t -> int *)
    Parameter compare_unsigned : t -> t -> M int.
    Extract Inlined Constant compare_unsigned => "Number_adjuncts.For_int32s.Num.compare_unsigned".
  End Num.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_int32s.standard_int_or_float_kind".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_int32s.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_int32s.unboxed_prover".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_int32s.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_int32s.this_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_int32s.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_int32s.these_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_int32s.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_int32s.term_unboxed".
  (* number_adjuncts.mli:124  val standard_int_kind : Flambda_kind.Standard_int.t *)
  Parameter standard_int_kind : Flambda_kind.Standard_int.t.
  Extract Inlined Constant standard_int_kind => "Number_adjuncts.For_int32s.standard_int_kind".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter boxable_number_kind : Flambda_kind.Boxable_number.t.
  Extract Inlined Constant boxable_number_kind => "Number_adjuncts.For_int32s.boxable_number_kind".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter this_boxed : Number_adjuncts.For_int32s.Num.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant this_boxed => "Number_adjuncts.For_int32s.this_boxed".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter these_boxed : Number_adjuncts.For_int32s.Num.Set_.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant these_boxed => "Number_adjuncts.For_int32s.these_boxed".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter box : Flambda2_types.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant box => "Number_adjuncts.For_int32s.box".
End For_int32s.
Module For_int64s.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_int64s.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_int64s.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_int64s.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_int64s.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_int64s.Num.T.t -> Number_adjuncts.For_int64s.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_int64s.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_int64s.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_int64s.Num.T.t -> Number_adjuncts.For_int64s.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_int64s.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_int64s.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_int64s.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_int64s.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_int64s.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_int64s.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_int64s.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_int64s.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_int64s.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_int64s.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_int64s.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_int64s.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_int64s.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_int64s.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_int64s.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_int64s.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int64s.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_int64s.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_int64s.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_int64s.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_int64s.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_int64s.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_int64s.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_int64s.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_int64s.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_int64s.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_int64s.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_int64s.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_int64s.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_int64s.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int64s.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_int64s.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int64s.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_int64s.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_int64s.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_int64s.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_int64s.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_int64s.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_int64s.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_int64s.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_int64s.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_int64s.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_int64s.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_int64s.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_int64s.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_int64s.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_int64s.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_int64s.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_int64s.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int64s.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int64s.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_int64s.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_int64s.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_int64s.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_int64s.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int64s.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int64s.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_int64s.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_int64s.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_int64s.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int64s.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int64s.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_int64s.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int64s.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_int64s.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_int64s.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int64s.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int64s.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_int64s.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int64s.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_int64s.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int64s.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_int64s.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_int64s.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int64s.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_int64s.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int64s.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_int64s.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int64s.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_int64s.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_int64s.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_int64s.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int64s.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_int64s.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_int64s.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int64s.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_int64s.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_int64s.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_int64s.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_int64s.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_int64s.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_int64s.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_int64s.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_int64s.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_int64s.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_int64s.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_int64s.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_int64s.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_int64s.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_int64s.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_int64s.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_int64s.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_int64s.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_int64s.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_int64s.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_int64s.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_int64s.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_int64s.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_int64s.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_int64s.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_int64s.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_int64s.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_int64s.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_int64s.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_int64s.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_int64s.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_int64s.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_int64s.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_int64s.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_int64s.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_int64s.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_int64s.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_int64s.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_int64s.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_int64s.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_int64s.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_int64s.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_int64s.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_int64s.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_int64s.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_int64s.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_int64s.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_int64s.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_int64s.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_int64s.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_int64s.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_int64s.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_int64s.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_int64s.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int64s.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_int64s.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_int64s.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_int64s.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_int64s.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_int64s.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_int64s.Num.t * Number_adjuncts.For_int64s.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_int64s.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_int64s.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_int64s.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_int64s.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_int64s.Num.Pair.T.t -> Number_adjuncts.For_int64s.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_int64s.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_int64s.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_int64s.Num.Pair.T.t -> Number_adjuncts.For_int64s.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_int64s.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_int64s.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_int64s.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_int64s.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_int64s.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int64s.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int64s.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_int64s.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_int64s.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_int64s.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_int64s.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int64s.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int64s.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_int64s.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_int64s.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_int64s.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int64s.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int64s.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_int64s.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int64s.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_int64s.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_int64s.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int64s.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int64s.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_int64s.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int64s.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_int64s.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int64s.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_int64s.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_int64s.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int64s.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_int64s.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int64s.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_int64s.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int64s.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_int64s.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_int64s.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_int64s.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int64s.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_int64s.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_int64s.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int64s.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_int64s.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_int64s.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_int64s.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_int64s.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_int64s.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_int64s.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_int64s.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_int64s.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_int64s.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_int64s.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_int64s.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_int64s.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_int64s.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_int64s.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_int64s.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_int64s.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_int64s.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_int64s.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_int64s.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_int64s.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_int64s.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_int64s.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_int64s.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_int64s.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_int64s.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_int64s.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_int64s.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_int64s.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_int64s.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_int64s.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_int64s.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_int64s.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_int64s.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_int64s.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_int64s.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_int64s.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_int64s.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_int64s.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_int64s.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_int64s.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_int64s.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_int64s.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_int64s.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_int64s.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_int64s.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_int64s.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_int64s.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_int64s.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_int64s.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_int64s.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_int64s.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_int64s.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_int64s.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_int64s.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_int64s.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_int64s.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_int64s.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_int64s.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_int64s.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_int64s.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_int64s.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_int64s.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_int64s.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_int64s.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_int64s.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_int64s.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_int64s.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_int64s.Num.Set_.t -> Number_adjuncts.For_int64s.Num.Set_.t -> M Number_adjuncts.For_int64s.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_int64s.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_int64s.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_int64s.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_int64s.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_int64s.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_int64s.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_int64s.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_int64s.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_int64s.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_int64s.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_int64s.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_int64s.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_int64s.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_int64s.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_int64s.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_int64s.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_int64s.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_int64s.Num.to_naked_nativeint".
    (* number_adjuncts.mli:95  val and_ : t -> t -> t *)
    Parameter and_ : t -> t -> M t.
    Extract Inlined Constant and_ => "Number_adjuncts.For_int64s.Num.and_".
    (* number_adjuncts.mli:97  val or_ : t -> t -> t *)
    Parameter or_ : t -> t -> M t.
    Extract Inlined Constant or_ => "Number_adjuncts.For_int64s.Num.or_".
    (* number_adjuncts.mli:99  val xor : t -> t -> t *)
    Parameter xor : t -> t -> M t.
    Extract Inlined Constant xor => "Number_adjuncts.For_int64s.Num.xor".
    (* number_adjuncts.mli:101  val not_ : t -> t *)
    Parameter not_ : t -> M t.
    Extract Inlined Constant not_ => "Number_adjuncts.For_int64s.Num.not_".
    (* number_adjuncts.mli:103  val unsigned_div : t -> t -> t option *)
    Parameter unsigned_div : t -> t -> M (option t).
    Extract Inlined Constant unsigned_div => "Number_adjuncts.For_int64s.Num.unsigned_div".
    (* number_adjuncts.mli:105  val unsigned_mod : t -> t -> t option *)
    Parameter unsigned_mod : t -> t -> M (option t).
    Extract Inlined Constant unsigned_mod => "Number_adjuncts.For_int64s.Num.unsigned_mod".
    (* number_adjuncts.mli:107  val shift_left : t -> Target_ocaml_int.t -> t *)
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_left => "Number_adjuncts.For_int64s.Num.shift_left".
    (* number_adjuncts.mli:111  val shift_right : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right => "Number_adjuncts.For_int64s.Num.shift_right".
    (* number_adjuncts.mli:113  val shift_right_logical : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right_logical => "Number_adjuncts.For_int64s.Num.shift_right_logical".
    (* number_adjuncts.mli:115  val swap_byte_endianness : t -> t *)
    Parameter swap_byte_endianness : t -> M t.
    Extract Inlined Constant swap_byte_endianness => "Number_adjuncts.For_int64s.Num.swap_byte_endianness".
    (* number_adjuncts.mli:117  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Number_adjuncts.For_int64s.Num.neg".
    (* number_adjuncts.mli:119  val compare_unsigned : t -> t -> int *)
    Parameter compare_unsigned : t -> t -> M int.
    Extract Inlined Constant compare_unsigned => "Number_adjuncts.For_int64s.Num.compare_unsigned".
  End Num.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_int64s.standard_int_or_float_kind".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_int64s.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_int64s.unboxed_prover".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_int64s.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_int64s.this_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_int64s.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_int64s.these_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_int64s.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_int64s.term_unboxed".
  (* number_adjuncts.mli:124  val standard_int_kind : Flambda_kind.Standard_int.t *)
  Parameter standard_int_kind : Flambda_kind.Standard_int.t.
  Extract Inlined Constant standard_int_kind => "Number_adjuncts.For_int64s.standard_int_kind".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter boxable_number_kind : Flambda_kind.Boxable_number.t.
  Extract Inlined Constant boxable_number_kind => "Number_adjuncts.For_int64s.boxable_number_kind".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter this_boxed : Number_adjuncts.For_int64s.Num.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant this_boxed => "Number_adjuncts.For_int64s.this_boxed".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter these_boxed : Number_adjuncts.For_int64s.Num.Set_.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant these_boxed => "Number_adjuncts.For_int64s.these_boxed".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter box : Flambda2_types.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant box => "Number_adjuncts.For_int64s.box".
End For_int64s.
Module For_nativeints.
  Module Num.
    (* container_types_intf.ml:297  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Number_adjuncts.For_nativeints.Num.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Number_adjuncts.For_nativeints.Num.t.
      Extract Inlined Constant t => "Number_adjuncts.For_nativeints.Num.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_nativeints.Num.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Number_adjuncts.For_nativeints.Num.T.t -> Number_adjuncts.For_nativeints.Num.T.t -> M bool.
    Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Number_adjuncts.For_nativeints.Num.T.t -> M int.
    Extract Inlined Constant hash => "Number_adjuncts.For_nativeints.Num.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Number_adjuncts.For_nativeints.Num.T.t -> Number_adjuncts.For_nativeints.Num.T.t -> M int.
    Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Number_adjuncts.For_nativeints.Num.T.t -> M unit.
    Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Number_adjuncts.For_nativeints.Num.t.
      Extract Inlined Constant elt => "Number_adjuncts.For_nativeints.Num.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Number_adjuncts.For_nativeints.Num.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Number_adjuncts.For_nativeints.Num.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_nativeints.Num.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_nativeints.Num.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Number_adjuncts.For_nativeints.Num.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Number_adjuncts.For_nativeints.Num.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Number_adjuncts.For_nativeints.Num.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Number_adjuncts.For_nativeints.Num.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_nativeints.Num.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Number_adjuncts.For_nativeints.Num.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Number_adjuncts.For_nativeints.Num.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Number_adjuncts.For_nativeints.Num.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Number_adjuncts.For_nativeints.Num.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_nativeints.Num.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_nativeints.Num.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Number_adjuncts.For_nativeints.Num.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_nativeints.Num.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Number_adjuncts.For_nativeints.Num.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Number_adjuncts.For_nativeints.Num.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_nativeints.Num.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_nativeints.Num.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Number_adjuncts.For_nativeints.Num.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Number_adjuncts.For_nativeints.Num.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Number_adjuncts.For_nativeints.Num.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_nativeints.Num.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Number_adjuncts.For_nativeints.Num.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Number_adjuncts.For_nativeints.Num.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_nativeints.Num.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Number_adjuncts.For_nativeints.Num.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_nativeints.Num.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Number_adjuncts.For_nativeints.Num.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_nativeints.Num.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Number_adjuncts.For_nativeints.Num.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Number_adjuncts.For_nativeints.Num.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Number_adjuncts.For_nativeints.Num.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Number_adjuncts.For_nativeints.Num.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Number_adjuncts.For_nativeints.Num.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Number_adjuncts.For_nativeints.Num.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_nativeints.Num.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Number_adjuncts.For_nativeints.Num.t.
      Extract Inlined Constant key => "Number_adjuncts.For_nativeints.Num.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Number_adjuncts.For_nativeints.Num.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_nativeints.Num.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Number_adjuncts.For_nativeints.Num.Set_.t.
        Extract Inlined Constant t => "Number_adjuncts.For_nativeints.Num.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_nativeints.Num.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_nativeints.Num.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_nativeints.Num.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_nativeints.Num.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_nativeints.Num.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_nativeints.Num.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_nativeints.Num.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_nativeints.Num.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_nativeints.Num.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_nativeints.Num.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_nativeints.Num.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_nativeints.Num.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_nativeints.Num.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_nativeints.Num.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_nativeints.Num.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_nativeints.Num.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_nativeints.Num.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_nativeints.Num.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_nativeints.Num.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_nativeints.Num.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_nativeints.Num.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_nativeints.Num.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_nativeints.Num.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_nativeints.Num.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_nativeints.Num.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_nativeints.Num.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_nativeints.Num.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_nativeints.Num.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_nativeints.Num.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_nativeints.Num.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_nativeints.Num.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_nativeints.Num.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_nativeints.Num.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_nativeints.Num.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_nativeints.Num.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_nativeints.Num.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_nativeints.Num.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_nativeints.Num.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Number_adjuncts.For_nativeints.Num.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Number_adjuncts.For_nativeints.Num.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Number_adjuncts.For_nativeints.Num.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Number_adjuncts.For_nativeints.Num.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Number_adjuncts.For_nativeints.Num.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Number_adjuncts.For_nativeints.Num.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Number_adjuncts.For_nativeints.Num.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Number_adjuncts.For_nativeints.Num.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Number_adjuncts.For_nativeints.Num.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Number_adjuncts.For_nativeints.Num.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Number_adjuncts.For_nativeints.Num.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Number_adjuncts.For_nativeints.Num.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Number_adjuncts.For_nativeints.Num.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Number_adjuncts.For_nativeints.Num.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Number_adjuncts.For_nativeints.Num.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Number_adjuncts.For_nativeints.Num.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Number_adjuncts.For_nativeints.Num.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Number_adjuncts.For_nativeints.Num.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Number_adjuncts.For_nativeints.Num.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Number_adjuncts.For_nativeints.Num.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Number_adjuncts.For_nativeints.Num.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Number_adjuncts.For_nativeints.Num.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Number_adjuncts.For_nativeints.Num.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_nativeints.Num.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Number_adjuncts.For_nativeints.Num.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Number_adjuncts.For_nativeints.Num.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Number_adjuncts.For_nativeints.Num.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Number_adjuncts.For_nativeints.Num.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_nativeints.Num.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Number_adjuncts.For_nativeints.Num.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_nativeints.Num.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Number_adjuncts.For_nativeints.Num.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Number_adjuncts.For_nativeints.Num.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Number_adjuncts.For_nativeints.Num.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Number_adjuncts.For_nativeints.Num.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Number_adjuncts.For_nativeints.Num.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Number_adjuncts.For_nativeints.Num.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Number_adjuncts.For_nativeints.Num.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Number_adjuncts.For_nativeints.Num.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Number_adjuncts.For_nativeints.Num.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Number_adjuncts.For_nativeints.Num.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Number_adjuncts.For_nativeints.Num.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_nativeints.Num.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Number_adjuncts.For_nativeints.Num.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_nativeints.Num.Map.Set_.t.
      Extract Inlined Constant keys => "Number_adjuncts.For_nativeints.Num.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Number_adjuncts.For_nativeints.Num.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_nativeints.Num.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Number_adjuncts.For_nativeints.Num.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Number_adjuncts.For_nativeints.Num.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Number_adjuncts.For_nativeints.Num.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Number_adjuncts.For_nativeints.Num.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Number_adjuncts.For_nativeints.Num.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Number_adjuncts.For_nativeints.Num.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Number_adjuncts.For_nativeints.Num.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_nativeints.Num.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Number_adjuncts.For_nativeints.Num.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Number_adjuncts.For_nativeints.Num.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Number_adjuncts.For_nativeints.Num.Map.map_sharing".
    End Map.
    Module Pair.
      (* number_adjuncts.mli:25  type nonrec t = t * t *)
      Definition t : Type := (Number_adjuncts.For_nativeints.Num.t * Number_adjuncts.For_nativeints.Num.t).
      Extract Inlined Constant t => "Number_adjuncts.For_nativeints.Num.Pair.t".
      Module T.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition t : Type := Number_adjuncts.For_nativeints.Num.Pair.t.
        Extract Inlined Constant t => "Number_adjuncts.For_nativeints.Num.Pair.T.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.Pair.T.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter hash : t -> M int.
        Extract Inlined Constant hash => "Number_adjuncts.For_nativeints.Num.Pair.T.hash".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.Pair.T.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.Pair.T.print".
      End T.
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter equal : Number_adjuncts.For_nativeints.Num.Pair.T.t -> Number_adjuncts.For_nativeints.Num.Pair.T.t -> M bool.
      Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.Pair.equal".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter hash : Number_adjuncts.For_nativeints.Num.Pair.T.t -> M int.
      Extract Inlined Constant hash => "Number_adjuncts.For_nativeints.Num.Pair.hash".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter compare : Number_adjuncts.For_nativeints.Num.Pair.T.t -> Number_adjuncts.For_nativeints.Num.Pair.T.t -> M int.
      Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.Pair.compare".
      (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> Number_adjuncts.For_nativeints.Num.Pair.T.t -> M unit.
      Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.Pair.print".
      Module Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition elt : Type := Number_adjuncts.For_nativeints.Num.Pair.t.
        Extract Inlined Constant elt => "Number_adjuncts.For_nativeints.Num.Pair.Set.elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type.
        Extract Inlined Constant t => "Number_adjuncts.For_nativeints.Num.Pair.Set.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Number_adjuncts.For_nativeints.Num.Pair.Set.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_nativeints.Num.Pair.Set.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_nativeints.Num.Pair.Set.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Number_adjuncts.For_nativeints.Num.Pair.Set.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Number_adjuncts.For_nativeints.Num.Pair.Set.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Number_adjuncts.For_nativeints.Num.Pair.Set.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Number_adjuncts.For_nativeints.Num.Pair.Set.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_nativeints.Num.Pair.Set.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Number_adjuncts.For_nativeints.Num.Pair.Set.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Number_adjuncts.For_nativeints.Num.Pair.Set.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Number_adjuncts.For_nativeints.Num.Pair.Set.disjoint".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Number_adjuncts.For_nativeints.Num.Pair.Set.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_nativeints.Num.Pair.Set.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_nativeints.Num.Pair.Set.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.Pair.Set.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.Pair.Set.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Number_adjuncts.For_nativeints.Num.Pair.Set.subset".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_nativeints.Num.Pair.Set.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Number_adjuncts.For_nativeints.Num.Pair.Set.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Number_adjuncts.For_nativeints.Num.Pair.Set.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_nativeints.Num.Pair.Set.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_nativeints.Num.Pair.Set.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Number_adjuncts.For_nativeints.Num.Pair.Set.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Number_adjuncts.For_nativeints.Num.Pair.Set.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Number_adjuncts.For_nativeints.Num.Pair.Set.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_nativeints.Num.Pair.Set.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Number_adjuncts.For_nativeints.Num.Pair.Set.elements".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Number_adjuncts.For_nativeints.Num.Pair.Set.min_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_nativeints.Num.Pair.Set.min_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Number_adjuncts.For_nativeints.Num.Pair.Set.max_elt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_nativeints.Num.Pair.Set.max_elt_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Number_adjuncts.For_nativeints.Num.Pair.Set.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_nativeints.Num.Pair.Set.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Number_adjuncts.For_nativeints.Num.Pair.Set.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Number_adjuncts.For_nativeints.Num.Pair.Set.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Number_adjuncts.For_nativeints.Num.Pair.Set.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Number_adjuncts.For_nativeints.Num.Pair.Set.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.Pair.Set.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Number_adjuncts.For_nativeints.Num.Pair.Set.to_string".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Number_adjuncts.For_nativeints.Num.Pair.Set.union_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_nativeints.Num.Pair.Set.get_singleton".
      End Set_.
      Module Map.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Definition key : Type := Number_adjuncts.For_nativeints.Num.Pair.t.
        Extract Inlined Constant key => "Number_adjuncts.For_nativeints.Num.Pair.Map.key".
        Module Set_.
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition elt : Type := Number_adjuncts.For_nativeints.Num.Pair.t.
          Extract Inlined Constant elt => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Definition t : Type := Number_adjuncts.For_nativeints.Num.Pair.Set_.t.
          Extract Inlined Constant t => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.t".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter empty : t.
          Extract Inlined Constant empty => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter is_empty : t -> M bool.
          Extract Inlined Constant is_empty => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.is_empty".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter mem : elt -> t -> M bool.
          Extract Inlined Constant mem => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.mem".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter add : elt -> t -> M t.
          Extract Inlined Constant add => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.add".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter singleton : elt -> M t.
          Extract Inlined Constant singleton => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.singleton".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter remove : elt -> t -> M t.
          Extract Inlined Constant remove => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.remove".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union : t -> t -> M t.
          Extract Inlined Constant union => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.union".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_sharing : t -> t -> M t.
          Extract Inlined Constant union_sharing => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.union_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_shared : t -> t -> M t.
          Extract Inlined Constant union_shared => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.union_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter inter : t -> t -> M t.
          Extract Inlined Constant inter => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.inter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter disjoint : t -> t -> M bool.
          Extract Inlined Constant disjoint => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.disjoint".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff : t -> t -> M t.
          Extract Inlined Constant diff => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.diff".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_sharing : t -> t -> M t.
          Extract Inlined Constant diff_sharing => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.diff_sharing".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter diff_shared : t -> t -> M t.
          Extract Inlined Constant diff_shared => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.diff_shared".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter compare : t -> t -> M int.
          Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.compare".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter equal : t -> t -> M bool.
          Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.equal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter subset : t -> t -> M bool.
          Extract Inlined Constant subset => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.subset".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter iter : (elt -> M unit) -> t -> M unit.
          Extract Inlined Constant iter => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.iter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter map : (elt -> M elt) -> t -> M t.
          Extract Inlined Constant map => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
          Extract Inlined Constant fold => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.fold".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter for_all : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant for_all => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.for_all".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter exists_ : (elt -> M bool) -> t -> M bool.
          Extract Inlined Constant exists_ => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.exists".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter : (elt -> M bool) -> t -> M t.
          Extract Inlined Constant filter => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.filter".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
          Extract Inlined Constant filter_map => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.filter_map".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter partition : (elt -> M bool) -> t -> M (t * t).
          Extract Inlined Constant partition => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.partition".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter cardinal : t -> M int.
          Extract Inlined Constant cardinal => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.cardinal".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter elements : t -> M (list elt).
          Extract Inlined Constant elements => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.elements".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt : t -> M elt.
          Extract Inlined Constant min_elt => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.min_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter min_elt_opt : t -> M (option elt).
          Extract Inlined Constant min_elt_opt => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.min_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt : t -> M elt.
          Extract Inlined Constant max_elt => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.max_elt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter max_elt_opt : t -> M (option elt).
          Extract Inlined Constant max_elt_opt => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.max_elt_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose : t -> M elt.
          Extract Inlined Constant choose => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.choose".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter choose_opt : t -> M (option elt).
          Extract Inlined Constant choose_opt => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.choose_opt".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter split : elt -> t -> M (tuple3 t bool t).
          Extract Inlined Constant split => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.split".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter find : elt -> t -> M elt.
          Extract Inlined Constant find => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.find".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter of_list : list elt -> M t.
          Extract Inlined Constant of_list => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.of_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_seq : t -> Seq.t elt.
          Extract Inlined Constant to_seq => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.to_seq".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter print : Format.formatter -> t -> M unit.
          Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.print".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter to_string : t -> M string.
          Extract Inlined Constant to_string => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.to_string".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter union_list : list t -> M t.
          Extract Inlined Constant union_list => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.union_list".
          (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
          Parameter get_singleton : t -> M (option elt).
          Extract Inlined Constant get_singleton => "Number_adjuncts.For_nativeints.Num.Pair.Map.Set.get_singleton".
        End Set_.
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter t : Type -> Type.
        Extract Constant t "'a1" => "('a1) Number_adjuncts.For_nativeints.Num.Pair.Map.t".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter empty : forall {A : Type}, t A.
        Extract Inlined Constant empty => "Number_adjuncts.For_nativeints.Num.Pair.Map.empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter is_empty : forall {A : Type}, t A -> M bool.
        Extract Inlined Constant is_empty => "Number_adjuncts.For_nativeints.Num.Pair.Map.is_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mem : forall {A : Type}, key -> t A -> M bool.
        Extract Inlined Constant mem => "Number_adjuncts.For_nativeints.Num.Pair.Map.mem".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
        Extract Inlined Constant add => "Number_adjuncts.For_nativeints.Num.Pair.Map.add".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant update => "Number_adjuncts.For_nativeints.Num.Pair.Map.update".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter singleton : forall {A : Type}, key -> A -> M (t A).
        Extract Inlined Constant singleton => "Number_adjuncts.For_nativeints.Num.Pair.Map.singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter remove : forall {A : Type}, key -> t A -> M (t A).
        Extract Inlined Constant remove => "Number_adjuncts.For_nativeints.Num.Pair.Map.remove".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
        Extract Inlined Constant merge => "Number_adjuncts.For_nativeints.Num.Pair.Map.merge".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union => "Number_adjuncts.For_nativeints.Num.Pair.Map.union".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_sharing => "Number_adjuncts.For_nativeints.Num.Pair.Map.union_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_shared => "Number_adjuncts.For_nativeints.Num.Pair.Map.union_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total => "Number_adjuncts.For_nativeints.Num.Pair.Map.union_total".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
        Extract Inlined Constant union_total_shared => "Number_adjuncts.For_nativeints.Num.Pair.Map.union_total_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_left_biased => "Number_adjuncts.For_nativeints.Num.Pair.Map.union_left_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
        Extract Inlined Constant union_right_biased => "Number_adjuncts.For_nativeints.Num.Pair.Map.union_right_biased".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant update_many => "Number_adjuncts.For_nativeints.Num.Pair.Map.update_many".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
        Extract Inlined Constant compare => "Number_adjuncts.For_nativeints.Num.Pair.Map.compare".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
        Extract Inlined Constant equal => "Number_adjuncts.For_nativeints.Num.Pair.Map.equal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
        Extract Inlined Constant iter => "Number_adjuncts.For_nativeints.Num.Pair.Map.iter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
        Extract Inlined Constant fold => "Number_adjuncts.For_nativeints.Num.Pair.Map.fold".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant for_all => "Number_adjuncts.For_nativeints.Num.Pair.Map.for_all".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
        Extract Inlined Constant exists_ => "Number_adjuncts.For_nativeints.Num.Pair.Map.exists".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
        Extract Inlined Constant filter => "Number_adjuncts.For_nativeints.Num.Pair.Map.filter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
        Extract Inlined Constant filter_map => "Number_adjuncts.For_nativeints.Num.Pair.Map.filter_map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
        Extract Inlined Constant filter_map_sharing => "Number_adjuncts.For_nativeints.Num.Pair.Map.filter_map_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
        Extract Inlined Constant partition => "Number_adjuncts.For_nativeints.Num.Pair.Map.partition".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter cardinal : forall {A : Type}, t A -> M int.
        Extract Inlined Constant cardinal => "Number_adjuncts.For_nativeints.Num.Pair.Map.cardinal".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
        Extract Inlined Constant bindings => "Number_adjuncts.For_nativeints.Num.Pair.Map.bindings".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant min_binding => "Number_adjuncts.For_nativeints.Num.Pair.Map.min_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant min_binding_opt => "Number_adjuncts.For_nativeints.Num.Pair.Map.min_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant max_binding => "Number_adjuncts.For_nativeints.Num.Pair.Map.max_binding".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant max_binding_opt => "Number_adjuncts.For_nativeints.Num.Pair.Map.max_binding_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose : forall {A : Type}, t A -> M (key * A).
        Extract Inlined Constant choose => "Number_adjuncts.For_nativeints.Num.Pair.Map.choose".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant choose_opt => "Number_adjuncts.For_nativeints.Num.Pair.Map.choose_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
        Extract Inlined Constant split => "Number_adjuncts.For_nativeints.Num.Pair.Map.split".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find : forall {A : Type}, key -> t A -> M A.
        Extract Inlined Constant find => "Number_adjuncts.For_nativeints.Num.Pair.Map.find".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
        Extract Inlined Constant find_opt => "Number_adjuncts.For_nativeints.Num.Pair.Map.find_opt".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
        Extract Inlined Constant find_or_null => "Number_adjuncts.For_nativeints.Num.Pair.Map.find_or_null".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
        Extract Inlined Constant map => "Number_adjuncts.For_nativeints.Num.Pair.Map.map".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
        Extract Inlined Constant mapi => "Number_adjuncts.For_nativeints.Num.Pair.Map.mapi".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
        Extract Inlined Constant to_seq => "Number_adjuncts.For_nativeints.Num.Pair.Map.to_seq".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print_debug => "Number_adjuncts.For_nativeints.Num.Pair.Map.print_debug".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
        Extract Inlined Constant of_list => "Number_adjuncts.For_nativeints.Num.Pair.Map.of_list".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
        Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Number_adjuncts.For_nativeints.Num.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
        Extract Inlined Constant map_keys => "Number_adjuncts.For_nativeints.Num.Pair.Map.map_keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter keys : forall {A : Type}, t A -> M Number_adjuncts.For_nativeints.Num.Pair.Map.Set_.t.
        Extract Inlined Constant keys => "Number_adjuncts.For_nativeints.Num.Pair.Map.keys".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter data : forall {A : Type}, t A -> M (list A).
        Extract Inlined Constant data => "Number_adjuncts.For_nativeints.Num.Pair.Map.data".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter of_set : forall {A : Type}, (key -> M A) -> Number_adjuncts.For_nativeints.Num.Pair.Map.Set_.t -> M (t A).
        Extract Inlined Constant of_set => "Number_adjuncts.For_nativeints.Num.Pair.Map.of_set".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
        Extract Inlined Constant print => "Number_adjuncts.For_nativeints.Num.Pair.Map.print".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
        Extract Inlined Constant subset_domain => "Number_adjuncts.For_nativeints.Num.Pair.Map.subset_domain".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
        Extract Inlined Constant diff_domains => "Number_adjuncts.For_nativeints.Num.Pair.Map.diff_domains".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
        Extract Inlined Constant inter => "Number_adjuncts.For_nativeints.Num.Pair.Map.inter".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff => "Number_adjuncts.For_nativeints.Num.Pair.Map.diff".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
        Extract Inlined Constant diff_sharing => "Number_adjuncts.For_nativeints.Num.Pair.Map.diff_sharing".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
        Extract Inlined Constant diff_shared => "Number_adjuncts.For_nativeints.Num.Pair.Map.diff_shared".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
        Extract Inlined Constant inter_domain_is_non_empty => "Number_adjuncts.For_nativeints.Num.Pair.Map.inter_domain_is_non_empty".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
        Extract Inlined Constant get_singleton => "Number_adjuncts.For_nativeints.Num.Pair.Map.get_singleton".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant replace => "Number_adjuncts.For_nativeints.Num.Pair.Map.replace".
        (* number_adjuncts.mli:27  include Container_types.S with type t := t *)
        Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
        Extract Inlined Constant map_sharing => "Number_adjuncts.For_nativeints.Num.Pair.Map.map_sharing".
      End Map.
    End Pair.
    (* number_adjuncts.mli:30  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
    Parameter cross_product : Number_adjuncts.For_nativeints.Num.Set_.t -> Number_adjuncts.For_nativeints.Num.Set_.t -> M Number_adjuncts.For_nativeints.Num.Pair.Set_.t.
    Extract Inlined Constant cross_product => "Number_adjuncts.For_nativeints.Num.cross_product".
    (* number_adjuncts.mli:32  val zero : Target_system.Machine_width.t -> t *)
    Parameter zero : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant zero => "Number_adjuncts.For_nativeints.Num.zero".
    (* number_adjuncts.mli:34  val one : Target_system.Machine_width.t -> t *)
    Parameter one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant one => "Number_adjuncts.For_nativeints.Num.one".
    (* number_adjuncts.mli:36  val minus_one : Target_system.Machine_width.t -> t *)
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Extract Inlined Constant minus_one => "Number_adjuncts.For_nativeints.Num.minus_one".
    (* number_adjuncts.mli:38  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Number_adjuncts.For_nativeints.Num.add".
    (* number_adjuncts.mli:40  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Number_adjuncts.For_nativeints.Num.sub".
    (* number_adjuncts.mli:42  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Number_adjuncts.For_nativeints.Num.mul".
    (* number_adjuncts.mli:44  val div : t -> t -> t option *)
    Parameter div : t -> t -> M (option t).
    Extract Inlined Constant div => "Number_adjuncts.For_nativeints.Num.div".
    (* number_adjuncts.mli:46  val mod_ : t -> t -> t option *)
    Parameter mod_ : t -> t -> M (option t).
    Extract Inlined Constant mod_ => "Number_adjuncts.For_nativeints.Num.mod_".
    (* number_adjuncts.mli:48  val to_const : t -> Reg_width_const.t *)
    Parameter to_const : t -> M Reg_width_const.t.
    Extract Inlined Constant to_const => "Number_adjuncts.For_nativeints.Num.to_const".
    (* number_adjuncts.mli:50  val to_immediate : t -> Target_system.Machine_width.t -> Target_ocaml_int.t *)
    Parameter to_immediate : t -> Target_system.Machine_width.t -> M Target_ocaml_int.t.
    Extract Inlined Constant to_immediate => "Number_adjuncts.For_nativeints.Num.to_immediate".
    (* number_adjuncts.mli:52  val to_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t *)
    Parameter to_naked_float32 : t -> M Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float32 => "Number_adjuncts.For_nativeints.Num.to_naked_float32".
    (* number_adjuncts.mli:54  val to_naked_float : t -> Numeric_types.Float_by_bit_pattern.t *)
    Parameter to_naked_float : t -> M Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant to_naked_float => "Number_adjuncts.For_nativeints.Num.to_naked_float".
    (* number_adjuncts.mli:56  val to_naked_int8 : t -> Numeric_types.Int8.t *)
    Parameter to_naked_int8 : t -> M Numeric_types.Int8.t.
    Extract Inlined Constant to_naked_int8 => "Number_adjuncts.For_nativeints.Num.to_naked_int8".
    (* number_adjuncts.mli:58  val to_naked_int16 : t -> Numeric_types.Int16.t *)
    Parameter to_naked_int16 : t -> M Numeric_types.Int16.t.
    Extract Inlined Constant to_naked_int16 => "Number_adjuncts.For_nativeints.Num.to_naked_int16".
    (* number_adjuncts.mli:60  val to_naked_int32 : t -> Numeric_types.Int32.t *)
    Parameter to_naked_int32 : t -> M Numeric_types.Int32.t.
    Extract Inlined Constant to_naked_int32 => "Number_adjuncts.For_nativeints.Num.to_naked_int32".
    (* number_adjuncts.mli:62  val to_naked_int64 : t -> Numeric_types.Int64.t *)
    Parameter to_naked_int64 : t -> M Numeric_types.Int64.t.
    Extract Inlined Constant to_naked_int64 => "Number_adjuncts.For_nativeints.Num.to_naked_int64".
    (* number_adjuncts.mli:64  val to_naked_nativeint : t -> Target_system.Machine_width.t -> Targetint_32_64.t *)
    Parameter to_naked_nativeint : t -> Target_system.Machine_width.t -> M Targetint_32_64.t.
    Extract Inlined Constant to_naked_nativeint => "Number_adjuncts.For_nativeints.Num.to_naked_nativeint".
    (* number_adjuncts.mli:95  val and_ : t -> t -> t *)
    Parameter and_ : t -> t -> M t.
    Extract Inlined Constant and_ => "Number_adjuncts.For_nativeints.Num.and_".
    (* number_adjuncts.mli:97  val or_ : t -> t -> t *)
    Parameter or_ : t -> t -> M t.
    Extract Inlined Constant or_ => "Number_adjuncts.For_nativeints.Num.or_".
    (* number_adjuncts.mli:99  val xor : t -> t -> t *)
    Parameter xor : t -> t -> M t.
    Extract Inlined Constant xor => "Number_adjuncts.For_nativeints.Num.xor".
    (* number_adjuncts.mli:101  val not_ : t -> t *)
    Parameter not_ : t -> M t.
    Extract Inlined Constant not_ => "Number_adjuncts.For_nativeints.Num.not_".
    (* number_adjuncts.mli:103  val unsigned_div : t -> t -> t option *)
    Parameter unsigned_div : t -> t -> M (option t).
    Extract Inlined Constant unsigned_div => "Number_adjuncts.For_nativeints.Num.unsigned_div".
    (* number_adjuncts.mli:105  val unsigned_mod : t -> t -> t option *)
    Parameter unsigned_mod : t -> t -> M (option t).
    Extract Inlined Constant unsigned_mod => "Number_adjuncts.For_nativeints.Num.unsigned_mod".
    (* number_adjuncts.mli:107  val shift_left : t -> Target_ocaml_int.t -> t *)
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_left => "Number_adjuncts.For_nativeints.Num.shift_left".
    (* number_adjuncts.mli:111  val shift_right : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right => "Number_adjuncts.For_nativeints.Num.shift_right".
    (* number_adjuncts.mli:113  val shift_right_logical : t -> Target_ocaml_int.t -> t *)
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    Extract Inlined Constant shift_right_logical => "Number_adjuncts.For_nativeints.Num.shift_right_logical".
    (* number_adjuncts.mli:115  val swap_byte_endianness : t -> t *)
    Parameter swap_byte_endianness : t -> M t.
    Extract Inlined Constant swap_byte_endianness => "Number_adjuncts.For_nativeints.Num.swap_byte_endianness".
    (* number_adjuncts.mli:117  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Number_adjuncts.For_nativeints.Num.neg".
    (* number_adjuncts.mli:119  val compare_unsigned : t -> t -> int *)
    Parameter compare_unsigned : t -> t -> M int.
    Extract Inlined Constant compare_unsigned => "Number_adjuncts.For_nativeints.Num.compare_unsigned".
  End Num.
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter standard_int_or_float_kind : Flambda_kind.Standard_int_or_float.t.
  Extract Inlined Constant standard_int_or_float_kind => "Number_adjuncts.For_nativeints.standard_int_or_float_kind".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter unboxed_prover : Flambda2_types.Typing_env.t -> Flambda2_types.t -> M (Flambda2_types.meet_shortcut Number_adjuncts.For_nativeints.Num.Set_.t).
  Extract Inlined Constant unboxed_prover => "Number_adjuncts.For_nativeints.unboxed_prover".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter this_unboxed : Number_adjuncts.For_nativeints.Num.t -> M Flambda2_types.t.
  Extract Inlined Constant this_unboxed => "Number_adjuncts.For_nativeints.this_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter these_unboxed : Number_adjuncts.For_nativeints.Num.Set_.t -> M Flambda2_types.t.
  Extract Inlined Constant these_unboxed => "Number_adjuncts.For_nativeints.these_unboxed".
  (* number_adjuncts.mli:122  include Number_kind_common with module Num := Num *)
  Parameter term_unboxed : Number_adjuncts.For_nativeints.Num.t -> M Flambda.Named.t.
  Extract Inlined Constant term_unboxed => "Number_adjuncts.For_nativeints.term_unboxed".
  (* number_adjuncts.mli:124  val standard_int_kind : Flambda_kind.Standard_int.t *)
  Parameter standard_int_kind : Flambda_kind.Standard_int.t.
  Extract Inlined Constant standard_int_kind => "Number_adjuncts.For_nativeints.standard_int_kind".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter boxable_number_kind : Flambda_kind.Boxable_number.t.
  Extract Inlined Constant boxable_number_kind => "Number_adjuncts.For_nativeints.boxable_number_kind".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter this_boxed : Number_adjuncts.For_nativeints.Num.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant this_boxed => "Number_adjuncts.For_nativeints.this_boxed".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter these_boxed : Number_adjuncts.For_nativeints.Num.Set_.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant these_boxed => "Number_adjuncts.For_nativeints.these_boxed".
  (* number_adjuncts.mli:148  include Boxable with module Num := Num *)
  Parameter box : Flambda2_types.t -> Alloc_mode.For_types.t -> M Flambda2_types.t.
  Extract Inlined Constant box => "Number_adjuncts.For_nativeints.box".
End For_nativeints.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Number_adjuncts. End Number_adjuncts.
