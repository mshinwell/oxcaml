(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Misc], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* Misc.fatal_error: in the kit (Port_monad.v). *)
(* Misc.fatal_errorf: in the kit (Port_monad.v). *)
(* Misc.Fatal_error: in the kit (Port_monad.v). *)
Module Stdlib.
  Module List.
    (* misc.mli:123  type 'a t = 'a list *)
    Definition t (A : Type) : Type := list A.
    Extract Constant t "'a1" => "('a1) Misc.Stdlib.List.t".
    (* misc.mli:136  val equal : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool *)
    Parameter equal : forall {A B : Type}, (A -> B -> M bool) -> t A -> t B -> M bool.
    Extract Inlined Constant equal => "Misc.Stdlib.List.equal".
    (* misc.mli:174  val map2_prefix : ('a -> 'b -> 'c) -> 'a t -> 'b t -> ('c t * 'b t) *)
    Parameter map2_prefix : forall {A B C : Type}, (A -> B -> M C) -> t A -> t B -> M (t C * t B).
    Extract Inlined Constant map2_prefix => "Misc.Stdlib.List.map2_prefix".
    (* misc.mli:191  val split_at : int -> 'a t -> 'a t * 'a t *)
    Parameter split_at : forall {A : Type}, int -> t A -> M (t A * t A).
    Extract Inlined Constant split_at => "Misc.Stdlib.List.split_at".
    (* misc.mli:200  val fold_lefti : (int -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a *)
    Parameter fold_lefti : forall {A B : Type}, (int -> A -> B -> M A) -> A -> list B -> M A.
    Extract Inlined Constant fold_lefti => "Misc.Stdlib.List.fold_lefti".
    (* misc.mli:204  val fold_left_map2 : ('acc -> 'a -> 'b -> 'acc * 'r) -> 'acc -> 'a list -> 'b list -> 'acc * 'r list *)
    Parameter fold_left_map2 : forall {Acc A B R : Type}, (Acc -> A -> B -> M (Acc * R)) -> Acc -> list A -> list B -> M (Acc * list R).
    Extract Inlined Constant fold_left_map2 => "Misc.Stdlib.List.fold_left_map2".
    (* misc.mli:219  val is_prefix : equal:('a -> 'a -> bool) -> 'a list -> of_:'a list -> bool *)
    Parameter is_prefix : forall {A : Type}, (A -> A -> M bool) -> list A -> list A -> M bool.
    Extract Inlined Constant is_prefix => "Misc.Stdlib.List.is_prefix".
  End List.
End Stdlib.
Module Colours.
  (* misc.mli:1340  type directive = Format.formatter -> unit *)
  Definition directive : Type := Format.formatter -> M unit.
  Extract Inlined Constant directive => "Misc.Colours.directive".
End Colours.
Module Sexp.
  (* misc.mli:1369  type field *)
  Parameter field : Type.
  Extract Inlined Constant field => "Misc.Sexp.field".
  (* misc.mli:1372  val d : ?colour:Colours.directive -> string -> int -> field *)
  Parameter d : option Misc.Colours.directive -> string -> int -> M field.
  Extract Inlined Constant d => "(fun x__1 x__2 x__3 -> Misc.Sexp.d ?colour:x__1 x__2 x__3)".
  (* misc.mli:1373  val b : ?colour:Colours.directive -> string -> bool -> field *)
  Parameter b : option Misc.Colours.directive -> string -> bool -> M field.
  Extract Inlined Constant b => "(fun x__1 x__2 x__3 -> Misc.Sexp.b ?colour:x__1 x__2 x__3)".
  (* misc.mli:1376  val a : ?colour:Colours.directive -> string -> 'a -> (Format.formatter -> 'a -> unit) -> field *)
  Parameter a : forall {A : Type}, option Misc.Colours.directive -> string -> A -> (Format.formatter -> A -> M unit) -> M field.
  Extract Inlined Constant a => "(fun x__1 x__2 x__3 x__4 -> Misc.Sexp.a ?colour:x__1 x__2 x__3 x__4)".
  (* misc.mli:1387  val o : ?colour:Colours.directive -> string -> 'a option -> (Format.formatter -> 'a -> unit) -> field *)
  Parameter o : forall {A : Type}, option Misc.Colours.directive -> string -> option A -> (Format.formatter -> A -> M unit) -> M field.
  Extract Inlined Constant o => "(fun x__1 x__2 x__3 x__4 -> Misc.Sexp.o ?colour:x__1 x__2 x__3 x__4)".
  (* misc.mli:1398  val print : Format.formatter -> field list -> unit *)
  Parameter print : Format.formatter -> list field -> M unit.
  Extract Inlined Constant print => "Misc.Sexp.print".
End Sexp.
