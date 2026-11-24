(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Profile], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Counters.
  (* profile.mli:26  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Profile.Counters.t".
  (* profile.mli:28  val create : unit -> t *)
  Parameter create : unit -> M t.
  Extract Inlined Constant create => "Profile.Counters.create".
  (* profile.mli:32  val incr : string -> t -> t *)
  Parameter incr : string -> t -> M t.
  Extract Inlined Constant incr => "Profile.Counters.incr".
End Counters.
(* profile.mli:40  val record_call : ?accumulate:bool -> string -> (unit -> 'a) -> 'a *)
Parameter record_call : forall {A : Type}, option bool -> string -> (unit -> M A) -> M A.
Extract Inlined Constant record_call => "(fun x__1 x__2 x__3 -> Profile.record_call ?accumulate:x__1 x__2 x__3)".
(* profile.mli:43  val record_call_with_counters : ?accumulate:bool -> counter_f:('a -> Counters.t) -> string -> (unit -> 'a) -> 'a *)
Parameter record_call_with_counters : forall {A : Type}, option bool -> (A -> M Profile.Counters.t) -> string -> (unit -> M A) -> M A.
Extract Inlined Constant record_call_with_counters => "(fun x__1 x__2 x__3 x__4 -> Profile.record_call_with_counters ?accumulate:x__1 x__2 x__3 x__4)".
(* profile.mli:52  val record_with_counters : ?accumulate:bool -> counter_f:('b -> Counters.t) -> string -> ('a -> 'b) -> 'a -> 'b *)
Parameter record_with_counters : forall {B A : Type}, option bool -> (B -> M Profile.Counters.t) -> string -> (A -> M B) -> A -> M B.
Extract Inlined Constant record_with_counters => "(fun x__1 x__2 x__3 x__4 x__5 -> Profile.record_with_counters ?accumulate:x__1 x__2 x__3 x__4 x__5)".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Profile. End Profile.
