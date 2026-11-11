(* TEST
   compile_only = "true";
   flambda2;
   setup-ocamlopt.opt-build-env;
   ocamlopt.opt with dump-simplify;
   check-fexpr-dump;
 *)

(* [Get_tag] reads the header of its argument.  Applied to something known to
   be a tagged immediate it must become [Invalid], whether the argument is a
   variable or a constant, and whether its result is switched on or used in
   arithmetic.

   Such uses arise in code that is never executed: here, in a branch that the
   GADT rules out, once [which] and [pick] have been inlined at the type
   [int].  In the reference, each of the four functions at the end has
   [invalid] in that branch and no [%get_tag]. *)

type blocks =
  | P of int
  | Q of string
  | R of int * int

type _ ty =
  | Int : int ty
  | Blocks : blocks ty

(* No constant constructors: [Get_tag] with no [Is_int] before it.  The arms
   form an arithmetic progression, so the tag is not switched on. *)
let[@inline] which (type a) (w : a ty) (x : a) : int =
  match w with
  | Int -> 0
  | Blocks -> ( match x with P _ -> 1 | Q _ -> 2 | R _ -> 3)

(* The same, with arms that stay a switch. *)
let[@inline] pick (type a) (w : a ty) (x : a) (f : int -> int) : int =
  match w with
  | Int -> 0
  | Blocks -> ( match x with P _ -> f 1 | Q _ -> f 2 | R _ -> f 3)

let tag_of_parameter (w : int ty) (n : int) = which w n

let tag_of_constant (w : int ty) = which w 5

let switch_on_tag_of_parameter (w : int ty) (n : int) f = pick w n f

let switch_on_tag_of_constant (w : int ty) f = pick w 5 f
