(* TEST
 flambda2;
 ocamlopt_flags += " -O3";
 native;
*)

(* [Get_tag] of something known to be a tagged immediate is made [Invalid]
   (see simplify/get_tag_of_immediate.ml).  That must only ever happen in code
   that is never executed.  Here the same inlined functions are run at the
   type [int], where the branch containing the [Get_tag] is ruled out by the
   GADT, and at the type [blocks], where it is taken.  The last part is a
   variant with constant and non-constant constructors: matched where nothing
   is known of it, and matched after a join at which it is unboxed (with -O3),
   where the use that passes the constant constructor passes a dummy tag. *)

type blocks =
  | P of int
  | Q of string
  | R of int * int

type _ ty =
  | Int : int ty
  | Blocks : blocks ty

let[@inline] which (type a) (w : a ty) (x : a) : int =
  match w with
  | Int -> 0
  | Blocks -> ( match x with P _ -> 1 | Q _ -> 2 | R _ -> 3)

let[@inline] pick (type a) (w : a ty) (x : a) (f : int -> int) : int =
  match w with
  | Int -> 0
  | Blocks -> ( match x with P _ -> f 1 | Q _ -> f 2 | R _ -> f 3)

let[@inline never] tag_of_parameter (w : int ty) (n : int) = which w n

let[@inline never] tag_of_constant (w : int ty) = which w 5

let[@inline never] switch_on_tag_of_parameter (w : int ty) (n : int) f =
  pick w n f

let[@inline never] switch_on_tag_of_constant (w : int ty) f = pick w 5 f

let[@inline never] tag_of_block (w : blocks ty) (b : blocks) = which w b

let[@inline never] tag_of_known_block (w : blocks ty) (s : string) =
  which w (Q s)

let[@inline never] switch_on_tag_of_block (w : blocks ty) (b : blocks) f =
  pick w b f

type mixed =
  | A
  | B of int
  | C of string

let[@inline never] mixed_unknown (v : mixed) : int =
  match v with A -> 100 | B m -> m | C s -> String.length s

let[@inline never] mixed_unboxed (c : int) (n : int) (s : string) : int =
  let v = if c = 0 then A else if c = 1 then B n else C s in
  match v with A -> 100 | B m -> m | C s -> String.length s

(* Matched twice after the join. *)
let[@inline never] mixed_unboxed_twice (c : int) (n : int) (s : string) : int =
  let v = if c = 0 then A else if c = 1 then B n else C s in
  let is_c = match v with C _ -> true | A | B _ -> false in
  let r = match v with A -> 100 | B m -> m | C s -> String.length s in
  if is_c then r + 1000 else r

(* The witness is not known where the functions above are compiled. *)
let int_witness : int ty = Sys.opaque_identity Int

let blocks_witness : blocks ty = Sys.opaque_identity Blocks

let () =
  let f n = n * 10 in
  Printf.printf "%d %d %d %d\n"
    (tag_of_parameter int_witness 7)
    (tag_of_constant int_witness)
    (switch_on_tag_of_parameter int_witness 7 f)
    (switch_on_tag_of_constant int_witness f);
  Printf.printf "%d %d %d %d\n"
    (tag_of_block blocks_witness (P 1))
    (tag_of_block blocks_witness (R (1, 2)))
    (tag_of_known_block blocks_witness "s")
    (switch_on_tag_of_block blocks_witness (Q "s") f);
  (* Everything known where it is used. *)
  Printf.printf "%d %d %d\n" (which Int 5) (which Blocks (Q "s"))
    (pick Blocks (R (1, 2)) f);
  Printf.printf "%d %d %d\n" (mixed_unknown A) (mixed_unknown (B 7))
    (mixed_unknown (C "abc"));
  Printf.printf "%d %d %d\n" (mixed_unboxed 0 7 "abc") (mixed_unboxed 1 7 "abc")
    (mixed_unboxed 2 7 "abc");
  Printf.printf "%d %d %d\n"
    (mixed_unboxed_twice 0 7 "abc")
    (mixed_unboxed_twice 1 7 "abc")
    (mixed_unboxed_twice 2 7 "abc")
