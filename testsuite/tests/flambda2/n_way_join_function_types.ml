(* TEST
 flambda2;
 ocamlopt_flags += " -O3 -flambda2-join-algorithm=n-way";
 native;
*)

(* The n-way join must not keep, for a function slot, a function type that only
   some of the joined closure types have.  Here [w] is the join of [y], a
   closure about whose code nothing is known (only a value slot was projected
   from it), with [z], a closure made locally whose code is known; the call of
   [w] must not be taken to reach only the code of [z]. *)

let sink : int list ref = ref []

let[@inline never] heavy (x : int) (v : int) : int =
  sink := x :: !sink;
  x + v

(* The function slot "F": every closure made by [mk_f] is at this slot. *)
let[@inline] mk_f (flag : bool) (v : int) =
  fun (mode : bool) (x : int) ->
    if mode then x + v else if flag then heavy x v else x + v

(* The function slot "G".  Its closure holds [y], a closure at F. *)
let[@inline] mk_g (y : bool -> int -> int) =
  fun (z : bool -> int -> int) (c : bool) (x : int) ->
    (* inlined when [y] is known: leaves a projection of [v] from [y] *)
    let r = y true x in
    (* a join of [y] with [z]; [z] is not known here *)
    let w = if c then y else z in
    (* a call of unknown arity *)
    w false r

let[@inline] build (flag : bool) (v : int) =
  let y = mk_f flag v in
  mk_g y

type 'a box = { b : 'a }

let top (c1 : bool) (c2 : bool) (fa : bool) (fb : bool) (n : int) : int =
  (* Two closures at G with the same code; four boxes put the type of their
     [y] beyond the depth at which the join stops (5 by default). *)
  let p =
    if c1
    then { b = { b = { b = { b = build fa n } } } }
    else { b = { b = { b = { b = build fb (n + 1) } } } }
  in
  let g = p.b.b.b.b in
  (* A closure at F made here: its type is exact and names its own code. *)
  let z = mk_f false 7 in
  g z c2 n

let () = Printf.printf "%d\n" (top true true true false 5)
