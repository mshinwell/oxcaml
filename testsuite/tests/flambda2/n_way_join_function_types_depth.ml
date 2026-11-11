(* TEST
 flambda2;
 ocamlopt_flags += " -O3 -flambda2-join-algorithm=n-way -flambda2-join-depth 1";
 native;
*)

(* As [n_way_join_function_types.ml], with the join depth lowered in place of
   the nested records. *)

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

let top (c1 : bool) (c2 : bool) (fa : bool) (fb : bool) (n : int) : int =
  let g = if c1 then build fa n else build fb (n + 1) in
  (* A closure at F made here: its type is exact and names its own code. *)
  let z = mk_f false 7 in
  g z c2 n

let () = Printf.printf "%d\n" (top true true true false 5)
