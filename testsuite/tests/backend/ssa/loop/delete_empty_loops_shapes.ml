(* TEST
 flags = "-O3 -use-ssa -ssa-delete-empty-loops";
 native;
*)

(* Loop shapes around empty-loop deletion: nested loops, several back edges, a
   self tail call as the back edge, a variable step, counters that outlive the
   loop, a non-integer counter. Deleting a loop never changes what a program
   does, so a loop that is deleted leaves nothing to observe; each function
   below checks whatever its loops do determine, and the rest exercises the
   analysis on shapes it must at least not mishandle.

   Each comment says whether the pass deletes the loop and, when it does not,
   why: the loop is not empty, or its shape is one the analysis does not
   recognise, marked as a known limitation. Compiling this file with [-dssa]
   prints "SSA after Delete_empty_loops (N deleted)" for every function in
   which a loop was deleted, which is how to check these notes. *)

(* Inner and outer loop both empty. Only the inner loop is deleted. Known
   limitation: the analysis takes the terminator of the loop's header for its
   exit branch, so it only recognises loops tested at the header: [while] loops,
   and [for] loops whose body is a single block. The outer loop's header is the
   block holding the inner loop's entry guard, and its exit test is in the block
   after the inner loop; deleting the inner loop leaves that shape as it is. *)
let[@inline never] nested_spin (n : int) (m : int) =
  for _i = 0 to n - 1 do
    for _j = 0 to m - 1 do
      ()
    done
  done

(* The inner loop is empty and is deleted; the outer counts its rounds, which
   are returned, so its counter is not dead and it is kept: [n]. *)
let[@inline never] nested_outer_effect (n : int) (m : int) =
  let count = ref 0 in
  for _i = 0 to n - 1 do
    for _j = 0 to m - 1 do
      ()
    done;
    incr count
  done;
  !count

(* The inner loop counts: [n * m]. Neither loop is deleted: both carry the
   count, which is returned. *)
let[@inline never] nested_inner_effect (n : int) (m : int) =
  let count = ref 0 in
  for _i = 0 to n - 1 do
    for _j = 0 to m - 1 do
      incr count
    done
  done;
  !count

(* Two back edges updating the counter by the same step: one induction
   variable with two update expressions. Deleted. *)
let[@inline never] two_back_edges_same (n : int) (p : bool) =
  let m = n lsr 3 in
  let rec loop i =
    if i < m then if p then loop (i + 1) else loop (1 + i) else ()
  in
  loop 0

(* Two back edges with different steps: not a single induction variable, so the
   loop is kept. The counter is also returned: [m] when stepping by one, the
   first even number not below [m] when stepping by two. *)
let[@inline never] two_back_edges_diff (n : int) (p : bool) =
  let m = n lsr 3 in
  let rec loop i =
    if i < m then if p then loop (i + 1) else loop (i + 2) else i
  in
  loop 0

(* The back edge is a self tail call ([@loop never] keeps Flambda 2 from
   turning it into a local loop), so the loop's header is the function's entry
   block, which thereby has a predecessor. With a constant bound the loop is
   empty, and is deleted. *)
let[@inline never] [@loop never] rec self_spin (i : int) =
  if i < 1000 then self_spin (i + 1) else 42

(* The same with the bound passed along unchanged. Kept. Known limitation:
   every parameter of the loop header must be an induction variable, and a
   parameter passed back unchanged (a step of zero) is not recognised as
   one. *)
let[@inline never] [@loop never] rec self_spin_bound (i : int) (n : int) =
  if i < n then self_spin_bound (i + 1) n else ()

(* A variable step. Kept: the step is not a constant, so no termination
   argument is attempted (it would need the sign of [s]); the counter is also
   returned: 0, 3, 6 for [m = 5]. *)
let[@inline never] var_step (n : int) (s : int) =
  let m = n lsr 3 in
  let rec loop i = if i < m then loop (i + s) else i in
  loop 0

(* The counter outlives the loop, so it is not dead and the loop is kept:
   [m]. *)
let[@inline never] counter_after (n : int) =
  let m = n lsr 3 in
  let i = ref 0 in
  while !i < m do
    incr i
  done;
  !i

(* An accumulator alongside the counter: the sum of [0 .. m - 1]. Kept: the
   accumulator is returned, and its step, the counter, is not loop-invariant,
   so it is not an induction variable either. *)
let[@inline never] sum_to (n : int) =
  let m = n lsr 3 in
  let rec loop i acc = if i < m then loop (i + 1) (acc + i) else acc in
  loop 0 0

(* Counting down to a constant. Deleted. *)
let[@inline never] countdown (n : int) =
  let rec loop i = if i > 0 then loop (i - 1) else () in
  loop (n lsr 3)

(* An inequality as the exit test; the counter meets the bound exactly. Kept.
   Known limitation: continuing while the counter differs from the bound is
   never shown to stop, as that needs the counter not to step over the bound
   (here: a step of one from a start not above it). *)
let[@inline never] ne_exit (n : int) =
  let m = n lsr 3 in
  let rec loop i = if i <> m then loop (i + 1) else () in
  loop 0

(* A floating-point counter. Kept: only integer induction variables are
   recognised. *)
let[@inline never] float_spin (n : int) =
  let f = ref 0.0 in
  let m = float_of_int (n lsr 3) in
  while !f < m do
    f := !f +. 1.0
  done

let () =
  nested_spin 10 10;
  Printf.printf "nested_outer_effect=%d\n" (nested_outer_effect 10 7);
  Printf.printf "nested_inner_effect=%d\n" (nested_inner_effect 10 7);
  two_back_edges_same 40 true;
  two_back_edges_same 40 false;
  Printf.printf "two_back_edges_diff=%d,%d\n" (two_back_edges_diff 40 true)
    (two_back_edges_diff 40 false);
  Printf.printf "self_spin=%d\n" (self_spin 0);
  self_spin_bound 0 12;
  Printf.printf "var_step=%d\n" (var_step 40 3);
  Printf.printf "counter_after=%d\n" (counter_after 40);
  Printf.printf "sum_to=%d\n" (sum_to 40);
  countdown 40;
  ne_exit 40;
  float_spin 40;
  print_endline "done"
