(* TEST
 flags = "-O3 -use-ssa -ssa-delete-empty-loops";
 native;
*)

(* Exercises empty-loop deletion. A terminating loop that does no observable
   work may be removed, but a loop whose body has *any* side effect -- even one
   that does not flow through a header parameter -- must be preserved, as must a
   loop whose termination cannot be established. Each comment says whether the
   pass deletes the loop; compiling this file with [-dssa] prints "SSA after
   Delete_empty_loops (N deleted)" for every function in which a loop was
   deleted. See delete_empty_loops_exits.ml for loops with a second way out and
   delete_empty_loops_shapes.ml for other shapes and the analysis's known
   limitations.

   For the loops the pass deletes, [check_deleted] below makes the deletion
   observable: it runs the loop with a trip count of 2^36, which takes well
   over ten seconds of processor time if the loop is still there and none if
   it is not, and reports which. The unit test oxcaml/tests/backend/ssa/
   loop_analysis.ml asserts exact deletion counts on hand-built graphs; this
   checks that the graphs the compiler builds for OCaml loops are among the
   shapes it recognises. *)

(* [check_deleted name f] reports whether the loop [f] runs was deleted, by
   the processor time [f] takes; see above. *)
let check_deleted name f =
  let start = Sys.time () in
  f ();
  let elapsed = Sys.time () -. start in
  Printf.printf "%s: %s\n" name (if elapsed < 2.0 then "deleted" else "kept")

let huge = 1 lsl 36

(* Genuinely empty: spins a dead counter, no observable effect. Safe to delete;
   observably a no-op either way. *)
let[@inline never] spin (n : int) =
  for _i = 0 to Sys.opaque_identity n - 1 do
    ()
  done

(* Both bounds variable: the termination proof must discharge the no-overflow
   obligation from the untagging shape of the bound (and the [a <= b] entry
   guard is among the facts). Deleted; observably a no-op either way. *)
let[@inline never] spin_range (a : int) (b : int) =
  for _i = Sys.opaque_identity a to Sys.opaque_identity b do
    ()
  done

(* Counting down with a variable bound. Kept. Known limitation: the
   termination check needs the bound register to be at least [- max_int], but
   the untagging shift bounds it below only by [min_int], and that fact cannot
   even be written with the analysis's [int] coefficients (see
   [LoopTermination.bound_in_range]). The symmetric [to] loop above is deleted
   because the upper bound of the shift, [max_int], is representable. *)
let[@inline never] spin_downto (a : int) (b : int) =
  for _i = Sys.opaque_identity a downto Sys.opaque_identity b do
    ()
  done

(* Side effect (print) not flowing through a header parameter: must NOT be
   deleted, so all [n] characters are printed. *)
let[@inline never] noisy (n : int) =
  for _i = 0 to n - 1 do
    print_char 'x'
  done

(* Side effect (store) not flowing through a header parameter: must NOT be
   deleted, so the store happens [n] times. *)
let[@inline never] store_loop (a : int array) (n : int) =
  for _i = 0 to n - 1 do
    a.(0) <- a.(0) + 1
  done

(* Two induction variables compared against each other: the comparison operand
   is loop-variant, so termination is genuinely unknown and the loop (which here
   does terminate because [j] outruns [i]) must run to completion rather than be
   deleted. *)
let[@inline never] two_counter (n : int) =
  let i = ref 0 and j = ref (Sys.opaque_identity n) and hits = ref 0 in
  while !i < !j do
    incr hits;
    i := !i + 2;
    j := !j + 1
  done;
  !hits

(* The exit comparison is also the loop's result. The loop must NOT be
   deleted: the header would then compute the comparison with the initial
   counter rather than with the one that ended the loop, and [0 < m] would be
   returned in place of [false]. The bound [n lsr 3] is what lets the
   termination analysis accept the loop in the first place (the logical shift
   bounds the register, so the tagged counter provably never wraps). *)
let[@inline never] exit_cond_returned (n : int) =
  let m = n lsr 3 in
  let rec loop i =
    let b = i < m in
    if b then loop (i + 1) else b
  in
  loop 0

(* The same through a mutable variable. *)
let[@inline never] exit_cond_via_ref (n : int) =
  let m = n lsr 3 in
  let i = ref 0 in
  let b = ref true in
  while
    b := !i < m;
    !b
  do
    incr i
  done;
  !b

(* The same with the comparison consumed by an instruction after the loop
   rather than returned directly. *)
let[@inline never] exit_cond_as_int (n : int) =
  let m = n lsr 3 in
  let rec loop i =
    let b = i < m in
    if b then loop (i + 1) else Sys.opaque_identity (Bool.to_int b)
  in
  loop 0

(* A loop inside a [try]: the handler is set up by a trap marker before the
   loop and popped after it, and the call may raise into it. The loop itself
   is as empty as [spin], and is deleted; the trap markers and the exception
   edge are outside it. *)
let[@inline never] spin_in_try (f : int -> int) (n : int) =
  try
    let k = f n in
    for _i = 0 to Sys.opaque_identity k - 1 do
      ()
    done;
    k
  with Exit -> -1

(* The header computes a value from outside the loop and the exit returns it.
   The value is the same on every visit of the header, so the loop is deleted
   and the value the retained header computes is the one returned. *)
let[@inline never] header_value (n : int) (x : int) =
  let m = n lsr 3 in
  let rec loop i =
    let t = x + 1 in
    if i < m then loop (i + 1) else t
  in
  loop 0

(* Continuing while the counter equals the bound: any non-zero step leaves
   the bound. Deleted (not checked by time: the loop runs at most twice). *)
let[@inline never] spin_while_equal (n : int) =
  let m = n lsr 3 in
  let rec loop i = if i = m then loop (i + 1) else () in
  loop 0

let () =
  spin 1000;
  check_deleted "spin" (fun () -> spin huge);
  spin_range 1 1000;
  check_deleted "spin_range" (fun () -> spin_range 0 huge);
  spin_downto 1000 1;
  Printf.printf "spin_in_try=%d,%d\n"
    (spin_in_try (fun k -> k) 1000)
    (spin_in_try (fun _ -> raise Exit) 1000);
  check_deleted "spin_in_try" (fun () -> ignore (spin_in_try (fun k -> k) huge));
  Printf.printf "header_value=%d,%d\n" (header_value 800 5) (header_value 0 5);
  check_deleted "header_value" (fun () -> ignore (header_value (huge lsl 3) 5));
  spin_while_equal 8;
  noisy 5;
  print_newline ();
  let a = [| 0 |] in
  store_loop a 100;
  Printf.printf "store=%d\n" a.(0);
  (* i: 0,2,4,...  j: n,n+1,...  gap n closes at rate 1 per step -> n steps *)
  Printf.printf "two_counter=%d\n" (two_counter 10);
  Printf.printf "exit_cond_returned=%b\n" (exit_cond_returned 40);
  Printf.printf "exit_cond_via_ref=%b\n" (exit_cond_via_ref 40);
  Printf.printf "exit_cond_as_int=%d\n" (exit_cond_as_int 40)
