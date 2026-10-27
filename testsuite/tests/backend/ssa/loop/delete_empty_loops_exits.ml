(* TEST
 flags = "-O3 -use-ssa -ssa-delete-empty-loops";
 native;
*)

(* Loops with more than one way out. Empty-loop deletion replaces the header's
   exit branch by a jump to its target, so a loop may only be deleted when that
   branch is the only edge leaving the loop body: a body that can return another
   value, raise, print or fail a bounds check must be kept, however little else
   it does.

   No loop in this file is deleted. Compiling it with [-dssa] prints "SSA after
   Delete_empty_loops (N deleted)" for every function in which a loop was
   deleted, and so prints no such line here. Each comment says which check of
   the analysis keeps the loop. *)

(* [p] is loop-invariant, but when it holds the loop returns [1] from inside
   the body rather than [0] from the header's exit. The body is effect-free, the
   counter is dead, the bound is in range and the exit target takes no
   arguments, so everything else about the loop would allow deletion; only the
   extra exit edge, from the body's test of [p] to the block returning [1],
   keeps it. Without that check [early_exit _ true] would return [0]. *)
let[@inline never] early_exit (n : int) (p : bool) =
  let m = n lsr 3 in
  let rec loop i = if i < m then if p then 1 else loop (i + 1) else 0 in
  loop 0

(* The same, leaving the body with an exception: the extra exit edge leads to
   the raise. *)
exception Early

let[@inline never] raise_exit (n : int) (p : bool) =
  let m = n lsr 3 in
  let rec loop i = if i < m then if p then raise Early else loop (i + 1) in
  loop 0

(* The same, leaving the body for a side effect that the header's exit does not
   perform: the extra exit edge leads to the call. The body itself is
   effect-free, so only that edge keeps the loop. *)
let[@inline never] early_exit_effect (n : int) (p : bool) =
  let m = n lsr 3 in
  let rec loop i =
    if i < m then if p then print_string "early" else loop (i + 1)
  in
  loop 0

(* A bounds check in a [for] loop. The loop body has two blocks: the header
   holds the check, and the block after it holds the counter's exit test. The
   analysis takes the header's branch for the loop's exit branch, so it sees the
   branch to the raise, whose condition does not involve the counter, and
   establishes no termination; the real exit test, in the second block, is a
   further edge out of the loop. The loop is kept so that the exception is
   raised. *)
let[@inline never] bounds_check (a : int array) (n : int) (k : int) =
  for _i = 0 to n - 1 do
    ignore a.(k)
  done

(* A second exit that returns the same value as the header's. The two returns
   are distinct blocks in the SSA graph, so this is a second exit like the
   others and the loop is kept. Known limitation: a second exit is rejected even
   when it leads to the same outcome as the header's exit; only edges to the
   header's exit target itself are allowed. *)
let[@inline never] same_exit (n : int) (p : bool) =
  let m = n lsr 3 in
  let rec loop i = if i < m then if p then 0 else loop (i + 1) else 0 in
  loop 0

let () =
  Printf.printf "early_exit=%d,%d\n" (early_exit 40 true) (early_exit 40 false);
  Printf.printf "raise_exit=%s\n"
    (match raise_exit 40 true with
    | () -> "returned"
    | exception Early -> "Early");
  raise_exit 40 false;
  print_string "early_exit_effect(true)=";
  early_exit_effect 40 true;
  print_newline ();
  print_string "early_exit_effect(false)=";
  early_exit_effect 40 false;
  print_newline ();
  Printf.printf "bounds_check=%s\n"
    (match bounds_check [| 1 |] 3 5 with
    | () -> "returned"
    | exception Invalid_argument _ -> "Invalid_argument");
  bounds_check [| 1 |] 3 0;
  Printf.printf "same_exit=%d,%d\n" (same_exit 40 true) (same_exit 40 false)
