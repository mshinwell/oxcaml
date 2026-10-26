(* TEST
 flags = "-O3 -use-ssa -ssa-delete-empty-loops";
 native;
*)

(* Exercises empty-loop deletion. A terminating loop that does no observable
   work may be removed, but a loop whose body has *any* side effect -- even one
   that does not flow through a header parameter -- must be preserved, as must a
   loop whose termination cannot be established. *)

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

(* Counting down with a variable bound: the increment could wrap below
   [min_int] at the machine level for an arbitrary 64-bit bound register, so
   termination is not established and the loop is kept. *)
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

let () =
  spin 1000;
  spin_range 1 1000;
  spin_downto 1000 1;
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
