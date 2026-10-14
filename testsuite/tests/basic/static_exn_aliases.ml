(* TEST *)

(* Pattern matches whose compilation involves static exception handlers that
   are themselves static raises, possibly with arguments. Flambda 2 does not
   compile such handlers to continuations; instead each static raise to them
   is replaced by the handler. *)

type t = A of int | B of int * int | C | D of string

let[@inline never] f1 x y =
  match x, y with
  | A n, A m when n = m -> 1
  | A _, _ | _, A _ -> 2
  | B (n, _), B (m, _) when n = m -> 3
  | _, _ -> 4

(* Handler with a parameter *)
let[@inline never] f2 x =
  match x with
  | A n when n > 0 -> n
  | A n | B (n, _) when n < 0 -> -n
  | A _ | B _ -> 0
  | C -> 1
  | D s -> String.length s

(* Mutable variable live across the static raises *)
let[@inline never] f3 r x y =
  let count = ref 0 in
  (match x, y with
   | A n, A m when (incr count; n = m) -> r := 1
   | A _, _ | _, A _ -> r := 2
   | _ -> r := 3);
  !count

(* Static raises inside a try-with *)
let[@inline never] f4 x y =
  try
    match x, y with
    | A n, A m when n = m -> 1
    | A _, _ | _, A _ -> raise Exit
    | _ -> 4
  with Exit -> 5

let[@inline never] f5 (x : int) (y : int) =
  match x, y with
  | 0, _ | _, 0 -> "zero"
  | 1, 1 -> "ones"
  | n, m when n = m -> "same"
  | _ -> "other"

(* Boolean-valued matches whose arms are static raises to constant handlers *)
let[@inline never] is_ab = function A _ | B _ -> true | C | D _ -> false

let[@inline never] is_not_c x = match x with C -> false | _ -> true

let[@inline never] both_small x y =
  match x, y with
  | A n, A m -> n < 10 && m < 10
  | _ -> false

let values = [A 1; A 2; A (-3); B (1, 2); B (-2, 5); C; D "abc"]

let () =
  List.iter
    (fun x ->
      List.iter
        (fun y ->
          let r = ref 0 in
          let c = f3 r x y in
          Printf.printf "%d %d %d %d %d %d %d\n" (f1 x y) (f2 x) (f2 y) c !r
            (f4 x y)
            (Bool.to_int (both_small x y)))
        values)
    values;
  List.iter (fun x -> Printf.printf "%b %b\n" (is_ab x) (is_not_c x)) values;
  List.iter
    (fun (x, y) -> print_endline (f5 x y))
    [0, 5; 5, 0; 1, 1; 2, 2; 2, 3]
