(* Modelling OCaml exceptions with [option].

   The compiler's code raises exceptions (e.g. [Fourier_motzkin.Overflow])
   where an operation cannot produce a result. The models return [None]
   instead, and [let* x := m in k] runs [k] on the result of [m] unless [m]
   returned [None], in which case the whole computation returns [None]: the
   same propagation an uncaught exception has. A [match ... with exception]
   in the OCaml corresponds to a [match ... with Some / None] in the model. *)

Notation "'let*' x ':=' m 'in' k" :=
  (match m with Some x => k | None => None end)
  (at level 10, x name, m at level 100, k at level 200).

(* The same with a pattern, as in [let* '(a, b) := m in k]. *)
Notation "'let*' ' p ':=' m 'in' k" :=
  (match m with Some p => k | None => None end)
  (at level 10, p pattern, m at level 100, k at level 200).

(* [Option.is_some]. *)
Definition is_some {A} (o : option A) : bool :=
  match o with Some _ => true | None => false end.
