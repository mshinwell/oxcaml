(* Optional arguments before and between the positional ones: a full
   application, a partial one that fixes the first positional argument (and with
   it the optional argument before it), and the rest given later with and
   without the second optional argument. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

let[@inline never] place ?(a = 1) x ?(b = 2) y =
  (a * 1000) + (x * 100) + (b * 10) + y

let all_omitted = place 3 4

let first_given = place ~a:5 3 4

let second_given = place 3 ~b:6 4

let second_given_early = place ~b:6 3 4

let both_given = place ~b:8 ~a:7 3 4

let after_first = place 9

let rest_plain = after_first 4

let rest_with_second = after_first ~b:5 4

let after_first_with_a = place ~a:2 9

let rest_of_that = after_first_with_a ~b:0 1
