(* TEST
 flambda2;
 setup-ocamlopt.opt-build-env;
 flags = "-O3 -flambda2-join-algorithm=n-way -flambda2-expert-shorten-symbol-names";
 ocamlopt_opt_exit_status = "2";
 ocamlopt.opt;
 check-ocamlopt.opt-output;
*)

(* As [n_way_join_function_types.ml]: the last call in [top] may reach [heavy],
   which allocates, so the zero_alloc check must refuse [top]. *)

let sink : int list ref = ref []

let[@inline never] heavy (x : int) (v : int) : int =
  sink := x :: !sink;
  x + v

let[@inline] mk_f (flag : bool) (v : int) = exclave_
  stack_ (fun (mode : bool) (x : int) ->
    if mode then x + v else if flag then heavy x v else x + v)

let[@inline] mk_g (local_ y : bool -> int -> int) = exclave_
  stack_ (fun (local_ z : bool -> int -> int) (c : bool) (x : int) ->
    let r = y true x in
    let w = if c then y else z in
    let res = w false r in
    res)

let[@inline] build (flag : bool) (v : int) = exclave_
  let y = mk_f flag v in
  mk_g y

type 'a box = { b : 'a }

let[@zero_alloc] [@inline never] top (c1 : bool) (c2 : bool) (fa : bool)
    (fb : bool) (n : int) : int =
  let p =
    if c1
    then stack_ { b = stack_ { b = stack_ { b = stack_ { b = build fa n } } } }
    else
      stack_
        { b = stack_ { b = stack_ { b = stack_ { b = build fb (n + 1) } } } }
  in
  let g = p.b.b.b.b in
  let z = mk_f false 7 in
  let res = g z c2 n in
  res
