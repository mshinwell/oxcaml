(* Binds, a sequence, a temporary, a realisation with a label, a custom
   match, an exception, the fuel. *)
let f dacc n k =
  port__bind (Dacc.denv dacc) (fun tmp1 ->
    port__bind
      ((fun x__1 x__2 x__3 -> Dacc.record x__1 x__2 ~env_at_use:x__3) dacc n
         tmp1)
      (fun x ->
        let (dacc0, m) = x in
        port__seq ((fun x__1 -> assert x__1) ((=) n m))
          (port__bind (Dacc.kind dacc0) (fun kd ->
             (fun f__1 f__2 x__0 -> match x__0 with Dacc.A x__1 -> f__1 x__1 | Dacc.B { a = x__1; b = x__2 } -> f__2 x__1 x__2)
               (fun n0 -> k dacc0 n0)
               (fun a _ ->
                 port__match_exn (fun _ -> Dacc.find a dacc0) Not_found
                   (fun _ -> port__ret 0)
                   (fun v -> port__ret ((+) v 1)))
               kd))))

let rec g fuel dacc n =
  (fun f__1 f__2 x__0 -> f__2 x__0)
    (fun _ -> port__out_of_fuel)
    (fun fuel0 ->
      port__bind (f dacc n (fun dacc0 n0 -> g fuel0 dacc0 n0)) (fun x ->
        g fuel0 dacc x))
    fuel

let top dacc = port__bind (port__get_fuel ()) (fun fuel -> g fuel dacc 0)
