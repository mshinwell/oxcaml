[@@@alert "-unsafe_effects"]

type _ Effect.t += Step : int -> int Effect.t

let rec count n acc = if n = 0 then acc else count (n - 1) (Effect.perform (Step acc))

let () =
  let r =
    Effect.Deep.try_with (fun () -> count 1_000_000 0) ()
      { effc =
          (fun (type a) (e : a Effect.t) ->
            match e with
            | Step x -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (x + 1))
            | _ -> None)
      }
  in
  Printf.printf "result %d\n" r
