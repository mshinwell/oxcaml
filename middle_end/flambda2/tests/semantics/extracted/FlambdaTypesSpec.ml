open BinPos
open FlambdaModel

type flambda_type =
  | Unknown
  | Bottom
  | Equals of simple

type typing_env = (variable * flambda_type) list

(** val find_alias : typing_env -> variable -> simple option **)

let rec find_alias tenv x =
  match tenv with
  | [] -> None
  | p :: tenv0 -> (
    let y, f = p in
    match f with
    | Equals s -> if Pos.eqb x y then Some s else find_alias tenv0 x
    | _ -> find_alias tenv0 x)

(** val canonical_simple : typing_env -> simple -> simple **)

let canonical_simple tenv s =
  match s with
  | Var x -> ( match find_alias tenv x with Some alias -> alias | None -> s)
  | _ -> s
