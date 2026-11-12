open FlambdaEnvAliases
open FlambdaModel

(** val canonical_element_of : Aliases.t -> simple -> simple **)

let canonical_element_of t0 e =
  match Aliases.canonical t0 e with
  | Aliases.Is_canonical -> e
  | Aliases.Alias_of_canonical canonical_element -> canonical_element
