open Datatypes
open FlambdaEnvAliases
open FlambdaModel
open FlambdaTypeGrammar
open List

(** val free_variables_of_aliases_of_canonical_element :
    Aliases.Aliases_of_canonical_element.t -> variable list **)

let free_variables_of_aliases_of_canonical_element aliases =
  flat_map (fun binding -> free_variables_of_name (fst binding)) aliases

(** val aliases_free_variables : Aliases.t -> variable list **)

let aliases_free_variables t0 =
  app
    (flat_map
       (fun binding ->
         app
           (free_variables_of_name (fst binding))
           (free_variables_of_simple (snd binding)))
       t0.Aliases.canonical_elements)
    (app
       (flat_map
          (fun binding ->
            app
              (free_variables_of_name (fst binding))
              (free_variables_of_aliases_of_canonical_element (snd binding)))
          t0.Aliases.aliases_of_canonical_names)
       (flat_map
          (fun binding ->
            free_variables_of_aliases_of_canonical_element (snd binding))
          t0.Aliases.aliases_of_consts))
