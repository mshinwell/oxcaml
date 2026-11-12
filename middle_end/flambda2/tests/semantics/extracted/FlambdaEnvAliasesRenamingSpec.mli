open Datatypes
open FlambdaEnvAliases
open FlambdaModel
open FlambdaTypeGrammar
open List

val free_variables_of_aliases_of_canonical_element :
  Aliases.Aliases_of_canonical_element.t -> variable list

val aliases_free_variables : Aliases.t -> variable list
