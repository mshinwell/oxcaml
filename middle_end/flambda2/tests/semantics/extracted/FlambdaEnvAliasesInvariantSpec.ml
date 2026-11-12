open FlambdaBindingTime
open FlambdaCompareSpec
open FlambdaEnvAliases
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open List

(** val demoted_to_b : Aliases.t -> name -> simple -> bool **)

let demoted_to_b t0 n canonical_element =
  match Keyed.lookup name_eqb n t0.Aliases.canonical_elements with
  | Some canonical_element' -> simple_equal canonical_element' canonical_element
  | None -> false

(** val is_canonical_b : Aliases.t -> simple -> bool **)

let is_canonical_b t0 e =
  match Aliases.canonical t0 e with
  | Aliases.Is_canonical -> true
  | Aliases.Alias_of_canonical _ -> false

(** val canonical_elements_canonical_b : Aliases.t -> bool **)

let canonical_elements_canonical_b t0 =
  Keyed.for_all_bindings_b name_eqb
    (fun _ canonical_element -> is_canonical_b t0 canonical_element)
    t0.Aliases.canonical_elements

(** val listed_aliases_demoted_b : Aliases.t -> simple ->
    Aliases.Aliases_of_canonical_element.t -> bool **)

let listed_aliases_demoted_b t0 canonical_element aliases =
  forallb
    (fun n -> demoted_to_b t0 n canonical_element)
    (Aliases.Aliases_of_canonical_element.all aliases)

(** val aliases_listed_b : Aliases.t -> bool **)

let aliases_listed_b t0 =
  (Keyed.for_all_bindings_b name_eqb
     (fun n canonical_element ->
       Aliases.Aliases_of_canonical_element.mem
         (Aliases.get_aliases_of_canonical_element t0 canonical_element)
         n)
     t0.Aliases.canonical_elements
  && Keyed.for_all_bindings_b name_eqb
       (fun canonical_name aliases ->
         listed_aliases_demoted_b t0 (simple_of_name canonical_name) aliases)
       t0.Aliases.aliases_of_canonical_names)
  && Keyed.for_all_bindings_b const_eqb
       (fun canonical_const aliases ->
         listed_aliases_demoted_b t0 (Const canonical_const) aliases)
       t0.Aliases.aliases_of_consts

(** val aliases_consistent_b : Aliases.t -> bool **)

let aliases_consistent_b t0 =
  canonical_elements_canonical_b t0 && aliases_listed_b t0

(** val name_modes_recorded_of_b : (name, 'a1 * Binding_time.With_name_mode.t)
    Keyed.finite_map -> Aliases.Aliases_of_canonical_element.t -> bool **)

let name_modes_recorded_of_b binding_times_and_modes aliases =
  Keyed.for_all_bindings_b name_eqb
    (fun n name_mode ->
      Name_mode.equal name_mode
        (Aliases.compute_name_mode_unscoped binding_times_and_modes
           (simple_of_name n)))
    aliases

(** val name_modes_recorded_b : (name, 'a1 * Binding_time.With_name_mode.t)
    Keyed.finite_map -> Aliases.t -> bool **)

let name_modes_recorded_b binding_times_and_modes t0 =
  Keyed.for_all_bindings_b name_eqb
    (fun _ aliases -> name_modes_recorded_of_b binding_times_and_modes aliases)
    t0.Aliases.aliases_of_canonical_names
  && Keyed.for_all_bindings_b const_eqb
       (fun _ aliases ->
         name_modes_recorded_of_b binding_times_and_modes aliases)
       t0.Aliases.aliases_of_consts
