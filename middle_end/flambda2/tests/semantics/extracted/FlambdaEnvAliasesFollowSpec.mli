open BinPos
open Datatypes
open FlambdaBindingTime
open FlambdaEnvAliases
open FlambdaEnvAliasesRenamingSpec
open FlambdaEnvAliasesSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaTypeGrammar
open FlambdaValueSpec
open List
open ListDef

module Known : sig
  type closure =
    | Of_code of code_id * (value_slot * simple) list
    | Of_set of
        function_slot
        * (function_slot * code_id) list
        * (value_slot * simple) list

  val closure_value_slots : closure -> (value_slot * simple) list

  val closure_code : closure -> code_id option

  val closure_slot : closure -> function_slot

  type static_closure =
    { as_closure : closure;
      closure_symbols : (function_slot * symbol) list
    }

  val as_closure : static_closure -> closure

  val closure_symbols : static_closure -> (function_slot * symbol) list

  type t =
    { aliases : Aliases.t;
      binding_times :
        (name, unit * Binding_time.With_name_mode.t) Keyed.finite_map;
      next_binding_time : Binding_time.t;
      closures : (variable * closure) list;
      static_closures : (symbol * static_closure) list
    }

  val aliases : t -> Aliases.t

  val binding_times :
    t -> (name, unit * Binding_time.With_name_mode.t) Keyed.finite_map

  val next_binding_time : t -> Binding_time.t

  val closures : t -> (variable * closure) list

  val static_closures : t -> (symbol * static_closure) list

  val empty : t

  val binding_time_resolver : name -> Binding_time.With_name_mode.t

  val canonical_simple : t -> simple -> simple

  val add_equal :
    (name, unit * Binding_time.With_name_mode.t) Keyed.finite_map ->
    Aliases.t ->
    simple ->
    simple ->
    Aliases.t

  val forget_in_aliases :
    (name, unit * Binding_time.With_name_mode.t) Keyed.finite_map ->
    Aliases.t ->
    variable ->
    Aliases.t

  val forget : t -> variable -> t

  val bind : t -> variable -> t

  val bind_all : t -> variable list -> t

  val with_aliases : t -> Aliases.t -> t

  val add_closure : t -> variable -> closure -> t

  val find_closure : t -> simple -> closure option

  val under_let : t -> variable -> named -> t

  val static_closure_of_binding :
    static_binding -> (symbol * static_closure) option

  val under_let_static : t -> static_binding list -> t
end

val canonical_value_slots :
  Known.t -> (value_slot * simple) list -> (value_slot * simple) list

val canonical_project : Known.t -> value_slot -> simple -> named

val canonical_project_from :
  Known.t -> function_slot -> value_slot -> simple -> named

val canonical_project_function_slot :
  Known.t -> function_slot -> function_slot -> simple -> named

val canonical_named : Known.t -> named -> named

val canonical_static_const : Known.t -> static_const -> static_const

val canonical_static_binding : Known.t -> static_binding -> static_binding

val canonical_apply_cont : Known.t -> apply_cont -> apply_cont

val canonical_call_kind : Known.t -> simple -> call_kind -> call_kind

val canonical_apply : Known.t -> apply_expr -> apply_expr

val follow_aliases : Known.t -> expr -> expr

val follow_aliases_in_handler :
  Known.t -> continuation_handler -> continuation_handler
