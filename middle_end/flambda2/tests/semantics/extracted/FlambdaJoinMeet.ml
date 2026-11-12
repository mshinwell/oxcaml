open Datatypes
open FlambdaExpandHead
open FlambdaJoinEnv
open FlambdaJoinEnvSpec
open FlambdaJoinSpec
open FlambdaJoinTypes
open FlambdaJoinTypesWithEnvSpec
open FlambdaMeet
open FlambdaMeetEnv
open FlambdaMeetSpec
open FlambdaNameAbstractionSpec
open FlambdaTypeEqualSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv

(** val meet_env_functions : (Meet_env.t, meet_expanded_head)
    Join_env.meet_env_functions **)

let meet_env_functions =
  { Join_env.create_meet_env = Meet_env.create;
    Join_env.current_typing_env = Meet_env.current_typing_env;
    Join_env.add_variable_definition = Meet_env.add_variable_definition;
    Join_env.add_env_extension = Meet_env.add_env_extension;
    Join_env.make_bottom = Meet_env.make_bottom;
    Join_env.final_typing_env = Meet_env.final_typing_env;
    Join_env.names_to_avoid = (fun t0 -> t0.Meet_env.names_to_avoid);
    Join_env.with_names_to_avoid = Meet_env.with_names_to_avoid
  }

(** val join_parameters : nat -> Join_env.parameters **)

let join_parameters join_depth0 =
  { Join_env.fresh = fresh_name;
    Join_env.type_eqb;
    Join_env.env_extension_eqb;
    Join_env.expand_const =
      (fun c ->
        FlambdaExpandHead.Expanded_type.to_type
          (FlambdaExpandHead.Expanded_type.create_const c));
    Join_env.join_depth = join_depth0
  }

(** val join_expanded : FlambdaExpandHead.Expanded_type.t -> Expanded_type.t **)

let join_expanded expanded =
  { Expanded_type.kind = expanded.FlambdaExpandHead.Expanded_type.kind;
    Expanded_type.descr = expanded.FlambdaExpandHead.Expanded_type.descr
  }

(** val expand_head_for_join : Typing_env.t -> flambda_type -> Expanded_type.t
    option **)

let expand_head_for_join tenv ty =
  option_map join_expanded (expand_head tenv ty)

type fuels =
  { fuel_of_env : nat;
    fuel_of_types : nat;
    fuel_of_meet : nat
  }

(** val model_join_of_types : nat -> fuels -> Join_env.n_way_join_type **)

let model_join_of_types join_depth0 fuel =
  n_way_join_of_types
    (join_parameters join_depth0)
    fuel.fuel_of_env expand_head_for_join reduce_head_of_kind_naked_immediate
    fuel.fuel_of_types

(** val model_join_scoped_envs : Join_env.choices -> nat -> fuels ->
    join_scoped_envs **)

let model_join_scoped_envs join_choices join_depth0 fuel meet_head cut_after
    menv tenv envs =
  Join_env.cut_and_n_way_join meet_env_functions
    (join_parameters join_depth0)
    fuel.fuel_of_env join_choices
    (model_join_of_types join_depth0 fuel)
    meet_head cut_after menv tenv envs

(** val model_meet_expanded_head : Join_env.choices -> meet_choices -> nat ->
    fuels -> meet_expanded_head **)

let model_meet_expanded_head join_choices meet_choices0 join_depth0 fuel =
  Meet.meet_expanded_head
    (model_join_scoped_envs join_choices join_depth0 fuel)
    meet_choices0 fuel.fuel_of_meet

(** val model_meet : Join_env.choices -> meet_choices -> nat -> fuels ->
    meet_function **)

let model_meet join_choices meet_choices0 join_depth0 fuel =
  Meet.meet
    (model_join_scoped_envs join_choices join_depth0 fuel)
    meet_choices0 fuel.fuel_of_meet

(** val model_add_equation : Join_env.choices -> meet_choices -> nat -> fuels ->
    add_equation_function **)

let model_add_equation join_choices meet_choices0 join_depth0 fuel =
  Flambda2_types.add_equation
    (model_join_scoped_envs join_choices join_depth0 fuel)
    meet_choices0 fuel.fuel_of_meet

(** val model_join : Join_env.choices -> meet_choices -> nat -> fuels -> 'a1
    join_of_environments **)

let model_join join_choices meet_choices0 join_depth0 fuel =
  join_with join_choices meet_env_functions
    (join_parameters join_depth0)
    fuel.fuel_of_env
    (model_join_of_types join_depth0 fuel)
    (model_meet_expanded_head join_choices meet_choices0 join_depth0 fuel)
