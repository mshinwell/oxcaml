open BinNums
open BinPos
open Datatypes
open FlambdaEnvAliasesInvariantSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveSpec
open FlambdaSimplifyPassSpec
open FlambdaSimplifyPrimitivesSpec
open FlambdaSimplifyStaticsSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv
open List
open ListDef
open OxCamlOption

(** val alias_keeps_fit : Typing_env.t -> simple -> simple -> flambda_kind ->
    bool **)

let alias_keeps_fit tenv e1 e2 kind0 =
  ((((is_canonical_b (Typing_env.aliases tenv) e1
     && is_canonical_b (Typing_env.aliases tenv) e2)
    && Typing_env.mem_simple None tenv e1)
   && Typing_env.mem_simple None tenv e2)
  && simple_of_kind_b tenv e1 kind0)
  && simple_of_kind_b tenv e2 kind0

(** val equation_keeps_fit : Typing_env.t -> name -> flambda_type -> bool **)

let equation_keeps_fit tenv n ty =
  ((((Typing_env.mem None tenv n
     && forallb
          (fun y -> Typing_env.mem None tenv (Name_var y))
          (free_variables ty))
    &&
    match Keyed.lookup name_eqb n (Typing_env.names_to_types tenv) with
    | Some entry -> kind_eqb (kind ty) (kind (fst entry))
    | None -> true)
   &&
   match get_alias_opt ty with
   | Some _ ->
     negb (is_canonical_b (Typing_env.aliases tenv) (simple_of_name n))
   | None -> true)
  && (negb (is_obviously_unknown ty)
     || negb
          (is_some
             (Keyed.lookup name_eqb n
                (flat_map
                   (fun t0 -> t0.Typing_env_level.equations)
                   (map
                      (fun t0 -> t0.Typing_env.One_level.level)
                      tenv.Typing_env.prev_levels))))))
  && simple_of_kind_b tenv (simple_of_name n) (kind ty)

(** val block_like_bindings_keep_fit : Typing_env.t -> static_binding list ->
    bool **)

let rec block_like_bindings_keep_fit tenv = function
  | [] -> true
  | s0 :: bindings0 -> (
    match s0 with
    | Bind_symbol (s, const) -> (
      if is_closure_const const
      then block_like_bindings_keep_fit tenv bindings0
      else
        match static_const_type_in tenv const with
        | Some ty ->
          equation_keeps_fit
            (Typing_env.add_symbol_definition tenv s)
            (Name_symbol s) ty
          && block_like_bindings_keep_fit
               (define_symbol_with_type tenv s ty)
               bindings0
        | None ->
          block_like_bindings_keep_fit
            (Typing_env.add_symbol_definition tenv s)
            bindings0)
    | _ -> block_like_bindings_keep_fit tenv bindings0)

(** val closure_bindings_keep_fit : Typing_env.t -> Typing_env.t ->
    static_binding list -> bool **)

let rec closure_bindings_keep_fit prior tenv = function
  | [] -> true
  | s0 :: bindings0 -> (
    match s0 with
    | Bind_symbol (s, const) ->
      if is_closure_const const
      then
        match static_const_type_in prior const with
        | Some ty ->
          equation_keeps_fit tenv (Name_symbol s) ty
          && closure_bindings_keep_fit prior
               (Typing_env.replace_equation tenv (Name_symbol s) ty)
               bindings0
        | None -> closure_bindings_keep_fit prior tenv bindings0
      else closure_bindings_keep_fit prior tenv bindings0
    | _ -> closure_bindings_keep_fit prior tenv bindings0)

(** val statics_keep_fit : Typing_env.t -> static_binding list -> bool **)

let statics_keep_fit tenv bindings =
  let defined =
    Typing_env.add_symbol_definitions tenv (closure_symbols_of bindings)
  in
  let prior = add_block_like_bindings defined bindings in
  block_like_bindings_keep_fit defined bindings
  && closure_bindings_keep_fit prior prior bindings

(** val arm_env_keeps_fit : Typing_env.t -> simple -> coq_Z -> bool **)

let arm_env_keeps_fit tenv scrutinee d =
  match simplify_simple tenv scrutinee with
  | Some p -> (
    let _, s = p in
    match s with
    | Var c ->
      if
        simple_in_terms_b tenv (Var c)
        && simple_of_kind_b tenv (Var c) naked_immediate_kind
      then
        match Typing_env.add_alias tenv (Var c) (Const (Naked_immediate d)) with
        | Some o -> (
          match o with
          | Ok _ ->
            alias_keeps_fit tenv (Var c) (Const (Naked_immediate d))
              naked_immediate_kind
          | _ -> true)
        | None -> true
      else true
    | _ -> true)
  | None -> true

(** val leaf_uses_keep_fit : Typing_env.t -> continuation -> expr -> bool **)

let leaf_uses_keep_fit tenv k = function
  | Switch (scrutinee, arms) ->
    forallb
      (fun arm ->
        negb (Pos.eqb (snd arm).ac_continuation k)
        || arm_env_keeps_fit tenv scrutinee (fst arm))
      arms
  | _ -> true
