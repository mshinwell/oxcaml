open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBindingTime
open FlambdaExpandHead
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaMeetEnv
open FlambdaMeetGrammar
open FlambdaModel
open FlambdaTypeEqualSpec
open FlambdaTypeGrammar
open FlambdaTypeMeaningBoolSpec
open FlambdaTypingEnv
open List
open ListDef
open PeanoNat

(** val map_return_value : ('a1 -> 'a2) -> 'a1 meet_return_value -> 'a2
    meet_return_value **)

let map_return_value f = function
  | Left_input -> Left_input
  | Right_input -> Right_input
  | Both_inputs -> Both_inputs
  | New_result x0 -> New_result (f x0)

(** val combine_meet_return_values : 'a1 meet_return_value -> 'a2
    meet_return_value -> (unit -> 'a3) -> 'a3 meet_return_value **)

let combine_meet_return_values a b compute_value =
  match a with
  | Left_input -> (
    match b with
    | Left_input -> Left_input
    | Both_inputs -> Left_input
    | _ -> New_result (compute_value ()))
  | Right_input -> (
    match b with
    | Left_input -> New_result (compute_value ())
    | New_result _ -> New_result (compute_value ())
    | _ -> Right_input)
  | Both_inputs -> (
    match b with
    | Left_input -> Left_input
    | Right_input -> Right_input
    | Both_inputs -> Both_inputs
    | New_result _ -> New_result (compute_value ()))
  | New_result _ -> New_result (compute_value ())

(** val sequence_return_value : 'a1 option meet_return_value -> 'a1
    meet_return_value option **)

let sequence_return_value = function
  | Left_input -> Some Left_input
  | Right_input -> Some Right_input
  | Both_inputs -> Some Both_inputs
  | New_result a -> (
    match a with Some x0 -> Some (New_result x0) | None -> None)

(** val set_meet : ('a1 -> 'a1 -> bool) -> ('a1 list -> 'a2) -> Meet_env.t ->
    'a1 list -> 'a1 list -> 'a2 Meet_result.t **)

let set_meet eqb0 of_set env s1 s2 =
  if Keyed.all_among eqb0 s1 s2
  then
    if Keyed.all_among eqb0 s2 s1
    then Meet_result.Ok (Both_inputs, env)
    else Meet_result.Ok (Left_input, env)
  else if Keyed.all_among eqb0 s2 s1
  then Meet_result.Ok (Right_input, env)
  else
    let s = Keyed.inter eqb0 s1 s2 in
    if Keyed.is_empty s
    then Meet_result.Bottom (New_result ())
    else Meet_result.Ok (New_result (of_set s), env)

type ('k, 'a) mapping_acc =
  { all_left : bool;
    all_right : bool;
    mapping : ('k * 'a) list;
    mapping_env : Meet_env.t
  }

type ('k, 'a) mapping_state = ('k, 'a) mapping_acc Or_bottom.t option

(** val meet_mapping : (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t option) ->
    (('a1 -> 'a2 option -> 'a2 option -> ('a1, 'a2) mapping_state -> ('a1, 'a2)
    mapping_state) -> 'a3 -> 'a3 -> ('a1, 'a2) mapping_state -> ('a1, 'a2)
    mapping_state) -> Meet_env.t -> 'a3 -> 'a3 -> (('a1 * 'a2) list -> 'a3) ->
    'a3 Meet_result.t option **)

let meet_mapping meet_data fold2 env left right rebuild =
  let step =
   fun key data_left_opt data_right_opt state ->
    match state with
    | Some t0 -> (
      match t0 with
      | Or_bottom.Ok acc -> (
        match data_left_opt with
        | Some data_left -> (
          match data_right_opt with
          | Some data_right -> (
            match meet_data acc.mapping_env data_left data_right with
            | Some t1 -> (
              match t1 with
              | Meet_result.Bottom _ -> Some Or_bottom.Bottom
              | Meet_result.Ok (res, env0) -> (
                let result =
                 fun all_left0 all_right0 data ->
                  Some
                    (Or_bottom.Ok
                       { all_left = all_left0;
                         all_right = all_right0;
                         mapping = (key, data) :: acc.mapping;
                         mapping_env = env0
                       })
                in
                match res with
                | Left_input -> result acc.all_left false data_left
                | Right_input -> result false acc.all_right data_right
                | Both_inputs -> result acc.all_left acc.all_right data_left
                | New_result data -> result false false data))
            | None -> None)
          | None ->
            Some
              (Or_bottom.Ok
                 { all_left = acc.all_left;
                   all_right = false;
                   mapping = (key, data_left) :: acc.mapping;
                   mapping_env = acc.mapping_env
                 }))
        | None -> (
          match data_right_opt with
          | Some data_right ->
            Some
              (Or_bottom.Ok
                 { all_left = false;
                   all_right = acc.all_right;
                   mapping = (key, data_right) :: acc.mapping;
                   mapping_env = acc.mapping_env
                 })
          | None -> None))
      | Or_bottom.Bottom -> Some Or_bottom.Bottom)
    | None -> None
  in
  match
    fold2 step left right
      (Some
         (Or_bottom.Ok
            { all_left = true;
              all_right = true;
              mapping = [];
              mapping_env = env
            }))
  with
  | Some t0 -> (
    match t0 with
    | Or_bottom.Ok res ->
      let result =
        if res.all_left
        then if res.all_right then Both_inputs else Left_input
        else if res.all_right
        then Right_input
        else New_result (rebuild res.mapping)
      in
      Some (Meet_result.Ok (result, res.mapping_env))
    | Or_bottom.Bottom -> Some (Meet_result.Bottom (New_result ())))
  | None -> None

(** val map_meet : ('a1 -> 'a1 -> bool) -> (Meet_env.t -> 'a2 -> 'a2 -> 'a2
    Meet_result.t option) -> Meet_env.t -> ('a1, 'a2) Keyed.finite_map -> ('a1,
    'a2) Keyed.finite_map -> ('a1, 'a2) Keyed.finite_map Meet_result.t option **)

let map_meet eqb0 meet_data env left right =
  let fold2 =
   fun f m1 m2 init ->
    Keyed.fold2_on eqb0 (Keyed.keys_of_both eqb0 m1 m2) f m1 m2 init
  in
  let rebuild = fun l -> fold_left (fun m binding -> binding :: m) l [] in
  meet_mapping meet_data fold2 env left right rebuild

(** val combine_results2 : Meet_env.t -> (Meet_env.t -> 'a1 -> 'a1 -> 'a1
    Meet_result.t option) -> (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t
    option) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> ('a1 -> 'a2 -> 'a3) -> 'a3
    Meet_result.t option **)

let combine_results2 env meet_a meet_b left_a right_a left_b right_b rebuild =
  match meet_a env left_a right_a with
  | Some result_a -> (
    match result_a with
    | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
    | Meet_result.Ok (result_a0, env0) -> (
      match meet_b env0 left_b right_b with
      | Some result_b -> (
        match result_b with
        | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
        | Meet_result.Ok (result_b0, env1) ->
          let return_value =
            combine_meet_return_values result_a0 result_b0 (fun _ ->
                rebuild
                  (extract_value result_a0 left_a right_a)
                  (extract_value result_b0 left_b right_b))
          in
          Some (Meet_result.Ok (return_value, env1)))
      | None -> None))
  | None -> None

(** val combine_results3 : Meet_env.t -> (Meet_env.t -> 'a1 -> 'a1 -> 'a1
    Meet_result.t option) -> (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t
    option) -> (Meet_env.t -> 'a3 -> 'a3 -> 'a3 Meet_result.t option) -> 'a1 ->
    'a1 -> 'a2 -> 'a2 -> 'a3 -> 'a3 -> ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a4
    Meet_result.t option **)

let combine_results3 env meet_a meet_b meet_c left_a right_a left_b right_b
    left_c right_c rebuild =
  match meet_a env left_a right_a with
  | Some result_a -> (
    match result_a with
    | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
    | Meet_result.Ok (result_a0, env0) -> (
      match meet_b env0 left_b right_b with
      | Some result_b -> (
        match result_b with
        | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
        | Meet_result.Ok (result_b0, env1) -> (
          match meet_c env1 left_c right_c with
          | Some result_c -> (
            match result_c with
            | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
            | Meet_result.Ok (result_c0, env2) ->
              let result_bc =
                combine_meet_return_values result_b0 result_c0 (fun _ ->
                    ( extract_value result_b0 left_b right_b,
                      extract_value result_c0 left_c right_c ))
              in
              let return_value =
                combine_meet_return_values result_a0 result_bc (fun _ ->
                    let bc =
                      extract_value result_bc (left_b, left_c) (right_b, right_c)
                    in
                    rebuild
                      (extract_value result_a0 left_a right_a)
                      (fst bc) (snd bc))
              in
              Some (Meet_result.Ok (return_value, env2)))
          | None -> None))
      | None -> None))
  | None -> None

(** val meet_code_id : Meet_env.t -> code_id -> code_id -> code_id Meet_result.t
    **)

let meet_code_id env code_id1 code_id2 =
  if Pos.eqb code_id1 code_id2
  then Meet_result.Ok (Both_inputs, env)
  else Meet_result.Bottom (New_result ())

(** val meet_alloc_mode : Meet_env.t -> Alloc_mode.t -> Alloc_mode.t ->
    Alloc_mode.t Meet_result.t **)

let meet_alloc_mode env alloc_mode1 alloc_mode2 =
  match alloc_mode1 with
  | Alloc_mode.Heap -> (
    match alloc_mode2 with
    | Alloc_mode.Heap -> Meet_result.Ok (Both_inputs, env)
    | _ -> Meet_result.Ok (Left_input, env))
  | _ -> (
    match alloc_mode2 with
    | Alloc_mode.Heap -> Meet_result.Ok (Right_input, env)
    | _ -> Meet_result.Ok (Both_inputs, env))

(** val meet_unknown : (Meet_env.t -> 'a1 -> 'a1 -> 'a1 Meet_result.t option) ->
    ('a1 -> bool) -> Meet_env.t -> 'a1 Or_unknown.t -> 'a1 Or_unknown.t -> 'a1
    Or_unknown.t Meet_result.t option **)

let meet_unknown meet_contents contents_is_bottom env or_unknown1 or_unknown2 =
  match or_unknown1 with
  | Or_unknown.Known contents -> (
    match or_unknown2 with
    | Or_unknown.Known contents2 ->
      if contents_is_bottom contents && contents_is_bottom contents2
      then Some (Meet_result.Bottom Both_inputs)
      else if contents_is_bottom contents
      then Some (Meet_result.Bottom Left_input)
      else if contents_is_bottom contents2
      then Some (Meet_result.Bottom Right_input)
      else
        option_map
          (map_result (fun x -> Or_unknown.Known x))
          (meet_contents env contents contents2)
    | Or_unknown.Unknown ->
      if contents_is_bottom contents
      then Some (Meet_result.Bottom Left_input)
      else Some (Meet_result.Ok (Left_input, env)))
  | Or_unknown.Unknown -> (
    match or_unknown2 with
    | Or_unknown.Known contents ->
      if contents_is_bottom contents
      then Some (Meet_result.Bottom Right_input)
      else Some (Meet_result.Ok (Right_input, env))
    | Or_unknown.Unknown -> Some (Meet_result.Ok (Both_inputs, env)))

(** val meet_or_unknown_or_bottom : (Meet_env.t -> 'a1 -> 'a1 -> 'a2
    Meet_result.t option) -> Meet_env.t -> 'a1 or_unknown_or_bottom -> 'a1
    or_unknown_or_bottom -> 'a2 Meet_result.t option **)

let meet_or_unknown_or_bottom meet_elt env input1 input2 =
  match input1 with
  | Unknown -> (
    match input2 with
    | Unknown -> Some (Meet_result.Ok (Both_inputs, env))
    | Ok _ -> Some (Meet_result.Ok (Right_input, env))
    | Bottom -> Some (Meet_result.Bottom Right_input))
  | Ok elt1 -> (
    match input2 with
    | Unknown -> Some (Meet_result.Ok (Left_input, env))
    | Ok elt2 -> meet_elt env elt1 elt2
    | Bottom -> Some (Meet_result.Bottom Right_input))
  | Bottom -> (
    match input2 with
    | Bottom -> Some (Meet_result.Bottom Both_inputs)
    | _ -> Some (Meet_result.Bottom Left_input))

(** val relation_eqb : Relation.t -> Relation.t -> bool **)

let relation_eqb relation relation' =
  match relation with
  | Relation.Is_null -> (
    match relation' with Relation.Is_null -> true | _ -> false)
  | Relation.Is_int -> (
    match relation' with Relation.Is_int -> true | _ -> false)
  | Relation.Get_tag -> (
    match relation' with Relation.Get_tag -> true | _ -> false)

(** val inverse_relation_eqb : (Relation.t * name) -> (Relation.t * name) ->
    bool **)

let inverse_relation_eqb r r' =
  relation_eqb (fst r) (fst r') && name_eqb (snd r) (snd r')

(** val head_of_kind_naked_immediate_from_descr : coq_Z list Or_unknown.t ->
    (Relation.t * name) list -> head_of_kind_naked_immediate Or_bottom.t **)

let head_of_kind_naked_immediate_from_descr naked_immediates0 inverse_relations0
    =
  match naked_immediates0 with
  | Or_unknown.Known a -> (
    match a with
    | [] -> Or_bottom.Bottom
    | _ :: _ ->
      Or_bottom.Ok
        { naked_immediates = naked_immediates0;
          inverse_relations = inverse_relations0
        })
  | Or_unknown.Unknown ->
    Or_bottom.Ok
      { naked_immediates = naked_immediates0;
        inverse_relations = inverse_relations0
      }

(** val head_of_kind_naked_immediate_from_descr_non_empty : coq_Z list
    Or_unknown.t -> (Relation.t * name) list -> head_of_kind_naked_immediate
    option **)

let head_of_kind_naked_immediate_from_descr_non_empty naked_immediates0
    inverse_relations0 =
  match
    head_of_kind_naked_immediate_from_descr naked_immediates0 inverse_relations0
  with
  | Or_bottom.Ok head0 -> Some head0
  | Or_bottom.Bottom -> None

type reduce_acc =
  { reduce_imms : coq_Z list Or_unknown.t;
    reduce_relations : (Relation.t * name) list;
    reduce_changed : bool
  }

(** val reduce_head_of_kind_naked_immediate : Typing_env.t ->
    head_of_kind_naked_immediate -> head_of_kind_naked_immediate Or_bottom.t **)

let reduce_head_of_kind_naked_immediate tenv head0 =
  let step =
   fun state inverse ->
    match state with
    | Or_bottom.Ok acc -> (
      let relation = fst inverse in
      let name0 = snd inverse in
      let changed =
       fun imms ->
        Or_bottom.Ok
          { reduce_imms = imms;
            reduce_relations = acc.reduce_relations;
            reduce_changed = true
          }
      in
      let keep =
       fun name' ->
        Or_bottom.Ok
          { reduce_imms = acc.reduce_imms;
            reduce_relations = (relation, name') :: acc.reduce_relations;
            reduce_changed = acc.reduce_changed || negb (name_eqb name' name0)
          }
      in
      match
        Typing_env.get_canonical_simple_ignoring_name_mode tenv
          (simple_of_name name0)
      with
      | Var x -> keep (Name_var x)
      | Symbol s -> keep (Name_symbol s)
      | Const const -> (
        match Relation.of_const relation const with
        | Or_bottom.Ok imm -> (
          let imms' = imm :: [] in
          match acc.reduce_imms with
          | Or_unknown.Known imms ->
            if Keyed.same_keys_b Z.eqb imms' imms
            then Or_bottom.Ok acc
            else if negb (Keyed.among Z.eqb imm imms)
            then Or_bottom.Bottom
            else changed (Or_unknown.Known imms')
          | Or_unknown.Unknown -> changed (Or_unknown.Known imms'))
        | Or_bottom.Bottom -> changed acc.reduce_imms))
    | Or_bottom.Bottom -> Or_bottom.Bottom
  in
  match
    fold_left step head0.inverse_relations
      (Or_bottom.Ok
         { reduce_imms = head0.naked_immediates;
           reduce_relations = [];
           reduce_changed = false
         })
  with
  | Or_bottom.Ok acc ->
    if negb acc.reduce_changed
    then Or_bottom.Ok head0
    else
      head_of_kind_naked_immediate_from_descr acc.reduce_imms
        (Keyed.dedup inverse_relation_eqb (rev acc.reduce_relations))
  | Or_bottom.Bottom -> Or_bottom.Bottom

type 'a reverse_mapping_meet_return_value =
  { left_inputs_only : 'a;
    meet_return_value_of : 'a meet_return_value;
    right_inputs_only : 'a
  }

(** val meet_inverse_relations : (Relation.t * name) list -> (Relation.t * name)
    list -> (Relation.t * name) list reverse_mapping_meet_return_value **)

let meet_inverse_relations inverse_relations1 inverse_relations2 =
  let left_inputs_only0 =
    Keyed.without inverse_relation_eqb inverse_relations2 inverse_relations1
  in
  let right_inputs_only0 =
    Keyed.without inverse_relation_eqb inverse_relations1 inverse_relations2
  in
  let inverse_relations0 =
    Keyed.dedup inverse_relation_eqb (app inverse_relations1 inverse_relations2)
  in
  let meet_return_value0 =
    if Keyed.is_empty left_inputs_only0
    then if Keyed.is_empty right_inputs_only0 then Both_inputs else Right_input
    else if Keyed.is_empty right_inputs_only0
    then Left_input
    else New_result inverse_relations0
  in
  { left_inputs_only = left_inputs_only0;
    meet_return_value_of = meet_return_value0;
    right_inputs_only = right_inputs_only0
  }

(** val is_tag : coq_Z -> bool **)

let is_tag i =
  Z.leb Z0 i
  && Z.leb i
       (Zpos
          (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))))

(** val is_structured_block : coq_Z -> bool **)

let is_structured_block tag = Z.leb Z0 tag && Z.ltb tag no_scan_tag

(** val immediate_or_blocks_with_these_tags : coq_Z list -> Alloc_mode.t ->
    flambda_type **)

let immediate_or_blocks_with_these_tags tags alloc_mode =
  create_variant false Or_unknown.Unknown
    (Or_unknown.Known
       (Row_like_for_blocks
          ( map (fun tag -> tag, Or_unknown.Unknown) tags,
            Or_bottom.Bottom,
            alloc_mode )))
    No_extensions

type meet_choices =
  { type_of_get_tag_scrutinee : coq_Z list -> Alloc_mode.t -> flambda_type;
    define_again : bool;
    lift_variables_of_single_case : bool
  }

(** val compiler_choices : meet_choices **)

let compiler_choices =
  { type_of_get_tag_scrutinee = blocks_with_these_tags;
    define_again = true;
    lift_variables_of_single_case = false
  }

(** val repaired_choices : meet_choices **)

let repaired_choices =
  { type_of_get_tag_scrutinee = immediate_or_blocks_with_these_tags;
    define_again = false;
    lift_variables_of_single_case = true
  }

(** val extension_of_level : Typing_env_level.t -> env_extension **)

let extension_of_level level =
  Env_extension (Keyed.compact name_eqb level.Typing_env_level.equations)

(** val meet : meet_expanded_head -> Meet_env.t -> flambda_type -> flambda_type
    -> flambda_type Meet_result.t option **)

let meet meet_expanded_head_rec env t1 t2 =
  Meet_env.meet_type env t1 t2 meet_expanded_head_rec

(** val define_in_types : meet_choices -> Meet_env.t -> variable -> flambda_kind
    -> Meet_env.t option **)

let define_in_types choices env var kind =
  if
    choices.define_again
    || negb (Typing_env.mem None env.Meet_env.typing_env (Name_var var))
  then Meet_env.add_definition env (Name_var var) Name_mode.in_types kind
  else Some env

(** val add_defined_vars : meet_choices -> Meet_env.t -> Typing_env_level.t ->
    Meet_env.t option **)

let add_defined_vars choices env level =
  match
    Typing_env_level.fold_on_defined_vars
      (fun var kind env0 ->
        match env0 with
        | Some env1 -> define_in_types choices env1 var kind
        | None -> None)
      level (Some env)
  with
  | Some env0 -> env0
  | None -> None

(** val meet_disjunction : (meet_expanded_head -> Scope.t -> Meet_env.t ->
    Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
    meet_expanded_head -> (Meet_env.t -> 'a1 -> 'a1 -> 'a1 Meet_result.t option)
    -> (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t option) -> (unit -> 'a1)
    -> (unit -> 'a2) -> Meet_env.t -> 'a1 -> 'a2 -> variant_extensions -> 'a1 ->
    'a2 -> variant_extensions -> (('a1 * 'a2) * variant_extensions)
    Meet_result.t option **)

let meet_disjunction join choices meet_expanded_head_rec meet_a meet_b bottom_a
    bottom_b initial_env val_a1 val_b1 extensions1 val_a2 val_b2 extensions2 =
  let p, env = Meet_env.enter_scope initial_env in
  let join_scope, initial_tenv = p in
  let direct_return =
   fun result scoped_env ->
    match Typing_env.cut scoped_env.Meet_env.typing_env join_scope with
    | Some level -> (
      match
        add_defined_vars choices
          (Meet_env.with_names_to_avoid initial_env
             scoped_env.Meet_env.names_to_avoid)
          level
      with
      | Some initial_env0 -> (
        let ext = extension_of_level level in
        match
          Meet_env.add_env_extension_strict initial_env0 ext
            meet_expanded_head_rec
        with
        | Some added -> (
          match added with
          | Or_bottom.Ok env0 -> Some (Meet_result.Ok (result, env0))
          | Or_bottom.Bottom ->
            Some (Meet_result.Bottom (map_return_value (fun _ -> ()) result)))
        | None -> None)
      | None -> None)
    | None -> None
  in
  let when_a =
   fun extensions ->
    match extensions with
    | No_extensions -> None
    | Ext (when_a, _) -> Some when_a
  in
  let when_b =
   fun extensions ->
    match extensions with
    | No_extensions -> None
    | Ext (_, when_b) -> Some when_b
  in
  let add_extension =
   fun env0 extension ->
    match extension with
    | Some extension0 -> (
      match env0 with
      | Or_bottom.Ok env1 ->
        Meet_env.add_env_extension_strict env1 extension0 meet_expanded_head_rec
      | Or_bottom.Bottom -> Some Or_bottom.Bottom)
    | None -> Some env0
  in
  let meet_side =
   fun meet_c env0 val1 val2 ->
    match env0 with
    | Or_bottom.Ok env1 -> (
      match meet_c env1 val1 val2 with
      | Some result -> (
        match result with
        | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
        | Meet_result.Ok (result0, env2) -> (
          match Meet_env.final_typing_env_strict env2 with
          | Or_bottom.Ok _ -> Some (Meet_result.Ok (result0, env2))
          | Or_bottom.Bottom -> Some (Meet_result.Bottom (New_result ()))))
      | None -> None)
    | Or_bottom.Bottom -> Some (Meet_result.Bottom (New_result ()))
  in
  match add_extension (Or_bottom.Ok env) (when_a extensions1) with
  | Some env_a -> (
    match add_extension env_a (when_a extensions2) with
    | Some env_a0 -> (
      match meet_side meet_a env_a0 val_a1 val_a2 with
      | Some a_result -> (
        let env0 =
          match a_result with
          | Meet_result.Bottom _ -> env
          | Meet_result.Ok (_, env_a1) ->
            Meet_env.with_names_to_avoid env env_a1.Meet_env.names_to_avoid
        in
        match add_extension (Or_bottom.Ok env0) (when_b extensions1) with
        | Some env_b -> (
          match add_extension env_b (when_b extensions2) with
          | Some env_b0 -> (
            match meet_side meet_b env_b0 val_b1 val_b2 with
            | Some b_result -> (
              match a_result with
              | Meet_result.Bottom a -> (
                match b_result with
                | Meet_result.Bottom r2 ->
                  Some
                    (Meet_result.Bottom
                       (combine_meet_return_values a r2 (fun _ -> ())))
                | Meet_result.Ok (b_result0, env1) ->
                  let result =
                    combine_meet_return_values a b_result0 (fun _ ->
                        let val_b = extract_value b_result0 val_b1 val_b2 in
                        let val_a = bottom_a () in
                        (val_a, val_b), No_extensions)
                  in
                  direct_return result env1)
              | Meet_result.Ok (a_result0, env_a1) -> (
                match b_result with
                | Meet_result.Bottom b ->
                  let result =
                    combine_meet_return_values a_result0 b (fun _ ->
                        let val_a = extract_value a_result0 val_a1 val_a2 in
                        let val_b = bottom_b () in
                        (val_a, val_b), No_extensions)
                  in
                  direct_return result env_a1
                | Meet_result.Ok (b_result0, env_b1) -> (
                  let tenv_a = Meet_env.final_typing_env env_a1 in
                  let tenv_b = Meet_env.final_typing_env env_b1 in
                  match
                    join meet_expanded_head_rec join_scope
                      (Meet_env.with_names_to_avoid initial_env
                         env_b1.Meet_env.names_to_avoid)
                      initial_tenv [tenv_a; tenv_b]
                  with
                  | Some result_env0 -> (
                    match Typing_env.cut tenv_a join_scope with
                    | Some when_a_level -> (
                      match Typing_env.cut tenv_b join_scope with
                      | Some when_b_level -> (
                        match
                          add_defined_vars choices result_env0 when_a_level
                        with
                        | Some result_env1 -> (
                          match
                            add_defined_vars choices result_env1 when_b_level
                          with
                          | Some result_env2 ->
                            let extensions =
                              if
                                Typing_env_level.is_empty when_a_level
                                && Typing_env_level.is_empty when_b_level
                              then No_extensions
                              else
                                let when_a0 = extension_of_level when_a_level in
                                let when_b0 = extension_of_level when_b_level in
                                Ext (when_a0, when_b0)
                            in
                            let env_extension_result =
                              match extensions with
                              | No_extensions -> (
                                match extensions1 with
                                | No_extensions -> (
                                  match extensions2 with
                                  | No_extensions -> Both_inputs
                                  | Ext (_, _) -> Left_input)
                                | Ext (_, _) -> (
                                  match extensions2 with
                                  | No_extensions -> Right_input
                                  | Ext (_, _) -> New_result ()))
                              | Ext (_, _) -> New_result ()
                            in
                            let result =
                              combine_meet_return_values
                                (combine_meet_return_values a_result0 b_result0
                                   (fun _ -> ()))
                                env_extension_result
                                (fun _ ->
                                  let val_a =
                                    extract_value a_result0 val_a1 val_a2
                                  in
                                  let val_b =
                                    extract_value b_result0 val_b1 val_b2
                                  in
                                  (val_a, val_b), extensions)
                            in
                            Some (Meet_result.Ok (result, result_env2))
                          | None -> None)
                        | None -> None)
                      | None -> None)
                    | None -> None)
                  | None -> None)))
            | None -> None)
          | None -> None)
        | None -> None)
      | None -> None)
    | None -> None)
  | None -> None

type row_like_state =
  { extra_variables : (variable * flambda_kind) list;
    result_env : Typing_env.t list option;
    result_is_t1 : bool;
    result_is_t2 : bool;
    avoid : variable list
  }

(** val not_t1 : row_like_state -> row_like_state **)

let not_t1 state =
  { extra_variables = state.extra_variables;
    result_env = state.result_env;
    result_is_t1 = false;
    result_is_t2 = state.result_is_t2;
    avoid = state.avoid
  }

(** val not_t2 : row_like_state -> row_like_state **)

let not_t2 state =
  { extra_variables = state.extra_variables;
    result_env = state.result_env;
    result_is_t1 = state.result_is_t1;
    result_is_t2 = false;
    avoid = state.avoid
  }

(** val update_refs : 'a1 meet_return_value -> row_like_state -> row_like_state
    **)

let update_refs r state =
  match r with
  | Left_input -> not_t2 state
  | Right_input -> not_t1 state
  | Both_inputs -> state
  | New_result _ -> not_t1 (not_t2 state)

(** val union_extra_variables : (variable * flambda_kind) list -> (variable *
    flambda_kind) list -> (variable * flambda_kind) list option **)

let rec union_extra_variables extra = function
  | [] -> Some extra
  | p :: vars0 -> (
    let var, kind = p in
    match lookup var extra with
    | Some kind' ->
      if kind_eqb kind kind' then union_extra_variables extra vars0 else None
    | None -> union_extra_variables (app extra ((var, kind) :: [])) vars0)

(** val meet_row_like : (meet_expanded_head -> Scope.t -> Meet_env.t ->
    Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
    meet_expanded_head -> (Meet_env.t -> 'a3 -> 'a3 -> 'a3 Meet_result.t option)
    -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> 'a1) ->
    ('a2 -> 'a2 -> 'a2 Or_bottom.t) -> ('a5 -> bool) -> ('a5 -> ('a4 * ('a1,
    'a2, 'a3, env_extension) row_like_case) option) -> (('a4 -> ('a1, 'a2, 'a3,
    env_extension) row_like_case Or_unknown.t option -> ('a1, 'a2, 'a3,
    env_extension) row_like_case Or_unknown.t option -> row_like_state -> (('a1,
    'a2, 'a3, env_extension) row_like_case Or_unknown.t option * row_like_state)
    option) -> 'a5 -> 'a5 -> row_like_state -> ('a5 * row_like_state) option) ->
    Meet_env.t -> 'a5 -> 'a5 -> ('a1, 'a2, 'a3, env_extension) row_like_case
    Or_bottom.t -> ('a1, 'a2, 'a3, env_extension) row_like_case Or_bottom.t ->
    ('a5 * ('a1, 'a2, 'a3, env_extension) row_like_case Or_bottom.t)
    Meet_result.t option **)

let meet_row_like join choices meet_expanded_head_rec meet_maps_to equal_index
    subset_index union_index meet_shape is_empty_map_known
    get_singleton_map_known merge_map_known initial_env known1 known2 other1
    other2 =
  let p, base_env = Meet_env.enter_scope initial_env in
  let common_scope, initial_tenv = p in
  let base_tenv = Meet_env.final_typing_env base_env in
  let add_extra_variables_and_extract_extension =
   fun scoped_env state ->
    match Typing_env.cut scoped_env common_scope with
    | Some level -> (
      match
        union_extra_variables state.extra_variables
          (rev (Typing_env_level.defined_variables_with_kinds level))
      with
      | Some extra ->
        Some
          ( extension_of_level level,
            { extra_variables = extra;
              result_env = state.result_env;
              result_is_t1 = state.result_is_t1;
              result_is_t2 = state.result_is_t2;
              avoid = state.avoid
            } )
      | None -> None)
    | None -> None
  in
  let extract_and_join_extensions =
   fun scoped_envs state ->
    match
      join meet_expanded_head_rec common_scope
        (Meet_env.with_names_to_avoid initial_env state.avoid)
        initial_tenv scoped_envs
    with
    | Some result_env0 ->
      fold_left
        (fun env binding ->
          match env with
          | Some env0 ->
            define_in_types choices env0 (fst binding) (snd binding)
          | None -> None)
        state.extra_variables (Some result_env0)
    | None -> None
  in
  let need_join =
    match other1 with
    | Or_bottom.Ok _ -> (
      match other2 with
      | Or_bottom.Ok _ ->
        if is_empty_map_known known1 && is_empty_map_known known2
        then false
        else true
      | Or_bottom.Bottom -> (
        match get_singleton_map_known known2 with
        | Some _ -> false
        | None ->
          if is_empty_map_known known1 && is_empty_map_known known2
          then false
          else true))
    | Or_bottom.Bottom -> (
      match get_singleton_map_known known1 with
      | Some _ -> false
      | None -> (
        match other2 with
        | Or_bottom.Ok _ ->
          if is_empty_map_known known1 && is_empty_map_known known2
          then false
          else true
        | Or_bottom.Bottom -> (
          match get_singleton_map_known known2 with
          | Some _ -> false
          | None ->
            if is_empty_map_known known1 && is_empty_map_known known2
            then false
            else true)))
  in
  let join_result_env =
   fun scoped_env names state ->
    match state.result_env with
    | Some other_envs ->
      if need_join
      then
        let new_result_env = scoped_env :: other_envs in
        Some
          { extra_variables = state.extra_variables;
            result_env = Some new_result_env;
            result_is_t1 = state.result_is_t1;
            result_is_t2 = state.result_is_t2;
            avoid = names
          }
      else None
    | None ->
      let new_result_env = scoped_env :: [] in
      Some
        { extra_variables = state.extra_variables;
          result_env = Some new_result_env;
          result_is_t1 = state.result_is_t1;
          result_is_t2 = state.result_is_t2;
          avoid = names
        }
  in
  let meet_index =
   fun env i1 i2 ->
    match meet_shape i1.index_shape i2.index_shape with
    | Or_bottom.Ok shape -> (
      match i1.index_domain with
      | Row_like_index_domain.Known known -> (
        match i2.index_domain with
        | Row_like_index_domain.Known i2' ->
          if equal_index known i2'
          then Meet_result.Ok (Both_inputs, env)
          else Meet_result.Bottom (New_result ())
        | Row_like_index_domain.At_least at_least ->
          if subset_index at_least known
          then Meet_result.Ok (Left_input, env)
          else Meet_result.Bottom (New_result ()))
      | Row_like_index_domain.At_least i1' -> (
        match i2.index_domain with
        | Row_like_index_domain.Known known ->
          if subset_index i1' known
          then Meet_result.Ok (Right_input, env)
          else Meet_result.Bottom (New_result ())
        | Row_like_index_domain.At_least i2' ->
          if subset_index i1' i2'
          then
            if subset_index i2' i1'
            then Meet_result.Ok (Both_inputs, env)
            else Meet_result.Ok (Right_input, env)
          else if subset_index i2' i1'
          then Meet_result.Ok (Left_input, env)
          else
            let domain = Row_like_index_domain.At_least (union_index i1' i2') in
            Meet_result.Ok
              (New_result { index_domain = domain; index_shape = shape }, env)))
    | Or_bottom.Bottom -> Meet_result.Bottom (New_result ())
  in
  let bottom_case = fun r state -> Some (None, update_refs r state) in
  let add_case_extension =
   fun extension state ->
    match
      Meet_env.add_env_extension_strict
        (Meet_env.with_names_to_avoid base_env state.avoid)
        extension meet_expanded_head_rec
    with
    | Some added -> (
      match added with
      | Or_bottom.Ok env -> (
        match Meet_env.final_typing_env_strict env with
        | Or_bottom.Ok _ -> Some (Or_bottom.Ok env)
        | Or_bottom.Bottom -> Some Or_bottom.Bottom)
      | Or_bottom.Bottom -> Some Or_bottom.Bottom)
    | None -> None
  in
  let meet_case =
   fun env case1 case2 state ->
    let env0 = Meet_env.with_names_to_avoid env state.avoid in
    match meet_index env0 case1.case_index case2.case_index with
    | Meet_result.Bottom r -> bottom_case r state
    | Meet_result.Ok (index_result, env1) -> (
      match meet_maps_to env1 case1.case_maps_to case2.case_maps_to with
      | Some maps_to -> (
        match maps_to with
        | Meet_result.Bottom r -> bottom_case r state
        | Meet_result.Ok (maps_to_result, env2) -> (
          match
            Meet_env.add_env_extension_strict env2 case1.case_env_extension
              meet_expanded_head_rec
          with
          | Some env3 -> (
            match
              match env3 with
              | Or_bottom.Ok env4 ->
                Meet_env.add_env_extension_strict env4 case2.case_env_extension
                  meet_expanded_head_rec
              | Or_bottom.Bottom -> Some Or_bottom.Bottom
            with
            | Some env4 -> (
              let env5 =
                match env4 with
                | Or_bottom.Ok env5 -> (
                  match Meet_env.final_typing_env_strict env5 with
                  | Or_bottom.Ok _ -> Or_bottom.Ok env5
                  | Or_bottom.Bottom -> Or_bottom.Bottom)
                | Or_bottom.Bottom -> Or_bottom.Bottom
              in
              match env5 with
              | Or_bottom.Ok env6 -> (
                let tenv = Meet_env.final_typing_env env6 in
                match
                  join_result_env tenv env6.Meet_env.names_to_avoid state
                with
                | Some state0 -> (
                  let state1 = update_refs index_result state0 in
                  let state2 = update_refs maps_to_result state1 in
                  let index =
                    extract_value index_result case1.case_index case2.case_index
                  in
                  let maps_to0 =
                    extract_value maps_to_result case1.case_maps_to
                      case2.case_maps_to
                  in
                  match
                    if need_join
                    then add_extra_variables_and_extract_extension tenv state2
                    else if choices.lift_variables_of_single_case
                    then
                      match
                        add_extra_variables_and_extract_extension tenv state2
                      with
                      | Some p0 ->
                        let _, state3 = p0 in
                        Some (empty_env_extension, state3)
                      | None -> None
                    else Some (empty_env_extension, state2)
                  with
                  | Some p0 ->
                    let env_extension0, state3 = p0 in
                    let state4 =
                      let (Env_extension equations0) = env_extension0 in
                      match equations0 with
                      | [] -> state3
                      | _ :: _ -> not_t1 (not_t2 state3)
                    in
                    let case =
                      { case_maps_to = maps_to0;
                        case_index = index;
                        case_env_extension = env_extension0
                      }
                    in
                    Some (Some (Or_unknown.Known case), state4)
                  | None -> None)
                | None -> None)
              | Or_bottom.Bottom -> bottom_case (New_result ()) state)
            | None -> None)
          | None -> None))
      | None -> None)
  in
  let meet_case_with_unknown =
   fun other_case change state ->
    match add_case_extension other_case.case_env_extension state with
    | Some env -> (
      match env with
      | Or_bottom.Ok env0 -> (
        match
          join_result_env
            (Meet_env.final_typing_env env0)
            env0.Meet_env.names_to_avoid state
        with
        | Some state0 -> Some (Some (Or_unknown.Known other_case), change state0)
        | None -> None)
      | Or_bottom.Bottom -> Some (None, state))
    | None -> None
  in
  let meet_knowns =
   fun case1 case2 state ->
    match case1 with
    | Some case3 -> (
      match case2 with
      | Some case4 -> (
        match case3 with
        | Or_unknown.Known case5 -> (
          match case4 with
          | Or_unknown.Known case6 -> meet_case base_env case5 case6 state
          | Or_unknown.Unknown -> meet_case_with_unknown case5 not_t2 state)
        | Or_unknown.Unknown -> (
          match case4 with
          | Or_unknown.Known case -> meet_case_with_unknown case not_t1 state
          | Or_unknown.Unknown -> (
            match join_result_env base_tenv state.avoid state with
            | Some state0 -> Some (Some Or_unknown.Unknown, state0)
            | None -> None)))
      | None -> (
        match other2 with
        | Or_bottom.Ok other_case -> (
          match case3 with
          | Or_unknown.Known case4 -> meet_case base_env case4 other_case state
          | Or_unknown.Unknown ->
            meet_case_with_unknown other_case
              (fun state0 -> not_t1 (not_t2 state0))
              state)
        | Or_bottom.Bottom -> Some (None, not_t1 state)))
    | None -> (
      match case2 with
      | Some case3 -> (
        match other1 with
        | Or_bottom.Ok other_case -> (
          match case3 with
          | Or_unknown.Known case4 -> meet_case base_env other_case case4 state
          | Or_unknown.Unknown ->
            meet_case_with_unknown other_case
              (fun state0 -> not_t1 (not_t2 state0))
              state)
        | Or_bottom.Bottom -> Some (None, not_t2 state))
      | None -> Some (None, state))
  in
  let state =
    { extra_variables = [];
      result_env = None;
      result_is_t1 = true;
      result_is_t2 = true;
      avoid = base_env.Meet_env.names_to_avoid
    }
  in
  match merge_map_known (fun _ -> meet_knowns) known1 known2 state with
  | Some p0 -> (
    let known, state0 = p0 in
    match other1 with
    | Or_bottom.Ok other3 -> (
      match other2 with
      | Or_bottom.Ok other4 -> (
        match meet_case base_env other3 other4 state0 with
        | Some p1 -> (
          let other, state1 = p1 in
          match other with
          | Some t0 -> (
            match t0 with
            | Or_unknown.Known r -> (
              let p2 = Or_bottom.Ok r, state1 in
              let other0, state2 = p2 in
              if
                is_empty_map_known known
                &&
                match other0 with
                | Or_bottom.Ok _ -> false
                | Or_bottom.Bottom -> true
              then Some (Meet_result.Bottom (New_result ()))
              else
                match state2.result_env with
                | Some scoped_envs -> (
                  match extract_and_join_extensions scoped_envs state2 with
                  | Some env -> (
                    let env0 = Or_bottom.Ok env in
                    let match_with_input =
                     fun v ->
                      if state2.result_is_t1
                      then
                        if state2.result_is_t2 then Both_inputs else Left_input
                      else if state2.result_is_t2
                      then Right_input
                      else New_result v
                    in
                    match env0 with
                    | Or_bottom.Ok env1 ->
                      Some
                        (Meet_result.Ok (match_with_input (known, other0), env1))
                    | Or_bottom.Bottom ->
                      Some (Meet_result.Bottom (match_with_input ())))
                  | None -> None)
                | None -> (
                  let env = Or_bottom.Bottom in
                  let match_with_input =
                   fun v ->
                    if state2.result_is_t1
                    then if state2.result_is_t2 then Both_inputs else Left_input
                    else if state2.result_is_t2
                    then Right_input
                    else New_result v
                  in
                  match env with
                  | Or_bottom.Ok env0 ->
                    Some
                      (Meet_result.Ok (match_with_input (known, other0), env0))
                  | Or_bottom.Bottom ->
                    Some (Meet_result.Bottom (match_with_input ()))))
            | Or_unknown.Unknown -> None)
          | None -> (
            let p2 = Or_bottom.Bottom, state1 in
            let other0, state2 = p2 in
            if
              is_empty_map_known known
              &&
              match other0 with
              | Or_bottom.Ok _ -> false
              | Or_bottom.Bottom -> true
            then Some (Meet_result.Bottom (New_result ()))
            else
              match state2.result_env with
              | Some scoped_envs -> (
                match extract_and_join_extensions scoped_envs state2 with
                | Some env -> (
                  let env0 = Or_bottom.Ok env in
                  let match_with_input =
                   fun v ->
                    if state2.result_is_t1
                    then if state2.result_is_t2 then Both_inputs else Left_input
                    else if state2.result_is_t2
                    then Right_input
                    else New_result v
                  in
                  match env0 with
                  | Or_bottom.Ok env1 ->
                    Some
                      (Meet_result.Ok (match_with_input (known, other0), env1))
                  | Or_bottom.Bottom ->
                    Some (Meet_result.Bottom (match_with_input ())))
                | None -> None)
              | None -> (
                let env = Or_bottom.Bottom in
                let match_with_input =
                 fun v ->
                  if state2.result_is_t1
                  then if state2.result_is_t2 then Both_inputs else Left_input
                  else if state2.result_is_t2
                  then Right_input
                  else New_result v
                in
                match env with
                | Or_bottom.Ok env0 ->
                  Some (Meet_result.Ok (match_with_input (known, other0), env0))
                | Or_bottom.Bottom ->
                  Some (Meet_result.Bottom (match_with_input ())))))
        | None -> None)
      | Or_bottom.Bottom -> (
        let p1 = Or_bottom.Bottom, not_t1 state0 in
        let other, state1 = p1 in
        if
          is_empty_map_known known
          &&
          match other with
          | Or_bottom.Ok _ -> false
          | Or_bottom.Bottom -> true
        then Some (Meet_result.Bottom (New_result ()))
        else
          match state1.result_env with
          | Some scoped_envs -> (
            match extract_and_join_extensions scoped_envs state1 with
            | Some env -> (
              let env0 = Or_bottom.Ok env in
              let match_with_input =
               fun v ->
                if state1.result_is_t1
                then if state1.result_is_t2 then Both_inputs else Left_input
                else if state1.result_is_t2
                then Right_input
                else New_result v
              in
              match env0 with
              | Or_bottom.Ok env1 ->
                Some (Meet_result.Ok (match_with_input (known, other), env1))
              | Or_bottom.Bottom ->
                Some (Meet_result.Bottom (match_with_input ())))
            | None -> None)
          | None -> (
            let env = Or_bottom.Bottom in
            let match_with_input =
             fun v ->
              if state1.result_is_t1
              then if state1.result_is_t2 then Both_inputs else Left_input
              else if state1.result_is_t2
              then Right_input
              else New_result v
            in
            match env with
            | Or_bottom.Ok env0 ->
              Some (Meet_result.Ok (match_with_input (known, other), env0))
            | Or_bottom.Bottom ->
              Some (Meet_result.Bottom (match_with_input ())))))
    | Or_bottom.Bottom -> (
      match other2 with
      | Or_bottom.Ok _ -> (
        let p1 = Or_bottom.Bottom, not_t2 state0 in
        let other, state1 = p1 in
        if
          is_empty_map_known known
          &&
          match other with
          | Or_bottom.Ok _ -> false
          | Or_bottom.Bottom -> true
        then Some (Meet_result.Bottom (New_result ()))
        else
          match state1.result_env with
          | Some scoped_envs -> (
            match extract_and_join_extensions scoped_envs state1 with
            | Some env -> (
              let env0 = Or_bottom.Ok env in
              let match_with_input =
               fun v ->
                if state1.result_is_t1
                then if state1.result_is_t2 then Both_inputs else Left_input
                else if state1.result_is_t2
                then Right_input
                else New_result v
              in
              match env0 with
              | Or_bottom.Ok env1 ->
                Some (Meet_result.Ok (match_with_input (known, other), env1))
              | Or_bottom.Bottom ->
                Some (Meet_result.Bottom (match_with_input ())))
            | None -> None)
          | None -> (
            let env = Or_bottom.Bottom in
            let match_with_input =
             fun v ->
              if state1.result_is_t1
              then if state1.result_is_t2 then Both_inputs else Left_input
              else if state1.result_is_t2
              then Right_input
              else New_result v
            in
            match env with
            | Or_bottom.Ok env0 ->
              Some (Meet_result.Ok (match_with_input (known, other), env0))
            | Or_bottom.Bottom ->
              Some (Meet_result.Bottom (match_with_input ()))))
      | Or_bottom.Bottom -> (
        let p1 = Or_bottom.Bottom, state0 in
        let other, state1 = p1 in
        if
          is_empty_map_known known
          &&
          match other with
          | Or_bottom.Ok _ -> false
          | Or_bottom.Bottom -> true
        then Some (Meet_result.Bottom (New_result ()))
        else
          match state1.result_env with
          | Some scoped_envs -> (
            match extract_and_join_extensions scoped_envs state1 with
            | Some env -> (
              let env0 = Or_bottom.Ok env in
              let match_with_input =
               fun v ->
                if state1.result_is_t1
                then if state1.result_is_t2 then Both_inputs else Left_input
                else if state1.result_is_t2
                then Right_input
                else New_result v
              in
              match env0 with
              | Or_bottom.Ok env1 ->
                Some (Meet_result.Ok (match_with_input (known, other), env1))
              | Or_bottom.Bottom ->
                Some (Meet_result.Bottom (match_with_input ())))
            | None -> None)
          | None -> (
            let env = Or_bottom.Bottom in
            let match_with_input =
             fun v ->
              if state1.result_is_t1
              then if state1.result_is_t2 then Both_inputs else Left_input
              else if state1.result_is_t2
              then Right_input
              else New_result v
            in
            match env with
            | Or_bottom.Ok env0 ->
              Some (Meet_result.Ok (match_with_input (known, other), env0))
            | Or_bottom.Bottom ->
              Some (Meet_result.Bottom (match_with_input ()))))))
  | None -> None

(** val meet_relation : meet_expanded_head -> Meet_env.t -> variable option ->
    variable option -> variable option Meet_result.t option **)

let meet_relation meet_expanded_head_rec env var1 var2 =
  match var1 with
  | Some var3 -> (
    match var2 with
    | Some var4 -> (
      match
        Meet_env.add_alias env (Var var3) (Var var4) meet_expanded_head_rec
      with
      | Some added -> (
        match added with
        | Or_bottom.Ok env0 -> Some (Meet_result.Ok (Both_inputs, env0))
        | Or_bottom.Bottom -> Some (Meet_result.Bottom (New_result ())))
      | None -> None)
    | None -> Some (Meet_result.Ok (Left_input, env)))
  | None -> (
    match var2 with
    | Some _ -> Some (Meet_result.Ok (Right_input, env))
    | None -> Some (Meet_result.Ok (Both_inputs, env)))

(** val meet_function_type : Meet_env.t -> function_type Or_unknown.t ->
    function_type Or_unknown.t -> function_type Or_unknown.t Meet_result.t
    option **)

let meet_function_type env func_type1 func_type2 =
  match func_type1 with
  | Or_unknown.Known func_type3 -> (
    match func_type2 with
    | Or_unknown.Known func_type4 ->
      Some
        (map_result
           (fun code_id0 ->
             Or_unknown.Known { function_type_code_id = code_id0 })
           (meet_code_id env func_type3.function_type_code_id
              func_type4.function_type_code_id))
    | Or_unknown.Unknown -> Some (Meet_result.Ok (Left_input, env)))
  | Or_unknown.Unknown -> (
    match func_type2 with
    | Or_unknown.Known _ -> Some (Meet_result.Ok (Right_input, env))
    | Or_unknown.Unknown -> Some (Meet_result.Ok (Both_inputs, env)))

(** val meet_array_of_types : meet_expanded_head -> Meet_env.t -> flambda_type
    list -> flambda_type list -> nat -> flambda_type list Meet_result.t option **)

let meet_array_of_types meet_expanded_head_rec env fields1 fields2 length0 =
  let fold2 =
   fun f left right init ->
    fold_left
      (fun acc i -> f i (nth_error left i) (nth_error right i) acc)
      (seq O length0) init
  in
  let rebuild =
   fun l ->
    match l with
    | [] -> []
    | p :: _ ->
      let _, data = p in
      map
        (fun i ->
          match Keyed.lookup Nat.eqb i l with
          | Some data0 -> data0
          | None -> data)
        (seq O length0)
  in
  meet_mapping (meet meet_expanded_head_rec) fold2 env fields1 fields2 rebuild

(** val meet_int_indexed_product : meet_expanded_head -> Meet_env.t ->
    flambda_type list -> flambda_type list -> flambda_type list Meet_result.t
    option **)

let meet_int_indexed_product meet_expanded_head_rec env fields1 fields2 =
  let length0 = Nat.max (length fields1) (length fields2) in
  meet_array_of_types meet_expanded_head_rec env fields1 fields2 length0

(** val meet_product_function_slot_indexed : meet_expanded_head -> Meet_env.t ->
    flambda_type finite_map -> flambda_type finite_map -> flambda_type
    finite_map Meet_result.t option **)

let meet_product_function_slot_indexed meet_expanded_head_rec env
    components_by_index1 components_by_index2 =
  map_meet Pos.eqb
    (meet meet_expanded_head_rec)
    env components_by_index1 components_by_index2

(** val meet_product_value_slot_indexed : meet_expanded_head -> Meet_env.t ->
    flambda_type finite_map -> flambda_type finite_map -> flambda_type
    finite_map Meet_result.t option **)

let meet_product_value_slot_indexed meet_expanded_head_rec env
    components_by_index1 components_by_index2 =
  map_meet Pos.eqb
    (meet meet_expanded_head_rec)
    env components_by_index1 components_by_index2

(** val meet_closures_entry : meet_expanded_head -> Meet_env.t -> closures_entry
    -> closures_entry -> closures_entry Meet_result.t option **)

let meet_closures_entry meet_expanded_head_rec env entry1 entry2 =
  let (Closures_entry (function_types1, closure_types1, value_slot_types1)) =
    entry1
  in
  let (Closures_entry (function_types2, closure_types2, value_slot_types2)) =
    entry2
  in
  combine_results3 env (map_meet Pos.eqb meet_function_type)
    (meet_product_function_slot_indexed meet_expanded_head_rec)
    (meet_product_value_slot_indexed meet_expanded_head_rec)
    function_types1 function_types2 closure_types1 closure_types2
    value_slot_types1 value_slot_types2
    (fun function_types closure_types value_slot_types ->
      Closures_entry (function_types, closure_types, value_slot_types))

(** val merge_fold_failing : ('a1 -> 'a1 -> bool) -> 'a1 list -> ('a1 -> 'a2
    option -> 'a3 option -> 'a5 -> ('a4 option * 'a5) option) -> ('a1, 'a2)
    Keyed.finite_map -> ('a1, 'a3) Keyed.finite_map -> 'a5 -> (('a1, 'a4)
    Keyed.finite_map * 'a5) option **)

let merge_fold_failing eqb0 keys f m1 m2 init =
  let out, state =
    Keyed.merge_fold_on eqb0 keys
      (fun key a b state ->
        match state with
        | Some state0 -> (
          match f key a b state0 with
          | Some p ->
            let c, state1 = p in
            c, Some state1
          | None -> None, None)
        | None -> None, None)
      m1 m2 (Some init)
  in
  option_map (fun state0 -> out, state0) state

(** val meet_row_like_for_blocks : (meet_expanded_head -> Scope.t -> Meet_env.t
    -> Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices
    -> meet_expanded_head -> Meet_env.t -> row_like_for_blocks ->
    row_like_for_blocks -> row_like_for_blocks Meet_result.t option **)

let meet_row_like_for_blocks join choices meet_expanded_head_rec env blocks1
    blocks2 =
  let (Row_like_for_blocks (known1, other1, alloc_mode1)) = blocks1 in
  let (Row_like_for_blocks (known2, other2, alloc_mode2)) = blocks2 in
  let meet_shape =
   fun shape1 shape2 ->
    if block_shape_eqb shape1 shape2
    then Or_bottom.Ok shape1
    else Or_bottom.Bottom
  in
  let get_singleton_map_known =
   fun known ->
    match Keyed.get_singleton_binding Z.eqb known with
    | Some p -> (
      let tag, t0 = p in
      match t0 with
      | Or_unknown.Known case -> Some (tag, case)
      | Or_unknown.Unknown -> None)
    | None -> None
  in
  let merge_map_known =
   fun merge_case known3 known4 state ->
    merge_fold_failing Z.eqb
      (sort_numbers (Keyed.keys_of_both Z.eqb known3 known4))
      merge_case known3 known4 state
  in
  combine_results2 env
    (fun env0 left right ->
      meet_row_like join choices meet_expanded_head_rec
        (meet_int_indexed_product meet_expanded_head_rec)
        Nat.eqb Nat.leb Nat.max meet_shape Keyed.is_empty
        get_singleton_map_known merge_map_known env0 (fst left) (fst right)
        (snd left) (snd right))
    (fun env0 alloc_mode3 alloc_mode4 ->
      Some (meet_alloc_mode env0 alloc_mode3 alloc_mode4))
    (known1, other1) (known2, other2) alloc_mode1 alloc_mode2
    (fun known_and_other alloc_mode ->
      Row_like_for_blocks (fst known_and_other, snd known_and_other, alloc_mode))

(** val meet_row_like_for_closures : (meet_expanded_head -> Scope.t ->
    Meet_env.t -> Typing_env.t -> Typing_env.t list -> Meet_env.t option) ->
    meet_choices -> meet_expanded_head -> Meet_env.t -> row_like_for_closures ->
    row_like_for_closures -> row_like_for_closures Meet_result.t option **)

let meet_row_like_for_closures join choices meet_expanded_head_rec env closures1
    closures2 =
  let (Row_like_for_closures known1) = closures1 in
  let (Row_like_for_closures known2) = closures2 in
  let meet_shape = fun _ _ -> Or_bottom.Ok () in
  let merge_map_known =
   fun merge_case known3 known4 state ->
    merge_fold_failing Pos.eqb
      (Keyed.keys_of_both Pos.eqb known3 known4)
      (fun fslot case1 case2 state0 ->
        let case3 = option_map (fun x -> Or_unknown.Known x) case1 in
        let case4 = option_map (fun x -> Or_unknown.Known x) case2 in
        match merge_case fslot case3 case4 state0 with
        | Some p -> (
          let case, state1 = p in
          match case with
          | Some t0 -> (
            match t0 with
            | Or_unknown.Known case0 -> Some (Some case0, state1)
            | Or_unknown.Unknown -> None)
          | None -> Some (None, state1))
        | None -> None)
      known3 known4 state
  in
  match
    meet_row_like join choices meet_expanded_head_rec
      (meet_closures_entry meet_expanded_head_rec)
      set_of_closures_contents_equal set_of_closures_contents_subset
      set_of_closures_contents_union meet_shape Keyed.is_empty
      (Keyed.get_singleton_binding Pos.eqb)
      merge_map_known env known1 known2 Or_bottom.Bottom Or_bottom.Bottom
  with
  | Some result -> (
    match result with
    | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
    | Meet_result.Ok (r, env0) -> (
      match r with
      | New_result a -> (
        let _, t0 = a in
        match t0 with
        | Or_bottom.Ok _ -> None
        | Or_bottom.Bottom ->
          Some
            (Meet_result.Ok
               ( map_return_value
                   (fun known_and_other ->
                     Row_like_for_closures (fst known_and_other))
                   r,
                 env0 )))
      | _ ->
        Some
          (Meet_result.Ok
             ( map_return_value
                 (fun known_and_other ->
                   Row_like_for_closures (fst known_and_other))
                 r,
               env0 ))))
  | None -> None

(** val type_of_get_tag_scrutinee_or_unknown : meet_choices -> coq_Z list ->
    Alloc_mode.t -> flambda_type Or_unknown.t **)

let type_of_get_tag_scrutinee_or_unknown choices tags alloc_mode =
  if forallb is_structured_block tags
  then Or_unknown.Known (choices.type_of_get_tag_scrutinee tags alloc_mode)
  else Or_unknown.Unknown

(** val reduce_inverse_relations : meet_choices -> meet_expanded_head ->
    Meet_env.t -> coq_Z list Or_unknown.t -> (Relation.t * name) list ->
    Meet_env.t Or_bottom.t option **)

let reduce_inverse_relations choices meet_expanded_head_rec env
    naked_immediates0 inverse_relations0 =
  match naked_immediates0 with
  | Or_unknown.Known imms ->
    let step =
     fun state inverse ->
      match state with
      | Some t0 -> (
        match t0 with
        | Or_bottom.Ok env0 -> (
          let name0 = snd inverse in
          let add_equation0 =
           fun ty ->
            Meet_env.add_equation_strict env0 name0 ty meet_expanded_head_rec
          in
          match fst inverse with
          | Relation.Is_null ->
            if Keyed.among Z.eqb Z0 imms
            then
              if Keyed.among Z.eqb (Zpos Coq_xH) imms
              then Some (Or_bottom.Ok env0)
              else add_equation0 any_non_null_value
            else if Keyed.among Z.eqb (Zpos Coq_xH) imms
            then add_equation0 null
            else Some Or_bottom.Bottom
          | Relation.Is_int ->
            if Keyed.among Z.eqb Z0 imms
            then
              if Keyed.among Z.eqb (Zpos Coq_xH) imms
              then Some (Or_bottom.Ok env0)
              else add_equation0 any_block
            else if Keyed.among Z.eqb (Zpos Coq_xH) imms
            then add_equation0 any_tagged_immediate
            else Some Or_bottom.Bottom
          | Relation.Get_tag -> (
            let tags = Keyed.dedup Z.eqb (filter is_tag imms) in
            match
              type_of_get_tag_scrutinee_or_unknown choices tags
                Alloc_mode.Heap_or_local
            with
            | Or_unknown.Known shape -> add_equation0 shape
            | Or_unknown.Unknown -> Some (Or_bottom.Ok env0)))
        | Or_bottom.Bottom -> Some Or_bottom.Bottom)
      | None -> None
    in
    fold_left step inverse_relations0 (Some (Or_bottom.Ok env))
  | Or_unknown.Unknown -> Some (Or_bottom.Ok env)

(** val meet_head_of_kind_naked_immediate : meet_choices -> meet_expanded_head
    -> Meet_env.t -> head_of_kind_naked_immediate ->
    head_of_kind_naked_immediate -> head_of_kind_naked_immediate Meet_result.t
    option **)

let meet_head_of_kind_naked_immediate choices meet_expanded_head_rec env t1 t2 =
  match
    reduce_head_of_kind_naked_immediate (Meet_env.current_typing_env env) t1
  with
  | Or_bottom.Ok t3 -> (
    match
      reduce_head_of_kind_naked_immediate (Meet_env.current_typing_env env) t2
    with
    | Or_bottom.Ok t4 -> (
      match
        meet_unknown
          (fun env0 s1 s2 -> Some (set_meet Z.eqb (fun s -> s) env0 s1 s2))
          Keyed.is_empty env t3.naked_immediates t4.naked_immediates
      with
      | Some naked_immediates0 -> (
        match naked_immediates0 with
        | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
        | Meet_result.Ok (naked_immediates1, env0) -> (
          let inverse_relations0 =
            meet_inverse_relations t3.inverse_relations t4.inverse_relations
          in
          match
            sequence_return_value
              (combine_meet_return_values naked_immediates1
                 inverse_relations0.meet_return_value_of (fun _ ->
                   let naked_immediates2 =
                     extract_value naked_immediates1 t3.naked_immediates
                       t4.naked_immediates
                   in
                   let inverse_relations1 =
                     extract_value inverse_relations0.meet_return_value_of
                       t3.inverse_relations t4.inverse_relations
                   in
                   head_of_kind_naked_immediate_from_descr_non_empty
                     naked_immediates2 inverse_relations1))
          with
          | Some head0 -> (
            let head_in_env_or_bottom =
             fun env_ob ->
              match env_ob with
              | Or_bottom.Ok env1 -> Meet_result.Ok (head0, env1)
              | Or_bottom.Bottom -> Meet_result.Bottom (New_result ())
            in
            match naked_immediates1 with
            | Left_input ->
              option_map head_in_env_or_bottom
                (reduce_inverse_relations choices meet_expanded_head_rec env0
                   t3.naked_immediates inverse_relations0.right_inputs_only)
            | Right_input ->
              option_map head_in_env_or_bottom
                (reduce_inverse_relations choices meet_expanded_head_rec env0
                   t4.naked_immediates inverse_relations0.left_inputs_only)
            | Both_inputs -> Some (Meet_result.Ok (head0, env0))
            | New_result naked_immediates2 ->
              option_map head_in_env_or_bottom
                (reduce_inverse_relations choices meet_expanded_head_rec env0
                   naked_immediates2
                   (extract_value inverse_relations0.meet_return_value_of
                      t3.inverse_relations t4.inverse_relations)))
          | None -> None))
      | None -> None)
    | Or_bottom.Bottom -> Some (Meet_result.Bottom Right_input))
  | Or_bottom.Bottom -> (
    match
      reduce_head_of_kind_naked_immediate (Meet_env.current_typing_env env) t2
    with
    | Or_bottom.Ok _ -> Some (Meet_result.Bottom Left_input)
    | Or_bottom.Bottom -> Some (Meet_result.Bottom Both_inputs))

(** val meet_head_of_kind_naked_number : Meet_env.t -> coq_Z list -> coq_Z list
    -> coq_Z list Meet_result.t **)

let meet_head_of_kind_naked_number env t1 t2 =
  set_meet Z.eqb (fun s -> s) env t1 t2

(** val meet_head_of_kind_rec_info : Meet_env.t -> unit -> unit -> unit
    Meet_result.t **)

let meet_head_of_kind_rec_info env _ _ = Meet_result.Ok (Both_inputs, env)

(** val meet_head_of_kind_region : Meet_env.t -> unit -> unit -> unit
    Meet_result.t **)

let meet_head_of_kind_region env _ _ = Meet_result.Ok (Both_inputs, env)

(** val meet_variant : (meet_expanded_head -> Scope.t -> Meet_env.t ->
    Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
    meet_expanded_head -> Meet_env.t -> variable option -> variable option ->
    row_like_for_blocks Or_unknown.t -> flambda_type Or_unknown.t -> variable
    option -> variable option -> row_like_for_blocks Or_unknown.t ->
    flambda_type Or_unknown.t -> variant_extensions -> variant_extensions ->
    ((((variable option * variable option) * row_like_for_blocks Or_unknown.t) *
    flambda_type Or_unknown.t) * variant_extensions) Meet_result.t option **)

let meet_variant join choices meet_expanded_head_rec env is_int1 get_tag1
    blocks1 imms1 is_int2 get_tag2 blocks2 imms2 extensions1 extensions2 =
  let meet_a = meet_unknown (meet meet_expanded_head_rec) is_obviously_bottom in
  let meet_b =
   fun env0 left right ->
    combine_results2 env0
      (meet_relation meet_expanded_head_rec)
      (meet_unknown
         (meet_row_like_for_blocks join choices meet_expanded_head_rec)
         row_like_for_blocks_is_bottom)
      (fst left) (fst right) (snd left) (snd right)
      (fun get_tag blocks -> get_tag, blocks)
  in
  let bottom_a =
   fun _ -> Or_unknown.Known (bottom (Naked_number Kind_naked_immediate))
  in
  let bottom_b = fun _ -> None, Or_unknown.Known row_like_for_blocks_bottom in
  combine_results2 env
    (meet_relation meet_expanded_head_rec)
    (fun env0 left right ->
      let p, extensions3 = left in
      let p0, imms3 = p in
      let p1, extensions4 = right in
      let p2, imms4 = p1 in
      option_map
        (map_result (fun result ->
             let p3, extensions = result in
             let imms, p4 = p3 in
             (p4, imms), extensions))
        (meet_disjunction join choices meet_expanded_head_rec meet_a meet_b
           bottom_a bottom_b env0 imms3 p0 extensions3 imms4 p2 extensions4))
    is_int1 is_int2
    (((get_tag1, blocks1), imms1), extensions1)
    (((get_tag2, blocks2), imms2), extensions2)
    (fun is_int rest ->
      let p, extensions = rest in
      let p0, imms = p in
      let get_tag, blocks = p0 in
      (((is_int, get_tag), blocks), imms), extensions)

(** val meet_head_of_kind_value_non_null : (meet_expanded_head -> Scope.t ->
    Meet_env.t -> Typing_env.t -> Typing_env.t list -> Meet_env.t option) ->
    meet_choices -> meet_expanded_head -> Meet_env.t ->
    head_of_kind_value_non_null -> head_of_kind_value_non_null ->
    head_of_kind_value_non_null Meet_result.t option **)

let meet_head_of_kind_value_non_null join choices meet_expanded_head_rec env
    head1 head2 =
  match head1 with
  | Variant (is_int1, imms1, get_tag1, blocks, extensions1, is_unique1) -> (
    match head2 with
    | Variant (is_int2, imms2, get_tag2, blocks2, extensions2, is_unique2) ->
      let is_unique = is_unique1 || is_unique2 in
      option_map
        (map_result (fun result ->
             let p, extensions = result in
             let p0, immediates = p in
             let p1, blocks0 = p0 in
             let is_int, get_tag = p1 in
             Variant
               (is_int, immediates, get_tag, blocks0, extensions, is_unique)))
        (meet_variant join choices meet_expanded_head_rec env is_int1 get_tag1
           blocks imms1 is_int2 get_tag2 blocks2 imms2 extensions1 extensions2)
    | Mutable_block alloc_mode_right -> (
      match blocks with
      | Or_unknown.Known a -> (
        let (Row_like_for_blocks (_, _, alloc_mode_left)) = a in
        match meet_alloc_mode env alloc_mode_left alloc_mode_right with
        | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
        | Meet_result.Ok (r, env0) -> (
          match r with
          | Left_input ->
            Some
              (Meet_result.Ok (New_result (Mutable_block alloc_mode_left), env0))
          | New_result alloc_mode ->
            Some (Meet_result.Ok (New_result (Mutable_block alloc_mode), env0))
          | _ -> Some (Meet_result.Ok (Right_input, env0))))
      | Or_unknown.Unknown -> Some (Meet_result.Ok (Right_input, env)))
    | _ -> Some (Meet_result.Bottom (New_result ())))
  | Mutable_block alloc_mode_left -> (
    match head2 with
    | Variant (_, _, _, blocks, _, _) -> (
      match blocks with
      | Or_unknown.Known a -> (
        let (Row_like_for_blocks (_, _, alloc_mode_right)) = a in
        match meet_alloc_mode env alloc_mode_left alloc_mode_right with
        | Meet_result.Bottom r -> Some (Meet_result.Bottom r)
        | Meet_result.Ok (r, env0) -> (
          match r with
          | Right_input ->
            Some
              (Meet_result.Ok (New_result (Mutable_block alloc_mode_right), env0))
          | New_result alloc_mode ->
            Some (Meet_result.Ok (New_result (Mutable_block alloc_mode), env0))
          | _ -> Some (Meet_result.Ok (Left_input, env0))))
      | Or_unknown.Unknown -> Some (Meet_result.Ok (Left_input, env)))
    | Mutable_block alloc_mode2 ->
      Some
        (map_result
           (fun x -> Mutable_block x)
           (meet_alloc_mode env alloc_mode_left alloc_mode2))
    | _ -> Some (Meet_result.Bottom (New_result ())))
  | Boxed_number (k1, n1, alloc_mode1) -> (
    match head2 with
    | Boxed_number (k2, n2, alloc_mode2) ->
      if boxable_number_eqb k1 k2
      then
        combine_results2 env
          (meet meet_expanded_head_rec)
          (fun env0 alloc_mode3 alloc_mode4 ->
            Some (meet_alloc_mode env0 alloc_mode3 alloc_mode4))
          n1 n2 alloc_mode1 alloc_mode2
          (fun x x0 -> Boxed_number (k1, x, x0))
      else Some (Meet_result.Bottom (New_result ()))
    | _ -> Some (Meet_result.Bottom (New_result ())))
  | Closures (by_function_slot1, alloc_mode1) -> (
    match head2 with
    | Closures (by_function_slot2, alloc_mode2) ->
      combine_results2 env
        (meet_row_like_for_closures join choices meet_expanded_head_rec)
        (fun env0 alloc_mode3 alloc_mode4 ->
          Some (meet_alloc_mode env0 alloc_mode3 alloc_mode4))
        by_function_slot1 by_function_slot2 alloc_mode1 alloc_mode2
        (fun x x0 -> Closures (x, x0))
    | _ -> Some (Meet_result.Bottom (New_result ())))
  | String strs1 -> (
    match head2 with
    | String strs2 ->
      Some
        (map_result
           (fun x -> String x)
           (set_meet (lists_eqb Z.eqb) (fun s -> s) env strs1 strs2))
    | _ -> Some (Meet_result.Bottom (New_result ())))

(** val meet_head_of_kind_value : (meet_expanded_head -> Scope.t -> Meet_env.t
    -> Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices
    -> meet_expanded_head -> Meet_env.t -> head_of_kind_value ->
    head_of_kind_value -> head_of_kind_value Meet_result.t option **)

let meet_head_of_kind_value join choices meet_expanded_head_rec env head1 head2
    =
  let (Head_of_kind_value (non_null1, is_null1)) = head1 in
  let (Head_of_kind_value (non_null2, is_null2)) = head2 in
  let meet_a =
    let meet_elt =
     fun env0 elt1 elt2 ->
      option_map
        (map_result (fun x -> Ok x))
        (meet_head_of_kind_value_non_null join choices meet_expanded_head_rec
           env0 elt1 elt2)
    in
    meet_or_unknown_or_bottom meet_elt
  in
  let meet_b =
   fun env0 is_null3 is_null4 ->
    match is_null3 with
    | Not_null -> (
      match is_null4 with
      | Not_null -> Some (Meet_result.Bottom Both_inputs)
      | Maybe_null _ -> Some (Meet_result.Bottom Left_input))
    | Maybe_null is_null5 -> (
      match is_null4 with
      | Not_null -> Some (Meet_result.Bottom Right_input)
      | Maybe_null is_null6 ->
        option_map
          (map_result (fun x -> Maybe_null x))
          (meet_relation meet_expanded_head_rec env0 is_null5 is_null6))
  in
  let bottom_a = fun _ -> Bottom in
  let bottom_b = fun _ -> Not_null in
  option_map
    (map_result (fun result ->
         let p, _ = result in
         let non_null, is_null = p in
         Head_of_kind_value (non_null, is_null)))
    (meet_disjunction join choices meet_expanded_head_rec meet_a meet_b bottom_a
       bottom_b env non_null1 is_null1 No_extensions non_null2 is_null2
       No_extensions)

(** val meet_expanded_head0 : (meet_expanded_head -> Scope.t -> Meet_env.t ->
    Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
    meet_expanded_head -> Meet_env.t -> Expanded_type.head -> Expanded_type.head
    -> Expanded_type.t Meet_result.t option **)

let meet_expanded_head0 join choices meet_expanded_head_rec env descr1 descr2 =
  match descr1 with
  | Expanded_type.Head_value head1 -> (
    match descr2 with
    | Expanded_type.Head_value head2 ->
      option_map
        (map_result Expanded_type.create_value)
        (meet_head_of_kind_value join choices meet_expanded_head_rec env head1
           head2)
    | _ -> None)
  | Expanded_type.Head_naked_immediate head1 -> (
    match descr2 with
    | Expanded_type.Head_naked_immediate head2 ->
      option_map
        (map_result Expanded_type.create_naked_immediate)
        (meet_head_of_kind_naked_immediate choices meet_expanded_head_rec env
           head1 head2)
    | _ -> None)
  | Expanded_type.Head_naked_number (k1, head1) -> (
    match descr2 with
    | Expanded_type.Head_naked_number (k2, head2) ->
      if naked_number_kind_eqb k1 k2
      then
        Some
          (map_result
             (Expanded_type.create_naked_number k1)
             (meet_head_of_kind_naked_number env head1 head2))
      else None
    | _ -> None)
  | Expanded_type.Head_rec_info head1 -> (
    match descr2 with
    | Expanded_type.Head_rec_info head2 ->
      Some
        (map_result Expanded_type.create_rec_info
           (meet_head_of_kind_rec_info env head1 head2))
    | _ -> None)
  | Expanded_type.Head_region head1 -> (
    match descr2 with
    | Expanded_type.Head_region head2 ->
      Some
        (map_result Expanded_type.create_region
           (meet_head_of_kind_region env head1 head2))
    | _ -> None)

(** val meet_expanded_head_step : (meet_expanded_head -> Scope.t -> Meet_env.t
    -> Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices
    -> meet_expanded_head -> meet_expanded_head **)

let meet_expanded_head_step join choices meet_expanded_head_rec env expanded1
    expanded2 =
  meet_or_unknown_or_bottom
    (meet_expanded_head0 join choices meet_expanded_head_rec)
    env expanded1.Expanded_type.descr expanded2.Expanded_type.descr

module Meet = struct
  (** val meet_expanded_head : (meet_expanded_head -> Scope.t -> Meet_env.t ->
      Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
      nat -> meet_expanded_head **)

  let rec meet_expanded_head join choices = function
    | O -> fun _ _ _ -> None
    | S fuel0 ->
      meet_expanded_head_step join choices
        (meet_expanded_head join choices fuel0)

  (** val meet : (meet_expanded_head -> Scope.t -> Meet_env.t -> Typing_env.t ->
      Typing_env.t list -> Meet_env.t option) -> meet_choices -> nat ->
      Typing_env.t -> flambda_type -> flambda_type -> (flambda_type *
      Typing_env.t) Or_bottom.t option **)

  let meet join choices fuel env ty1 ty2 =
    if env.Typing_env.is_bottom
    then Some Or_bottom.Bottom
    else
      match
        Meet_env.meet_type (Meet_env.create env) ty1 ty2
          (meet_expanded_head join choices fuel)
      with
      | Some result -> (
        match result with
        | Meet_result.Bottom _ -> Some Or_bottom.Bottom
        | Meet_result.Ok (r, env0) -> (
          let res_ty = extract_value r ty1 ty2 in
          if is_obviously_bottom res_ty
          then Some Or_bottom.Bottom
          else
            match Meet_env.final_typing_env_strict env0 with
            | Or_bottom.Ok env1 -> Some (Or_bottom.Ok (res_ty, env1))
            | Or_bottom.Bottom -> Some Or_bottom.Bottom))
      | None -> None
end

module Flambda2_types = struct
  (** val add_equation : (meet_expanded_head -> Scope.t -> Meet_env.t ->
      Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
      nat -> Typing_env.t -> name -> flambda_type -> Typing_env.t option **)

  let add_equation join choices fuel =
    let meet_expanded_head1 = Meet.meet_expanded_head join choices fuel in
    fun tenv name0 ty ->
      Meet_env.use_meet_env tenv (fun env ->
          Meet_env.add_equation env name0 ty meet_expanded_head1)

  (** val add_relation : (meet_expanded_head -> Scope.t -> Meet_env.t ->
      Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
      nat -> Typing_env.t -> name -> simple -> flambda_type -> (variable ->
      head_of_kind_value) -> Typing_env.t option **)

  let add_relation join choices fuel =
    let meet_expanded_head1 = Meet.meet_expanded_head join choices fuel in
    fun tenv name0 scrutinee name_ty scrutinee_head ->
      Meet_env.use_meet_env tenv (fun env ->
          match Meet_env.add_equation env name0 name_ty meet_expanded_head1 with
          | Some env0 -> (
            match name0 with
            | Name_var var ->
              Meet_env.add_equation_on_simple env0 scrutinee
                (Type_value (Ok (No_alias (scrutinee_head var))))
                meet_expanded_head1
            | Name_symbol _ -> Some env0)
          | None -> None)

  (** val is_null_of_simple : simple -> flambda_type **)

  let is_null_of_simple = function
    | Var x -> is_null_for_scrutinee (Name_var x)
    | Symbol s -> is_null_for_scrutinee (Name_symbol s)
    | Const c -> (
      match c with
      | Null -> this_naked_immediate (Zpos Coq_xH)
      | _ -> this_naked_immediate Z0)

  (** val is_int_of_simple : simple -> flambda_type **)

  let is_int_of_simple = function
    | Var x -> is_int_for_scrutinee (Name_var x)
    | Symbol s -> is_int_for_scrutinee (Name_symbol s)
    | Const _ -> this_naked_immediate (Zpos Coq_xH)

  (** val get_tag_of_simple : simple -> flambda_type **)

  let get_tag_of_simple = function
    | Var x -> get_tag_for_block (Name_var x)
    | Symbol s -> get_tag_for_block (Name_symbol s)
    | Const _ -> unknown (Naked_number Kind_naked_immediate)

  (** val add_is_null_relation : (meet_expanded_head -> Scope.t -> Meet_env.t ->
      Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
      nat -> Typing_env.t -> name -> simple -> Typing_env.t option **)

  let add_is_null_relation join choices fuel tenv name0 scrutinee =
    add_relation join choices fuel tenv name0 scrutinee
      (is_null_of_simple scrutinee) (fun var ->
        Head_of_kind_value (Unknown, Maybe_null (Some var)))

  (** val add_is_int_relation : (meet_expanded_head -> Scope.t -> Meet_env.t ->
      Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
      nat -> Typing_env.t -> name -> simple -> Typing_env.t option **)

  let add_is_int_relation join choices fuel tenv name0 scrutinee =
    add_relation join choices fuel tenv name0 scrutinee
      (is_int_of_simple scrutinee) (fun var ->
        Head_of_kind_value
          ( Ok
              (Variant
                 ( Some var,
                   Or_unknown.Unknown,
                   None,
                   Or_unknown.Unknown,
                   No_extensions,
                   false )),
            Not_null ))

  (** val add_get_tag_relation : (meet_expanded_head -> Scope.t -> Meet_env.t ->
      Typing_env.t -> Typing_env.t list -> Meet_env.t option) -> meet_choices ->
      nat -> Typing_env.t -> name -> simple -> Typing_env.t option **)

  let add_get_tag_relation join choices fuel tenv name0 scrutinee =
    add_relation join choices fuel tenv name0 scrutinee
      (get_tag_of_simple scrutinee) (fun var ->
        Head_of_kind_value
          ( Ok
              (Variant
                 ( None,
                   Or_unknown.Unknown,
                   Some var,
                   Or_unknown.Unknown,
                   No_extensions,
                   false )),
            Not_null ))
end
