open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBlockLoadSpec
open FlambdaCompareSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaSemanticsSpec
open FlambdaUnboxParamsSpec
open FlambdaUnboxSpec
open FlambdaUnusedContsSpec
open List
open ListDef
open Nat
open OxCamlOption

(** val dummy_of : bool -> unary_primitive -> flambda_kind -> const **)

let dummy_of variant p kind =
  match p with
  | Is_int _ ->
    if kind_eqb kind (Naked_number Kind_naked_immediate)
    then Naked_immediate Z0
    else Poison kind
  | Get_tag ->
    if kind_eqb kind (Naked_number Kind_naked_immediate)
    then Naked_immediate Z0
    else Poison kind
  | Untag_immediate ->
    if variant && kind_eqb kind (Naked_number Kind_naked_immediate)
    then Naked_immediate Z0
    else Poison kind
  | _ -> Poison kind

(** val no_value_on : facts -> unary_primitive -> simple -> bool **)

let no_value_on known p arg =
  match p with
  | Block_load (_, _, _) -> ( match arg with Const _ -> true | _ -> false)
  | Get_tag -> ( match arg with Const _ -> true | _ -> false)
  | Untag_immediate -> (
    match arg with
    | Var y -> is_bound y known.facts_blocks.known_vars
    | Symbol _ -> true
    | Const _ -> false)
  | _ -> false

(** val made_field : facts -> unary_primitive -> flambda_kind -> simple ->
    simple option **)

let made_field known p kind arg =
  match p with
  | Block_load (access, mut, field) -> (
    match mut with
    | Mutable -> None
    | _ -> (
      match arg with
      | Var y -> (
        match lookup y known.facts_blocks.known_vars with
        | Some block -> (
          match field_loaded access field block with
          | Some contents -> if kind_eqb kind Value then Some contents else None
          | None -> None)
        | None -> None)
      | _ -> None))
  | _ -> None

(** val made_number : facts -> unary_primitive -> flambda_kind -> simple ->
    simple option **)

let made_number known p kind arg =
  match p with
  | Unbox_number boxed -> (
    match arg with
    | Var y -> (
      match unwrapped known.facts_numbers (Boxed boxed) (Var y) with
      | Some contents ->
        if kind_eqb kind (unboxed_kind boxed) then Some contents else None
      | None -> None)
    | _ -> None)
  | Untag_immediate -> (
    match arg with
    | Var y -> (
      match unwrapped known.facts_numbers Tagged (Var y) with
      | Some contents ->
        if kind_eqb kind (Naked_number Kind_naked_immediate)
        then Some contents
        else None
      | None -> None)
    | _ -> None)
  | _ -> None

(** val certain_projection : facts -> unary_primitive -> flambda_kind -> simple
    -> simple option **)

let certain_projection known p kind arg =
  match projection_of known p arg with
  | Some s -> (
    match s with
    | Const c ->
      if kind_eqb (kind_of_const c) kind then Some (Const c) else None
    | _ -> (
      match made_field known p kind arg with
      | Some contents -> Some contents
      | None -> made_number known p kind arg))
  | None -> (
    match made_field known p kind arg with
    | Some contents -> Some contents
    | None -> made_number known p kind arg)

(** val known_immediates : variable list -> simple list -> (variable * coq_Z)
    list **)

let rec known_immediates params args =
  match params with
  | [] -> []
  | param :: params0 -> (
    match args with
    | [] -> []
    | s :: args0 -> (
      match s with
      | Const c -> (
        match c with
        | Naked_immediate i -> (param, i) :: known_immediates params0 args0
        | _ -> known_immediates params0 args0)
      | _ -> known_immediates params0 args0))

(** val forget_immediates : variable list -> (variable * coq_Z) list ->
    (variable * coq_Z) list **)

let forget_immediates bound consts =
  filter (fun entry -> negb (among (fst entry) bound)) consts

(** val take_arms : (variable * coq_Z) list -> expr -> expr **)

let rec take_arms consts e =
  match e with
  | Let (y, kind, d, body) ->
    Let (y, kind, d, take_arms (forget_immediates (y :: []) consts) body)
  | Let_static (bindings, body) -> Let_static (bindings, take_arms consts body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (handler_params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler
          ( handler_params,
            metadata,
            take_arms (forget_immediates handler_params consts) handler ),
        take_arms consts body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, take_arms consts body)
  | Switch (scrutinee, arms) -> (
    match scrutinee with
    | Var t -> (
      match lookup t consts with
      | Some i -> (
        match find_arm i arms with Some ac -> Apply_cont ac | None -> e)
      | None -> e)
    | _ -> e)
  | _ -> e

(** val never_reads : (variable * coq_Z) list -> expr -> expr -> bool **)

let never_reads consts handler without =
  expr_eqb [] []
    (remove_unused_conts (take_arms consts handler))
    (remove_unused_conts (take_arms consts without))

(** val only_of : variable list -> (variable * coq_Z) list -> (variable * coq_Z)
    list **)

let only_of tests consts = filter (fun entry -> among (fst entry) tests) consts

(** val extend_args_certain : bool -> variable list -> variable list -> expr ->
    expr -> facts -> nat -> unary_primitive -> flambda_kind -> simple list ->
    simple list option **)

let extend_args_certain variant tests params handler without known i p kind args
    =
  match nth_error args i with
  | Some arg -> (
    if
      never_reads (only_of tests (known_immediates params args)) handler without
    then Some (app args (Const (dummy_of variant p kind) :: []))
    else
      match certain_projection known p kind arg with
      | Some projection -> Some (app args (projection :: []))
      | None ->
        if no_value_on known p arg
        then Some (app args (Const (dummy_of variant p kind) :: []))
        else None)
  | None -> None

type read =
  { read_variable : variable;
    read_kind : flambda_kind;
    read_primitive : unary_primitive;
    read_position : nat;
    read_without : expr
  }

(** val reads_tag : unary_primitive -> bool **)

let reads_tag = function Get_tag -> true | _ -> false

(** val reads_constant_constructor : unary_primitive -> bool **)

let reads_constant_constructor = function Untag_immediate -> true | _ -> false

(** val reads_is_int : unary_primitive -> bool **)

let reads_is_int = function Is_int _ -> true | _ -> false

(** val reads_contents : unary_primitive -> bool **)

let reads_contents = function
  | Block_load (_, _, _) -> true
  | Unbox_number _ -> true
  | _ -> false

(** val reads_any : unary_primitive -> bool **)

let reads_any _ = true

(** val param_read : (unary_primitive -> bool) -> variable list -> variable list
    -> variable -> named -> (unary_primitive * nat) option **)

let param_read wanted params bound f = function
  | Prim (p0, args) -> (
    match p0 with
    | Unary p -> (
      match args with
      | [] -> None
      | s :: l -> (
        match s with
        | Var x -> (
          match l with
          | [] ->
            if
              ((wanted p && reads_a_box p) && negb (among x bound))
              && negb (among f bound)
            then option_map (fun i -> p, i) (position x params)
            else None
          | _ :: _ -> None)
        | _ -> None))
    | _ -> None)
  | _ -> None

(** val head_read : variable list -> expr -> read option **)

let head_read params = function
  | Let (f, kind, d, rest) -> (
    match param_read reads_any params [] f d with
    | Some p ->
      let p0, i = p in
      Some
        { read_variable = f;
          read_kind = kind;
          read_primitive = p0;
          read_position = i;
          read_without = rest
        }
    | None -> None)
  | _ -> None

(** val load_read : named -> (variable * coq_Z) option **)

let load_read = function
  | Prim (p, args) -> (
    match p with
    | Unary p0 -> (
      match p0 with
      | Block_load (_, _, field) -> (
        match args with
        | [] -> None
        | s :: l -> (
          match s with
          | Var x -> ( match l with [] -> Some (x, field) | _ :: _ -> None)
          | _ -> None))
      | _ -> None)
    | _ -> None)
  | _ -> None

(** val loads_above : coq_Z -> unary_primitive -> bool **)

let loads_above field = function
  | Block_load (_, _, field') -> Z.ltb field field'
  | _ -> false

(** val first_read : (unary_primitive -> bool) -> variable list -> variable list
    -> expr -> read option **)

let rec first_read wanted params bound = function
  | Let (y, kind, d, body) -> (
    match param_read wanted params bound y d with
    | Some p0 -> (
      let p, i = p0 in
      match
        match load_read d with
        | Some p1 ->
          let x, field = p1 in
          first_read (loads_above field) (x :: []) (y :: bound) body
        | None -> None
      with
      | Some r ->
        Some
          { read_variable = r.read_variable;
            read_kind = r.read_kind;
            read_primitive = r.read_primitive;
            read_position = i;
            read_without = Let (y, kind, d, r.read_without)
          }
      | None ->
        Some
          { read_variable = y;
            read_kind = kind;
            read_primitive = p;
            read_position = i;
            read_without = body
          })
    | None -> (
      match first_read wanted params (y :: bound) body with
      | Some r ->
        Some
          { read_variable = r.read_variable;
            read_kind = r.read_kind;
            read_primitive = r.read_primitive;
            read_position = r.read_position;
            read_without = Let (y, kind, d, r.read_without)
          }
      | None -> None))
  | Let_cont_non_recursive (k, handler0, body) -> (
    let (Handler (handler_params, metadata, handler)) = handler0 in
    match first_read wanted params bound body with
    | Some r ->
      Some
        { read_variable = r.read_variable;
          read_kind = r.read_kind;
          read_primitive = r.read_primitive;
          read_position = r.read_position;
          read_without =
            Let_cont_non_recursive
              (k, Handler (handler_params, metadata, handler), r.read_without)
        }
    | None -> (
      match first_read wanted params (app handler_params bound) handler with
      | Some r ->
        Some
          { read_variable = r.read_variable;
            read_kind = r.read_kind;
            read_primitive = r.read_primitive;
            read_position = r.read_position;
            read_without =
              Let_cont_non_recursive
                (k, Handler (handler_params, metadata, r.read_without), body)
          }
      | None -> None))
  | _ -> None

(** val next_read : variable list -> expr -> read option **)

let next_read params handler =
  match first_read reads_tag params [] handler with
  | Some r -> Some r
  | None -> (
    match first_read reads_constant_constructor params [] handler with
    | Some r -> Some r
    | None -> (
      match first_read reads_is_int params [] handler with
      | Some r -> Some r
      | None -> first_read reads_contents params [] handler))

(** val lets_in : expr -> nat **)

let rec lets_in = function
  | Let (_, _, _, body) -> S (lets_in body)
  | Let_cont_non_recursive (_, handler0, body) ->
    let (Handler (_, _, handler)) = handler0 in
    add (lets_in handler) (lets_in body)
  | _ -> O

(** val unbox_read : (facts -> simple list -> simple list option) -> facts ->
    continuation -> variable list -> handler_metadata -> expr -> expr -> read ->
    (((variable list * handler_metadata) * expr) * expr) option **)

let unbox_read extend known k params metadata handler body r =
  if
    may_take params metadata r.read_variable
    && negb (var_free_b r.read_variable handler)
  then
    match extend_applications_by extend known k body with
    | Some body0 ->
      Some
        ( ( ( app params (r.read_variable :: []),
              with_one_more metadata r.read_kind ),
            r.read_without ),
          body0 )
    | None -> None
  else None

(** val tested_is_int : variable list -> nat -> expr -> bool **)

let tested_is_int params i handler =
  match nth_error params i with
  | Some param -> is_some (first_read reads_is_int (param :: []) [] handler)
  | None -> false

(** val reads_test : unary_primitive -> bool **)

let reads_test p =
  (reads_tag p || reads_constant_constructor p) || reads_is_int p

(** val boxes_of : nat -> (nat * nat list) list -> nat list **)

let rec boxes_of i = function
  | [] -> i :: []
  | p :: above0 ->
    let j, boxes = p in
    if PeanoNat.Nat.eqb i j then boxes else boxes_of i above0

(** val tests_of : nat -> (variable * nat) list -> (nat * nat list) list ->
    variable list **)

let tests_of i made above =
  map fst
    (filter
       (fun entry -> existsb (PeanoNat.Nat.eqb (snd entry)) (boxes_of i above))
       made)

(** val tags_at_apply_cont : (facts -> simple list -> coq_Z list) -> facts ->
    continuation -> apply_cont -> coq_Z list **)

let tags_at_apply_cont tag_of known k ac =
  if Pos.eqb ac.ac_continuation k then tag_of known ac.ac_args else []

(** val tags_given : (facts -> simple list -> coq_Z list) -> facts ->
    continuation -> expr -> coq_Z list **)

let rec tags_given tag_of known k = function
  | Let (x, _, d, body) -> tags_given tag_of (facts_under_let known x d) k body
  | Let_static (bindings, body) ->
    tags_given tag_of (facts_under_statics known bindings) k body
  | Let_cont_non_recursive (k', h, body) ->
    app
      (tags_given_in_handler tag_of known k h)
      (if Pos.eqb k' k then [] else tags_given tag_of known k body)
  | Let_cont_recursive (handlers, body) ->
    if is_bound k handlers
    then []
    else
      app
        (flat_map
           (fun pat ->
             let _, h = pat in
             tags_given_in_handler tag_of known k h)
           handlers)
        (tags_given tag_of known k body)
  | Apply_cont ac -> tags_at_apply_cont tag_of known k ac
  | Switch (_, arms) ->
    flat_map
      (fun pat ->
        let _, ac = pat in
        tags_at_apply_cont tag_of known k ac)
      arms
  | _ -> []

(** val tags_given_in_handler : (facts -> simple list -> coq_Z list) -> facts ->
    continuation -> continuation_handler -> coq_Z list **)

and tags_given_in_handler tag_of known k = function
  | Handler (params, _, handler) ->
    tags_given tag_of (facts_under_params known params) k handler

(** val tag_read : variable list -> variable list -> expr -> expr -> nat ->
    facts -> simple list -> coq_Z list **)

let tag_read tests params handler without i known args =
  match nth_error args i with
  | Some arg -> (
    if
      never_reads (only_of tests (known_immediates params args)) handler without
    then []
    else
      match known_block_of known.facts_blocks arg with
      | Some block -> fst block :: []
      | None -> [])
  | None -> []

(** val all_same : coq_Z list -> bool **)

let all_same = function [] -> true | tag :: tags0 -> forallb (Z.eqb tag) tags0

(** val reads_field : unary_primitive -> bool **)

let reads_field = function Block_load (_, _, _) -> true | _ -> false

(** val loads_of_two_tags : facts -> continuation -> variable list -> variable
    list -> expr -> expr -> read -> bool **)

let loads_of_two_tags known k tests params handler body r =
  reads_field r.read_primitive
  && negb
       (all_same
          (tags_given
             (tag_read tests params handler r.read_without r.read_position)
             known k body))

(** val unbox_reads : nat -> facts -> continuation -> (variable * nat) list ->
    (nat * nat list) list -> variable list -> handler_metadata -> expr -> expr
    -> expr **)

let rec unbox_reads fuel known k made above params metadata handler body =
  let unchanged =
    Let_cont_non_recursive (k, Handler (params, metadata, handler), body)
  in
  match fuel with
  | O -> unchanged
  | S fuel0 -> (
    let certain =
     fun r ->
      unbox_read
        (fun known0 ->
          extend_args_certain
            (tested_is_int params r.read_position handler)
            (tests_of r.read_position made above)
            params handler r.read_without known0 r.read_position
            r.read_primitive r.read_kind)
        known k params metadata handler body r
    in
    match next_read params handler with
    | Some r -> (
      if
        loads_of_two_tags known k
          (tests_of r.read_position made above)
          params handler body r
      then unchanged
      else
        let step =
          match head_read params handler with
          | Some head ->
            if Pos.eqb head.read_variable r.read_variable
            then
              unbox_read
                (fun known0 ->
                  extend_args known0 head.read_position head.read_primitive)
                known k params metadata handler body head
            else certain r
          | None -> certain r
        in
        match step with
        | Some p ->
          let p0, body0 = p in
          let p1, handler0 = p0 in
          let params', metadata0 = p1 in
          unbox_reads fuel0 known k
            (if reads_test r.read_primitive
             then (r.read_variable, r.read_position) :: made
             else made)
            ((length params, length params :: boxes_of r.read_position above)
            :: above)
            params' metadata0 handler0 body0
        | None -> unchanged)
    | None -> unchanged)

(** val unbox_variants_knowing : facts -> expr -> expr **)

let rec unbox_variants_knowing known e =
  match e with
  | Let (x, kind, d, body) ->
    Let (x, kind, d, unbox_variants_knowing (facts_under_let known x d) body)
  | Let_static (bindings, body) ->
    Let_static
      ( bindings,
        unbox_variants_knowing (facts_under_statics known bindings) body )
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    let handler1 =
      unbox_variants_knowing (facts_under_params known params) handler
    in
    unbox_reads (lets_in handler1) known k [] [] params metadata handler1
      (unbox_variants_knowing known body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, unbox_variants_knowing known body)
  | _ -> e
