open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List
open ListDef

type known_block = coq_Z * simple option list

type known_blocks =
  { known_vars : (variable * known_block) list;
    known_symbols : (symbol * known_block) list
  }

(** val no_blocks : known_blocks **)

let no_blocks = { known_vars = []; known_symbols = [] }

(** val forget_field : variable -> simple option -> simple option **)

let forget_field x field =
  match field with
  | Some s -> if var_in_simple x s then None else field
  | None -> None

(** val forget_in_block : variable -> known_block -> known_block **)

let forget_in_block x block = fst block, map (forget_field x) (snd block)

(** val forget_var : variable -> known_blocks -> known_blocks **)

let forget_var x known =
  { known_vars =
      map
        (fun entry -> fst entry, forget_in_block x (snd entry))
        (filter (fun entry -> negb (Pos.eqb x (fst entry))) known.known_vars);
    known_symbols =
      map
        (fun entry -> fst entry, forget_in_block x (snd entry))
        known.known_symbols
  }

(** val forget_vars : variable list -> known_blocks -> known_blocks **)

let rec forget_vars xs known =
  match xs with [] -> known | x :: xs0 -> forget_vars xs0 (forget_var x known)

(** val block_made : named -> known_block option **)

let block_made = function
  | Prim (p, fields) -> (
    match p with
    | Variadic p0 ->
      let (Make_block kind) = p0 in
      let (Block_kind_values tag) = kind in
      Some (tag, map (fun x -> Some x) fields)
    | _ -> None)
  | _ -> None

(** val known_under_let : known_blocks -> variable -> named -> known_blocks **)

let known_under_let known x d =
  let known0 = forget_var x known in
  match block_made d with
  | Some block ->
    { known_vars = (x, forget_in_block x block) :: known0.known_vars;
      known_symbols = known0.known_symbols
    }
  | None -> known0

(** val static_block_made : static_binding -> (symbol * known_block) list **)

let static_block_made = function
  | Bind_symbol (s, const) -> (
    match const with
    | Static_const_block (tag, fields) ->
      (s, (tag, map (fun x -> Some x) fields)) :: []
    | _ -> [])
  | _ -> []

(** val known_under_statics : known_blocks -> static_binding list ->
    known_blocks **)

let known_under_statics known bindings =
  { known_vars = known.known_vars;
    known_symbols =
      app (flat_map static_block_made bindings) known.known_symbols
  }

(** val known_block_of : known_blocks -> simple -> known_block option **)

let known_block_of known = function
  | Var x -> lookup x known.known_vars
  | Symbol sym -> lookup sym known.known_symbols
  | Const _ -> None

(** val field_loaded : block_access_kind -> coq_Z -> known_block -> simple
    option **)

let field_loaded kind field block =
  let (Block_access_values (tag, size, field_kind)) = kind in
  match field_kind with
  | Any_value ->
    if
      (known_is tag (fst block) && known_is size (Z.of_nat (length (snd block))))
      && Z.leb Z0 field
    then
      match nth_error (snd block) (Z.to_nat field) with
      | Some o -> o
      | None -> None
    else None
  | Immediate -> None

(** val of_known_block : unary_primitive -> known_block -> simple option **)

let of_known_block p block =
  match p with
  | Block_load (kind, field) -> field_loaded kind field block
  | Is_int _ -> Some (Const (Naked_immediate Z0))
  | Get_tag -> Some (Const (Naked_immediate (fst block)))
  | _ -> None

(** val unary_applied : prim -> simple list -> (unary_primitive * simple) option
    **)

let unary_applied p args =
  match p with
  | Unary p0 -> (
    match args with
    | [] -> None
    | arg :: l -> ( match l with [] -> Some (p0, arg) | _ :: _ -> None))
  | _ -> None

(** val load_known_named : known_blocks -> named -> named **)

let load_known_named known d =
  match d with
  | Prim (p, args) -> (
    match unary_applied p args with
    | Some p0 -> (
      let p1, block = p0 in
      match known_block_of known block with
      | Some known_block0 -> (
        match of_known_block p1 known_block0 with
        | Some result -> Simple result
        | None -> d)
      | None -> d)
    | None -> d)
  | _ -> d

(** val load_blocks_knowing : known_blocks -> expr -> expr **)

let rec load_blocks_knowing known e =
  match e with
  | Let (x, d, body) ->
    Let
      ( x,
        load_known_named known d,
        load_blocks_knowing (known_under_let known x d) body )
  | Let_static (bindings, body) ->
    Let_static
      (bindings, load_blocks_knowing (known_under_statics known bindings) body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, load_blocks_in_handler known h, load_blocks_knowing known body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, load_blocks_knowing known body)
  | _ -> e

(** val load_blocks_in_handler : known_blocks -> continuation_handler ->
    continuation_handler **)

and load_blocks_in_handler known = function
  | Handler (params, handler) ->
    Handler (params, load_blocks_knowing (forget_vars params known) handler)

(** val load_known_blocks : expr -> expr **)

let load_known_blocks e = load_blocks_knowing no_blocks e
