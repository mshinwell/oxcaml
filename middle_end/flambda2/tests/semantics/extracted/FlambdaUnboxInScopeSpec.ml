open Datatypes
open FlambdaBlockLoadSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnboxParamsSpec
open FlambdaUnboxSpec
open ListDef

(** val closed_field : simple option -> simple option **)

let closed_field field =
  match field with
  | Some s -> ( match s with Var _ -> None | _ -> field)
  | None -> None

(** val facts_of_symbols : facts -> facts **)

let facts_of_symbols known =
  { facts_blocks =
      { known_vars = [];
        known_symbols =
          map
            (fun entry ->
              fst entry, (fst (snd entry), map closed_field (snd (snd entry))))
            known.facts_blocks.known_symbols
      };
    facts_numbers =
      { known_wrapped_vars = [];
        known_boxed_symbols = known.facts_numbers.known_boxed_symbols
      }
  }

(** val symbols_under_statics : facts -> static_binding list -> facts **)

let symbols_under_statics known bindings =
  facts_of_symbols (facts_under_statics known bindings)

(** val rewrite_code_in_scope : (facts -> expr -> expr) -> facts -> expr -> expr
    **)

let rec rewrite_code_in_scope f known e =
  match e with
  | Let (x, kind, d, body) ->
    Let (x, kind, d, rewrite_code_in_scope f known body)
  | Let_static (bindings, body) ->
    let known0 = symbols_under_statics known bindings in
    Let_static
      ( map (rewrite_code_in_binding (f known0)) bindings,
        rewrite_code_in_scope f known0 body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        rewrite_code_in_scope_in_handler f known h,
        rewrite_code_in_scope f known body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, rewrite_code_in_scope_in_handler f known h)
          handlers,
        rewrite_code_in_scope f known body )
  | _ -> e

(** val rewrite_code_in_scope_in_handler : (facts -> expr -> expr) -> facts ->
    continuation_handler -> continuation_handler **)

and rewrite_code_in_scope_in_handler f known = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, rewrite_code_in_scope f known handler)

(** val rewrite_rec_handlers_in_scope : (facts -> expr -> expr) -> facts -> expr
    -> expr **)

let rec rewrite_rec_handlers_in_scope f known e =
  match e with
  | Let (x, kind, d, body) ->
    Let (x, kind, d, rewrite_rec_handlers_in_scope f known body)
  | Let_static (bindings, body) ->
    Let_static
      ( bindings,
        rewrite_rec_handlers_in_scope f
          (symbols_under_statics known bindings)
          body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        rewrite_rec_handlers_in_scope_in_handler f known h,
        rewrite_rec_handlers_in_scope f known body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, rewrite_rec_handler_in_scope f known h)
          handlers,
        rewrite_rec_handlers_in_scope f known body )
  | _ -> e

(** val rewrite_rec_handlers_in_scope_in_handler : (facts -> expr -> expr) ->
    facts -> continuation_handler -> continuation_handler **)

and rewrite_rec_handlers_in_scope_in_handler f known = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, rewrite_rec_handlers_in_scope f known handler)

(** val rewrite_rec_handler_in_scope : (facts -> expr -> expr) -> facts ->
    continuation_handler -> continuation_handler **)

and rewrite_rec_handler_in_scope f known = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        rewrite_code_body (f known)
          (rewrite_rec_handlers_in_scope f known handler) )
