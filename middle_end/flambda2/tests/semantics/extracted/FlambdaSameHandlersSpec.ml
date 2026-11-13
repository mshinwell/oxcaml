open BinPos
open Datatypes
open FlambdaCompareSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaUnusedContsSpec
open List
open ListDef

(** val may_be_static : named -> bool **)

let may_be_static = function
  | Prim (p, _) -> (
    match p with
    | Unary p0 -> ( match p0 with Box_number _ -> true | _ -> false)
    | Variadic _ -> true
    | _ -> false)
  | Set_of_closures (_, _) -> true
  | Closure_of_set (_, _, _) -> true
  | _ -> false

(** val straight : nat -> expr -> bool **)

let rec straight lets = function
  | Let (_, _, d, body) -> (
    if may_be_static d
    then false
    else match lets with O -> false | S lets0 -> straight lets0 body)
  | Apply_cont ac -> no_trap_action ac
  | _ -> false

(** val sharable : continuation_handler -> bool **)

let sharable = function
  | Handler (_, metadata, handler) -> (
    match handler with
    | Let (_, _, _, _) ->
      negb metadata.hm_is_exn_handler
      && straight
           (S
              (S
                 (S
                    (S
                       (S
                          (S
                             (S
                                (S
                                   (S
                                      (S
                                         (S
                                            (S
                                               (S
                                                  (S
                                                     (S
                                                        (S
                                                           (S
                                                              (S
                                                                 (S
                                                                    (S
                                                                       (S
                                                                          (S
                                                                             (S
                                                                                (
                                                                                S
                                                                                (
                                                                                S
                                                                                (
                                                                                S
                                                                                (
                                                                                S
                                                                                (
                                                                                S
                                                                                (
                                                                                S
                                                                                (
                                                                                S
                                                                                (
                                                                                S
                                                                                O)))))))))))))))))))))))))))))))
           handler
    | _ -> false)

(** val handler_params : continuation_handler -> variable list **)

let handler_params = function Handler (params, _, _) -> params

(** val same_handler : continuation_handler -> variable list -> continuation
    list -> continuation_handler -> bool **)

let same_handler h xs ks h' =
  ((handler_eqb [] [] h' h && distinct (handler_params h'))
  && negb (existsb (fun x -> var_free_in_handler_b x h') xs))
  && negb (existsb (fun c -> cont_free_in_handler_b c h') ks)

(** val share_with : continuation -> continuation_handler -> variable list ->
    continuation list -> expr -> expr **)

let rec share_with k h xs ks e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, share_with k h (x :: xs) ks body)
  | Let_static (bindings, body) ->
    Let_static (bindings, share_with k h xs ks body)
  | Let_cont_non_recursive (k', handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    if Pos.eqb k' k
    then e
    else
      Let_cont_non_recursive
        ( k',
          (if same_handler h xs ks (Handler (params, metadata, handler))
           then
             Handler
               ( params,
                 metadata,
                 Apply_cont
                   { ac_continuation = k;
                     ac_args = map (fun x -> Var x) params;
                     ac_trap_action = None
                   } )
           else Handler (params, metadata, handler)),
          share_with k h xs (k' :: ks) body )
  | _ -> e

(** val share_handlers : expr -> expr **)

let rec share_handlers e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, share_handlers body)
  | Let_static (bindings, body) -> Let_static (bindings, share_handlers body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    let h = Handler (params, metadata, share_handlers handler) in
    let body0 = share_handlers body in
    Let_cont_non_recursive
      (k, h, if sharable h then share_with k h [] (k :: []) body0 else body0)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, share_handlers body)
  | _ -> e
