(* The openings of binders that do not freshen the bound names
   ([pattern_match_for_printing] in [Flambda]), against those that do
   ([pattern_match]). *)

open Flambda2_bound_identifiers
open Flambda2_identifiers
open Flambda2_kinds
open Flambda2_lattices
open Flambda2_nominal
open Flambda2_parser
open Flambda2_term_basics
open Flambda2_terms
module TE_internal = Flambda2_types__Typing_env

let machine_width = Target_system.Machine_width.Sixty_four

(* One handler, built here: [x. apply_cont k x]. *)
let test_one_handler () =
  let open Flambda in
  let x = Variable.create "x" Flambda_kind.value in
  let y = Variable.create "y" Flambda_kind.value in
  let k = Continuation.create () in
  let handler =
    Continuation_handler.create
      (Bound_parameters.create
         [ Bound_parameter.create x Flambda_kind.With_subkind.any_value
             Flambda_debug_uid.none ])
      ~handler:
        (Expr.create_apply_cont
           (Apply_cont.create k ~args:[Simple.var x] ~dbg:Debuginfo.none))
      ~free_names_of_handler:Unknown ~is_exn_handler:false ~is_cold:false
  in
  (* The parameter, and whether the argument in the body is that parameter. *)
  let for_printing handler =
    Continuation_handler.pattern_match_for_printing handler
      ~f:(fun params ~handler ->
        let param =
          match Bound_parameters.to_list params with
          | [param] -> Bound_parameter.var param
          | [] | _ :: _ :: _ -> Misc.fatal_error "Unexpected parameters"
        in
        match Expr.descr handler with
        | Apply_cont apply_cont ->
          ( param,
            List.equal Simple.equal
              (Apply_cont.args apply_cont)
              [Simple.var param] )
        | Let _ | Let_cont _ | Apply _ | Switch _ | Invalid _ ->
          Misc.fatal_error "Unexpected handler")
  in
  let param1, same_in_body1 = for_printing handler in
  let param2, _ = for_printing handler in
  Format.eprintf
    "A handler opened for printing: its parameter is the one it was built \
     with: %b; the same when it is opened again: %b; the argument in its body \
     is its parameter: %b.@."
    (Variable.equal param1 x)
    (Variable.equal param1 param2)
    same_in_body1;
  Continuation_handler.pattern_match handler ~f:(fun params ~handler:_ ->
      Format.eprintf
        "Opened with [pattern_match]: its parameter is the one it was built \
         with: %b.@."
        (List.exists
           (fun param -> Variable.equal (Bound_parameter.var param) x)
           (Bound_parameters.to_list params)));
  (* A renaming that has been applied to the handler, and is still delayed, is
     applied to the parameter and to the body. *)
  let renamed =
    Continuation_handler.apply_renaming handler
      (Renaming.add_fresh_variable Renaming.empty x ~guaranteed_fresh:y)
  in
  let param, same_in_body = for_printing renamed in
  Format.eprintf
    "After the renaming of x to y, opened for printing: its parameter is y: \
     %b; the argument in its body is its parameter: %b.@."
    (Variable.equal param y) same_in_body

(* The five openings of binders. *)
type openings =
  { let_ :
      'a.
      Flambda.Let.t -> f:(Bound_pattern.t -> body:Flambda.Expr.t -> 'a) -> 'a;
    non_recursive :
      'a.
      Flambda.Non_recursive_let_cont_handler.t ->
      f:(Continuation.t -> body:Flambda.Expr.t -> 'a) ->
      'a;
    recursive :
      'a.
      Flambda.Recursive_let_cont_handlers.t ->
      f:
        (invariant_params:Bound_parameters.t ->
        body:Flambda.Expr.t ->
        Flambda.Continuation_handlers.t ->
        'a) ->
      'a;
    handler :
      'a.
      Flambda.Continuation_handler.t ->
      f:(Bound_parameters.t -> handler:Flambda.Expr.t -> 'a) ->
      'a;
    code :
      'a.
      Flambda.Function_params_and_body.t ->
      f:
        (return_continuation:Continuation.t ->
        exn_continuation:Continuation.t ->
        Bound_parameters.t ->
        body:Flambda.Expr.t ->
        my_closure:Variable.t ->
        is_my_closure_used:bool Or_unknown.t ->
        my_alloc_mode:Alloc_mode.For_applications.t ->
        my_depth:Variable.t ->
        free_names_of_body:Name_occurrences.t Or_unknown.t ->
        'a) ->
      'a
  }

let freshening =
  let open Flambda in
  { let_ = Let.pattern_match;
    non_recursive = Non_recursive_let_cont_handler.pattern_match;
    recursive = Recursive_let_cont_handlers.pattern_match;
    handler = Continuation_handler.pattern_match;
    code = Function_params_and_body.pattern_match
  }

let for_printing =
  let open Flambda in
  { let_ = Let.pattern_match_for_printing;
    non_recursive = Non_recursive_let_cont_handler.pattern_match_for_printing;
    recursive = Recursive_let_cont_handlers.pattern_match_for_printing;
    handler = Continuation_handler.pattern_match_for_printing;
    code = Function_params_and_body.pattern_match_for_printing
  }

(* The variables and the continuations that a unit binds, in the order of the
   traversal; and the continuations that have handlers. *)
let bound_names openings unit =
  let open Flambda in
  let vars = ref [] in
  let conts = ref [] in
  let handlers = ref [] in
  let bind_var var = vars := var :: !vars in
  let bind_cont cont = conts := cont :: !conts in
  let bind_params params =
    List.iter
      (fun param -> bind_var (Bound_parameter.var param))
      (Bound_parameters.to_list params)
  in
  let rec expr e =
    match Expr.descr e with
    | Let let_expr ->
      named (Let.defining_expr let_expr);
      openings.let_ let_expr ~f:(fun pattern ~body ->
          Bound_pattern.fold_all_bound_vars pattern ~init:()
            ~f:(fun () bound_var -> bind_var (Bound_var.var bound_var));
          expr body)
    | Let_cont (Non_recursive { handler; _ }) ->
      openings.non_recursive handler ~f:(fun cont ~body ->
          bind_cont cont;
          one_handler cont (Non_recursive_let_cont_handler.handler handler);
          expr body)
    | Let_cont (Recursive handlers) ->
      openings.recursive handlers ~f:(fun ~invariant_params ~body handlers ->
          bind_params invariant_params;
          Continuation.Lmap.iter
            (fun cont handler ->
              bind_cont cont;
              one_handler cont handler)
            (Continuation_handlers.to_map handlers);
          expr body)
    | Apply _ | Apply_cont _ | Switch _ | Invalid _ -> ()
  and one_handler cont handler =
    handlers := cont :: !handlers;
    openings.handler handler ~f:(fun params ~handler ->
        bind_params params;
        expr handler)
  and named n =
    Named.fold_code_and_sets_of_closures n ~init:()
      ~f_code:(fun () code ->
        openings.code (Code0.params_and_body code)
          ~f:(fun
              ~return_continuation
              ~exn_continuation
              params
              ~body
              ~my_closure
              ~is_my_closure_used:_
              ~my_alloc_mode:_
              ~my_depth
              ~free_names_of_body:_
            ->
            bind_cont return_continuation;
            bind_cont exn_continuation;
            bind_params params;
            bind_var my_closure;
            bind_var my_depth;
            expr body))
      ~f_set:(fun () _ -> ())
  in
  expr (Flambda_unit.body unit);
  List.rev !vars, List.rev !conts, List.rev !handlers

let count_in_common equal xs ys =
  List.length (List.filter (fun x -> List.exists (equal x) ys) xs)

(* A unit with the five constructs that bind names. *)
let test_unit filename =
  match Parse_flambda.parse_fexpr filename with
  | Error _ -> Misc.fatal_errorf "Cannot parse %s" filename
  | Ok fexpr ->
    let unit_info = Parse_flambda.make_unit_info ~filename in
    Env.set_current_unit unit_info;
    let converted = Fexpr_to_flambda.conv (Unit_info.modname unit_info) fexpr in
    let unit = converted.unit in
    let vars, conts, _ = bound_names for_printing unit in
    let vars', conts', _ = bound_names for_printing unit in
    Format.eprintf
      "A unit opened for printing: it binds %d variables and %d continuations; \
       the same ones when it is opened again: %b.@."
      (List.length vars) (List.length conts)
      (List.equal Variable.equal vars vars'
      && List.equal Continuation.equal conts conts');
    let report how (vars', conts', _) =
      Format.eprintf "%s: %d of the variables and %d of the continuations.@."
        how
        (count_in_common Variable.equal vars vars')
        (count_in_common Continuation.equal conts conts')
    in
    let freshened = bound_names freshening unit in
    report "Opened with [pattern_match], it binds" freshened;
    (* The openings for printing freshen when [-dfreshen] is given. *)
    Oxcaml_flags.Flambda2.Dump.freshen := true;
    report "Opened for printing with -dfreshen, it binds"
      (bound_names for_printing unit);
    Oxcaml_flags.Flambda2.Dump.freshen := false;
    (* What the openings for printing are exported for: the typing environments
       that Simplify reports to a test are keyed by the names that it built its
       output with. *)
    let reported = ref [] in
    TE_internal.For_testing.set_observer
      (Some (fun _env cont -> reported := cont :: !reported));
    let null_formatter =
      Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
    in
    let result =
      Flambda2.flambda_to_flambda ~ppf_dump:null_formatter
        ~prefixname:(Filename.chop_extension filename)
        ~machine_width ~code_slot_offsets:converted.code_slot_offsets unit
    in
    TE_internal.For_testing.set_observer None;
    let report how (_, _, handlers) =
      Format.eprintf
        "The output of Simplify, opened %s: %d handlers, of which %d are \
         continuations whose environment was reported.@."
        how (List.length handlers)
        (count_in_common Continuation.equal handlers !reported)
    in
    report "for printing" (bound_names for_printing result.flambda);
    report "with [pattern_match]" (bound_names freshening result.flambda)

let () =
  Clflags.set_target Clflags.Target.Native;
  let comp_unit =
    Compilation_unit.create Compilation_unit.Prefix.empty
      (Compilation_unit.Name.of_string "camlTest")
  in
  Env.set_current_unit (Unit_info.make_dummy ~input_name:"camlTest" comp_unit);
  test_one_handler ();
  test_unit Sys.argv.(1)
