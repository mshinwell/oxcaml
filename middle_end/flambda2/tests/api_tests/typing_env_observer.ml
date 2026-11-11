(* The observer of typing environments that a test can register with the types
   library, and the places where Simplify reports to it. *)

open Flambda2_bound_identifiers
open Flambda2_identifiers
open Flambda2_kinds
open Flambda2_nominal
open Flambda2_numbers
open Flambda2_parser
open Flambda2_term_basics
open Flambda2_terms
module T = Flambda2_types
module TE = Flambda2_types.Typing_env

(* The internal interface of the types library, which [Flambda2_types] does not
   export. A test names these modules to register its observer and to read the
   types it is given. *)
module TE_internal = Flambda2_types__Typing_env
module TG = Flambda2_types__Type_grammar
module TD = Flambda2_types__Type_descr
module Provers = Flambda2_types__Provers

let machine_width = Target_system.Machine_width.Sixty_four

let observations : (TE_internal.t * Continuation.t) list ref = ref []

let observe env cont = observations := (env, cont) :: !observations

let take_observations () =
  let result = List.rev !observations in
  observations := [];
  result

(* What an observed environment knows of a name. The environment and the type
   are those of the internal interface, so its functions apply to them. *)
let print_what_is_known env ppf name =
  if not (TE_internal.mem env name)
  then Format.fprintf ppf "unbound"
  else
    let ty : TG.t = TE_internal.find env name (Some Flambda_kind.value) in
    match Provers.prove_equals_tagged_immediates env ty with
    | Proved immediates ->
      Format.fprintf ppf "@[<h>one of the tagged immediates %a@]"
        Target_ocaml_int.Set.print immediates
    | Unknown -> Format.fprintf ppf "not known to be an immediate"

(* The library on its own: nothing is reported unless an observer is registered,
   and the observer is given the environment and the continuation. *)
let test_library () =
  let env = TE.create ~resolver:(fun _ -> None) ~machine_width in
  let x = Name.var (Variable.create "x" Flambda_kind.value) in
  let env =
    TE.add_definition env
      (Bound_name.create x Name_mode.normal)
      Flambda_kind.value
  in
  let env =
    TE.add_equation env x
      (T.this_tagged_immediate (Target_ocaml_int.of_int machine_width 42))
  in
  let k = Continuation.create () in
  TE.notify_test_observer env ~at_handler:k;
  Format.eprintf "No observer: %d observation(s).@."
    (List.length (take_observations ()));
  TE_internal.For_testing.set_observer (Some observe);
  TE.notify_test_observer env ~at_handler:k;
  TE_internal.For_testing.set_observer None;
  TE.notify_test_observer env ~at_handler:k;
  match take_observations () with
  | [(env, k')] ->
    Format.eprintf
      "An observer, registered and then removed: 1 observation, at the \
       continuation given: %b.@."
      (Continuation.equal k k');
    Format.eprintf "In the environment observed, x is %a.@."
      (print_what_is_known env) x
  | observations ->
    Format.eprintf "Unexpected: %d observations.@." (List.length observations)

(* If [ty] is the type of a block with a single field whose type is an alias of
   a variable, that variable. This reads the grammar of types. *)
let[@ocaml.warning "-fragile-match"] variable_in_field_of_block (ty : TG.t) =
  match ty with
  | Value ty -> (
    match TD.descr ty with
    | Ok (No_alias { non_null = Ok (Variant { blocks = Known blocks; _ }); _ })
      -> (
      match TG.Row_like_for_blocks.get_singleton blocks with
      | Some (_tag, _shape, _size, [| field |], _alloc_mode) ->
        Option.bind (TG.get_alias_opt field) (fun simple ->
            Simple.pattern_match' simple
              ~var:(fun var ~coercion:_ -> Some var)
              ~symbol:(fun _ ~coercion:_ -> None)
              ~const:(fun _ -> None))
      | Some _ | None -> None)
    | _ -> None)
  | _ -> None

(* Simplify reports the environment at the start of each continuation handler
   that it simplifies, and the final environment of the unit, at the return
   continuation of the unit. *)
let test_simplify filename =
  match Parse_flambda.parse_fexpr filename with
  | Error _ -> Misc.fatal_errorf "Cannot parse %s" filename
  | Ok fexpr -> (
    let unit_info = Parse_flambda.make_unit_info ~filename in
    Env.set_current_unit unit_info;
    let converted = Fexpr_to_flambda.conv (Unit_info.modname unit_info) fexpr in
    let null_formatter =
      Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
    in
    TE_internal.For_testing.set_observer (Some observe);
    let result =
      Flambda2.flambda_to_flambda ~ppf_dump:null_formatter
        ~prefixname:(Filename.chop_extension filename)
        ~machine_width ~code_slot_offsets:converted.code_slot_offsets
        converted.unit
    in
    TE_internal.For_testing.set_observer None;
    let unit = result.flambda in
    let return_continuation = Flambda_unit.return_continuation unit in
    let module_symbol = Name.symbol (Flambda_unit.module_symbol unit) in
    let at_end, at_handlers =
      List.partition
        (fun (_, cont) -> Continuation.equal cont return_continuation)
        (take_observations ())
    in
    Format.eprintf
      "Simplify: %d observation(s) at the return continuation of the unit, %d \
       at other continuations.@."
      (List.length at_end) (List.length at_handlers);
    (* The module block has one field, which is the parameter of the handler
       under the name that Simplify gave it. *)
    let param =
      match at_end with
      | [(env, _)] ->
        variable_in_field_of_block
          (TE_internal.find env module_symbol (Some Flambda_kind.value))
      | [] | _ :: _ :: _ -> None
    in
    match param with
    | None ->
      Format.eprintf "The field of the module block is not a variable.@."
    | Some param ->
      Format.eprintf "The field of the module block is the variable %s.@."
        (Variable.name param);
      List.iter
        (fun (env, cont) ->
          Format.eprintf "At the start of the handler of %s, %s is %a.@."
            (Continuation.name cont) (Variable.name param)
            (print_what_is_known env) (Name.var param))
        at_handlers)

let () =
  Clflags.set_target Clflags.Target.Native;
  (* So that the parameter of the handler is given the join of its arguments. *)
  Oxcaml_flags.Flambda2.join_points := Oxcaml_flags.Set true;
  let comp_unit =
    Compilation_unit.create Compilation_unit.Prefix.empty
      (Compilation_unit.Name.of_string "camlTest")
  in
  Env.set_current_unit (Unit_info.make_dummy ~input_name:"camlTest" comp_unit);
  test_library ();
  test_simplify Sys.argv.(1)
