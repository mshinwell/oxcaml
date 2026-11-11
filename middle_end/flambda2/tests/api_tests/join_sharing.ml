(* The result of a join must not depend on how the types of the joined
   environments are shared in memory.

   Each test joins two environments in which a name has equal types, once given
   as the same value in both environments ("shared") and once as two copies
   ("unshared"), for each join algorithm and each [-flambda2-join-sharing]. With
   [physical] the two results may differ; with [structural] and [none] they must
   not. *)

open Flambda2_bound_identifiers
open Flambda2_identifiers
open Flambda2_kinds
open Flambda2_nominal
open Flambda2_numbers
open Flambda2_term_basics
module K = Flambda_kind
module T = Flambda2_types
module TE = T.Typing_env

let machine_width = Target_system.Machine_width.Sixty_four

let create_env () =
  let resolver _ = None in
  TE.create ~resolver ~machine_width

let define ?(kind = K.value) env v =
  let v' = Bound_var.create v Flambda_debug_uid.none Name_mode.normal in
  TE.add_definition env (Bound_name.create_var v') kind

let tag_0 = Tag.Scannable.zero

let tag_1 = Option.get (Tag.Scannable.of_tag (Tag.create_exn 1))

let variant fields_of_tag_0 =
  T.variant
    ~const_ctors:(T.bottom K.naked_immediate)
    ~non_const_ctors:
      (Tag.Scannable.Map.of_list
         [ tag_0, (K.Block_shape.Scannable Value_only, fields_of_tag_0);
           tag_1, (K.Block_shape.Scannable Value_only, []) ])
    Alloc_mode.For_types.heap ~machine_width

let block fields =
  T.immutable_block ~is_unique:false Tag.zero
    ~shape:(K.Block_shape.Scannable Value_only) Alloc_mode.For_types.heap
    ~fields ~machine_width

let tagged_immediate i =
  T.this_tagged_immediate (Target_ocaml_int.of_int machine_width i)

let join scoped_env ~cut_after left_env right_env =
  let joined_env, _analysis =
    T.cut_and_n_way_join scoped_env
      [ left_env, Apply_cont_rewrite_id.create (), Inlinable;
        right_env, Apply_cont_rewrite_id.create (), Inlinable ]
      ~params:Bound_parameters.empty ~cut_after
      ~extra_allowed_names:Name_occurrences.empty
      ~extra_lifted_consts_in_use_envs:Symbol.Set.empty
  in
  joined_env

type sharing =
  | Shared
  | Unshared

(* [make ()] must build a new copy of the same thing at each call. The two calls
   for [Unshared] go through [Sys.opaque_identity] so that the compiler cannot
   inline them and then share the two results, which it is allowed to do for
   immutable values. *)
let two_copies sharing make =
  match sharing with
  | Shared ->
    let x = make () in
    x, x
  | Unshared ->
    let make = Sys.opaque_identity make in
    let x1 = make () in
    let x2 = make () in
    if x1 == x2 then Misc.fatal_error "The two copies are shared";
    x1, x2

(* What a test returns: the types of these variables after the join, printed. *)
let print_types env vars =
  Format.asprintf "@[<v>%a@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_cut (fun ppf var ->
         Format.fprintf ppf "@[<hov 2>%a:@ %a@]" Variable.print var T.print
           (TE.find env (Name.var var) (Some (Variable.kind var)))))
    vars

(* A variant whose first case has an env extension: the meet of [Variant (tag_0
   [= a]) (tag_1 [])] and [Variant (tag_0 [= b]) (tag_1 [])] learns [a = b] in
   the first case only. *)
let variant_with_extension env ~a ~b () =
  let ty_a = variant [T.tagged_immediate_alias_to ~naked_immediate:a] in
  let ty_b = variant [T.tagged_immediate_alias_to ~naked_immediate:b] in
  match T.meet env ty_a ty_b with Ok (ty, _env) -> ty | Bottom -> assert false

(* In the first three tests, [wrap] says where the variant with an extension is
   put in the type of [y] in the left and right environments. *)
let test_variant_with_extension wrap =
  let env = create_env () in
  let y = Variable.create "y" K.value in
  let a = Variable.create "a" K.naked_immediate in
  let b = Variable.create "b" K.naked_immediate in
  let env = define env y in
  let env = define ~kind:K.naked_immediate env a in
  let env = define ~kind:K.naked_immediate env b in
  let scope = TE.current_scope env in
  let scoped_env = TE.increment_scope env in
  fun sharing ->
    let left_ty, right_ty =
      two_copies sharing (variant_with_extension scoped_env ~a ~b)
    in
    let left_ty, right_ty = wrap left_ty right_ty in
    let left_env = TE.add_equation scoped_env (Name.var y) left_ty in
    let right_env = TE.add_equation scoped_env (Name.var y) right_ty in
    let joined_env = join scoped_env ~cut_after:scope left_env right_env in
    print_types joined_env [y]

(* The joined types are blocks that differ in their second field, so they are
   never the same type; their first field is the variant. Only the extensions of
   the variant can be the same on both sides. *)
let test_env_extension () =
  test_variant_with_extension (fun left_ty right_ty ->
      block [left_ty; tagged_immediate 1], block [right_ty; tagged_immediate 2])

(* The joined types are the variant itself. *)
let test_whole_type () =
  test_variant_with_extension (fun left_ty right_ty -> left_ty, right_ty)

(* The joined types are blocks whose only field is the variant: the blocks are
   never shared, their field is. *)
let test_block_field () =
  test_variant_with_extension (fun left_ty right_ty ->
      block [left_ty], block [right_ty])

(* Both environments learn that [t] is the tag of [x]. *)
let test_relation () =
  let env = create_env () in
  let x = Variable.create "x" K.value in
  let t = Variable.create "t" K.naked_immediate in
  let u = Variable.create "u" K.value in
  let env = define env x in
  let env = define ~kind:K.naked_immediate env t in
  let env = define env u in
  let scope = TE.current_scope env in
  let scoped_env = TE.increment_scope env in
  fun sharing ->
    let left_env, right_env =
      two_copies sharing (fun () ->
          TE.add_get_tag_relation scoped_env (Name.var t)
            ~scrutinee:(Simple.var x))
    in
    let left_env = TE.add_equation left_env (Name.var u) (tagged_immediate 1) in
    let right_env =
      TE.add_equation right_env (Name.var u) (tagged_immediate 2)
    in
    let joined_env = join scoped_env ~cut_after:scope left_env right_env in
    print_types joined_env [t; x]

(* The joined types are blocks whose only field is an alias to [x], and both
   environments know that [x] is an alias of [z]. *)
let test_alias_field () =
  let env = create_env () in
  let z = Variable.create "z" K.value in
  let x = Variable.create "x" K.value in
  let y = Variable.create "y" K.value in
  let env = define env z in
  let env = define env x in
  let env = define env y in
  let scope = TE.current_scope env in
  let scoped_env = TE.increment_scope env in
  let scoped_env =
    TE.add_equation scoped_env (Name.var x)
      (T.alias_type_of K.value (Simple.var z))
  in
  fun sharing ->
    let left_field, right_field =
      two_copies sharing (fun () -> T.alias_type_of K.value (Simple.var x))
    in
    let left_env =
      TE.add_equation scoped_env (Name.var y) (block [left_field])
    in
    let right_env =
      TE.add_equation scoped_env (Name.var y) (block [right_field])
    in
    let joined_env = join scoped_env ~cut_after:scope left_env right_env in
    print_types joined_env [y]

let tests =
  [ "env extension", test_env_extension;
    "whole type", test_whole_type;
    "block field", test_block_field;
    "relation", test_relation;
    "alias field", test_alias_field ]

let join_algorithms =
  ["binary", Oxcaml_flags.Binary; "n-way", Oxcaml_flags.N_way]

let join_sharings =
  [ "physical", Oxcaml_flags.Physical;
    "structural", Oxcaml_flags.Structural;
    "none", Oxcaml_flags.No_sharing ]

let run_test ~test_name test ~algorithm_name ~sharing_name =
  let test = test () in
  let shared = test Shared in
  let unshared = test Unshared in
  let same = String.equal shared unshared in
  Format.eprintf "%s, %s join, %s:@." test_name algorithm_name sharing_name;
  if same
  then Format.eprintf "shared and unshared:@.%s@.@." shared
  else Format.eprintf "shared:@.%s@.unshared:@.%s@.@." shared unshared;
  match sharing_name with
  | "physical" -> ()
  | _ ->
    if not same
    then
      Misc.fatal_errorf
        "%s, %s join, -flambda2-join-sharing %s: the result depends on sharing"
        test_name algorithm_name sharing_name

let () =
  let comp_unit = "Join_sharing" |> Compilation_unit.of_string in
  let unit_info = Unit_info.make_dummy ~input_name:"join_sharing" comp_unit in
  Env.set_current_unit unit_info;
  Misc.Colours.without_colours ~f:(fun () ->
      List.iter
        (fun (test_name, test) ->
          List.iter
            (fun (algorithm_name, join_algorithm) ->
              Oxcaml_flags.Flambda2.join_algorithm
                := Oxcaml_flags.Set join_algorithm;
              List.iter
                (fun (sharing_name, join_sharing) ->
                  Oxcaml_flags.Flambda2.join_sharing
                    := Oxcaml_flags.Set join_sharing;
                  run_test ~test_name test ~algorithm_name ~sharing_name)
                join_sharings)
            join_algorithms)
        tests)
