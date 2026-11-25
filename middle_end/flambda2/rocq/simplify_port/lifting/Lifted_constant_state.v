(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows
   middle_end/flambda2/simplify/lifting/lifted_constant_state.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order) is that of GUIDE.md; the Rocq form of the type [t] and
   its extraction directives; the two declarations of OCaml's array
   literals. No proof. *)

From SimplifyPort Require Import Port_monad.
(* The compiler's file does not open [Simplify_import], which uses it: the
   declarations of that module are not loaded here. *)
From SimplifyPort.decl Require Array ArrayLabels Bound_static
  Code_id_or_symbol Format Function_slot Lifted_constant List ListLabels
  Name_mode Name_occurrences Symbol.
From SimplifyPort.decl Require Import Lifted_constant_state__local.
(* CONSTRUCTORS-WITHOUT-MODULE: Lifted_constant.Definition_.descr_ *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
From SimplifyPort.abbrev.lifted_constant_state Require Import Port_abbreviations.
(*OCAML
module LC = Lifted_constant
OCAML*)

(* 81-82. The abbreviation [CIS] and the application of the functor are the
   compiler's two lines. They stand at the head of the extracted file, not at
   their place (OCaml text can stand at the head or the end only).
   decl/Lifted_constant_state__local.v declares what the file uses of
   [SCC_lifted_constants]. *)
(*OCAML
module CIS = Code_id_or_symbol
module SCC_lifted_constants = Strongly_connected_components.Make (CIS)
OCAML*)

(* 19-26 *)
(* The constructors [Leaf_array] and [Union] have inline records: the Rocq
   type takes the fields by place, in the order of the type ([ts]; [t1],
   [t2]), and the directive gives the match; the compiler's definition is the
   text that Rocq prints. *)
Inductive t_ : Type :=
| Empty : t_
| Leaf : LC.t -> t_
| Leaf_array : array LC.t -> t_
| Union : t_ -> t_ -> t_.
Extract Inductive t_ => "t" [ "Empty" "Leaf" "(fun x__1 -> Leaf_array { ts = x__1 })" "(fun (x__1, x__2) -> Union { t1 = x__1; t2 = x__2 })" ] "(fun f__1 f__2 f__3 f__4 x__0 -> match x__0 with Empty -> f__1 () | Leaf x__1 -> f__2 x__1 | Leaf_array { ts = x__1 } -> f__3 x__1 | Union { t1 = x__1; t2 = x__2 } -> f__4 x__1 x__2)".
Definition t : Type := t_.
Extract Constant t => "| Empty | Leaf of LC.t | Leaf_array of { ts : LC.t array } | Union of { t1 : t; t2 : t }".

(* 28-41 *)
Definition print (ppf : Format.formatter) (t : Lifted_constant_state.t)
    : M unit :=
  let& to_list :=
    fun (t : Lifted_constant_state.t) =>
    (* 30: the recursion is on the structure of [t]. *)
    let to_list :=
      fix to_list (t : Lifted_constant_state.t) (acc : list LC.t) {struct t}
          : M (list LC.t) :=
        match t with
        | Empty => ret acc
        | Leaf const => ret (const :: acc)
        | Leaf_array ts =>
          let! tmp1 := Array.to_list ts in
          let! tmp2 := List.rev tmp1 in
          ret ((tmp2 ++ acc)%list)
        | Union t1 t2 =>
          let! tmp1 := to_list t2 acc in
          to_list t1 tmp1
        end
    in
    to_list t []
  in
  let! tmp1 := to_list t in
  let! tmp2 :=
    papp2 Format.pp_print_list (Some Format.pp_print_space) LC.print
  in
  Format.fprintf2 ppf "@[<hov 1>(%a)@]" tmp2 tmp1.

(* 43 *)
Definition empty : t := Empty.

(* 45-46 *)
Definition is_empty (t : Lifted_constant_state.t) : M bool :=
  match t with
  | Empty => ret true
  | Leaf _ | Leaf_array _ | Union _ _ => ret false
  end.

(* 48 *)
Definition singleton (const : LC.t) : M t := ret (Leaf const).

(* 50-54 *)
Definition singleton_list_of_constants (constants : list LC.t) : M t :=
  match constants with
  | [] => ret empty
  | [constant] => singleton constant
  | _ :: _ =>
    let! tmp1 := Array.of_list constants in
    ret (Leaf_array tmp1)
  end.

(* 56-57: [Union { t2 = Leaf const; t1 = t }], the fields by place. *)
Definition add (t : Lifted_constant_state.t) (const : LC.t)
    : M Lifted_constant_state.t :=
  let! tmp1 := is_empty t in
  if tmp1 then ret (Leaf const) else ret (Union t (Leaf const)).

(* 59-64: [Union { t2 = t1; t1 = t2 }], the fields by place. *)
Definition union (t1 t2 : t) : M t :=
  match t1, t2 with
  | Empty, Empty => ret Empty
  | Empty, (Leaf _ | Leaf_array _ | Union _ _) => ret t2
  | (Leaf _ | Leaf_array _ | Union _ _), Empty => ret t1
  | (Leaf _ | Leaf_array _ | Union _ _), t2 => ret (Union t2 t1)
  end.

(* 66-75. In the compiler: [t ~init ~f]. *)
(* PORT-GAP(loose): 66, the attribute [@inline] is not kept. *)
Definition fold {A : Type} (t : Lifted_constant_state.t) (init : A)
    (f : A -> LC.t -> M A) : M A :=
  (* 67: the recursion is on the structure of [t]. 70, [ArrayLabels.fold_left
     ts ~init ~f]: the arguments are in the order of the interface. *)
  let loop :=
    fix loop (init : A) (t : Lifted_constant_state.t) {struct t} : M A :=
      match t with
      | Empty => ret init
      | Leaf const => f init const
      | Leaf_array ts => ArrayLabels.fold_left f init ts
      | Union t1 t2 =>
        let* init := loop init t2 in
        loop init t1
      end
  in
  loop init t.

(* 77-79: [a |> f b] is [f b a]. *)
Definition all_defined_symbols (t : Lifted_constant_state.t)
    : M Symbol.Set_.t :=
  fold t Symbol.Set_.empty
    (fun symbols const =>
      let! tmp1 := LC.all_defined_symbols const in
      Symbol.Set_.union symbols tmp1).

(* 81-82: [module CIS] and [module SCC_lifted_constants] are at the head of
   the extracted file. *)

(* 84-129 *)
Definition build_dep_graph (t : Lifted_constant_state.t)
    : M (CIS.Lmap.t CIS.Set_.t * CIS.Map.t LC.t) :=
  fold t (CIS.Lmap.empty, CIS.Map.empty)
    (fun '(dep_graph, code_id_or_symbol_to_const) lifted_constant =>
      (* 87-89, [ListLabels.fold_left l ~init ~f]: the arguments are in the
         order of the interface. [tmp1] is used after the function: the
         temporaries inside the function begin at [tmp2]. *)
      let! tmp1 := LC.definitions lifted_constant in
      ListLabels.fold_left
        (fun '(dep_graph, code_id_or_symbol_to_const) definition =>
          (* PORT-GAP(loose): 90, [let module D = LC.Definition in] is not
             kept: the functions of [D] are written [LC.Definition_.f]. *)
          let* free_names :=
            let* free_names := LC.Definition_.free_names definition in
            let! tmp2 := LC.Definition_.descr definition in
            match tmp2 with
            | LC.Definition_.Code _ | LC.Definition_.Block_like _ _ _ _ =>
              ret free_names
            | LC.Definition_.Set_of_closures _ closure_symbols_with_types _ =>
              (* To avoid existing sets of closures (with or without
                 associated code) being pulled apart, we add a dependency
                 from each of the closure symbols (in the current set) to
                 all of the others (in the current set). *)
              let! tmp3 :=
                Function_slot.Lmap.data closure_symbols_with_types
              in
              ListLabels.fold_left
                (fun free_names '(symbol, _) =>
                  Name_occurrences.add_symbol free_names symbol
                    Name_mode.normal)
                free_names tmp3
            end
          in
          (* 105-109 *)
          let* free_syms := Name_occurrences.symbols free_names in
          let* free_code_ids :=
            Name_occurrences.code_ids_and_newer_version_of_code_ids free_names
          in
          (* 110-114 *)
          let* deps :=
            let! tmp2 := CIS.set_of_code_id_set free_code_ids in
            let! tmp3 := CIS.set_of_symbol_set free_syms in
            CIS.Set_.union tmp3 tmp2
          in
          (* 115-118 *)
          let* being_defined :=
            let! tmp2 := LC.Definition_.bound_static definition in
            Bound_static.everything_being_defined_as_list tmp2
          in
          (* 119-129 *)
          List.fold_left
            (fun '(dep_graph, code_id_or_symbol_to_const) being_defined =>
              let* dep_graph := CIS.Lmap.add being_defined deps dep_graph in
              let* code_id_or_symbol_to_const :=
                let! tmp2 := Lifted_constant.create_definition definition in
                CIS.Map.add being_defined tmp2 code_id_or_symbol_to_const
              in
              ret (dep_graph, code_id_or_symbol_to_const))
            (dep_graph, code_id_or_symbol_to_const)
            being_defined)
        (dep_graph, code_id_or_symbol_to_const)
        tmp1).

(* 131-142 *)
Definition remove_values_not_in_domain (m : CIS.Lmap.t CIS.Set_.t)
    : M (CIS.Lmap.t CIS.Set_.t) :=
  let* domain :=
    CIS.Lmap.fold
      (fun value _ domain => CIS.Set_.add value domain)
      m CIS.Set_.empty
  in
  CIS.Lmap.map
    (fun values =>
      (* 139-140: the compiler's note (lmaurer): this should use a map/set
         intersection function, which should be easy to define with the
         Patricia tree refactor. *)
      CIS.Set_.filter (fun value => CIS.Set_.mem value domain) values)
    m.

(* 144 *)
Record sort_result : Type := { innermost_first : array LC.t }.

(* 146-197 *)
Definition sort0 (t : Lifted_constant_state.t) : M sort_result :=
  (* The various lifted constants may exhibit recursion between themselves
     (specifically between closures and/or code). We use SCC to obtain a
     topological sort of groups that must be coalesced into single
     code-and-set-of-closures definitions. *)
  let* '(lifted_constants_dep_graph, code_id_or_symbol_to_const) :=
    build_dep_graph t
  in
  let* lifted_constants_dep_graph :=
    (* This graph has vertices for all code ids and symbols that appear free
       in the definitions, including pre-existing ones. However, any such
       "external vertex" is a leaf, and in fact it won't even appear as a key
       in the map representation of the graph. However,
       [SCC_lifted_constants] assumes that all vertices appear as keys.
       Fortunately, we're only concerned with the interdependencies between
       code ids and symbols being defined here, so we can just filter out
       external dependencies from the graph. *)
    remove_values_not_in_domain lifted_constants_dep_graph
  in
  (* 164-196: [a |> f b] is [f b a]. *)
  let* innermost_first :=
    let! tmp1 := CIS.Lmap.bindings lifted_constants_dep_graph in
    let! tmp2 :=
      SCC_lifted_constants
      .stable_connected_components_sorted_from_roots_to_leaf tmp1
    in
    ArrayLabels.map
      (fun (group : SCC_lifted_constants.component) =>
        let* code_id_or_symbols :=
          match group with
          | SCC_lifted_constants.No_loop code_id_or_symbol =>
            ret [code_id_or_symbol]
          | SCC_lifted_constants.Has_loop code_id_or_symbols =>
            ret code_id_or_symbols
          end
        in
        (* 174-194, [ListLabels.fold_left l ~init ~f]: the arguments are in
           the order of the interface. 176: [((already_seen, definitions) as
           acc)]. *)
        let* '(_, lifted_constants) :=
          ListLabels.fold_left
            (fun (acc : CIS.Set_.t * list LC.t) code_id_or_symbol =>
              let '(already_seen, definitions) := acc in
              let! tmp1 := CIS.Set_.mem code_id_or_symbol already_seen in
              if tmp1
              then ret acc
              else
                let* lifted_constant :=
                  CIS.Map.find code_id_or_symbol code_id_or_symbol_to_const
                in
                let* already_seen :=
                  (* We may encounter the same defining expression more than
                     once, in the case of sets of closures, which may bind
                     more than one symbol. We must avoid duplicates in the
                     resulting [LC.t]. *)
                  let* bound_static := LC.bound_static lifted_constant in
                  let! tmp1 :=
                    Bound_static.everything_being_defined bound_static
                  in
                  CIS.Set_.union tmp1 already_seen
                in
                ret (already_seen, lifted_constant :: definitions))
            (CIS.Set_.empty, [])
            code_id_or_symbols
        in
        LC.concat lifted_constants)
      tmp2
  in
  ret {| innermost_first := innermost_first |}.

(* 199-203 *)
Definition sort (t : Lifted_constant_state.t) : M sort_result :=
  match t with
  | Empty => ret {| innermost_first := array_empty |}
  | Leaf const =>
    let! tmp1 := array_singleton const in
    ret {| innermost_first := tmp1 |}
  | Leaf_array _ | Union _ _ => sort0 t
  end.
