(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* unmonad RAW.ml -o OUT.ml

   Takes the OCaml that Rocq extracts from one file of the port of Simplify
   and writes the same program in direct style. It follows no file of the
   compiler. The steps, in order:

   1. REDUCE. The realisations of the declared things are closed lambdas
      ([(fun x__1 x__2 -> F.f x__1 ~lbl:x__2)]); an application of a literal
      lambda to values is reduced. This is valid for the program read as a
      pure program (which is what Rocq means by it) and for the program read
      with OCaml's effects (the arguments are values).

   2. CHECK. The reduced program must be in the fragment below; if not, the
      tool stops and names the place. C is a computation, V a value:

        C ::= port__bind C (fun p -> C) | port__ret V | h V .. V
            | match V with p -> C .. | if V then C else C | let p = V in C
            | the operations of Port_monad.v (sequence, raise, try, assert,
              while, lazy), with C where they run something
        V ::= x | constant | constructor, tuple, record of V | V.field
            | fun p .. -> C | a pure primitive of V .. V
            | if, match, let of V

      So: a call is never an argument of a call or the right side of a plain
      [let]; every function ends in a computation; a variable is never run.
      For such a program, replacing [port__bind e (fun x -> k)] by
      [let x = e in k] and [port__ret v] by [v] gives the direct-style
      program whose effects are those that the binds state, in their order,
      each once.

   3. REMOVE THE MONAD, and write each operation as OCaml's own syntax.

   4. TIDY (no change of meaning under OCaml's right-to-left evaluation of
      arguments, which is the order that the port's rule fixes): the
      temporaries [tmpN] go back into the expression that uses them, where
      they are the first thing that it evaluates; the fuel is removed. *)

open Parsetree
open Asttypes
module S = Set.Make (String)
module SM = Map.Make (String)

exception Reject of Location.t * string

let reject loc fmt =
  Printf.ksprintf (fun s -> raise (Reject (loc, s))) fmt

let no_renest = ref false

let keep_fuel = ref false

(* ------------------------------------------------------------------ *)
(* Small things                                                       *)
(* ------------------------------------------------------------------ *)

let mk ?(loc = Location.none) d = Ast_helper.Exp.mk ~loc d

let lid s = Location.mknoloc (Longident.Lident s)

let evar s = mk (Pexp_ident (lid s))

let pvar s = Ast_helper.Pat.var (Location.mknoloc s)

let ident_name e =
  match e.pexp_desc with
  | Pexp_ident { txt = Lident x; _ } -> Some x
  | _ -> None

let is_ident name e = ident_name e = Some name

let rec lid_string (l : Longident.t) =
  match l with
  | Lident s -> s
  | Ldot (a, b) -> lid_string a.txt ^ "." ^ b.txt
  | Lapply _ -> "<apply>"

let path_name e =
  match e.pexp_desc with
  | Pexp_ident { txt; _ } -> Some (lid_string txt)
  | _ -> None

let is_unit_expr e =
  match e.pexp_desc with
  | Pexp_construct ({ txt = Lident "()"; _ }, None) -> true
  | _ -> false

let is_unit_pat p =
  match p.ppat_desc with
  | Ppat_construct ({ txt = Lident "()"; _ }, None) -> true
  | _ -> false

(* A binder of a realisation: one letter, two underscores, digits ([x__1],
   [f__2]), and what [freshen] puts after. *)
let is_real_var s =
  String.length s >= 4
  && s.[0] >= 'a'
  && s.[0] <= 'z'
  && s.[1] = '_'
  && s.[2] = '_'
  && s.[3] >= '0'
  && s.[3] <= '9'

(* A parameter [name__opt] of the port is OCaml's optional [?name]. *)
let opt_name s =
  let n = String.length s in
  let rec strip i =
    if i > 0 && s.[i - 1] >= '0' && s.[i - 1] <= '9' then strip (i - 1) else i
  in
  let n' = strip n in
  if n' > 5 && String.sub s (n' - 5) 5 = "__opt"
  then Some (String.sub s 0 (n' - 5))
  else None

let is_marker s = String.length s > 6 && String.sub s 0 6 = "port__"

let is_tmp s =
  let n = String.length s in
  n >= 3
  && String.sub s 0 3 = "tmp"
  &&
  let rec digits i = i >= n || (s.[i] >= '0' && s.[i] <= '9' && digits (i + 1)) in
  digits 3

let is_fuel s =
  let n = String.length s in
  n >= 4
  && String.sub s 0 4 = "fuel"
  &&
  let rec digits i = i >= n || (s.[i] >= '0' && s.[i] <= '9' && digits (i + 1)) in
  digits 4

(* The primitives of OCaml that the kit maps Rocq's pure functions to. *)
let pure_ops =
  S.of_list
    [ "&&"; "||"; "not"; "+"; "-"; "*"; "~-"; "="; "<"; "<="; ">"; ">=";
      "succ"; "pred"; "max"; "min"; "@"; "^"; "fst"; "snd"; "String.equal" ]

let is_pure_op e =
  match path_name e with Some s -> S.mem s pure_ops | None -> false

(* ------------------------------------------------------------------ *)
(* Binders                                                            *)
(* ------------------------------------------------------------------ *)

let pat_vars (p : pattern) : S.t =
  let acc = ref S.empty in
  let it =
    { Ast_iterator.default_iterator with
      pat =
        (fun it p ->
          (match p.ppat_desc with
          | Ppat_var { txt; _ } -> acc := S.add txt !acc
          | Ppat_alias (_, { txt; _ }) -> acc := S.add txt !acc
          | _ -> ());
          Ast_iterator.default_iterator.pat it p)
    }
  in
  it.pat it p;
  !acc

let vbs_vars vbs =
  List.fold_left (fun acc vb -> S.union acc (pat_vars vb.pvb_pat)) S.empty vbs

(* [f] is called on every free occurrence of an unqualified identifier. *)
let rec iter_free (f : string -> unit) (bound : S.t) (e : expression) : unit =
  let sub bound e = iter_free f bound e in
  match e.pexp_desc with
  | Pexp_ident { txt = Lident x; _ } -> if not (S.mem x bound) then f x
  | Pexp_let (rf, vbs, body) ->
    let inner = S.union bound (vbs_vars vbs) in
    List.iter
      (fun vb -> sub (if rf = Recursive then inner else bound) vb.pvb_expr)
      vbs;
    sub inner body
  | Pexp_function (params, _, body) -> (
    let bound =
      List.fold_left
        (fun bound p ->
          match p.pparam_desc with
          | Pparam_val (_, default, pat) ->
            Option.iter (sub bound) default;
            S.union bound (pat_vars pat)
          | Pparam_newtype _ -> bound)
        bound params
    in
    match body with
    | Pfunction_body e -> sub bound e
    | Pfunction_cases (cases, _, _) -> List.iter (iter_free_case f bound) cases)
  | Pexp_match (s, cases) | Pexp_try (s, cases) ->
    sub bound s;
    List.iter (iter_free_case f bound) cases
  | Pexp_for (pat, e1, e2, _, body) ->
    sub bound e1;
    sub bound e2;
    sub (S.union bound (pat_vars pat)) body
  | _ ->
    let it =
      { Ast_iterator.default_iterator with expr = (fun _ e -> sub bound e) }
    in
    Ast_iterator.default_iterator.expr it e

and iter_free_case f bound c =
  let bound = S.union bound (pat_vars c.pc_lhs) in
  Option.iter (iter_free f bound) c.pc_guard;
  iter_free f bound c.pc_rhs

let count x e =
  let n = ref 0 in
  iter_free (fun y -> if String.equal x y then incr n) S.empty e;
  !n

let free_vars e =
  let acc = ref S.empty in
  iter_free (fun y -> acc := S.add y !acc) S.empty e;
  !acc

(* What stands for an expression that cannot be put under a binder that would
   capture one of its variables. *)
let poison : expression = mk Pexp_unreachable

(* Substitution of expressions for free unqualified identifiers. A capture
   stops the tool: the names of the realisations are made new at each use
   and Rocq's extraction never reuses a name that is in scope, so none is
   expected. *)
let rec subst (env : expression SM.t) (e : expression) : expression =
  if SM.is_empty env
  then e
  else
    let enter bound env =
      let env = S.fold SM.remove bound env in
      SM.map
        (fun r ->
          let captured = ref false in
          iter_free (fun y -> if S.mem y bound then captured := true) S.empty r;
          if !captured then poison else r)
        env
    in
    match e.pexp_desc with
    | Pexp_ident { txt = Lident x; _ } -> (
      match SM.find_opt x env with
      | Some r when r == poison ->
        reject e.pexp_loc "the tool would capture a variable in place of %s" x
      | Some r -> r
      | None -> e)
    | Pexp_let (rf, vbs, body) ->
      let inner = enter (vbs_vars vbs) env in
      let rhs_env = if rf = Recursive then inner else env in
      let vbs =
        List.map (fun vb -> { vb with pvb_expr = subst rhs_env vb.pvb_expr }) vbs
      in
      { e with pexp_desc = Pexp_let (rf, vbs, subst inner body) }
    | Pexp_function (params, c, body) ->
      let env, params =
        List.fold_left
          (fun (env, acc) p ->
            match p.pparam_desc with
            | Pparam_val (lbl, default, pat) ->
              let default = Option.map (subst env) default in
              let env = enter (pat_vars pat) env in
              env, { p with pparam_desc = Pparam_val (lbl, default, pat) } :: acc
            | Pparam_newtype _ -> env, p :: acc)
          (env, []) params
      in
      let params = List.rev params in
      let body =
        match body with
        | Pfunction_body b -> Pfunction_body (subst env b)
        | Pfunction_cases (cases, l, a) ->
          Pfunction_cases (List.map (subst_case enter env) cases, l, a)
      in
      { e with pexp_desc = Pexp_function (params, c, body) }
    | Pexp_match (s, cases) ->
      { e with
        pexp_desc =
          Pexp_match (subst env s, List.map (subst_case enter env) cases)
      }
    | Pexp_try (s, cases) ->
      { e with
        pexp_desc = Pexp_try (subst env s, List.map (subst_case enter env) cases)
      }
    | Pexp_for (pat, e1, e2, d, body) ->
      let inner = enter (pat_vars pat) env in
      { e with
        pexp_desc = Pexp_for (pat, subst env e1, subst env e2, d, subst inner body)
      }
    | _ ->
      let m =
        { Ast_mapper.default_mapper with expr = (fun _ e -> subst env e) }
      in
      Ast_mapper.default_mapper.expr m e

and subst_case enter env c =
  let env = enter (pat_vars c.pc_lhs) env in
  { c with
    pc_guard = Option.map (subst env) c.pc_guard;
    pc_rhs = subst env c.pc_rhs
  }

(* ------------------------------------------------------------------ *)
(* Step 1: reduction                                                  *)
(* ------------------------------------------------------------------ *)

let rec is_value e =
  match e.pexp_desc with
  | Pexp_ident _ | Pexp_constant _ | Pexp_function _ -> true
  | Pexp_construct (_, None) | Pexp_variant (_, None) -> true
  | Pexp_construct (_, Some a) | Pexp_variant (_, Some a) -> is_value a
  | Pexp_tuple l -> List.for_all (fun (_, e) -> is_value e) l
  | Pexp_record (fs, base) ->
    List.for_all (fun (_, e) -> is_value e) fs
    && Option.fold ~none:true ~some:is_value base
  | Pexp_field (a, _) -> is_value a
  | Pexp_constraint (a, _) -> is_value a
  | Pexp_apply (f, args) ->
    (is_pure_op f || path_name f = Some "Obj.magic"
    || is_ident "port__fmt_cons" f)
    && List.for_all (fun (_, a) -> is_value a) args
  | _ -> false

let is_atom e =
  match e.pexp_desc with
  | Pexp_ident _ | Pexp_constant _ | Pexp_construct (_, None) -> true
  | _ -> false

(* A value that reads a field is not moved: the field may be mutable, and a
   read must stay where it is among the writes. *)
let reads_field (e : expression) : bool =
  let found = ref false in
  let it =
    { Ast_iterator.default_iterator with
      expr =
        (fun it e ->
          match e.pexp_desc with
          | Pexp_field _ -> found := true
          | Pexp_function _ -> () (* nothing is read when a function is made *)
          | _ -> Ast_iterator.default_iterator.expr it e)
    }
  in
  it.expr it e;
  !found

let param_pat p =
  match p.pparam_desc with
  | Pparam_val (Nolabel, None, pat) -> Some pat
  | _ -> None

let simple_params params =
  params <> [] && List.for_all (fun p -> param_pat p <> None) params

let unlabelled args = List.for_all (fun (l, _) -> l = Nolabel) args

let is_realisation params =
  List.exists
    (fun p ->
      match param_pat p with
      | Some pat -> S.exists is_real_var (pat_vars pat)
      | None -> false)
    params

let fresh_counter = ref 0

(* The binders of a realisation all have two underscores; here each gets a
   name that occurs nowhere else. *)
let freshen (e : expression) : expression =
  incr fresh_counter;
  let k = string_of_int !fresh_counter in
  let rn s = if is_real_var s then s ^ "_" ^ k else s in
  let m =
    { Ast_mapper.default_mapper with
      pat =
        (fun m p ->
          let p = Ast_mapper.default_mapper.pat m p in
          match p.ppat_desc with
          | Ppat_var v -> { p with ppat_desc = Ppat_var { v with txt = rn v.txt } }
          | Ppat_alias (q, v) ->
            { p with ppat_desc = Ppat_alias (q, { v with txt = rn v.txt }) }
          | _ -> p);
      expr =
        (fun m e ->
          let e = Ast_mapper.default_mapper.expr m e in
          match e.pexp_desc with
          | Pexp_ident ({ txt = Lident x; _ } as l) ->
            { e with pexp_desc = Pexp_ident { l with txt = Lident (rn x) } }
          | _ -> e)
    }
  in
  m.expr m e

let rename_pat (ren : string option SM.t) (p : pattern) : pattern =
  let m =
    { Ast_mapper.default_mapper with
      pat =
        (fun m p ->
          let p = Ast_mapper.default_mapper.pat m p in
          match p.ppat_desc with
          | Ppat_var v -> (
            match SM.find_opt v.txt ren with
            | Some (Some q) -> { p with ppat_desc = Ppat_var { v with txt = q } }
            | Some None -> { p with ppat_desc = Ppat_any }
            | None -> p)
          | Ppat_alias (q, v) -> (
            match SM.find_opt v.txt ren with
            | Some (Some n) -> { p with ppat_desc = Ppat_alias (q, { v with txt = n }) }
            | Some None -> q
            | None -> p)
          | _ -> p)
    }
  in
  m.pat m p

(* In the body of a match function, a case [C (x__1, x__2) -> f__1 x__1 x__2]
   whose [f__1] is the lambda [fun a b -> rhs] becomes [C (a, b) -> rhs]: the
   names of the port are kept. *)
let fuse (env : expression SM.t) (body : expression) : expression =
  let fuse_case pat rhs =
    match rhs.pexp_desc with
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident fname; _ }; _ }, cargs)
      when unlabelled cargs -> (
      match SM.find_opt fname env with
      | Some { pexp_desc = Pexp_function (lps, None, Pfunction_body lbody); _ }
        when simple_params lps && List.length lps = List.length cargs -> (
        let pv = pat_vars pat in
        try
          let ren =
            List.fold_left2
              (fun ren lp (_, carg) ->
                let lpat = Option.get (param_pat lp) in
                match lpat.ppat_desc, carg.pexp_desc with
                | Ppat_var { txt = q; _ }, Pexp_ident { txt = Lident y; _ }
                  when S.mem y pv && not (SM.mem y ren) ->
                  SM.add y (Some q) ren
                | Ppat_any, Pexp_ident { txt = Lident y; _ }
                  when S.mem y pv && not (SM.mem y ren) ->
                  SM.add y None ren
                | _, _ when (lpat.ppat_desc = Ppat_any || is_unit_pat lpat)
                            && is_unit_expr carg ->
                  ren
                | _ -> raise Exit)
              SM.empty lps cargs
          in
          Some (rename_pat ren pat, lbody)
        with Exit -> None)
      | _ -> None)
    | _ -> None
  in
  match body.pexp_desc with
  | Pexp_match (s, cases) ->
    let cases =
      List.map
        (fun c ->
          match c.pc_guard with
          | Some _ -> c
          | None -> (
            match fuse_case c.pc_lhs c.pc_rhs with
            | Some (pat, rhs) -> { c with pc_lhs = pat; pc_rhs = rhs }
            | None -> c))
        cases
    in
    { body with pexp_desc = Pexp_match (s, cases) }
  | Pexp_let (Nonrecursive, [vb], rhs) -> (
    match fuse_case vb.pvb_pat rhs with
    | Some (pat, rhs) ->
      { body with
        pexp_desc = Pexp_let (Nonrecursive, [{ vb with pvb_pat = pat }], rhs)
      }
    | None -> body)
  | _ -> body

let int_const e =
  match e.pexp_desc with
  | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } ->
    int_of_string_opt s
  | _ -> None

let mk_int n = mk (Pexp_constant (Ast_helper.Const.integer (string_of_int n)))

let rec simp (e : expression) : expression =
  match e.pexp_desc with
  | Pexp_ident { txt = Lident "port__ret"; _ } ->
    (* [ret] alone, which the extraction writes for [fun x => ret x] *)
    incr fresh_counter;
    let x = "x__r_" ^ string_of_int !fresh_counter in
    mk
      (Pexp_function
         ( [ { pparam_loc = Location.none;
               pparam_desc = Pparam_val (Nolabel, None, pvar x)
             } ],
           None,
           Pfunction_body (mk (Pexp_apply (e, [Nolabel, evar x]))) ))
  | Pexp_apply (({ pexp_desc = Pexp_ident { txt = Lident h; _ }; _ } as head), args)
    when is_marker h ->
    reduce
      { e with pexp_desc = Pexp_apply (head, List.map (fun (l, a) -> l, simp a) args) }
  | _ ->
    let m = { Ast_mapper.default_mapper with expr = (fun _ e -> simp e) } in
    reduce (Ast_mapper.default_mapper.expr m e)

and reduce (e : expression) : expression =
  match e.pexp_desc with
  | Pexp_apply ({ pexp_desc = Pexp_apply (f, args1); _ }, args2)
    when not (is_pure_op f) ->
    reduce { e with pexp_desc = Pexp_apply (f, args1 @ args2) }
  | Pexp_apply
      ( ({ pexp_desc = Pexp_function (params, None, Pfunction_body _); _ } as f),
        args )
    when simple_params params && unlabelled args
         && List.for_all (fun (_, a) -> is_value a) args ->
    beta f args
  | Pexp_apply (op, [(Nolabel, a); (Nolabel, b)]) -> (
    match ident_name op, int_const a, int_const b with
    | Some "+", Some x, Some y -> mk_int (x + y)
    | Some "*", Some x, Some y -> mk_int (x * y)
    | Some "-", Some x, Some y -> mk_int (x - y)
    | _ -> e)
  | Pexp_apply (op, [(Nolabel, a)]) -> (
    match ident_name op, int_const a with
    | Some "~-", Some x -> mk_int (-x)
    | _ -> e)
  | Pexp_let (Nonrecursive, [vb], body) -> (
    let v = vb.pvb_expr in
    match vb.pvb_pat.ppat_desc with
    | Ppat_var { txt = x; _ } when is_atom v && not (is_tmp x) ->
      simp (subst (SM.singleton x v) body)
    | Ppat_any when is_value v -> body
    | _ when is_unit_pat vb.pvb_pat && is_unit_expr v -> body
    | Ppat_tuple (ps, Closed) -> (
      match v.pexp_desc with
      | Pexp_tuple es
        when List.length ps = List.length es
             && List.for_all (fun (l, _) -> l = None) ps
             && List.for_all (fun (l, e) -> l = None && is_value e) es ->
        List.fold_right2
          (fun (_, p) (_, a) body ->
            reduce
              (mk
                 (Pexp_let
                    (Nonrecursive, [Ast_helper.Vb.mk p a], body))))
          ps es body
      | _ -> e)
    | _ -> e)
  | _ -> e

and beta (f : expression) args : expression =
  let f =
    match f.pexp_desc with
    | Pexp_function (params, _, _) when is_realisation params -> freshen f
    | _ -> f
  in
  let params, body =
    match f.pexp_desc with
    | Pexp_function (params, None, Pfunction_body body) -> params, body
    | _ -> assert false
  in
  let real = is_realisation params in
  let env = ref SM.empty in
  let lets = ref [] in
  let rec bind_pat (pat : pattern) (a : expression) =
    match pat.ppat_desc with
    | Ppat_var { txt = x; _ } ->
      if is_atom a
      then env := SM.add x a !env
      else
        let n = count x body in
        if n = 0
        then ()
        else if n = 1 && not (reads_field a)
        then env := SM.add x a !env
        else lets := (pat, a) :: !lets
    | Ppat_any -> ()
    | _ when is_unit_pat pat && is_unit_expr a -> ()
    | Ppat_constraint (p, _) -> bind_pat p a
    | Ppat_tuple (ps, Closed) -> (
      match a.pexp_desc with
      | Pexp_tuple es
        when List.length ps = List.length es
             && List.for_all (fun (l, _) -> l = None) ps
             && List.for_all (fun (l, _) -> l = None) es ->
        List.iter2 (fun (_, p) (_, a) -> bind_pat p a) ps es
      | _ -> lets := (pat, a) :: !lets)
    | _ -> lets := (pat, a) :: !lets
  in
  let rec go params args =
    match params, args with
    | p :: ps, (_, a) :: rest ->
      bind_pat (Option.get (param_pat p)) a;
      go ps rest
    | [], [] -> body
    | [], rest -> mk ~loc:body.pexp_loc (Pexp_apply (body, rest))
    | ps, [] ->
      { f with pexp_desc = Pexp_function (ps, None, Pfunction_body body) }
  in
  let rest = go params args in
  let rest = if real then fuse !env rest else rest in
  let rest = subst !env rest in
  let rest =
    List.fold_left
      (fun body (pat, a) ->
        mk ~loc:body.pexp_loc
          (Pexp_let (Nonrecursive, [Ast_helper.Vb.mk pat a], body)))
      rest !lets
  in
  simp rest

(* ------------------------------------------------------------------ *)
(* Step 2: the check                                                  *)
(* ------------------------------------------------------------------ *)

let rec is_fmt_chain e =
  match e.pexp_desc with
  | Pexp_ident { txt = Lident "port__fmt_nil"; _ } -> true
  | Pexp_apply (f, [(Nolabel, { pexp_desc = Pexp_tuple [(None, _); (None, r)]; _ })])
    when is_ident "port__fmt_cons" f ->
    is_fmt_chain r
  | _ -> false

let exn_ok e =
  match e.pexp_desc with
  | Pexp_construct (_, None) -> true
  | Pexp_function ([p], None, Pfunction_body { pexp_desc = Pexp_construct (_, Some a); _ })
    -> (
    match param_pat p with
    | Some { ppat_desc = Ppat_var { txt = x; _ }; _ } -> is_ident x a
    | _ -> false)
  | _ -> false

let rec check_c (e : expression) : unit =
  let bad what = reject e.pexp_loc "%s" what in
  match e.pexp_desc with
  | Pexp_apply (h, args) when ident_name h <> None && is_marker (Option.get (ident_name h))
    -> (
    let args = List.map snd args in
    match Option.get (ident_name h), args with
    | "port__bind", [m; k] ->
      check_c m;
      check_fun k
    | "port__ret", [v] -> check_v v
    | "port__seq", [a; b] ->
      check_c a;
      check_c b
    | "port__raise", [x; v] ->
      if not (exn_ok x) then bad "port__raise: not a declared exception";
      check_v v
    | "port__try_with", [body; x; h] ->
      if not (exn_ok x) then bad "port__try_with: not a declared exception";
      check_fun body;
      check_fun h
    | "port__try_with_any", [body; h] ->
      check_fun body;
      check_fun h
    | "port__match_exn", [body; x; h; k] ->
      if not (exn_ok x) then bad "port__match_exn: not a declared exception";
      check_fun body;
      check_fun h;
      check_fun k
    | "port__get_fuel", [u] -> check_v u
    | ( ( "port__poly_equal" | "port__poly_not_equal" | "port__poly_compare"
        | "port__phys_equal" | "port__phys_not_equal" ),
        [a; b] ) ->
      check_v a;
      check_v b
    | "port__gap", _ :: rest -> List.iter check_v rest
    | name, _ -> bad (name ^ ": not applied as the kit applies it"))
  | Pexp_ident { txt = Lident "port__out_of_fuel"; _ } -> ()
  | Pexp_apply (h, args) ->
    (match h.pexp_desc with
    | Pexp_ident _ ->
      if is_pure_op h
      then bad "a pure primitive where a computation is expected (use ret)"
    | Pexp_field (v, _) -> check_v v
    | Pexp_apply (g, [(Nolabel, _)]) when is_ident "port__gap" g -> ()
    | Pexp_function _ ->
      bad "a literal function applied to something that is not a value"
    | _ -> bad "the head of a call is not a name");
    List.iter (fun (_, a) -> check_v a) args
  | Pexp_match (s, cases) ->
    check_v s;
    List.iter (check_case check_c) cases
  | Pexp_ifthenelse (c, a, b) ->
    check_v c;
    check_c a;
    Option.iter check_c b
  | Pexp_let (rf, vbs, body) ->
    List.iter (check_vb rf) vbs;
    check_c body
  | Pexp_sequence (a, b) ->
    check_c a;
    check_c b
  | Pexp_assert v -> check_v v
  | Pexp_try (b, cases) ->
    check_c b;
    List.iter (check_case check_c) cases
  | Pexp_while (c, b) ->
    check_c c;
    check_c b
  | Pexp_lazy b -> check_c b
  | Pexp_setfield (a, _, b) ->
    check_v a;
    check_v b
  | Pexp_field (a, _) ->
    (* the read of a mutable field, which the declarations give in the monad *)
    check_v a
  | Pexp_constraint (e, _) -> check_c e
  | Pexp_ident _ | Pexp_constant _ | Pexp_construct _ | Pexp_tuple _
  | Pexp_record _ | Pexp_function _ | Pexp_variant _ ->
    bad "a value where a computation is expected (use ret)"
  | _ -> bad "a form that the tool does not know, where a computation is expected"

and check_vb rf vb =
  (match rf, vb.pvb_expr.pexp_desc with
  | Recursive, Pexp_function _ | Nonrecursive, _ -> ()
  | Recursive, _ ->
    reject vb.pvb_expr.pexp_loc "let rec of something that is not a function");
  check_v vb.pvb_expr

and check_case chk c =
  Option.iter check_v c.pc_guard;
  chk c.pc_rhs

and check_fun (k : expression) : unit =
  match k.pexp_desc with
  | Pexp_function _ | Pexp_ident _ -> check_v k
  | _ -> reject k.pexp_loc "a continuation that is neither a function nor a name"

and check_v (e : expression) : unit =
  let bad what = reject e.pexp_loc "%s" what in
  match e.pexp_desc with
  | Pexp_ident { txt = Lident x; _ } when is_marker x ->
    if not (String.equal x "port__fmt_nil")
    then bad (x ^ ": an operation of the monad used as a value")
  | Pexp_ident _ | Pexp_constant _ -> ()
  | Pexp_function (params, _, body) -> (
    List.iter
      (fun p ->
        match p.pparam_desc with
        | Pparam_val (_, Some d, _) -> check_v d
        | _ -> ())
      params;
    match body with
    | Pfunction_body b -> check_c b
    | Pfunction_cases (cases, _, _) -> List.iter (check_case check_c) cases)
  | Pexp_construct (_, None) | Pexp_variant (_, None) -> ()
  | Pexp_construct (_, Some a) | Pexp_variant (_, Some a) -> check_v a
  | Pexp_tuple l -> List.iter (fun (_, e) -> check_v e) l
  | Pexp_record (fs, base) ->
    List.iter (fun (_, e) -> check_v e) fs;
    Option.iter check_v base
  | Pexp_field (a, _) -> check_v a
  | Pexp_constraint (a, _) -> check_v a
  | Pexp_apply (f, args)
    when is_pure_op f || path_name f = Some "Obj.magic"
         || is_ident "port__fmt_cons" f ->
    List.iter (fun (_, a) -> check_v a) args
  | Pexp_ifthenelse (c, a, Some b) ->
    check_v c;
    check_v a;
    check_v b
  | Pexp_match (s, cases) ->
    check_v s;
    List.iter (check_case check_v) cases
  | Pexp_let (Nonrecursive, vbs, body) ->
    List.iter (check_vb Nonrecursive) vbs;
    check_v body
  | Pexp_apply _ ->
    bad "a call where a value is expected (bind its result first: let* x := ... in)"
  | _ -> bad "an effect or an unknown form where a value is expected"

(* ------------------------------------------------------------------ *)
(* Step 3: the monad goes                                             *)
(* ------------------------------------------------------------------ *)

let let_ pat rhs body =
  mk ~loc:rhs.pexp_loc (Pexp_let (Nonrecursive, [Ast_helper.Vb.mk pat rhs], body))

(* The body of a thunk [fun _ -> b] or [fun () -> b]. *)
let thunk_body (k : expression) : expression =
  match k.pexp_desc with
  | Pexp_function ([p], None, Pfunction_body b) -> (
    match param_pat p with
    | Some pat when pat.ppat_desc = Ppat_any || is_unit_pat pat -> b
    | Some { ppat_desc = Ppat_var { txt = x; _ }; _ } when count x b = 0 -> b
    | _ -> mk (Pexp_apply (k, [Nolabel, mk (Pexp_construct (lid "()", None))])))
  | _ -> mk (Pexp_apply (k, [Nolabel, mk (Pexp_construct (lid "()", None))]))

(* A handler [fun p -> h] as the pattern [p] and the expression [h]. *)
let handler (k : expression) : pattern * expression =
  match k.pexp_desc with
  | Pexp_function ([p], None, Pfunction_body b) when param_pat p <> None ->
    Option.get (param_pat p), b
  | _ ->
    incr fresh_counter;
    let x = "x__h_" ^ string_of_int !fresh_counter in
    pvar x, mk (Pexp_apply (k, [Nolabel, evar x]))

(* The pattern [E p] of a declared exception. *)
let exn_pat (x : expression) (p : pattern) : pattern =
  match x.pexp_desc with
  | Pexp_construct (c, None) -> Ast_helper.Pat.construct c None
  | Pexp_function (_, _, Pfunction_body { pexp_desc = Pexp_construct (c, Some _); _ })
    ->
    Ast_helper.Pat.construct c (Some ([], p))
  | _ -> reject x.pexp_loc "not a declared exception"

(* The handler of a declared exception. For a constant exception the
   pattern [E] binds nothing, so a handler that names its unit argument gets
   [let x = () in] before its body. *)
let exn_handler (x : expression) (h : expression) : pattern * expression =
  let p, hb = handler h in
  match x.pexp_desc, p.ppat_desc with
  | Pexp_construct (_, None), Ppat_any -> p, hb
  | Pexp_construct (_, None), _ when is_unit_pat p -> p, hb
  | Pexp_construct (_, None), _ ->
    p, let_ p (mk (Pexp_construct (lid "()", None))) hb
  | _ -> p, hb

let exn_expr (x : expression) (v : expression) : expression =
  match x.pexp_desc with
  | Pexp_construct (c, None) -> mk (Pexp_construct (c, None))
  | Pexp_function (_, _, Pfunction_body { pexp_desc = Pexp_construct (c, Some _); _ })
    ->
    mk (Pexp_construct (c, Some v))
  | _ -> reject x.pexp_loc "not a declared exception"

let rec fmt_chain_args e =
  match e.pexp_desc with
  | Pexp_ident { txt = Lident "port__fmt_nil"; _ } -> []
  | Pexp_apply (_, [(Nolabel, { pexp_desc = Pexp_tuple [(None, a); (None, r)]; _ })])
    ->
    let a =
      match a.pexp_desc with
      | Pexp_apply (g, [(Nolabel, a')]) when path_name g = Some "Obj.magic" -> a'
      | _ -> a
    in
    (Nolabel, a) :: fmt_chain_args r
  | _ -> assert false

let binop name a b = mk (Pexp_apply (evar name, [Nolabel, a; Nolabel, b]))

let rec unm (e : expression) : expression =
  let m = { Ast_mapper.default_mapper with expr = (fun _ e -> unm e) } in
  let e = Ast_mapper.default_mapper.expr m e in
  match e.pexp_desc with
  | Pexp_ident { txt = Lident "port__out_of_fuel"; _ } ->
    mk (Pexp_assert (mk (Pexp_construct (lid "false", None))))
  | Pexp_apply (h, args) -> (
    let argl = List.map snd args in
    match ident_name h, argl with
    | Some "port__bind", [m; k] -> (
      match k.pexp_desc with
      | Pexp_function ([p], None, Pfunction_body body) when param_pat p <> None
        -> (
        let pat = Option.get (param_pat p) in
        match pat.ppat_desc with
        | Ppat_var { txt = x; _ } -> (
          match body.pexp_desc with
          | Pexp_let (Nonrecursive, [vb], k')
            when is_ident x vb.pvb_expr && count x k' = 0 ->
            let_ vb.pvb_pat m k'
          | Pexp_match (s, [{ pc_lhs; pc_guard = None; pc_rhs }])
            when is_ident x s && count x pc_rhs = 0 ->
            let_ pc_lhs m pc_rhs
          | _ -> let_ pat m body)
        | _ -> let_ pat m body)
      | _ ->
        incr fresh_counter;
        let x = "x__k_" ^ string_of_int !fresh_counter in
        let_ (pvar x) m (mk (Pexp_apply (k, [Nolabel, evar x]))))
    | Some "port__ret", [v] -> v
    | Some "port__seq", [a; b] -> mk ~loc:e.pexp_loc (Pexp_sequence (a, b))
    | Some "port__raise", [x; v] ->
      mk (Pexp_apply (evar "raise", [Nolabel, exn_expr x v]))
    | Some "port__try_with", [body; x; h] ->
      let p, hb = exn_handler x h in
      mk
        (Pexp_try
           (thunk_body body, [Ast_helper.Exp.case (exn_pat x p) hb]))
    | Some "port__try_with_any", [body; h] ->
      let p, hb = handler h in
      mk (Pexp_try (thunk_body body, [Ast_helper.Exp.case p hb]))
    | Some "port__match_exn", [body; x; h; k] ->
      let p, hb = exn_handler x h in
      let q, kb = handler k in
      mk
        (Pexp_match
           ( thunk_body body,
             [ Ast_helper.Exp.case
                 (Ast_helper.Pat.exception_ (exn_pat x p))
                 hb;
               Ast_helper.Exp.case q kb ] ))
    | Some "port__get_fuel", [_] -> mk (Pexp_construct (lid "()", None))
    | Some "port__poly_equal", [a; b] -> binop "=" a b
    | Some "port__poly_not_equal", [a; b] -> binop "<>" a b
    | Some "port__poly_compare", [a; b] -> binop "compare" a b
    | Some "port__phys_equal", [a; b] -> binop "==" a b
    | Some "port__phys_not_equal", [a; b] -> binop "!=" a b
    | Some "port__gap", name :: _ -> gap name
    | _ -> (
      match h.pexp_desc with
      | Pexp_apply (g, [(Nolabel, name)]) when is_ident "port__gap" g -> gap name
      | _ -> (
        (* the arguments of a format, after the format again *)
        match List.rev args with
        | (Nolabel, last) :: before when is_fmt_chain last ->
          { e with
            pexp_desc = Pexp_apply (h, List.rev before @ fmt_chain_args last)
          }
        | _ -> e)))
  | _ -> e

and gap (name : expression) : expression =
  let s =
    match name.pexp_desc with
    | Pexp_constant { pconst_desc = Pconst_string (s, _, _); _ } -> s
    | _ -> "?"
  in
  mk
    (Pexp_apply
       ( mk (Pexp_ident (Location.mknoloc (Longident.Ldot (Location.mknoloc (Longident.Lident "Misc"), Location.mknoloc "fatal_error")))),
         [ ( Nolabel,
             mk
               (Pexp_constant
                  (Ast_helper.Const.string ("PORT-GAP(unported): " ^ s))) ) ] ))

(* ------------------------------------------------------------------ *)
(* Step 4: tidying                                                    *)
(* ------------------------------------------------------------------ *)

(* [?l:None] is nothing and [?l:(Some v)] is [~l:v]. *)
let tidy_optional args =
  List.filter_map
    (fun (l, a) ->
      match l, a.pexp_desc with
      | Optional _, Pexp_construct ({ txt = Lident "None"; _ }, None) -> None
      | Optional s, Pexp_construct ({ txt = Lident "Some"; _ }, Some v) ->
        Some (Labelled s, v)
      | _ -> Some (l, a))
    args

(* The fuel is [()] in OCaml: the parameters and the arguments of that name
   go, with their bindings. *)
let is_fuel_expr e = match ident_name e with Some x -> is_fuel x | None -> false

let is_fuel_pat p =
  match p.ppat_desc with Ppat_var { txt; _ } -> is_fuel txt | _ -> false

let rec defuel (e : expression) : expression =
  let m = { Ast_mapper.default_mapper with expr = (fun _ e -> defuel e) } in
  let e = Ast_mapper.default_mapper.expr m e in
  match e.pexp_desc with
  | Pexp_apply (h, args) -> (
    let args = List.filter (fun (_, a) -> not (is_fuel_expr a)) args in
    match args with [] -> h | _ -> { e with pexp_desc = Pexp_apply (h, args) })
  | Pexp_function (params, c, body) -> (
    let params =
      List.filter
        (fun p ->
          match param_pat p with Some pat -> not (is_fuel_pat pat) | None -> true)
        params
    in
    match params, body with
    | [], Pfunction_body b -> b
    | _ -> { e with pexp_desc = Pexp_function (params, c, body) })
  | Pexp_let (Nonrecursive, [vb], body)
    when is_fuel_pat vb.pvb_pat
         && (is_unit_expr vb.pvb_expr || is_fuel_expr vb.pvb_expr) ->
    (* [let fuel = () in], which is what [get_fuel tt] has become; any other
       right side stays, with its effects *)
    body
  | _ -> e

(* Does [t], which occurs once in [e], stand where OCaml evaluates it before
   anything else of [e] that has an effect? Arguments, the components of
   tuples and of constructors go right to left. *)
type scan =
  | Found
  | Pure
  | Blocked

let rec scan (t : string) (e : expression) : scan =
  let seq (es : expression list) : scan =
    (* in the order of evaluation *)
    let rec go = function
      | [] -> Pure
      | e :: rest -> ( match scan t e with Pure -> go rest | r -> r)
    in
    go es
  in
  match e.pexp_desc with
  | Pexp_ident { txt = Lident x; _ } -> if String.equal x t then Found else Pure
  | Pexp_ident _ | Pexp_constant _ -> Pure
  | Pexp_function _ -> if count t e > 0 then Blocked else Pure
  | Pexp_construct (_, None) | Pexp_variant (_, None) -> Pure
  | Pexp_construct (_, Some a) | Pexp_variant (_, Some a) -> scan t a
  | Pexp_tuple l -> seq (List.rev_map snd l)
  | Pexp_record (fs, None) -> (
    (* OCaml evaluates the fields in the order of the type, which the tool
       does not know: [t] goes in only if nothing else in the record has an
       effect, and then the order does not matter. *)
    let rs = List.map (fun (_, e) -> scan t e) fs in
    let others_pure =
      List.length (List.filter (fun r -> r <> Pure) rs) <= 1
    in
    match List.find_opt (fun r -> r <> Pure) rs with
    | None -> Pure
    | Some Found when others_pure -> Found
    | Some _ -> Blocked)
  | Pexp_field (a, _) -> (
    (* the read of a field, which may be mutable, is not crossed *)
    match scan t a with Pure -> Blocked | r -> r)
  | Pexp_constraint (a, _) -> scan t a
  | Pexp_apply (h, [(Nolabel, a); (Nolabel, b)])
    when ident_name h = Some "&&" || ident_name h = Some "||" -> (
    match scan t a with Pure -> if count t b > 0 then Blocked else Pure | r -> r)
  | Pexp_apply (h, args) -> (
    match seq (List.rev_map snd args @ [h]) with
    | Pure -> if is_pure_op h then Pure else Blocked
    | r -> r)
  | Pexp_let (Nonrecursive, [vb], body) -> (
    match scan t vb.pvb_expr with Pure -> scan t body | r -> r)
  | Pexp_sequence (a, b) -> ( match scan t a with Pure -> scan t b | r -> r)
  | Pexp_match (s, _) | Pexp_ifthenelse (s, _, _) -> (
    match scan t s with Pure -> Blocked | r -> r)
  | Pexp_assert a -> ( match scan t a with Pure -> Blocked | r -> r)
  | _ -> Blocked

let rec renest (e : expression) : expression =
  let m = { Ast_mapper.default_mapper with expr = (fun _ e -> renest e) } in
  let e = Ast_mapper.default_mapper.expr m e in
  match e.pexp_desc with
  | Pexp_let
      (Nonrecursive, [{ pvb_pat = { ppat_desc = Ppat_var { txt = t; _ }; _ }; pvb_expr; _ }], body)
    when is_tmp t && count t body = 1 && scan t body = Found ->
    subst (SM.singleton t pvb_expr) body
  | _ -> e

(* [if a then true else b] is [a || b]; [if a then b else false] is
   [a && b]. *)
let rec sugar (e : expression) : expression =
  let m = { Ast_mapper.default_mapper with expr = (fun _ e -> sugar e) } in
  let e = Ast_mapper.default_mapper.expr m e in
  let is_bool b x =
    match x.pexp_desc with
    | Pexp_construct ({ txt = Lident s; _ }, None) -> String.equal s b
    | _ -> false
  in
  match e.pexp_desc with
  | Pexp_ifthenelse (a, t, Some b) when is_bool "true" t -> binop "||" a b
  | Pexp_ifthenelse (a, b, Some f) when is_bool "false" f -> binop "&&" a b
  | Pexp_ifthenelse (a, b, Some u) when is_unit_expr u ->
    { e with pexp_desc = Pexp_ifthenelse (a, b, None) }
  | Pexp_apply (h, [(Nolabel, { pexp_desc = Pexp_apply (eq, [a; b]); _ })])
    when is_ident "not" h && is_ident "=" eq ->
    mk (Pexp_apply (evar "<>", [a; b]))
  | Pexp_apply (h, args) ->
    { e with pexp_desc = Pexp_apply (h, tidy_optional args) }
  | _ -> e

(* THE NAMES OF THE PORT. Rocq's extraction renames a variable that hides
   another, or that has the name of a declared thing ([dacc] becomes [dacc0]).
   [names] holds the identifiers of the .v file. A binder [xN] that is not
   one of them, and for which exactly one of them is [x] with other digits or
   none, takes that name back when no occurrence of that name is in its
   scope and no sibling binder has it: OCaml's own shadowing, as the
   compiler's code uses it. *)
let names : S.t ref = ref S.empty

let strip_digits s =
  let n = String.length s in
  let rec go i = if i > 0 && s.[i - 1] >= '0' && s.[i - 1] <= '9' then go (i - 1) else i in
  String.sub s 0 (go n)

let original (x : string) : string option =
  if S.mem x !names || is_tmp x || is_real_var x
  then None
  else
    let base = strip_digits x in
    if String.equal base x
    then None
    else
      match S.elements (S.filter (fun n -> String.equal (strip_digits n) base) !names) with
      | [n] -> Some n
      | _ -> None

(* [rename_binders vars scopes]: for each variable of [vars] (the binders of
   one construct) that can take its name back, the renaming; [scopes] are
   the expressions in which the binders are visible. *)
let renaming (vars : S.t) (scopes : expression list) : string SM.t =
  S.fold
    (fun x (ren, taken) ->
      match original x with
      | Some n
        when (not (S.mem n taken))
             && List.for_all (fun e -> count n e = 0) scopes ->
        SM.add x n ren, S.add n taken
      | _ -> ren, taken)
    vars
    (SM.empty, vars)
  |> fst

let apply_renaming ren (e : expression) : expression =
  subst (SM.map evar ren) e

let rename_in_pat ren (p : pattern) : pattern =
  rename_pat (SM.map (fun n -> Some n) ren) p

let rec reshadow (e : expression) : expression =
  let e =
    try
      match e.pexp_desc with
      | Pexp_let (Nonrecursive, vbs, body) ->
        let ren = renaming (vbs_vars vbs) [body] in
        if SM.is_empty ren
        then e
        else
          let vbs =
            List.map (fun vb -> { vb with pvb_pat = rename_in_pat ren vb.pvb_pat }) vbs
          in
          { e with pexp_desc = Pexp_let (Nonrecursive, vbs, apply_renaming ren body) }
      | Pexp_function (params, c, fbody) when params <> [] ->
        let vars =
          List.fold_left
            (fun acc p ->
              match p.pparam_desc with
              | Pparam_val (_, _, pat) -> S.union acc (pat_vars pat)
              | Pparam_newtype _ -> acc)
            S.empty params
        in
        (* the body as one expression: for [function] cases, the cases alone *)
        let body_expr =
          match fbody with
          | Pfunction_body b -> b
          | Pfunction_cases _ -> mk (Pexp_function ([], None, fbody))
        in
        let ren = renaming vars [body_expr] in
        if SM.is_empty ren
        then e
        else
          let params =
            List.map
              (fun p ->
                match p.pparam_desc with
                | Pparam_val (l, d, pat) ->
                  { p with pparam_desc = Pparam_val (l, d, rename_in_pat ren pat) }
                | Pparam_newtype _ -> p)
              params
          in
          let fbody =
            match fbody, (apply_renaming ren body_expr).pexp_desc with
            | Pfunction_body _, _ -> Pfunction_body (apply_renaming ren body_expr)
            | Pfunction_cases _, Pexp_function ([], None, fb) -> fb
            | Pfunction_cases _, _ -> assert false
          in
          { e with pexp_desc = Pexp_function (params, c, fbody) }
      | Pexp_match (s, cases) ->
        { e with pexp_desc = Pexp_match (s, List.map reshadow_case cases) }
      | Pexp_try (s, cases) ->
        { e with pexp_desc = Pexp_try (s, List.map reshadow_case cases) }
      | _ -> e
    with Reject _ -> e
  in
  let m = { Ast_mapper.default_mapper with expr = (fun _ e -> reshadow e) } in
  Ast_mapper.default_mapper.expr m e

and reshadow_case c =
  try
    let scopes = c.pc_rhs :: Option.to_list c.pc_guard in
    let ren = renaming (pat_vars c.pc_lhs) scopes in
    if SM.is_empty ren
    then c
    else
      { pc_lhs = rename_in_pat ren c.pc_lhs;
        pc_guard = Option.map (apply_renaming ren) c.pc_guard;
        pc_rhs = apply_renaming ren c.pc_rhs
      }
  with Reject _ -> c

(* THE SHORT NAMES OF MODULES. With [-aliases FILE] ([simplify_import.ml]),
   a module path that FILE gives a shorter name is written with it ([DA] for
   [Downwards_acc]), as the compiler's files do after [open! Simplify_import].
*)
let aliases : (string list * string) list ref = ref []

let rec flatten_lid (l : Longident.t) : string list =
  match l with
  | Lident s -> [s]
  | Ldot (a, b) -> flatten_lid a.txt @ [b.txt]
  | Lapply _ -> raise Exit

let unflatten_lid (l : string list) : Longident.t =
  match l with
  | [] -> assert false
  | x :: rest ->
    List.fold_left
      (fun acc s -> Longident.Ldot (Location.mknoloc acc, Location.mknoloc s))
      (Longident.Lident x) rest

let load_aliases file =
  let ic = open_in file in
  let str = Parse.implementation (Lexing.from_channel ic) in
  close_in ic;
  let expand path =
    match path with
    | m :: rest -> (
      match List.find_opt (fun (_, a) -> String.equal a m) !aliases with
      | Some (full, _) -> full @ rest
      | None -> path)
    | [] -> path
  in
  List.iter
    (fun item ->
      match item.pstr_desc with
      | Pstr_module
          { pmb_name = { txt = Some name; _ };
            pmb_expr = { pmod_desc = Pmod_ident { txt; _ }; _ };
            _
          } -> (
        match flatten_lid txt with
        | path ->
          let path = expand path in
          if path <> [name] then aliases := !aliases @ [path, name]
        | exception Exit -> ())
      | _ -> ())
    str

let shorten (l : Longident.t) : Longident.t =
  match flatten_lid l with
  | exception Exit -> l
  | comps ->
    let n = List.length comps in
    (* the module part is all but the last component *)
    let rec try_prefix k =
      if k = 0
      then l
      else
        let prefix = List.filteri (fun i _ -> i < k) comps in
        let rest = List.filteri (fun i _ -> i >= k) comps in
        let candidates =
          List.filter (fun (p, a) -> p = prefix && String.length a < String.length (String.concat "." prefix)) !aliases
        in
        match candidates with
        | [] -> try_prefix (k - 1)
        | (_, a0) :: more ->
          let best =
            List.fold_left
              (fun best (_, a) -> if String.length a < String.length best then a else best)
              a0 more
          in
          unflatten_lid (best :: rest)
    in
    try_prefix (n - 1)

let shorten_mapper =
  let sl (l : Longident.t Location.loc) = { l with txt = shorten l.txt } in
  { Ast_mapper.default_mapper with
    expr =
      (fun m e ->
        let e = Ast_mapper.default_mapper.expr m e in
        match e.pexp_desc with
        | Pexp_ident l -> { e with pexp_desc = Pexp_ident (sl l) }
        | Pexp_construct (l, a) -> { e with pexp_desc = Pexp_construct (sl l, a) }
        | Pexp_field (a, l) -> { e with pexp_desc = Pexp_field (a, sl l) }
        | Pexp_setfield (a, l, b) -> { e with pexp_desc = Pexp_setfield (a, sl l, b) }
        | Pexp_record (fs, b) ->
          { e with pexp_desc = Pexp_record (List.map (fun (l, x) -> sl l, x) fs, b) }
        | _ -> e);
    pat =
      (fun m p ->
        let p = Ast_mapper.default_mapper.pat m p in
        match p.ppat_desc with
        | Ppat_construct (l, a) -> { p with ppat_desc = Ppat_construct (sl l, a) }
        | Ppat_record (fs, c) ->
          { p with ppat_desc = Ppat_record (List.map (fun (l, x) -> sl l, x) fs, c) }
        | _ -> p);
    typ =
      (fun m t ->
        let t = Ast_mapper.default_mapper.typ m t in
        match t.ptyp_desc with
        | Ptyp_constr (l, args) -> { t with ptyp_desc = Ptyp_constr (sl l, args) }
        | _ -> t)
  }

(* THE NAMES THAT ROCQ REFUSED. OCaml has separate name spaces for values,
   types, fields and constructors, and Rocq has one; and some OCaml names are
   words of Rocq. The port puts ONE underscore after such a name (GUIDE.md).
   Here a field, a constructor or a type loses one underscore at its end, and
   a value does if what is left is a word of Rocq. *)
let rocq_words =
  S.of_list
    [ "at"; "by"; "cofix"; "exists"; "exists2"; "fix"; "forall"; "return";
      "using"; "where" ]

let strip_us s =
  let n = String.length s in
  if n > 1 && s.[n - 1] = '_' && s.[n - 2] <> '_' then String.sub s 0 (n - 1) else s

let strip_value s =
  let s' = strip_us s in
  if S.mem s' rocq_words then s' else s

let strip_last (f : string -> string) (l : Longident.t Location.loc) =
  match l.txt with
  | Lident s -> { l with txt = Longident.Lident (f s) }
  | Ldot (a, b) -> { l with txt = Longident.Ldot (a, { b with txt = f b.txt }) }
  | Lapply _ -> l

let underscore_mapper =
  let sl = strip_last strip_us in
  { Ast_mapper.default_mapper with
    expr =
      (fun m e ->
        let e = Ast_mapper.default_mapper.expr m e in
        match e.pexp_desc with
        | Pexp_ident ({ txt = Lident x; _ } as l) ->
          { e with pexp_desc = Pexp_ident { l with txt = Lident (strip_value x) } }
        | Pexp_construct (l, a) -> { e with pexp_desc = Pexp_construct (sl l, a) }
        | Pexp_field (a, l) -> { e with pexp_desc = Pexp_field (a, sl l) }
        | Pexp_setfield (a, l, b) -> { e with pexp_desc = Pexp_setfield (a, sl l, b) }
        | Pexp_record (fs, b) ->
          { e with pexp_desc = Pexp_record (List.map (fun (l, x) -> sl l, x) fs, b) }
        | _ -> e);
    pat =
      (fun m p ->
        let p = Ast_mapper.default_mapper.pat m p in
        match p.ppat_desc with
        | Ppat_var v -> { p with ppat_desc = Ppat_var { v with txt = strip_value v.txt } }
        | Ppat_construct (l, a) -> { p with ppat_desc = Ppat_construct (sl l, a) }
        | Ppat_record (fs, c) ->
          { p with ppat_desc = Ppat_record (List.map (fun (l, x) -> sl l, x) fs, c) }
        | _ -> p);
    typ =
      (fun m t ->
        let t = Ast_mapper.default_mapper.typ m t in
        match t.ptyp_desc with
        | Ptyp_constr (l, args) -> { t with ptyp_desc = Ptyp_constr (sl l, args) }
        | _ -> t);
    type_declaration =
      (fun m d ->
        let d = Ast_mapper.default_mapper.type_declaration m d in
        { d with ptype_name = { d.ptype_name with txt = strip_us d.ptype_name.txt } });
    label_declaration =
      (fun m d ->
        let d = Ast_mapper.default_mapper.label_declaration m d in
        { d with pld_name = { d.pld_name with txt = strip_us d.pld_name.txt } });
    constructor_declaration =
      (fun m d ->
        let d = Ast_mapper.default_mapper.constructor_declaration m d in
        { d with pcd_name = { d.pcd_name with txt = strip_us d.pcd_name.txt } })
  }

let load_names file =
  let ic = open_in file in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  let is_id c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
    || c = '_' || c = '\''
  in
  let i = ref 0 in
  while !i < n do
    if is_id s.[!i]
    then (
      let j = ref !i in
      while !j < n && is_id s.[!j] do incr j done;
      names := S.add (String.sub s !i (!j - !i)) !names;
      i := !j)
    else incr i
  done

(* A parameter [name__opt] is written [?name]; a call, in the same file, of
   a function defined with such parameters passes them with [?name:]. *)
let opt_table : (string, (int * string) list) Hashtbl.t = Hashtbl.create 16

let opt_positions params =
  List.mapi (fun i p ->
         match param_pat p with
         | Some { ppat_desc = Ppat_var { txt; _ }; _ } -> (
           match opt_name txt with Some n -> Some (i, n) | None -> None)
         | _ -> None)
    params
  |> List.filter_map (fun x -> x)

let rec optional (e : expression) : expression =
  (* the definitions first, so that the calls below them know *)
  (match e.pexp_desc with
  | Pexp_let (_, vbs, _) -> List.iter note_vb vbs
  | _ -> ());
  let m = { Ast_mapper.default_mapper with expr = (fun _ e -> optional e) } in
  let e = Ast_mapper.default_mapper.expr m e in
  match e.pexp_desc with
  | Pexp_function (params, c, body) when opt_positions params <> [] ->
    let env = ref SM.empty in
    let params =
      List.map
        (fun p ->
          match param_pat p with
          | Some { ppat_desc = Ppat_var { txt; _ }; _ } -> (
            match opt_name txt with
            | Some n ->
              env := SM.add txt (evar n) !env;
              { p with pparam_desc = Pparam_val (Optional n, None, pvar n) }
            | None -> p)
          | _ -> p)
        params
    in
    let body =
      match body with
      | Pfunction_body b -> Pfunction_body (subst !env b)
      | Pfunction_cases _ -> body
    in
    { e with pexp_desc = Pexp_function (params, c, body) }
  | Pexp_apply (h, args) -> (
    match ident_name h with
    | Some f when Hashtbl.mem opt_table f ->
      let pos = Hashtbl.find opt_table f in
      let args =
        List.mapi
          (fun i (l, a) ->
            match l, List.assoc_opt i pos with
            | Nolabel, Some n -> Optional n, a
            | _ -> l, a)
          args
      in
      { e with pexp_desc = Pexp_apply (h, args) }
    | _ -> e)
  | _ -> e

and note_vb vb =
  match vb.pvb_pat.ppat_desc, vb.pvb_expr.pexp_desc with
  | Ppat_var { txt = f; _ }, Pexp_function (params, _, _) -> (
    match opt_positions params with
    | [] -> ()
    | pos -> Hashtbl.replace opt_table f pos)
  | _ -> ()

(* ------------------------------------------------------------------ *)
(* The file                                                           *)
(* ------------------------------------------------------------------ *)

(* [let f = failwith "AXIOM TO BE REALIZED ..."]: a parameter of the .v file
   without a realisation, which is a thing of the compiler's file that is not
   ported yet (PORT-GAP(unported)). The extracted file gets a function that
   stops with a fatal error that names it. *)
let axiom_stub (vb : value_binding) : value_binding =
  match vb.pvb_pat.ppat_desc, vb.pvb_expr.pexp_desc with
  | ( Ppat_var { txt = name; _ },
      Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident "failwith"; _ }; _ },
          [ ( Nolabel,
              { pexp_desc =
                  Pexp_constant { pconst_desc = Pconst_string (msg, _, _); _ };
                _
              } ) ] ) )
    when String.length msg >= 5 && String.sub msg 0 5 = "AXIOM" ->
    let body =
      mk
        (Pexp_apply
           ( mk
               (Pexp_ident
                  (Location.mknoloc
                     (Longident.Ldot
                        ( Location.mknoloc (Longident.Lident "Misc"),
                          Location.mknoloc "fatal_error" )))),
             [ ( Nolabel,
                 mk
                   (Pexp_constant
                      (Ast_helper.Const.string ("PORT-GAP(unported): " ^ name)))
               ) ] ))
    in
    { vb with
      pvb_expr =
        mk
          (Pexp_function
             ( [ { pparam_loc = Location.none;
                   pparam_desc =
                     Pparam_val (Nolabel, None, Ast_helper.Pat.any ())
                 } ],
               None,
               Pfunction_body body ))
    }
  | _ -> vb

(* [let f x = x.f]: the projection that Rocq makes for the field [f] of a
   record of the .v file. The compiler's file has no such function, and the
   uses are printed as [x.f]. *)
let is_projection (vb : value_binding) : bool =
  match vb.pvb_pat.ppat_desc, vb.pvb_expr.pexp_desc with
  | ( Ppat_var { txt = name; _ },
      Pexp_function
        ( [ { pparam_desc =
                Pparam_val (Nolabel, None, { ppat_desc = Ppat_var { txt = x; _ }; _ });
              _
            } ],
          None,
          Pfunction_body
            { pexp_desc = Pexp_field (r, { txt = Lident field; _ }); _ } ) ) ->
    String.equal name field && is_ident x r
  | _ -> false

let rec map_structure (f : expression -> expression) (str : structure) : structure =
  List.filter_map
    (fun item ->
      match item.pstr_desc with
      | Pstr_value (_, [vb]) when is_projection vb -> None
      | Pstr_open _ | Pstr_attribute _ -> None
      | Pstr_module { pmb_expr = { pmod_desc = Pmod_ident _; _ }; _ } -> None
      | Pstr_module ({ pmb_expr = { pmod_desc = Pmod_structure s; _ } as me; _ } as mb)
        ->
        Some
          { item with
            pstr_desc =
              Pstr_module
                { mb with
                  pmb_expr = { me with pmod_desc = Pmod_structure (map_structure f s) }
                }
          }
      | Pstr_value (rf, vbs) ->
        Some
          { item with
            pstr_desc =
              Pstr_value
                ( rf,
                  List.map
                    (fun vb ->
                      { vb with pvb_expr = f vb.pvb_expr; pvb_attributes = [] })
                    vbs )
          }
      | _ -> Some item)
    str

let rec stub_structure (str : structure) : structure =
  List.map
    (fun item ->
      match item.pstr_desc with
      | Pstr_value (rf, vbs) ->
        { item with pstr_desc = Pstr_value (rf, List.map axiom_stub vbs) }
      | Pstr_module ({ pmb_expr = { pmod_desc = Pmod_structure s; _ } as me; _ } as mb)
        ->
        { item with
          pstr_desc =
            Pstr_module
              { mb with
                pmb_expr = { me with pmod_desc = Pmod_structure (stub_structure s) }
              }
        }
      | _ -> item)
    str

let rec check_structure (str : structure) =
  List.iter
    (fun item ->
      match item.pstr_desc with
      | Pstr_value (rf, vbs) -> List.iter (check_vb rf) vbs
      | Pstr_module { pmb_expr = { pmod_desc = Pmod_structure s; _ }; _ } ->
        check_structure s
      | _ -> ())
    str

let () =
  let input = ref None in
  let output = ref None in
  Arg.parse
    [ "-o", Arg.String (fun s -> output := Some s), "FILE  the file to write";
      "-no-renest", Arg.Set no_renest, "  keep the temporaries as lets";
      "-keep-fuel", Arg.Set keep_fuel, "  keep the fuel arguments";
      "-names", Arg.String load_names, "FILE.v  the .v file, for its names";
      ( "-aliases",
        Arg.String load_aliases,
        "FILE.ml  module aliases to write paths with" ) ]
    (fun s -> input := Some s)
    "unmonad RAW.ml -o OUT.ml";
  let input =
    match !input with
    | Some s -> s
    | None ->
      prerr_endline "unmonad: no input";
      exit 2
  in
  let ic = open_in input in
  let lexbuf = Lexing.from_channel ic in
  Location.init lexbuf input;
  let str = Parse.implementation lexbuf in
  close_in ic;
  match
    let str = stub_structure str in
    let str = map_structure simp str in
    check_structure str;
    let str = map_structure unm str in
    let str = if !keep_fuel then str else map_structure defuel str in
    let str = if !no_renest then str else map_structure renest str in
    List.iter
      (fun item ->
        match item.pstr_desc with
        | Pstr_value (_, vbs) -> List.iter note_vb vbs
        | _ -> ())
      str;
    let str = map_structure optional str in
    let str = map_structure sugar str in
    let str = if S.is_empty !names then str else map_structure reshadow str in
    let str = underscore_mapper.structure underscore_mapper str in
    if !aliases = [] then str else shorten_mapper.structure shorten_mapper str
  with
  | str -> (
    let print ppf = Format.fprintf ppf "%a@." Pprintast.structure str in
    match !output with
    | None -> print Format.std_formatter
    | Some o ->
      let oc = open_out o in
      print (Format.formatter_of_out_channel oc);
      close_out oc)
  | exception Reject (loc, msg) ->
    Format.eprintf "%a:@ unmonad: %s@." Location.print_loc loc msg;
    exit 1
