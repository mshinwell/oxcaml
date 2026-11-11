(* What realises the abstract primitives of the Rocq model in the extracted
   machine (see middle_end/flambda2/rocq/FlambdaExtract.v). Written by hand; the
   other modules of this directory are extracted.

   The model's [eval_prim : prim -> value list -> value option] is extracted to
   a call of the function held here, on untyped representations because this
   module comes before the one that defines [value]. The test tool installs a
   typed function with [Obj.repr]. *)

let eval_prim : (Obj.t -> Obj.t -> Obj.t) ref =
  ref (fun _ _ -> failwith "Prim_hook.eval_prim: no evaluator installed")

(* The model's [prim_eqb : prim -> prim -> bool], likewise. It has to decide
   equality of the tool's primitives, as the model takes that as an axiom. *)
let prim_eqb : (Obj.t -> Obj.t -> bool) ref =
  ref (fun _ _ -> failwith "Prim_hook.prim_eqb: no equality installed")

(* The model's [prim_may_fold : prim -> bool]: which primitives the
   normalisation may fold when their arguments are constants. Any answer is
   sound. *)
let prim_may_fold : (Obj.t -> bool) ref = ref (fun _ -> false)
