(* Proof helpers for boolean comparisons on [Z]. *)

From Stdlib Require Import ZArith Lia.

Local Open Scope Z_scope.

(* Split on every boolean comparison in the goal, turning [x <? y] into the
   cases [x < y] / [y <= x] etc., then let [lia] (a decision procedure for
   linear integer arithmetic) finish. *)
Ltac case_zcmp :=
  repeat match goal with
         | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
         | |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
         | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
         end; simpl; first [ reflexivity | exfalso; lia ].

(* Turn a hypothesis [(x <? y) = true] into [x < y], etc. *)
Ltac zcmp_hyp H :=
  first [ apply Z.ltb_lt in H | apply Z.leb_le in H | apply Z.eqb_eq in H ].
