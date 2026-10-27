(* Extraction directives for IntegerComparison.v, trusted by inspection:

   - [integer_comparison] is [Cmm.integer_comparison]; the constructor lists
     must be in the same order (compare with typing/scalar.ml).
   - [negate] and [swap] are [Cmm.negate_integer_comparison] and
     [Cmm.swap_integer_comparison]; the model's definitions are copies of
     the ones in typing/scalar.ml, so the extracted code calls the
     originals. *)

From Stdlib Require Import Extraction.
From OxCamlBackend Require Import IntegerComparison.

Extract Inductive integer_comparison => "Cmm.integer_comparison"
  [ "Cmm.Ceq" "Cmm.Cne" "Cmm.Clt" "Cmm.Cgt" "Cmm.Cle" "Cmm.Cge"
    "Cmm.Cult" "Cmm.Cugt" "Cmm.Cule" "Cmm.Cuge" ].
Extract Inlined Constant negate => "Cmm.negate_integer_comparison".
Extract Inlined Constant swap => "Cmm.swap_integer_comparison".
