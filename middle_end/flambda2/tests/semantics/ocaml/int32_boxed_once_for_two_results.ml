(* One number given back by two operations, each exported: its conjunction with
   -1 and its disjunction with 0, on boxed 32-bit integers. The front end
   unboxes the operand, computes and boxes the result, once for each. Simplify
   finds that each result is the operand unboxed, and boxes it once for the two.
   The validation makes the second box the first (FlambdaCseSpec.shareable). *)

external opaque : 'a -> 'a = "%opaque"

external logand : int32 -> int32 -> int32 = "%int32_and"

external logor : int32 -> int32 -> int32 = "%int32_or"

let x = opaque 12345l

let kept_by_and = logand x (-1l)

let kept_by_or = logor x 0l
