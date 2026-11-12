(* Swaps of the bytes of constants, which Simplify computes. *)

external bswap16 : int -> int = "%bswap16"

external bswap32 : int32 -> int32 = "%bswap_int32"

external bswap64 : int64 -> int64 = "%bswap_int64"

external int32_to_int : int32 -> int = "%int32_to_int"

external int64_to_int : int64 -> int = "%int64_to_int"

let result =
  ( bswap16 0x1234,
    bswap16 (-1),
    int32_to_int (bswap32 0x12345678l),
    int32_to_int (bswap32 128l),
    int64_to_int (bswap64 0x0102030405060708L) )
