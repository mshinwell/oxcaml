(* A loop over a string that counts its vowels by a match on each character. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external length : string -> int = "%string_length"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

let rec vowels s i acc =
  if i < length s
  then
    match unsafe_get s i with
    | 'a' | 'e' | 'i' | 'o' | 'u' -> vowels s (i + 1) (acc + 1)
    | _ -> vowels s (i + 1) acc
  else acc

let result = vowels (opaque "a quiet house") 0 0
