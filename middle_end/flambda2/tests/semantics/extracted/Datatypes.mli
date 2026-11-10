type nat =
  | O
  | S of nat

val snd : 'a1 * 'a2 -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list
