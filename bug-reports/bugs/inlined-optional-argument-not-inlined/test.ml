let f ?(x = 10) y =
  x + (y + 1) * (y + 2) + (y + 2) * (y + 3) + (y + 3) * (y + 4) + (y + 4) * (y + 5)
  + (y + 5) * (y + 6) + (y + 6) * (y + 7) + (y + 7) * (y + 8) + (y + 8) * (y + 9)
  + (y + 9) * (y + 10) + (y + 10) * (y + 11)

let[@inline never] caller y = (f [@inlined]) ~x:1 y
