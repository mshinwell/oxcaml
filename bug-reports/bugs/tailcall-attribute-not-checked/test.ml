let f x =
  let g y = y * 2 in
  1 + (g [@tailcall]) x

class c =
  object (self)
    method depth n = if n = 0 then 0 else 1 + (self#depth [@tailcall]) (n - 1)
  end
