type size =
  { width : int;
    height : int
  }

type window =
  { title : int;
    size : size
  }

val width_of : window -> int

val widen : window -> window

val widened_width : int -> size -> int

val result : int
