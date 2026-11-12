type size =
  { width : int;
    height : int
  }

type window =
  { title : int;
    size : size
  }

val measure : window -> int

val result : int
