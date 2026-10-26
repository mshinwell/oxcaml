open SsaModel

type natural_loop =
  { header : block;
    body : blockset;
    back_edges : block list
  }

val add_new : blockset * block list -> block -> blockset * block list

val walk : block list -> blockset -> block list -> blockset

val natural_loop_body : block list -> block -> block list -> blockset

val add_back_edge :
  block -> block -> (block * block list) list -> (block * block list) list

val record_back_edge :
  block -> (block * block list) list -> block -> (block * block list) list

val record_back_edges :
  (block * block list) list -> block -> (block * block list) list

val find_loops : block list -> natural_loop list

val edge_dominates : block -> block -> block -> bool
