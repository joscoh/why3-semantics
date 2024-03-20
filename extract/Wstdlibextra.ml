module Hint = Exthtbl.Make(struct
  type t = Int.t
  let compare = Int.compare
  let equal = Int.equal
  let hash x = x
end)

module Hstr = Exthtbl.Make(struct
  type t    = String.t
  let hash  = (Hashtbl.hash : string -> int)
  let equal = ((=) : string -> string -> bool)
end)