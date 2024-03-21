
(* Set, Map, Hashtbl on ints and strings *)

module Int = struct
  type t = int
  let tag (x: int) : BigInt.t = BigInt.of_int x
  let eq = ((=) : int -> int -> bool)
  let compare (x : int) y = Stdlib.compare x y
  let equal (x : int) y = x = y
  let hash  (x : int) = BigInt.of_int x
end

module Mint = Extmap.Make(Int)
module Sint = Extset.MakeOfMap(Mint)
module Hint = Exthtbl.Make(struct
  type t = Int.t
  let compare = Stdlib.compare
  let equal = Int.eq
  let hash x = x
end)

module Str = struct
  type t = string
  (*TODO bad could overwrite*)
  let tag (s: string) : BigInt.t = (BigInt.of_int (Hashtbl.hash s))
  let eq (s1 : string) (s2: string) : bool = s1 = s2
end

module Mstr = Extmap.Make(Str)
module Sstr = Extset.MakeOfMap(Mstr)
module Hstr = Exthtbl.Make(struct
  type t    = String.t
  let hash  = (Hashtbl.hash : string -> int)
  let equal = ((=) : string -> string -> bool)
end)


module Float = struct
  type t = float
  (*Same with hash*)
  let tag (x: float) : BigInt.t = BigInt.of_int (Exthtbl.hash x)
  let eq (f1: float) (f2: float) : bool = Float.equal f1 f2
  let compare (x : float) y = Stdlib.compare x y
  let equal (x : float) y = x = y
  let hash  (x : float) = Exthtbl.hash x
end

module Mfloat = Extmap.Make(Float)
module Sfloat = Extset.MakeOfMap(Mfloat)
module Hfloat = Exthtbl.Make(Float)


(*TODO: Coq extraction does not extract module types?*)
module type TaggedType =
sig
  type t
  val tag : t -> BigInt.t
  val eq : t -> t -> bool (*JOSH: added*)
end

module type OrderedHashedType =
sig
  type t
  val hash : t -> BigInt.t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end


module OrderedHashedList (X : TaggedType) =
struct
  type t = X.t list
  let hash = Hashcons.combine_big_list X.tag (BigInt.of_int 3)
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let equal = Lists.equal equ_ts
  let cmp_ts ts1 ts2 = BigInt.compare (X.tag ts1) (X.tag ts2)
  let compare = Lists.compare cmp_ts
end

module OrderedIntHashed (X: OrderedHashedType) =
struct
type t = X.t
let hash x = BigInt.hash (X.hash x)
let equal = X.equal
let compare = X.compare
end


module MakeMSH (X : TaggedType) =
struct
  module T = OrderedHashed(X)
  module M = Extmap.Make(X)
  module S = Extset.MakeOfMap(M)
  module O = OrderedIntHashed(T)
  module H = Exthtbl.Make(O)
end

(*module MakeTagged (X : Weakhtbl.Weakey) =
struct
  type t = X.t
  let tag t = Weakhtbl.tag_hash (X.tag t)
  let eq x1 x2 = X.eq x1 x2
end*)

module MakeMSHW (X : Weakhtbl.Weakey) =
struct
  module Tg = MakeTagged(X)
  module T = OrderedHashed(Tg)
  module M = Extmap.Make(Tg)
  module S = Extset.MakeOfMap(M)
  module O = OrderedIntHashed(T)
  module H = Exthtbl.Make(O)
  module W = Weakhtbl.Make(X)
end
