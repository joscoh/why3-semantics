let oty_type = function Some ty -> ty | None -> raise UnexpectedProp
let ts_tuple_ids = Hid.create 17

(*JOSH: remove memoization*)
let ts_tuple = Hint.memo 17 (fun n ->
  let vl = ref [] in
  for _i = 1 to n do vl := create_tvsymbol (id_fresh "a") :: !vl done;
  let ts = create_tysymbol (id_fresh ("tuple" ^ string_of_int n)) !vl NoDef in
  Hid.add ts_tuple_ids ts.ts_name n;
  ts)

let ty_tuple tyl = ty_app (ts_tuple (List.length tyl)) tyl

let is_ts_tuple ts = ts_equal ts (ts_tuple (List.length ts.ts_args))

let is_ts_tuple_id id =
  try Some (Hid.find ts_tuple_ids id) with Not_found -> None

module Ty2 = MakeMSHW(TyTagged)
module Hty = Ty2.H
module Wty = Ty2.W

module Tsym2 = MakeMSHW(TsymTagged)
module Wts = Tsym2.W

module Tvar2 = MakeMSHW(TvarTagged)
module Htv = Tvar2.H