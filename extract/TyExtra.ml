let oty_type = function Some ty -> ty | None -> raise UnexpectedProp


let ts_tuple_ids = Hid.create 17

let ts_tuple = Hint.memo 17 (fun n ->
  let vl = ref [] in
  for _i = 1 to n do vl := create_tvsymbol (id_fresh "a") :: !vl done;
  let ts = create_tysymbol (id_fresh ("tuple" ^ string_of_int n)) !vl NoDef in
  Hid.add ts_tuple_ids ts.ts_name n;
  ts)

let ty_tuple tyl = ty_app (ts_tuple (List.length tyl)) tyl

let is_ts_tuple ts = ts_equal ts (ts_tuple (List.length ts.ts_args))
