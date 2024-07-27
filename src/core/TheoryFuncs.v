Require Export Monads TheoryDefs.
Import MonadNotations.
Local Open Scope errst_scope.

(* Meta Properties *)

Definition BadMetaArity (x: meta * CoqBigInt.t) : errtype :=
  mk_errtype "BadMetaArity" x.
Definition MetaTypeMismatch (x: meta * meta_arg_type * meta_arg_type) : errtype :=
  mk_errtype "MetaTypeMismatch" x.

Definition get_meta_arg_type (m: meta_arg) : meta_arg_type :=
  match m with
  | MAty  _ => MTty
  | MAts  _ => MTtysymbol
  | MAls  _ => MTlsymbol
  | MApr  _ => MTprsymbol
  | MAstr _ => MTstring
  | MAint _ => MTint
  | MAid _ => MTid
  end.

Definition create_meta (m : meta) (al : list meta_arg) : 
  errState (hashcons_ty ty_c * hashcons_ty tdecl_c) tdecl_c :=
  let get_meta_arg (aty : meta_arg_type) (a: meta_arg) : errorHashconsT ty_c meta_arg :=
    (* we allow "constant tysymbol <=> ty" conversion *)
    a <- match aty,a with
      | MTtysymbol, MAty t =>
        errst_ret (match ty_node_of t with
        | Tyapp ts l => if null l then MAts ts else a
        | _ => a
        end) (*({ ty_node = Tyapp (ts,[]) }) -> MAts ts*)
      | MTty, MAts ts =>
        match ts_args_of ts with
        | nil => t1 <- (ty_app ts []);; errst_ret (MAty t1) 
        | _ => errst_ret a
        end (*({ts_args = []} as ts) -> MAty (ty_app ts [])*)
      | _, _ => errst_ret a
    end;;
    let mt := get_meta_arg_type a in
    if meta_arg_type_eqb aty mt then errst_ret a else errst_lift2 (throw (MetaTypeMismatch (m,aty,mt)))
  in
  if null m.(meta_type) && list_eqb meta_arg_eqb [MAstr ""] al then
    (* backward compatibility *)
    errst_tup2 (errst_lift1 (mk_tdecl (Meta m nil)))
  else
    o <- errst_tup1 (map2_errst get_meta_arg m.(meta_type) al) ;;
    match o with
    | Some al => errst_tup2 (errst_lift1 (mk_tdecl (Meta m al)))
    | None => errst_lift2 (throw (BadMetaArity (m, IntFuncs.int_length al)))
    end.