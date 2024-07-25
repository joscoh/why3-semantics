From Src Require Import TyDefs TransDefs.
Import MonadNotations.

Local Open Scope errst_scope.

(*TODO: do log, axm, imp when we know types of
  monads*)

Definition log {A: Type} (acc: list decl) 
  (x: lsymbol * A) : errorHashconsT decl (list decl) :=
  let (ps, _) := x in
  p1 <- create_param_decl ps;;
  errst_ret (p1 :: acc).
Definition axm (acc: list decl) (x: prsymbol * term_c) : 
  errorHashconsT decl (list decl) :=
  let (pr, f) := x in
  p1 <- create_prop_decl Paxiom pr f ;;
  errst_ret (p1 :: acc).
Definition imp {A: Type} (acc: list decl) (x: A * list (prsymbol * term_c)) : 
  errorHashconsT decl (list decl) :=
  let (_, al) := x in
  foldl_errst axm al acc.

(*TODO: non-typechecking versions of some API
  functions - then we can avoid error monad.
  We already know that things are well-typed*)
Definition exi {A: Type} (vl: list term_c) (x: A * term_c) : 
  errorHashconsT ty_c term_c :=
  let fix descend (f: term_c) : errorHashconsT ty_c term_c :=
    match t_node_of f with
    | Tquant Tforall f =>
      (*TODO: is t_view_quant OK or do we need to open?*)
      let '(vl, tl, f) := t_view_quant f in
      d <- (descend f);;
      errst_lift2 (t_exists_close vl tl d)
    | Tbinop Timplies g f =>
      d <- (descend f);;
      errst_lift2 (t_and g d) 
    | Tapp _ tl =>
      let marry acc v t := 
        t1 <- (t_equ v t) ;;
        errst_lift2 (t_and_simp acc t1) in
      o <- fold_left2_errst marry t_true vl tl;;
      match o with
      | None => (*cannot happen w typechecking*) errst_ret f
      | Some x => errst_ret x
      end
    | Tlet t tb =>
      let (v, f) := t_view_bound tb in
      d <- (descend f);;
      t1 <- errst_lift2 (t_let_close v t d);;
      errst_ret t1
    | _ => errst_ret f (*cannot be reached*)
    end
    in
  descend (snd x).

(*TODO: LOTS of monad stuff we would like to avoid*)
Definition inv {A: Type} (acc: list decl) (x: lsymbol * list (A * term_c)) : 
  errState (CoqBigInt.t * (hashcons_ty ty_c * hashcons_ty decl)) (list decl) :=
  let (ps, al) := x in
  vl <- errst_tup1 ((errst_lift1 (
    st_list (map (create_vsymbol (id_fresh1 "z")) ps.(ls_args))))) ;;
  let tl := map t_var vl in
  hd <- errst_tup2 (errst_tup1 (ps_app ps tl));;
  (*TODO: don't need errState but dont want other ma_join_fold*)
  dj <- errst_tup2 (errst_tup1 (map_join_left_errst t_true (exi tl) (fun t1 t2 => errst_lift2 (t_or t1 t2)) 
    al)) ;;
  (*TODO: implement simplification*)
  hsdj <- errst_lift2 (t_implies hd dj) ;;
  ax <- errst_lift2 (t_forall_close vl nil hsdj) ;;
  let nm := id_derive1 (ps.(ls_name).(id_string) ++ "_inversion"%string)%string ps.(ls_name) in
  p <- errst_lift1 (st_lift1 (create_prsymbol nm));;
  pd <- errst_tup2 (errst_tup2 (create_prop_decl Paxiom p ax));;
  errst_ret (pd :: acc).

Definition elim (d: decl) : 
  errState (CoqBigInt.t * (hashcons_ty ty_c * hashcons_ty decl)) (list decl) :=
  match d.(d_node) with
  | Dind x =>
    let il := snd x in
    dl <- errst_tup2 (errst_tup2 (foldl_errst log il nil)) ;;
    dl <- errst_tup2 (errst_tup2 (foldl_errst imp il dl)) ;;
    dl <- foldl_errst inv il dl ;;
    errst_ret (rev dl)
  | _ => errst_ret [d]
  end.

(*Lift to hashcons_full*)

Definition elim_lift (d: decl) :
  errState (CoqBigInt.t * hashcons_full) (list decl) :=
  @errst_congr1 CoqBigInt.t (hashcons_ty ty_c * hashcons_ty decl) _ _ full_of_ty_d (elim d).

Definition eliminate_inductive := TransDefs.decl_errst elim_lift None.