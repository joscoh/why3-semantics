Require Export CoqWstdlib TaskFuncs.
Import MonadNotations.
Local Open Scope errst_scope.

(** Task transformation *)
Definition trans (A: Type) := task -> A.
Definition trans_errst (A: Type) := task -> errState (CoqBigInt.t * hashcons_full) A. (*extracts to same OCaml but we need diff version*)
Definition tlist (A: Type) := trans (list A).

(*trans defn is opaque, we need this for monadic ops*)
(* Definition func_trans {St: Type} (A: Type) (f: task -> errState St A): trans A := f.
Definition trans_func {St: Type} {A: Type} (t: trans A) : task -> errState St A := t. *)
Definition trans_bind {A B: Type} (y: errState (CoqBigInt.t * hashcons_full) A) (t1: A -> trans_errst B) : trans_errst B := 
fun t =>
  x <- y ;;
  t1 x t.

(*Fold without memoization*)
Definition task_list (t: task) : list task_hd :=
  let task_list (acc: list task_hd) (t: task) :=
    task_rect _ (fun acc => acc)
      (fun thd rec acc => rec (thd :: acc)) t acc
  in
  task_list nil t.

Definition fold {A: Type} (fn: task_hd -> A -> A) (v: A) : trans A :=
  fun t => fold_left (fun x y => fn y x) (task_list t) v.
Definition fold_errst {A: Type} (fn: task_hd -> A -> errState (CoqBigInt.t * hashcons_full) A) (v: A) : trans_errst A := fun t =>
  foldl_errst (fun x y => fn y x) (task_list t) v.

(*No memoization*)
(*TODO: does not have a general type at all - just make it all for now*)
(*TODO: not general type, specialized to CoqBigInt.t - do we need any other state?*)
Definition gen_decl1 {A (*St*): Type} (add : task -> A -> errState (CoqBigInt.t * hashcons_full) task) 
  (fn: decl -> errState (CoqBigInt.t * hashcons_full) (list A)):
  task -> task -> errState (CoqBigInt.t * hashcons_full) task :=
  let fn (tsk: task_hd) acc := 
    match td_node_of tsk.(task_decl) with
    | Decl d => 
      l <- (fn d) ;;
      foldl_errst add l acc
    | _ =>  add_tdecl acc tsk.(task_decl)
    end
  in
  fold_errst fn.

(*same*)
Definition decl_errst (*{St: Type}*) (f: decl -> errState (CoqBigInt.t * hashcons_full) (list decl))
  (t1 t2: task) : errState (CoqBigInt.t * hashcons_full) task :=
  gen_decl1 (fun (t : task) (d: decl) => (TaskFuncs.add_decl t d)) f t1 t2.

Definition tdecl_errst (*{St: Type}*) (f: decl -> errState (CoqBigInt.t * hashcons_full) (list tdecl_c))
  (t1 t2: task) : errState (CoqBigInt.t * hashcons_full) task :=
  gen_decl1 (fun (t : task) (d: tdecl_c) => TaskFuncs.add_tdecl t d) f t1 t2.

(*No memoization*)
Definition on_meta_tds {A: Type} (t: meta) (fn: tdecl_set -> task -> A) : task ->  A :=
  (* let fn = Wtds.memoize 17 fn in *)
  fun task => fn (find_meta_tds task t) task.
Local Open Scope errst_scope.
(*TODO: will prob have to add state*)

Definition on_meta {St A: Type} (t: meta) (fn: list (list meta_arg) -> task -> errState St A) : task -> errState St A :=
fun tsk =>
  let add td acc := match td_node_of td with
    | Meta _ ma => err_ret (ma::acc)
    | _ => assert_false "on_meta"
    end
  in
  on_meta_tds t (fun tds t => 
    x <- errst_lift2 (foldl_err (fun x y => add y x) (HStdecl.elements tds) []) ;;
    (fn x t) 
  (*(HStdecl.fold add tds Sts.empty))*)) tsk.

(*Basically, do trans on the typesymbols with given meta tag
  (for elim ADT, this gives us the set of inifinte types)*)
Definition on_tagged_ts {St: Type} {A: Type} (t: meta) (fn: Sts.t -> task -> errState St A) 
  : task -> errState St A := fun tsk =>
  _ <- errst_lift2 match t.(meta_type) with
    | MTtysymbol :: _ => err_ret tt
    | _ => throw (NotTaggingMeta t)
  end ;;
  (*Need to fold over bindings*)
  let add td acc := match (td_node_of td) with
    | Meta _ (MAts ts :: _) => err_ret (Sts.add ts acc)
    | _ => assert_false "on_tagged_ts"
  end
  in
  on_meta_tds t (fun tds t => 
    x <- errst_lift2 (foldl_err (fun x y => add y x) (HStdecl.elements tds) Sts.empty ) ;;
    (fn x t) 
  (*(HStdecl.fold add tds Sts.empty))*)) tsk.