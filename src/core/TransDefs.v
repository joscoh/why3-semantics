Require Export CoqWstdlib TaskFuncs.
Import MonadNotations.
Local Open Scope errst_scope.

(** Task transformation *)
Definition trans (A: Type) := task -> A.
Definition tlist (A: Type) := trans (list A).

(*Fold without memoization*)
Definition task_list (t: task) : list task_hd :=
  let task_list (acc: list task_hd) (t: task) :=
    task_rect _ (fun acc => acc)
      (fun thd rec acc => rec (thd :: acc)) t acc
  in
  task_list nil t.

Definition fold {A: Type} (fn: task_hd -> A -> A) (v: A) : trans A :=
  fun t => fold_left (fun x y => fn y x) (task_list t) v.
Definition fold_errst {St A: Type} (fn: task_hd -> A -> errState St A) (v: A) (t: task) : errState St A :=
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