Require Export CoqWstdlib TaskDefs TaskFuncs.
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
  fold_left_errst (fun x y => fn y x) (task_list t) v.

(*Note: very bad solution (TODO) and move if using*)
(* Record hashcons_ty_decl : Type :=
  {hashcons_ty_decl1 : hashcons_ty ty_c;
   hashcons_ty_decl2 : hashcons_ty decl}.
Record hashcons_ty_decl_tdecl : Type :=
  {hashcons_ty_decl_tdecl1: hashcons_ty ty_c;
   hashcons_ty_decl_tdecl2: hashcons_ty decl;
   hashcons_ty_decl_tdecl3: hashcons_ty tdecl_c;
  }.
Record hashcons_full : Type :=
  {hashcons_ty_c : hashcons_ty ty_c;
  (*TODO: term*)
   hashcons_decl : hashcons_ty decl;
   hashcons_tdecl: hashcons_ty tdecl_c;
   hashcons_task_hd: hashcons_ty task_hd }. *)

(*TODO: start here*)
(*Need to figure out lens, composition, etc*)

(* Definition hashcons_lift1 : hashcons_ty_decl  *)

Definition hashcons_full : Type :=
  (hashcons_ty ty_c) * (hashcons_ty decl) * (hashcons_ty tdecl_c) * (hashcons_ty task_hd).

(*And lift all of these to it
  TODO: this is really not ergonomic*)
(*also TODO: do we need to add CoqBigInt to these?*)
Section Lifts.
Context {A: Type} {St: Type}.
(*type*)
Definition full_of_ty (s: errState (hashcons_ty ty_c) A) : errState hashcons_full A :=
  errst_tup1 (errst_tup1 (errst_tup1 s)).
  (* errst_assoc13 (@errst_tup1 _ ((hashcons_ty decl) * (hashcons_ty tdecl_c) * (hashcons_ty task_hd)) _ s). *)

(*decl*)
Definition full_of_d (s: errState (hashcons_ty decl) A) : errState hashcons_full A :=
  errst_tup1 (errst_tup1 (errst_tup2 s)).
  (* errst_assoc22 (errst_tup1 (errst_tup2 s)). *)

(*tdecl*)
Definition full_of_td (s: errState (hashcons_ty tdecl_c) A) : errState hashcons_full A :=
  errst_tup1 (errst_tup2 s).

(*task*)
Definition full_of_tsk (s: errState (hashcons_ty task_hd) A) : errState hashcons_full A :=
  errst_tup2 s.

(*type + decl*)
Definition full_of_ty_d (s: errState (hashcons_ty ty_c * hashcons_ty decl) A) : errState hashcons_full A :=
  errst_tup1 (errst_tup1 s).

(*type + tdecl*)
Definition full_of_ty_td (s: errState (hashcons_ty ty_c * hashcons_ty tdecl_c) A) : errState hashcons_full A :=
  errst_tup1 (errst_insert s).

(*type + task*)
Definition full_of_ty_tsk (s: errState (hashcons_ty ty_c * hashcons_ty task_hd) A) : errState hashcons_full A :=
  errst_assoc (errst_insert (errst_assoc_rev (errst_insert s))).

(*decl + tdecl*)
Definition full_of_d_td (s: errState (hashcons_ty decl * hashcons_ty tdecl_c) A) : errState hashcons_full A :=
  errst_assoc13 (errst_tup2 (errst_tup1 s)).

(*decl + task*)
Definition full_of_d_tsk (s: errState (hashcons_ty decl * hashcons_ty task_hd) A) : errState hashcons_full A :=
  errst_assoc13 (errst_tup2 (errst_insert s)).

(*tdecl + task*)
Definition full_of_td_tsk (s: errState (hashcons_ty tdecl_c * hashcons_ty task_hd) A) : errState hashcons_full A :=
  errst_assoc (errst_tup2 s).

(*type + decl + tdecl*)
Definition full_of_ty_d_td (s: errState (hashcons_ty ty_c * hashcons_ty decl * hashcons_ty tdecl_c) A) : errState hashcons_full A :=
  errst_tup1 s.

(*type + decl + task*)
Definition full_of_ty_d_tsk (s: errState (hashcons_ty ty_c * hashcons_ty decl * hashcons_ty task_hd) A) : errState hashcons_full A :=
  errst_insert s.

(*type + tdecl + task*)
Definition full_of_ty_td_tsk (s: errState (hashcons_ty ty_c * hashcons_ty tdecl_c * hashcons_ty task_hd) A) : errState hashcons_full A :=
  errst_assoc22 (errst_insert (errst_assoc_rev s)).

(*decl + tdecl + task*)
Definition full_of_d_td_tsk (s: errState (hashcons_ty decl * hashcons_ty tdecl_c * hashcons_ty task_hd) A) : errState hashcons_full A :=
  errst_assoc13 (errst_tup2 s).
End Lifts.

(*No memoization*)
(*TODO: does not have a general type at all - just make it all for now*)
Definition gen_decl1 {A St: Type} (add : task -> A -> errState (St * hashcons_full) task) 
  (fn: decl -> errState (St * hashcons_full) (list A)):
  task -> task -> errState (St * hashcons_full) task :=
  let fn (tsk: task_hd) acc := 
    match td_node_of tsk.(task_decl) with
    | Decl d => 
      l <- (fn d) ;;
      fold_left_errst add l acc
    | _ =>  errst_tup2 (full_of_td_tsk (add_tdecl1 acc tsk.(task_decl)))
    end
  in
  fold_errst fn.

Definition decl_errst {St: Type} (f: decl -> errState (St * hashcons_full) (list decl))
  (t1 t2: task) : errState (St * hashcons_full) task :=
  gen_decl1 (fun (t : task) (d: decl) => errst_tup2 (full_of_td_tsk (TaskFuncs.add_decl t d))) f t1 t2.
