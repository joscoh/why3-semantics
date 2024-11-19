Require Export TyDefs TaskDefs.
Import MonadNotations.
(* Constructors with Checks*)

Definition LemmaFound : errtype :=
  mk_errtype "LemmaFound" tt.
Definition GoalFound : errtype :=
  mk_errtype "GoalFound" tt.
Definition GoalNotFound : errtype :=
  mk_errtype "GoalNotFound" tt.

Definition find_goal (t: task) : option (prsymbol * term_c) :=
  option_bind t (fun t =>
  match td_node_of t.(task_decl) with
  | Decl d =>
    match d.(d_node) with
    | Dprop x =>
      let '(k, p, f) := of_tup3 x in
      match k with
      | Pgoal => Some (p, f)
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end).

Definition task_goal (t: task) : errorM prsymbol :=
  match find_goal t with
  | Some (pr, _) => err_ret pr
  | _ => throw GoalNotFound
  end.

Definition task_goal_fmla (t: task) : errorM term_c :=
  match find_goal t with
  | Some(_, f) => err_ret f
  | _ => throw GoalNotFound
  end.

Definition task_separate_goal (t: task) : errorM (tdecl_c * task) :=
 match t with
 | Some t =>
  match td_node_of t.(task_decl) with
  | Decl d =>
    match d.(d_node) with
    | Dprop x =>
      let '(k, p, f) := of_tup3 x in
      match k with
      | Pgoal => err_ret (t.(task_decl), t.(task_prev))
      | _ => throw GoalNotFound
      end
    | _ => throw GoalNotFound
    end
  | _ => throw GoalNotFound
  end
  | _ => throw GoalNotFound
 end.

Definition check_task (t: task) : errorM task := 
  match find_goal t with
  | Some _  => throw GoalFound
  | None    => err_ret t
  end.

Definition check_decl (d: decl) : errorM decl :=
  match d.(d_node) with
  | Dprop x =>
    let '(k, _, _) := of_tup3 x in
    match k with
    | Plemma => throw LemmaFound
    | _ => err_ret d
    end
  | _ => err_ret d
  end.

Local Open Scope errst_scope.
(*TODO: how to avoid all of the lifts?*)
Definition new_decl1 (t: task) (d : decl) (td: tdecl_c) : 
  errState (CoqBigInt.t * hashcons_full) (known_res task) :=
  d1 <- errst_lift2 (check_decl d);;
  o <- (errst_assoc5 (errst_tup1 (errst_tup1 (errst_tup1 (known_add_decl_informative (task_known1 t) d1)))));;
  match o with
  | Known i => errst_ret (Known _ i)
  | Normal (d1, kn) =>
  td1 <- errst_tup2 (full_of_td (errst_lift1 (create_decl d1))) ;;
  _ <- errst_lift2 (check_task t);;
  h <- errst_tup2 (full_of_tsk (errst_lift1 (mk_task td1 t kn (task_clone1 t) (task_meta1 t))));;
  errst_ret (Normal _ h)
  end.

(* Definition new_decl1 (t: task) (d : decl) (td: tdecl_c) : 
  errState (CoqBigInt.t * hashcons_ty ty_c * hashcons_ty tdecl_c * hashcons_ty task_hd) (known_res task) :=
  d1 <- errst_lift2 (check_decl d);;
  o <- errst_tup1 (errst_tup1 (known_add_decl_informative (task_known1 t) d1));;
  match o with
  | Known i => errst_ret (Known _ i)
  | Normal (d1, kn) =>
  td1 <- errst_lift1 (st_lift1 (st_lift2 (create_decl d1))) ;;
  _ <- errst_lift2 (check_task t);;
  h <- errst_lift1  (st_lift2 (mk_task td1 t kn (task_clone1 t) (task_meta1 t)));;
  errst_ret (Normal _ h)
  end. *)

(*Why we needed this known_res stuff*)
Definition new_decl (t: task) (d: decl) (td: tdecl_c) : 
  errState (CoqBigInt.t * hashcons_full) task :=
  o <- new_decl1 t d td ;;
  match o with
  | Known i => errst_ret t
  | Normal n => errst_ret n
  end.

Definition new_clone (tsk : task) (th: theory_c) (td: tdecl_c) :
  errState (hashcons_ty task_hd) task :=
  let cl := cm_add (task_clone1 tsk) th td in
  t1 <- errst_lift2 (check_task tsk) ;;
  errst_lift1 (mk_task td t1 (task_known1 tsk) cl (task_meta1 tsk)).

Definition new_meta tsk t td :=
  let mt := mm_add (task_meta1 tsk) t td in
  t1 <- errst_lift2 (check_task tsk) ;;
  errst_lift1 (mk_task td t1 (task_known1 tsk) (task_clone1 tsk) mt).

(*Skip [new_clone], [new_meta]*)

(* declaration constructors + add_decl *)

Definition add_decl (t: task) (d: decl) : 
  errState (CoqBigInt.t * hashcons_full) task :=
  td <-  (errst_tup2 (full_of_td (errst_lift1 (create_decl d))));;
  new_decl t d td.

Definition add_ty_decl tk ts :
  errState (CoqBigInt.t * hashcons_full) task :=
  td <- errst_tup2 (full_of_d (errst_lift1 (create_ty_decl ts)));;
  add_decl tk td.
Definition add_data_decl tk dl :
  (*4 hashcons here - really, really need to have better composition*)
  errState (CoqBigInt.t * hashcons_full) task :=
  td <- (errst_tup2 (full_of_ty_d (create_data_decl dl))) ;;
  add_decl tk td.
Definition add_param_decl tk ls :
  errState (CoqBigInt.t * hashcons_full) task :=
  td <- errst_tup2 (full_of_d (create_param_decl ls));;
  add_decl tk td.
Definition add_logic_decl tk dl :
  errState (CoqBigInt.t * hashcons_full) task :=
  td <- errst_tup2 (full_of_d (create_logic_decl_nocheck dl));;
  add_decl tk td.
Definition add_ind_decl tk s dl :
  errState (CoqBigInt.t * hashcons_full) task :=
  td <- errst_tup2 (full_of_d (create_ind_decl s dl));;
  add_decl tk td.
Definition add_prop_decl tk k p f :
  errState (CoqBigInt.t * hashcons_full) task :=
  td <- errst_tup2 (full_of_d (create_prop_decl k p f));;
  add_decl tk td.

(*We will only add decls for now*)
Definition add_tdecl (tsk: option task_hd) (td: tdecl_c) : 
  errState (CoqBigInt.t * hashcons_full) task :=
  match td_node_of td with
  | Decl d => new_decl tsk d td
  | Use th => if Stdecl2.mem td (find_clone_tds tsk th) then errst_ret tsk else 
    errst_tup2 (full_of_tsk (new_clone tsk th td))
  | Clone th _ => errst_tup2 (full_of_tsk (new_clone tsk th td))
  | Meta t _ => errst_tup2 (full_of_tsk (new_meta tsk t td))
  end.