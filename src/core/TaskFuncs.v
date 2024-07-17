Require Export TaskDefs.
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
  errState (hashcons_ty tdecl_c * hashcons_ty task_hd) (known_res task) :=
  d1 <- errst_lift2 (check_decl d);;
  o <- errst_lift2 (known_add_decl_informative (task_known1 t) d1);;
  match o with
  | Known i => errst_ret (Known _ i)
  | Normal (d1, kn) =>
  td1 <- errst_lift1 (st_lift1 (create_decl d1)) ;;
  _ <- errst_lift2 (check_task t);;
  h <- errst_lift1 (st_lift2 (mk_task td1 t kn (task_clone1 t) (task_meta1 t)));;
  errst_ret (Normal _ h)
  end.

(*Why we needed this known_res stuff*)
Definition new_decl (t: task) (d: decl) (td: tdecl_c) : errState (hashcons_ty tdecl_c * hashcons_ty task_hd) task :=
  o <- new_decl1 t d td ;;
  match o with
  | Known i => errst_ret t
  | Normal n => errst_ret n
  end.

(*Skip [new_clone], [new_meta]*)