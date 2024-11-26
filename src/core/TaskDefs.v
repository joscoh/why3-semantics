Require Export Monads PmapExtra CoqWeakhtbl IdentDefs TyDefs TermDefs TermFuncs DeclDefs DeclFuncs TheoryDefs.
Import MonadNotations. (*TODO: fix once fix imports*)

(*Clone and Meta History*)
Module Stdecl2 := TheoryDefs.Stdecl1.
Module HStdecl := Stdecl2.
Definition tdecl_set := Stdecl2.t.

Definition tds_empty : tdecl_set := Stdecl2.empty.
Definition tds_singleton td : tdecl_set := Stdecl2.singleton td.
Definition tds_add := Stdecl2.add.

Definition clone_map := Mid.t tdecl_set.
Definition meta_map := Mmeta.t tdecl_set.

Definition cm_find (cm : clone_map) (th : theory_c) : tdecl_set := 
  Mid.find_def _ tds_empty (th_name_of th) cm.

Definition mm_find (mm: Mmeta.t tdecl_set) (t: meta) : tdecl_set := Mmeta.find_def _ tds_empty t mm.

Definition cm_add cm th td := Mid.change _ (fun o => 
  match o with
  | None => Some (tds_singleton td)
  | Some tds => Some (tds_add td tds)
  end) (th_name_of th) cm.

Definition mm_add_aux mm t td := Mmeta.change _ (fun o =>
  match o with
  | None => Some (tds_singleton td)
  | Some tds => Some (tds_add td tds)
  end) t mm.

Definition mm_add (mm : meta_map) (t: meta) (td : tdecl_c) : meta_map := 
  if t.(meta_excl)
  then Mmeta.add t (tds_singleton td) mm
  else mm_add_aux mm t td.


(** Task *)
Unset Elimination Schemes.
Inductive task_hd := mk_task_head {
  task_decl  : tdecl_c;        (* last declaration *)
  task_prev  : option task_hd;         (* context *)
  task_known : known_map;    (* known identifiers *)
  task_clone : clone_map;    (* use/clone history *)
  task_meta  : meta_map;     (* meta properties *)
  task_tag   : CoqWeakhtbl.tag; (* unique magical tag *)
}.
Set Elimination Schemes.

Definition task := option task_hd.

(*Induction and Decidable Equality*)
Section TaskInd.

Variable (P: task_hd -> Prop).
Variable (Hind: forall t, option_Forall P t.(task_prev) ->
  P t).

Fixpoint task_hd_ind (t: task_hd) : P t :=
  Hind t (mk_option_Forall task_hd_ind t.(task_prev)).

End TaskInd.

(*Write functions over task*)
Section TaskRect.

Variable (P: task -> Type).
Variable (Hnone: P None).
Variable (Hsome: forall t, P t.(task_prev) -> P (Some t)).

(*Need well-founded induction*)
Definition option_size {A: Type} (sz: A -> nat) (o: option A) : nat :=
  match o with
  | None => 1
  | Some x => 1 + sz x
  end.
Fixpoint task_hd_size (t: task_hd) {struct t} : nat :=
  option_size task_hd_size t.(task_prev).
Definition task_size (t: task) : nat :=
  option_size task_hd_size t.

Lemma task_size_lt t: task_size (t.(task_prev)) < task_size (Some t).
Proof.
  simpl. destruct t; simpl.
  unfold task_size. lia.
Qed.

Fixpoint task_rect_aux (t: task)  (ACC: Acc lt (task_size t)) {struct ACC} : 
  P t.
destruct t.
- apply Hsome. apply task_rect_aux. 
  apply (Acc_inv ACC).
  apply task_size_lt.
- apply Hnone.
Defined.

Definition task_rect (t: task) : P t :=
  task_rect_aux t (Wf_nat.lt_wf _).

End TaskRect.

Fixpoint task_hd_eqb (t1 t2: task_hd) : bool :=
  CoqWeakhtbl.tag_equal t1.(task_tag) t2.(task_tag) && (*tag first*)
  td_equal t1.(task_decl) t2.(task_decl) &&
  option_eqb task_hd_eqb t1.(task_prev) t2.(task_prev) &&
  Mid.equal d_equal t1.(task_known) t2.(task_known) &&
  Mid.equal Stdecl2.equal t1.(task_clone) t2.(task_clone) &&
  Mmeta.equal Stdecl2.equal t1.(task_meta) t2.(task_meta).

Lemma task_hd_eqb_eq t1 t2:
  t1 = t2 <-> task_hd_eqb t1 t2.
Proof.
  revert t2. apply task_hd_ind with (P:=fun t1 =>
    forall t2, t1 = t2 <-> task_hd_eqb t1 t2); clear; intros t1 IH t2.
  destruct t1; destruct t2; simpl in *.
  rewrite !andb_true, <- tdecl_eqb_eq, <- (option_eqb_Forall IH),
  <- (Mid.eqb_eq _ decl_eqb_eq ident_eqb_eq),
  <- (Mid.eqb_eq _ (Stdecl2.equal_eq tdecl_eqb_eq) ident_eqb_eq),
  <- (Mmeta.eqb_eq _ (Stdecl2.equal_eq tdecl_eqb_eq) meta_eqb_eq),
  <- CoqWeakhtbl.tag_equal_eq.
  solve_eqb_eq.
Qed.

Definition task_hd_eqb_fast := task_hd_eqb.


(*Equality and Hashconsing*)

Definition task_hd_equal (t1 t2: task_hd) : bool :=
  match td_node_of t1.(task_decl), td_node_of t2.(task_decl) with
  | Decl d1, Decl d2 =>
    match d1.(d_node), d2.(d_node) with
    | Dprop x1, Dprop x2 =>
      let '(k1, p1, g1) := of_tup3 x1 in
      let '(k2, p2, g2) := of_tup3 x2 in
      match k1, k2 with
      | Pgoal, Pgoal =>
        option_eqb task_hd_eqb_fast t1.(task_prev) t2.(task_prev) &&
        pr_equal p1 p2 && t_equal_strict g1 g2
      | _, _ => task_hd_eqb_fast t1 t2
      end
    | _, _ => task_hd_eqb_fast t1 t2
    end
  | _, _ => task_hd_eqb_fast t1 t2
  end.

Definition task_hd_hash (t: task_hd) : CoqBigInt.t :=
  CoqWeakhtbl.tag_hash t.(task_tag).

Definition task_equal (t1 t2: task) : bool :=
  option_eqb task_hd_eqb_fast t1 t2.

Definition task_hash (t: task) : CoqBigInt.t :=
  option_fold CoqBigInt.zero (fun t => CoqBigInt.succ (task_hd_hash t)) t.

(*Hashconsing*)
Module TaskHash <: hashcons.HashedType.
Definition t := task_hd.
Definition equal (t1 t2: t) : bool :=
  td_equal t1.(task_decl) t2.(task_decl) &&
  task_equal t1.(task_prev) t2.(task_prev).
Definition hash (t1: t) : CoqBigInt.t :=
  hashcons.combine_big (td_hash t1.(task_decl)) (task_hash t1.(task_prev)).
Definition tag (i: CoqBigInt.t) (t1: t) : t :=
  {| task_decl := t1.(task_decl);
     task_prev := t1.(task_prev);
     task_known := t1.(task_known);
     task_clone := t1.(task_clone);
     task_meta := t1.(task_meta);
     task_tag := CoqWeakhtbl.create_tag i |}. (*TODO: coq-record-update?*)
End TaskHash.

Module Hstask := hashcons.Make TaskHash.
Definition mk_task (decl: tdecl_c) (prev: task) (known: known_map)
  (clone: clone_map) (meta: meta_map) : hashcons_st task_hd task :=
  (t <- (Hstask.hashcons {|
    task_decl := decl;
    task_prev := prev;
    task_known := known;
    task_clone := clone;
    task_meta := meta;
    task_tag := CoqWeakhtbl.dummy_tag
  |});;
  st_ret (Some t))%state.

Definition task_known1 (o : task) := option_fold Mid.empty (fun t => t.(task_known)) o.
Definition task_clone1 (o: task) := option_fold Mid.empty (fun t => t.(task_clone)) o. 
Definition task_meta1 (o: task) := option_fold Mmeta.empty (fun t => t.(task_meta)) o.

Definition find_clone_tds task (th : theory_c) := 
  cm_find (task_clone1 task) th.

Definition find_meta_tds task (t : meta) := mm_find (task_meta1 task) t.

(*Now that we have ty, decl, tdecl, and task, we have all the hashconsed types
  (ignoring term for now, will maybe have to change)
  We define functions to lift subsets of these hashconsed states to the full state.
  TODO: it would be really, really nice to have better composition*)
Require Import TyDefs.
Definition hashcons_full : Type :=
  (hashcons_ty ty_c) * (hashcons_ty decl) * (hashcons_ty tdecl_c) * (hashcons_ty task_hd).

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

Definition NotTaggingMeta (m: meta) : errtype := mk_errtype "NotTaggingMeta" m.