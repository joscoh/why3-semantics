Require Import Monads PmapExtra CoqWeakhtbl IdentDefs TermFuncs DeclDefs DeclFuncs TheoryDefs.
Import MonadNotations.

(*Clone and Meta History*)
Module Stdecl := TheoryDefs.Stdecl1.
Module HStdecl := Stdecl.
Definition tdecl_set := Stdecl.t.
Definition clone_map := Mid.t tdecl_set.
Definition meta_map := Mmeta.t tdecl_set.


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

Fixpoint task_hd_eqb (t1 t2: task_hd) : bool :=
  CoqWeakhtbl.tag_equal t1.(task_tag) t2.(task_tag) && (*tag first*)
  td_equal t1.(task_decl) t2.(task_decl) &&
  option_eqb task_hd_eqb t1.(task_prev) t2.(task_prev) &&
  Mid.equal d_equal t1.(task_known) t2.(task_known) &&
  Mid.equal Stdecl.equal t1.(task_clone) t2.(task_clone) &&
  Mmeta.equal Stdecl.equal t1.(task_meta) t2.(task_meta).

Lemma task_hd_eqb_eq t1 t2:
  t1 = t2 <-> task_hd_eqb t1 t2.
Proof.
  revert t2. apply task_hd_ind with (P:=fun t1 =>
    forall t2, t1 = t2 <-> task_hd_eqb t1 t2); clear; intros t1 IH t2.
  destruct t1; destruct t2; simpl in *.
  rewrite !andb_true, <- tdecl_eqb_eq, <- (option_eqb_Forall IH),
  <- (Mid.eqb_eq _ decl_eqb_eq ident_eqb_eq),
  <- (Mid.eqb_eq _ (Stdecl.equal_eq tdecl_eqb_eq) ident_eqb_eq),
  <- (Mmeta.eqb_eq _ (Stdecl.equal_eq tdecl_eqb_eq) meta_eqb_eq),
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

(* Constructors with Checks*)