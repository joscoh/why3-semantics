(*An example of how to prove soundness of stateful functions:

We use a version of [eliminate_let], as implemented in proofs/transform/eliminate_let.v.
Notably, this is NOT why3's version (which we proved sound), which has a nontrivial 
termination argument. Instead, we substitute only on subterms. Also, it only eliminates
let-bindings in goals, not elsewhere, this simplifies things a bit.
The primary proof goal is to relate stateless and stateful substitution (which is
really the primary difference between the two layers) so it does encompass the main
difficulties.
*)
Require Import TaskDefs.
Require Import TermTraverse.

(*First, define the stateful transformation*)

Import MonadNotations.

Local Open Scope errst_scope.

(*Simple: eliminate all*)
Check term_map.
Definition elim_let_rewrite (t: term_c) : errState (CoqBigInt.t * hashcons_full) term_c :=
  term_map hashcons_full
  (*let is only interesting one*)
  (fun t1 t2 t3 v r1 r2 =>
    t_subst_single1 v r1 r2)
  (tmap_if_default _)
  (tmap_app_default _)
  (tmap_match_default _)
  (tmap_eps_default _)
  (tmap_quant_default _)
  (tmap_binop_default _)
  (tmap_not_default _)
  t.

(*And the transformation*)


(*Change decl in task_hd*)

Definition change_tdecl_node (t: tdecl_c) (new: tdecl_node) : tdecl_c :=
  mk_tdecl_c new (td_tag_of t).

Definition change_tdecl_c (t: task_hd) (new: tdecl_c) : task_hd :=
  mk_task_head new (task_prev t) (task_known t) (task_clone t) (task_meta t) (task_tag t).

Definition change_decl_node (d: decl) (new: decl_node) : decl :=
  build_decl new (d_news d) (d_tag d).

(*NOTE: assuming goal is at the end (just like with eval)*)
Definition rewrite_goal {St} (f: prsymbol -> term_c -> errState St term_c)
  (t: task_hd) : errState St task_hd :=
  match (td_node_of (task_decl t)) with
  | Decl d =>
    match d_node d with
      | Dprop x =>
        let '(k, pr, f1) := of_tup3 x in
        match k with
        | Pgoal => 
          f2 <- f pr f1 ;;
          errst_ret (change_tdecl_c t (change_tdecl_node (task_decl t) (Decl (change_decl_node d (Dprop (k, pr, f2))))))
        | _ => (*dont do anything*) errst_ret t
        end
      | _ => errst_ret t
      end
  | _ => errst_ret t
  end.

Definition elim_let_aux (t: task_hd) : errState (CoqBigInt.t * hashcons_full) task_hd :=
  rewrite_goal (fun _ => elim_let_rewrite) t.

Require Import TransDefs.

Definition lift_trans (f: task_hd -> errState (CoqBigInt.t * hashcons_full) task_hd) :
  trans_errst task :=
  fun t => 
    match t with
    | None => errst_ret None
    | Some t => x <- f t;; errst_ret (Some x)
    end.

Definition elim_let : trans_errst task := lift_trans elim_let_aux.
Set Bullet Behavior "Strict Subproofs".
(*Soundness*)
Require Import Task Relations ErrStateHoare StateInvar Soundness.
Require Import eliminate_let.
Check trans_errst.

(*TODO: move*)
(*We can remove a pure proposition from a precondition of errst_spec*)
Definition errst_spec_pure_pre {St A: Type} (P1: St -> Prop) (P2: Prop) (s: errState St A) Q:
  (P2 -> errst_spec P1 s Q) ->
  errst_spec (fun x => P1 x /\ P2) s Q.
Proof.
  unfold errst_spec.
  intros Hspec i b [Hp1 Hp2']. auto.
Qed.

(*[eval_task_goal] is annoying. This lets us rewrite it in terms of [find_goal] and relate the formulas*)
Lemma eval_task_find_goal (tsk: task_hd) (f: formula):
  eval_task_goal tsk = Some f <->
  exists f1 pr, find_goal (Some tsk) = Some (pr, f1) /\ eval_fmla f1 = Some f.
Proof.
  unfold eval_task_goal, eval_tdecl_goal, eval_tdecl_node_aux, eval_decl_goal.
  unfold find_goal. simpl.
  destruct (td_node_of (task_decl tsk)) as [d | | |] eqn : Htd; try solve[split; intros; destruct_all; discriminate].
  unfold get_goal.
  destruct (d_node d) as [| | | | | [[k pr] f1]] eqn : Hd; try solve[split; intros; destruct_all; discriminate].
  simpl in *. destruct k; try solve[split; intros; destruct_all; discriminate].
  split.
  - intros Heval. exists f1. exists pr. auto.
  - intros [f2 [pr1 [Hsome Heval]]]. inversion Hsome; subst; auto.
Qed.

Require Import Alpha.

(*Another attempt*)

(*Lemma errst_spec_goal {St: Type} (tr: errState St TaskDefs.task) (fr: term_c -> errState St term_c) 
  (f: formula -> formula)
  (gamma gamma1: context)
  (delta delta1: list (string * formula))
  (goal goal1: formula)
  (tsk1' : task_hd)
  (*(gamma, delta, goal) is eval of tsk1*)
  (Hgamma : eval_task_ctx tsk1' = Some gamma)
  (Hdelta : eval_task_hyps tsk1' = Some delta)
  (Hgoal : eval_task_goal tsk1' = Some goal)
  (*Two tasks are alpha equivalent*)
  (Halpha: a_equiv_task (gamma, delta, goal) (gamma1, delta1, goal1))
  
  errst_spec P1 (tr
  



gamma1 : context
delta1 : list (string * formula)
goal1 : formula
gamma : context
tsk1' : task_hd
Hgamma : eval_task_ctx tsk1' = Some gamma
delta : list (string * formula)
Hdelta : eval_task_hyps tsk1' = Some delta
goal : formula
d : decl
Htd : td_node_of (task_decl tsk1') = Decl d
pr : prsymbol
f1 : term_c
Hd : d_node d = Dprop (Pgoal, pr, f1)
Hgoal : eval_fmla f1 = Some goal
Halphag : a_equiv_ctx gamma gamma1
Hleng : Datatypes.length delta =? Datatypes.length delta1
Halphad : all2 a_equiv_f (map snd delta) (map snd delta1)
Halphagoal : a_equiv_f goal goal1
______________________________________(1/1)
errst_spec (st_wf (Some tsk1'))
  (x <-
   (f2 <- elim_let_rewrite f1;;
    errst_ret
      (change_tdecl_c tsk1'
         (change_tdecl_node (task_decl tsk1') (Decl (change_decl_node d (Dprop (Pgoal, pr, f2)))))));;
   errst_ret (Some x))
  (fun (_ : full_st) (r : TaskDefs.task) (_ : full_st) =>
   task_related r (gamma1, delta1, elim_let_f true true goal1)) *)

(*tsk is initial task*)
(*
Lemma errst_spec_goal {St: Type} (tr: errState St TaskDefs.task) (fr: term_c -> errState St term_c) 
  (f: formula -> formula)
  (g1: term_c) (g2: formula) (Hgoal: eval_fmla g1 = Some g2)
  P1 P2 (tsk: task_hd) gamma1 delta1
  (Hg2: eval_task_goal tsk = Some g2)
  (Hrel: task_related (Some tsk) tsk1)
  (Hp12: forall s, P1 s -> P2 s):
  (*condition: tr doesnt change context or hyps*)
  errst_spec (fun _ => True) tr 
    (fun _ r _ => exists (r': task_hd), r = Some r' /\ eval_task_ctx tsk = eval_task_ctx r' /\ 
      eval_task_hyps tsk = eval_task_hyps r') ->
  (*and tr changes goal to fr*)
  (*TODO: not great that I don't use errst_spec but easier*)
  (forall s1 b1 pr f1, fst (run_errState tr s1) = inr b1 -> find_goal (Some tsk) = Some (pr, f1) -> 
      exists b2, fst (run_errState (fr g1) s1)= inr b2 /\
       find_goal b1 = Some (pr, b2)) ->
(*     exists pr f1, find_goal s1 = Some (pr, f1) -> find_goal b1 = Some 

  errst_spec P1 tr (fun s1 r _ => forall pr f, find_goal s1 = Some (pr, f1) -> find_goal r = Some (pr, ) -> *)
  errst_spec P2 (fr g1) (fun _ f2 _ => fmla_related f2 (f g2)) ->
  errst_spec P1 tr (fun _ r _ => task_related r tsk1). (*Not tsk1, *)
Proof.
  (*This one we prove by unfolding*)
  unfold errst_spec. intros Htr Htf Hfr i b Hp1 Hrun.
  unfold task_related in *.
  (*TODO: very wasteful to expand twice*)
  destruct Hrel as [t1 [Heval Halpha]].
  unfold eval_task in Heval.
  apply option_bind_some in Heval.
  destruct Heval as [gamma [Hgamma Heval]].
  apply option_bind_some in Hgamma.
  destruct Hgamma as [tsk1' [Hsome Hgamma]]. subst.
  apply option_bind_some in Heval. simpl in Heval.
  destruct Heval as [delta [Hdelta Heval]].
  apply option_bind_some in Heval.
  inversion Hsome; subst; clear Hsome.
  destruct Heval as [goal1 [Hgoal1 Ht1]]. inversion Ht1; subst; clear Ht1.
  rewrite Hg2 in Hgoal1. inversion Hgoal1; subst;clear Hgoal1.
  (*Use assumptions and tr and fr*)
  specialize (Htr i b I Hrun).
  destruct b as [t|]; [|destruct_all; discriminate].
  destruct Htr as [r' [Hr' [Hctx Hhyps]]]. inversion Hr'; subst; clear Hr'.
  rewrite eval_task_find_goal in Hg2.
  destruct Hg2 as [f1 [pr [Hfind Heval]]].

 (*  unfold find_goal at 1 in Htf. simpl in Htf.
  apply eval_task_find_goal 

  unfold eval_task_goal, eval_tdecl_goal, eval_tdecl_node_aux, eval_decl_goal in Hg2.
  unfold rewrite_goal.
  destruct (td_node_of (task_decl tsk1')) as [d | | |] eqn : Htd; try discriminate.
  unfold get_goal in Hgoal.
  destruct (d_node d) as [| | | | | [[k pr] f1]] eqn : Hd; try discriminate.
  simpl in *. destruct k; try discriminate. *)
  specialize (Htf _ _ pr f1 Hrun Hfind).
  destruct Htf as [b2 [Hb2 Hgoalr']].
  specialize (Hfr _ _ (Hp12 _ Hp1) Hb2).
  (*Now no more state monads*)
  unfold fmla_related in Hfr. destruct Hfr as [f2 [Hevalb2 Halphaf]].
  exists (gamma, delta, f2). split.
  - unfold eval_task. simpl. rewrite <- Hctx, Hgamma. simpl.
    rewrite <- Hhyps, Hdelta. simpl.
    assert (Heval': eval_task_goal r' = Some f2).
    {
      apply eval_task_find_goal. exists b2. exists pr. split; auto.
    }
    rewrite Heval'. reflexivity.
  - clear -Halpha Halphaf. (*TODO: make sure*) unfold a_equiv_task in *. 
    destruct tsk1 as [[gamma1 delta1] goal1']. simpl_task.
    bool_hyps. bool_to_prop; split_all; auto.
    eapply a_equiv_f_trans. apply Halphaf.  
    apply Alpha. *)


(*The main part: prove related*)
Theorem elim_let_related (tsk1 : TaskDefs.task) (tsk2 : Task.task):
errst_spec
  (fun s : full_st => st_wf tsk1 s /\ task_related tsk1 tsk2)
  (elim_let tsk1)
  (fun (_ : full_st) (r : TaskDefs.task) (_ : full_st) =>
   task_related r (single_goal (elim_let_f true true) tsk2)).
Proof.
  apply errst_spec_pure_pre.
  intros Hrel.


  (*Need to reason about goal formula*)
  (*Lots of boilerplate to simplify tasks (TODO: separate lemma?)*)
  unfold task_related in Hrel.
  destruct Hrel as [t1 [Heval Halpha]].
  unfold eval_task in Heval.
  apply option_bind_some in Heval.
  destruct Heval as [gamma [Hgamma Heval]].
  apply option_bind_some in Hgamma.
  destruct Hgamma as [tsk1' [Hsome Hgamma]]. subst.
  apply option_bind_some in Heval. simpl in Heval.
  destruct Heval as [delta [Hdelta Heval]].
  apply option_bind_some in Heval.
  destruct Heval as [goal [Hgoal Ht1]]. inversion Ht1; subst; clear Ht1.
  destruct tsk2 as [[gamma1 delta1] goal1].
  (*Now get info from [a_equiv_task]*)
  unfold a_equiv_task in Halpha. simpl in Halpha. simpl_task.
  rewrite !andb_true in Halpha.
  destruct Halpha as [[[Halphag Hleng] Halphad] Halphagoal].
  (*Now simplify elim_let (both) to reduce to goal *)
  unfold single_goal. simpl_task.
  unfold elim_let_aux.
  (*Reduce to [rewrite_goal]*)
  eapply prove_errst_spec_bnd with (Q1:=fun _ r _ => task_related (Some r) (gamma1, delta1, elim_let_f true true goal1))
  (P2:=fun x _ => task_related (Some x)  (gamma1, delta1, elim_let_f true true goal1))
  (Q2:= fun x _ y _ => task_related y  (gamma1, delta1, elim_let_f true true goal1)); auto.
  2: { intros x. apply prove_errst_spec_ret. auto. }
  (*Simplify [rewrite_goal] - could do separate lemma maybe*)
  rewrite eval_task_find_goal in Hgoal. destruct Hgoal as [f1 [pr [Hfind Hevalf]]].
  unfold find_goal in Hfind. simpl in Hfind. unfold rewrite_goal.
  destruct (td_node_of (task_decl tsk1')) as [d | | |] eqn : Htd; try discriminate.
  destruct (d_node d) as [| | | | | [[k pr1] f1']] eqn : Hd; try discriminate.
  simpl in *. destruct k; try discriminate. inversion Hfind; subst; clear Hfind.
  (*Now decompose bind again: first just gives us [elim_let_f goal], second
    builds the task*)
  (*TODO: think we will need to prove that result of [elim_let_f] is alpha equivalent*)
  eapply prove_errst_spec_bnd with (Q1:=fun _ f2 _ => eval_fmla f2 = Some (elim_let_f true true goal))
  (Q2:=fun x _ y _ => task_related (Some y) (gamma1, delta1, elim_let_f true true goal1))
  (P2:=fun x _ => eval_fmla x = Some (elim_let_f true true goal)) (*TODO: see*); auto.
  2: { (*Prove ending spec assuming [elim_let] correct*) intros f2. apply prove_errst_spec_ret. intros _ Hf2.
    unfold task_related.
    exists (gamma, delta, (elim_let_f true true goal)).
    split.
    - unfold eval_task. simpl.
      (*TODO: prove these equal in separate lemmas for [change_*] lemmas since we change goal *)
      admit.
    - unfold a_equiv_task. simpl_task. bool_to_prop; split_all; auto.
      (*TODO: prove that a_equiv_f preserved by elim_let_f*)
      admit.
  }
  (*TODO: prove that these transformations related. NOTE: everything up to now wasnt super
    specific to [elim_let] and it could/should be refactored*)
  (*TODO: weaken precondition and use separate lemma*)
Admitted.


Theorem elim_let_sound: trans_errst_sound elim_let.
Proof.
  apply prove_trans_errst_decompose with (tr1:=single_goal (elim_let_f true true)).
  - (*already proved soundness*) apply elim_let_sound. 
  - (*Now prove related*) apply elim_let_related.
Qed.


