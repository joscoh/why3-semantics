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

Definition elim_let_rewrite (t: term_c) : errState (CoqBigInt.t * hashcons_full) term_c :=
  term_map hashcons_full
  (*let is only interesting one*)
  (fun t t1 r1 v t2 r2 =>
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
From Proofs Require Import Task eliminate_let Alpha.
Require Import Relations ErrStateHoare StateInvar Soundness.

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
  destruct (eval_fmla f1) as [f2|] eqn : Heval.
  - split.
    + intros Hsome; inversion Hsome; subst. exists f1. exists pr. auto.
    + intros [f2' [pr1 [Hsome Heval']]]. inversion Hsome; subst; auto. rewrite Heval in Heval'.
      inversion Heval'; subst; auto.
  - split; try discriminate. 
    intros [f2' [pr1 [Hsome Heval']]]. inversion Hsome; subst; auto.  rewrite Heval in Heval'. discriminate.
Qed.

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

Lemma alpha_equiv_var_sym m1 m2 x y:
  alpha_equiv_var m1 m2 x y -> alpha_equiv_var m2 m1 y x.
Proof.
  rewrite !alpha_equiv_var_iff.
  intros [[Hlook1 Hlook2] | [Hlook1 [Hlook2 Heq]]]; subst; auto.
Qed.

Lemma alpha_equiv_var_uniq m1 m2 x y z:
  alpha_equiv_var m1 m2 x y ->
  alpha_equiv_var m1 m2 x z ->
  y = z.
Proof.
  rewrite !alpha_equiv_var_iff.
  intros [[Hlook1 Hlook2] | [Hlook1 [Hlook2 Heq]]] [[Hlook3 Hlook4] | [Hlook3 [Hlook4 Heq2]]]; subst; auto;
  rewrite Hlook1 in Hlook3; inversion Hlook3; auto.
Qed.


Lemma alpha_equiv_map_fv x y t1 f1:
  (forall m1 m2 t2 (Hv: amap_lookup m1 x = Some y) (Halpha: alpha_equiv_t m1 m2 t1 t2),
    aset_mem x (tm_fv t1) -> amap_lookup m2 y = Some x /\ aset_mem y (tm_fv t2)) /\
  (forall m1 m2 f2 (Hv: amap_lookup m1 x = Some y) (Halpha: alpha_equiv_f m1 m2 f1 f2),
    aset_mem x (fmla_fv f1) -> amap_lookup m2 y = Some x /\ aset_mem y (fmla_fv f2)).
Proof.
  revert t1 f1; apply term_formula_ind; simpl.
  - intros c m1 m2 t2 Hv Halpha. destruct t2; try discriminate. 
  - (*Tvar *)
    intros v m1 m2 t2 Hv Halpha. destruct t2; try discriminate. simpl.
    simpl_set. intros; subst.
    rewrite alpha_equiv_var_iff in Halpha.
    destruct Halpha as [[Hlook1 Hlook2] | [Hlook3 [Hlook4 Heq]]]; subst.
    + rewrite Hlook1 in Hv; inversion Hv; subst; auto.
    + rewrite Hlook3 in Hv; discriminate.
  - (*Tfun*)
    intros f1 tys1 tms1 IH m1 m2 t2 Hv Halpha. destruct t2 as [| | f2 tys2 tms2 | | | | ]; try discriminate.
    simpl. destruct (funsym_eq_dec f1 f2); subst; [|discriminate]; simpl in Halpha. 
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate]; simpl in *.
    destruct (list_eq_dec _ tys1 tys2); [|discriminate]; subst. simpl in *.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true.
    intros [Halpha Hall] Hlentms. inversion IH as [| ? ? IH1 IH2]; subst.
    simpl_set_small. intros [Hmemx | Hmemx]; auto.
    + apply IH1 in Halpha; auto. destruct_all; auto.
    + specialize (IHtms IH2 _ Hall ltac:(lia) Hmemx). destruct_all; auto.
  - (*Tlet - interesting*)
    intros tm1 v1 tm2 IH1 IH2 m1 m2 t2 Hv Halpha.
    destruct t2 as [| | | e1 v2 e3 | | | ]; try discriminate.
    simpl. destruct (vty_eq_dec (snd v1) (snd v2)) as [Htyeq|]; [|discriminate]; simpl in Halpha.
    rewrite andb_true in Halpha. destruct Halpha as [Halpha1 Halpha2].
    simpl_set. intros [Hxfv | [Hxfv Hxv1]].
    + apply IH1 in Halpha1; auto. destruct Halpha1 as [Hlook2 Hmemy]; auto.
    + (*Why we need the [amap_lookup] condition: this proves that y <> v2*) apply IH2 in Halpha2; auto.
      2: { rewrite amap_set_lookup_diff; auto. }
      destruct Halpha2 as [Hlook2 Hmemy].
      (*Here, know that y <> v2. Otherwise, v1 = x, a contradiction. This also proves the lookup condition*)
      vsym_eq y v2.
      1: { rewrite amap_set_lookup_same in Hlook2. inversion Hlook2; subst; contradiction. }
      rewrite amap_set_lookup_diff in Hlook2; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 m1 m2 tm2 Hv Halpha.
    destruct tm2; try discriminate.
    simpl. simpl_set. rewrite !andb_true in Halpha.
    destruct Halpha as [[Ha1 Ha2] Ha3].
    intros [Hfv | [Hfv | Hfv]]; [apply IH1 in Ha1; auto| apply IH2 in Ha2; auto |apply IH3 in Ha3; auto];
    destruct_all; auto.
  - (*Tmatch*)
    intros tm1 v1 ps1 IH1 IHps1 m1 m2 t2 Hv Halpha.
    destruct t2 as [| | | | | tm2 v2 ps2 |]; try discriminate.
    simpl. rewrite !andb_true in Halpha. destruct Halpha as [[[Halpha Hlenps] Hv12] Hall].
    apply Nat.eqb_eq in Hlenps.
    simpl_set_small. intros [Hfv | Hfv].
    1 : { apply IH1 in Halpha; auto. destruct_all; auto. }
    (*Get rid of "or"*)
    assert (amap_lookup m2 y = Some x /\
       aset_mem y
         (aset_big_union (fun x0 : pattern * term => aset_diff (pat_fv (fst x0)) (tm_fv (snd x0))) ps2));
    [| destruct_all; auto].
    clear -IHps1 Hlenps Hall Hfv Hv.
    generalize dependent ps2. induction ps1 as [| [p1 t1] ps1 IHps]; intros [| [p2 t2] ps2]; simpl; try discriminate; auto.
    intros Hlenps. rewrite all2_cons. simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite andb_true. intros [Halphat Hall]. simpl_set_small.
    simpl in Hfv. inversion IHps1 as [|? ? IH1 IH2]; subst; clear IHps1. destruct Hfv as [Hmemx | Hmemx].
    + (*head case*)
      clear IH2 IHps Hall.
      simpl_set_small. destruct Hmemx as [Hmemx Hnotfv].
      (*Use properties of r1 and r2*)
      assert (Ha:=Halphap). apply a_equiv_p_vars_iff in Ha. simpl in Ha. destruct Ha as [Ha1 Ha2].
      apply IH1 in Halphat; auto.
      2: { rewrite aunion_lookup. specialize (Ha1 x). rewrite amap_mem_spec in Ha1.
        destruct (amap_lookup r1 x); auto.
        exfalso. apply Hnotfv. apply Ha1. reflexivity.
      }
      destruct Halphat as [Hlook2 Hmemy].
      rewrite aunion_lookup in Hlook2.
      destruct (amap_lookup r2 y) eqn : Hr2.
      * inversion Hlook2; subst; clear Hlook2.
        (*So now we know that r1(x) = y - but then x is in pat_fv p1, contradiction*)
        apply a_equiv_p_bij in Halphap. simpl in Halphap. unfold bij_map in Halphap.
        apply Halphap in Hr2. exfalso. apply Hnotfv. apply Ha1. rewrite amap_mem_spec, Hr2. reflexivity.
      * (*In this case, know that y not in [pat_fv p2], bc not in r2*)
        split; auto. left. split; auto. intros Hyfv.
        apply Ha2 in Hyfv. rewrite amap_mem_spec, Hr2 in Hyfv. discriminate.
    + (*IH case*)
      specialize (IHps IH2 Hmemx ps2 ltac:(lia) Hall).
      destruct_all; auto.
  - (*Teps*)
    intros f1 v1 IH m1 m2 t2 Hv Halpha. destruct t2 as [| | | | | | f2 v2]; try discriminate.
    simpl. rewrite andb_true in Halpha. destruct Halpha as [Hty Halpha].
    simpl_set. intros [Hxfv Hxv1].
    apply IH in Halpha; auto.
    2: { rewrite amap_set_lookup_diff; auto. }
    destruct Halpha as [Hlook2 Hmemy].
    vsym_eq y v2.
    + rewrite amap_set_lookup_same in Hlook2. inversion Hlook2; subst; contradiction.
    + rewrite amap_set_lookup_diff in Hlook2; auto.
  - (*Fpred*)
    intros p1 tys1 tms1 IH m1 m2 t2 Hv Halpha. destruct t2 as [p2 tys2 tms2 | | | | | | | | |]; try discriminate.
    simpl. destruct (predsym_eq_dec p1 p2); subst; [|discriminate]; simpl in Halpha. 
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate]; simpl in *.
    destruct (list_eq_dec _ tys1 tys2); [|discriminate]; subst. simpl in *.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true.
    intros [Halpha Hall] Hlentms. inversion IH as [| ? ? IH1 IH2]; subst.
    simpl_set_small. intros [Hmemx | Hmemx]; auto.
    + apply IH1 in Halpha; auto. destruct_all; auto.
    + specialize (IHtms IH2 _ Hall ltac:(lia) Hmemx). destruct_all; auto.
  - (*Fquant*)
    intros q1 v1 f1 IH m1 m2 f2 Hv Halpha.
    destruct f2 as [| q2 v2 f2 | | | | | | | |]; try discriminate.
    simpl. rewrite !andb_true in Halpha. destruct Halpha as [_ Halpha].
    simpl_set. intros [Hxfv Hxv1].
    apply IH in Halpha; auto.
    2: { rewrite amap_set_lookup_diff; auto. }
    destruct Halpha as [Hlook2 Hmemy].
    vsym_eq y v2.
    + rewrite amap_set_lookup_same in Hlook2. inversion Hlook2; subst; contradiction.
    + rewrite amap_set_lookup_diff in Hlook2; auto.
  - (*Feq*)
    intros ty t1 t2 IH1 IH2 m1 m2 f2 Hv Halpha.
    destruct f2; try discriminate.
    simpl. simpl_set. rewrite !andb_true in Halpha.
    destruct Halpha as [[_ Ha1] Ha2].
    intros [Hfv | Hfv]; [apply IH1 in Ha1; auto| apply IH2 in Ha2; auto];
    destruct_all; auto.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2 m1 m2 fm2 Hv Halpha.
    destruct fm2; try discriminate.
    simpl. simpl_set. rewrite !andb_true in Halpha.
    destruct Halpha as [[_ Ha1] Ha2].
    intros [Hfv | Hfv]; [apply IH1 in Ha1; auto| apply IH2 in Ha2; auto];
    destruct_all; auto.
  - (*Fnot*)
    intros f1 IH m1 m2 f2 Hv Halpha. destruct f2; try discriminate.
    intros Hfv.
    apply IH in Halpha; auto.
  - (*Ftrue*) intros m1 m2 f2 Hv Halpha. destruct f2; try discriminate; auto.
  - (*Ffalse*) intros m1 m2 f2 Hv Halpha. destruct f2; try discriminate; auto.
  - (*Flet*) 
    intros tm1 v1 tm2 IH1 IH2 m1 m2 t2 Hv Halpha.
    destruct t2 as [| | | | | | | e1 v2 e3 | | ]; try discriminate.
    simpl. destruct (vty_eq_dec (snd v1) (snd v2)) as [Htyeq|]; [|discriminate]; simpl in Halpha.
    rewrite andb_true in Halpha. destruct Halpha as [Halpha1 Halpha2].
    simpl_set. intros [Hxfv | [Hxfv Hxv1]].
    + apply IH1 in Halpha1; auto. destruct Halpha1 as [Hlook2 Hmemy]; auto.
    + apply IH2 in Halpha2; auto.
      2: { rewrite amap_set_lookup_diff; auto. }
      destruct Halpha2 as [Hlook2 Hmemy]. vsym_eq y v2.
      * rewrite amap_set_lookup_same in Hlook2. inversion Hlook2; subst; contradiction.
      * rewrite amap_set_lookup_diff in Hlook2; auto.
  - (*Fif*)
    intros f1 f2 f3 IH1 IH2 IH3 m1 m2 fm1 Hv Halpha.
    destruct fm1; try discriminate.
    simpl. simpl_set. rewrite !andb_true in Halpha.
    destruct Halpha as [[Ha1 Ha2] Ha3].
    intros [Hfv | [Hfv | Hfv]]; [apply IH1 in Ha1; auto| apply IH2 in Ha2; auto |apply IH3 in Ha3; auto];
    destruct_all; auto.
  - (*Fmatch*)
    intros tm1 v1 ps1 IH1 IHps1 m1 m2 t2 Hv Halpha.
    destruct t2 as [| | | | | | | | | tm2 v2 ps2]; try discriminate.
    simpl. rewrite !andb_true in Halpha. destruct Halpha as [[[Halpha Hlenps] Hv12] Hall].
    apply Nat.eqb_eq in Hlenps.
    simpl_set_small. intros [Hfv | Hfv].
    1 : { apply IH1 in Halpha; auto. destruct_all; auto. }
    assert (amap_lookup m2 y = Some x /\
       aset_mem y
         (aset_big_union (fun x0 : pattern * formula => aset_diff (pat_fv (fst x0)) (fmla_fv (snd x0))) ps2));
    [| destruct_all; auto].
    clear -IHps1 Hlenps Hall Hfv Hv.
    generalize dependent ps2. induction ps1 as [| [p1 t1] ps1 IHps]; intros [| [p2 t2] ps2]; simpl; try discriminate; auto.
    intros Hlenps. rewrite all2_cons. simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite andb_true. intros [Halphat Hall]. simpl_set_small.
    simpl in Hfv. inversion IHps1 as [|? ? IH1 IH2]; subst; clear IHps1. destruct Hfv as [Hmemx | Hmemx].
    + (*head case*)
      clear IH2 IHps Hall.
      simpl_set_small. destruct Hmemx as [Hmemx Hnotfv].
      assert (Ha:=Halphap). apply a_equiv_p_vars_iff in Ha. simpl in Ha. destruct Ha as [Ha1 Ha2].
      apply IH1 in Halphat; auto.
      2: { rewrite aunion_lookup. specialize (Ha1 x). rewrite amap_mem_spec in Ha1.
        destruct (amap_lookup r1 x); auto.
        exfalso. apply Hnotfv. apply Ha1. reflexivity.
      }
      destruct Halphat as [Hlook2 Hmemy].
      rewrite aunion_lookup in Hlook2.
      destruct (amap_lookup r2 y) eqn : Hr2.
      * inversion Hlook2; subst; clear Hlook2.
        apply a_equiv_p_bij in Halphap. simpl in Halphap. unfold bij_map in Halphap.
        apply Halphap in Hr2. exfalso. apply Hnotfv. apply Ha1. rewrite amap_mem_spec, Hr2. reflexivity.
      * split; auto. left. split; auto. intros Hyfv.
        apply Ha2 in Hyfv. rewrite amap_mem_spec, Hr2 in Hyfv. discriminate.
    + (*IH case*)
      specialize (IHps IH2 Hmemx ps2 ltac:(lia) Hall).
      destruct_all; auto.
Qed.

Definition alpha_equiv_t_map_fv m1 m2 t1 t2 x y
  (Halpha: alpha_equiv_t m1 m2 t1 t2)
  (Hxy: amap_lookup m1 x = Some y)
  (Hfv: aset_mem x (tm_fv t1)):
  amap_lookup m2 y = Some x /\ aset_mem y (tm_fv t2) :=
  proj_tm (alpha_equiv_map_fv x y) t1 m1 m2 t2 Hxy Halpha Hfv.

Definition alpha_equiv_f_map_fv m1 m2 f1 f2 x y
  (Halpha: alpha_equiv_f m1 m2 f1 f2)
  (Hxy: amap_lookup m1 x = Some y)
  (Hfv: aset_mem x (fmla_fv f1)):
  amap_lookup m2 y = Some x /\ aset_mem y (fmla_fv f2) :=
  proj_fmla (alpha_equiv_map_fv x y) f1 m1 m2 f2 Hxy Halpha Hfv.

(*More useful corollaries*)
(*First, an aux lemma*)
Lemma alpha_equiv_t_map_fv_aux m1 m2 t1 t2 x y
  (Halpha: alpha_equiv_t m1 m2 t1 t2)
  (Hvar: alpha_equiv_var m1 m2 x y):
  aset_mem x (tm_fv t1) -> aset_mem y (tm_fv t2).
Proof.
  rewrite alpha_equiv_var_iff in Hvar.
  destruct Hvar as [[Hlook1 Hlook2] | [Hlook1 [Hlook2 Heq]]]; subst.
  - intros Hfv. apply alpha_equiv_t_map_fv with(x:=x)(y:=y) in Halpha; auto.
    destruct_all; auto.
  - apply alpha_t_fv_filter in Halpha.
    apply (f_equal (fun s => aset_mem y s)) in Halpha.
    (*Why is it here? - provable half of propext*)
    apply ZifyClasses.eq_iff in Halpha.
    rewrite !aset_mem_filter in Halpha.
    intros Hmem.
    apply Halpha. split; auto.
    rewrite amap_mem_spec, Hlook1. auto.
Qed.

(*Then the iff (what we wanted to prove)*)
Corollary alpha_equiv_t_map_fv_iff m1 m2 t1 t2 x y
  (Halpha: alpha_equiv_t m1 m2 t1 t2)
  (Hvar: alpha_equiv_var m1 m2 x y):
  aset_mem x (tm_fv t1) <-> aset_mem y (tm_fv t2).
Proof.
  split.
  - eapply alpha_equiv_t_map_fv_aux; eauto.
  - apply alpha_equiv_t_map_fv_aux with (m1:=m2)(m2:=m1).
    + rewrite alpha_equiv_t_sym; auto.
    + apply alpha_equiv_var_sym; auto.
Qed.

Lemma alpha_equiv_f_map_fv_aux m1 m2 f1 f2 x y
  (Halpha: alpha_equiv_f m1 m2 f1 f2)
  (Hvar: alpha_equiv_var m1 m2 x y):
  aset_mem x (fmla_fv f1) -> aset_mem y (fmla_fv f2).
Proof.
  rewrite alpha_equiv_var_iff in Hvar.
  destruct Hvar as [[Hlook1 Hlook2] | [Hlook1 [Hlook2 Heq]]]; subst.
  - intros Hfv. apply alpha_equiv_f_map_fv with(x:=x)(y:=y) in Halpha; auto.
    destruct_all; auto.
  - apply alpha_f_fv_filter in Halpha.
    apply (f_equal (fun s => aset_mem y s)) in Halpha.
    apply ZifyClasses.eq_iff in Halpha.
    rewrite !aset_mem_filter in Halpha.
    intros Hmem.
    apply Halpha. split; auto.
    rewrite amap_mem_spec, Hlook1. auto.
Qed.

(*Then the iff (what we wanted to prove)*)
Corollary alpha_equiv_f_map_fv_iff m1 m2 f1 f2 x y
  (Halpha: alpha_equiv_f m1 m2 f1 f2)
  (Hvar: alpha_equiv_var m1 m2 x y):
  aset_mem x (fmla_fv f1) <-> aset_mem y (fmla_fv f2).
Proof.
  split.
  - eapply alpha_equiv_f_map_fv_aux; eauto.
  - apply alpha_equiv_f_map_fv_aux with (m1:=m2)(m2:=m1).
    + rewrite alpha_equiv_f_sym; auto.
    + apply alpha_equiv_var_sym; auto.
Qed.

(*General [same_in] - TODO: replace other version with this*)

Fixpoint same_in_p (p1 p2: pattern) (x y: vsymbol) : bool :=
  match p1, p2 with
  | Pvar v1, Pvar v2 => eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 y)
  | Pconstr f1 tys1 ps1, Pconstr t2 tys2 ps2 =>
    (length ps1 =? length ps2) &&
    all2 (fun p1 p2 => same_in_p p1 p2 x y) ps1 ps2
  | Pwild, Pwild => true
  | Por p1 p2, Por p3 p4 =>
    same_in_p p1 p3 x y &&
    same_in_p p2 p4 x y
  | Pbind p1 v1, Pbind p2 v2 =>
    same_in_p p1 p2 x y &&
    eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 y)
  | _, _ => false
  end.

Fixpoint same_in_t (t1 t2: term) (x y: vsymbol) : bool :=
  match t1, t2 with
  | Tconst _, Tconst _ => true
  | Tvar v1, Tvar v2 => eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 y)
  | Tlet tm1 v1 tm2, Tlet tm3 v2 tm4 =>
    same_in_t tm1 tm3 x y &&
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 y)) &&
    same_in_t tm2 tm4 x y
  | Tfun f1 tys1 tms1, Tfun f2 tys2 tms2 =>
    (length tms1 =? length tms2) &&
    all2 (fun t1 t2 => same_in_t t1 t2 x y) tms1 tms2
  | Tif f1 tm1 tm2, Tif f2 tm3 tm4 =>
    same_in_f f1 f2 x y &&
    same_in_t tm1 tm3 x y &&
    same_in_t tm2 tm4 x y
  | Tmatch tm1 v1 ps1, Tmatch tm2 v2 ps2 =>
    (length ps1 =? length ps2) &&
    same_in_t tm1 tm2 x y &&
    all2 (fun x1 x2 => 
      same_in_p (fst x1) (fst x2) x y &&
      same_in_t (snd x1) (snd x2) x y) ps1 ps2
  | Teps f1 v1, Teps f2 v2 =>
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 y)) &&
    same_in_f f1 f2 x y
  | _, _ => false
  end
with same_in_f (f1 f2: formula) (x y: vsymbol) : bool :=
  match f1, f2 with
  | Fpred p1 tys1 tms1, Fpred p2 tys2 tms2 =>
    (length tms1 =? length tms2) &&
    all2 (fun t1 t2 => same_in_t t1 t2 x y) tms1 tms2
  | Fquant q1 v1 f1, Fquant q2 v2 f2 =>
    eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 y) &&
    same_in_f f1 f2 x y
  | Feq v1 t1 t2, Feq v2 t3 t4 =>
    same_in_t t1 t3 x y &&
    same_in_t t2 t4 x y
  | Fbinop b1 f1 f2, Fbinop b2 f3 f4 =>
    same_in_f f1 f3 x y &&
    same_in_f f2 f4 x y
  | Fnot f1, Fnot f2 =>
    same_in_f f1 f2 x y
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet tm1 v1 f1, Flet tm2 v2 f2 =>
    same_in_t tm1 tm2 x y &&
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 y)) &&
    same_in_f f1 f2 x y
  | Fif f1 f2 f3, Fif f4 f5 f6 =>
    same_in_f f1 f4 x y &&
    same_in_f f2 f5 x y &&
    same_in_f f3 f6 x y
  | Fmatch tm1 v1 ps1, Fmatch tm2 v2 ps2 =>
    (length ps1 =? length ps2) &&
    same_in_t tm1 tm2 x y &&
    all2 (fun x1 x2 => 
     (* (length (pat_fv (fst x1)) =? length (pat_fv (fst x2))) && *)
      same_in_p (fst x1) (fst x2) x y &&
      same_in_f (snd x1) (snd x2) x y) ps1 ps2
  | _, _ => false
  end.

(*Also generalization*)
Lemma same_in_p_fv (p1 p2: pattern) x y:
  same_in_p p1 p2 x y ->
  aset_mem x (pat_fv p1) <-> aset_mem y (pat_fv p2).
Proof.
  revert p2. induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; 
  intros [x2| f2 tys2 ps2 | | p2 q2 | p2 x2]; try discriminate; simpl; try reflexivity;
  intros Hsame.
  - simpl_set. vsym_eq x1 x.
    + vsym_eq x2 y; try discriminate. split; auto.
    + vsym_eq x2 y; try discriminate. split; intros; subst; contradiction.
  - rewrite andb_true in Hsame. destruct Hsame as [Hlen Hall].
    apply Nat.eqb_eq in Hlen.
    generalize dependent ps2. induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto.
    simpl. intros Hlen. simpl_set_small. rewrite all2_cons, andb_true. intros [Hsamep Hallsame].
    inversion IH as [| ? ? IH1 IH2]; subst.
    rewrite IH1; auto. rewrite IHps; auto. auto.
  - simpl_set_small. bool_hyps. rewrite (IH1 p2), (IH2 q2); auto.
  - simpl_set_small. bool_hyps. rewrite (IH p2); auto.
    apply or_iff_compat_l. vsym_eq x1 x.
    + vsym_eq x2 y; try discriminate. split; auto.
    + vsym_eq x2 y; try discriminate. split; intros; subst; contradiction.
Qed. 

Lemma same_in_p_notfv m1 m2 (p1 p2: pattern) x y:
  ~ aset_mem x (pat_fv p1) ->
  ~ aset_mem y (pat_fv p2) ->
  or_cmp m1 m2 p1 p2 -> (*for shape*)
  same_in_p p1 p2 x y.
Proof.
  revert p2. induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; 
  intros [x2| f2 tys2 ps2 | | p2 q2 | p2 x2]; try discriminate; simpl; try reflexivity;
  intros Hn1 Hn2 Hor.
  - rewrite aset_mem_singleton in Hn1, Hn2.
    vsym_eq x1 x. vsym_eq x2 y.
  - rewrite !andb_true in Hor. destruct Hor as [[[_ Hlenps] _] Hall].
    rewrite Hlenps. simpl.
    apply Nat.eqb_eq in Hlenps.
    generalize dependent ps2. induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto.
    simpl. revert Hn1. simpl. intros Hn1 Hn2.  rewrite all2_cons, andb_true.
    intros Hlen [Hor1 Hallor]. simpl_set_small.
    not_or Hn. inversion IH as [| ? ? IH1 IH2]; subst.
    rewrite all2_cons. rewrite andb_true; split; auto.
  - simpl_set_small. not_or Hn. bool_hyps. rewrite (IH1 p2), (IH2 q2); auto.
  - simpl_set_small. bool_hyps. rewrite (IH p2); auto. simpl.
    not_or Hn. vsym_eq x1 x. vsym_eq x2 y.
Qed.

(*Need something stronger: not just that they are both free or not but they map to each other*)
(*NOTE: this is true but we don't need*)
(* Lemma same_in_p_or_cmp (p1 p2: pattern) m1 m2 x y:
  or_cmp m1 m2 p1 p2 ->
  same_in_p p1 p2 x y ->
  aset_mem x (pat_fv p1) ->
  amap_lookup m1 x = Some y /\ amap_lookup m2 y = Some x.
Proof.
  revert p2. induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; 
  intros [x2| f2 tys2 ps2 | | p2 q2 | p2 x2]; try discriminate; simpl; try reflexivity;
  intros Horcmp Hsame Hfv.
  - unfold or_cmp_vsym in Horcmp. 
    destruct (amap_lookup m1 x1) as [y1|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m2 x2) as [y2|] eqn : Hlook2; [|discriminate].
    vsym_eq x2 y1; [|discriminate]. vsym_eq x1 y2; [|discriminate].
    simpl_set. subst.
    vsym_eq y2 y2. vsym_eq y1 y. discriminate.
  - rewrite !andb_true in Hsame; rewrite !andb_true in Horcmp.
    destruct Horcmp as [_ Hor]. destruct Hsame as [Hlen Hall].
    apply Nat.eqb_eq in Hlen.
    generalize dependent ps2. induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto.
    simpl. rewrite !all2_cons, !andb_true. intros [Hor1 Hor2] Hlen [Hsamep Hallsame].
    inversion IH as [| ? ? IH1 IH2]; subst.
    simpl in Hfv. simpl_set_small. destruct Hfv as [Hx | Hx]; [eapply IH1 | eapply IHps]; eauto.
  - simpl_set_small. bool_hyps. destruct Hfv; [apply (IH1 p2) | apply (IH2 q2)]; auto.
  - simpl_set_small. bool_hyps. destruct Hfv; [apply (IH p2); auto|].
    simpl_set. subst. vsym_eq x1 x1. vsym_eq x2 y; try discriminate.
    unfold or_cmp_vsym in H2. 
    destruct (amap_lookup m1 x1) as [y1|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m2 y) as [y2|] eqn : Hlook2; [|discriminate].
    vsym_eq y y1; [|discriminate]. vsym_eq x1 y2. discriminate.
Qed. *)

Lemma keys_disj_equiv {A B: Type} `{countable.Countable A} (s: aset A) (m: amap A B):
  (forall x, aset_mem x s -> amap_lookup m x = None) <-> aset_disj (keys m) s.
Proof.
  rewrite aset_disj_equiv.
  split.
  - intros Hnone x [Hx1 Hx2].
    apply Hnone in Hx2. apply amap_lookup_none in Hx2. contradiction.
  - intros Hdisj x Hmemx.
    specialize (Hdisj x).
    apply amap_lookup_none. tauto.
Qed.

Lemma aset_disj_union_l {A: Type} `{countable.Countable A} (s1 s2 s3: aset A):
  aset_disj (aset_union s1 s2) s3 ->
  aset_disj s1 s3.
Proof.
  apply disj_asubset2, union_asubset_l.
Qed.

Lemma aset_disj_union_r {A: Type} `{countable.Countable A} (s1 s2 s3: aset A):
  aset_disj (aset_union s1 s2) s3 ->
  aset_disj s2 s3.
Proof.
  apply disj_asubset2, union_asubset_r.
Qed.

Lemma aset_disj_singleton {A: Type} `{countable.Countable A} (x: A) (s: aset A):
  aset_disj (aset_singleton x) s <-> ~ aset_mem x s.
Proof.
  rewrite aset_disj_equiv. split.
  - intros Hnotin Hmemx.
    specialize (Hnotin x). apply Hnotin; simpl_set; auto.
  - intros Hnotin y [Hmem Hmem']. simpl_set. subst. contradiction.
Qed.

Ltac split_disj_union :=
  repeat match goal with
  | H: aset_disj (aset_union ?s1 ?s2) ?s |- _ =>
    let H1 := fresh "Hd" in
    assert (H1:=H);
    apply aset_disj_union_l in H; apply aset_disj_union_r in H1
  end.

Ltac solve_disj_union :=
  split_disj_union; solve[auto].

(*TODO: do single version*)

Lemma amap_diff_aunion {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (s: aset A):
  amap_diff (aunion m1 m2) s = aunion (amap_diff m1 s) (amap_diff m2 s).
Proof.
  apply amap_ext.
  intros x. rewrite aunion_lookup. destruct (aset_mem_dec x s).
  - rewrite !amap_diff_in; auto.
  - rewrite !amap_diff_notin; auto.
    rewrite aunion_lookup. reflexivity.
Qed.

Lemma amap_diff_keys {A B: Type} `{countable.Countable A} (m1: amap A B):
  amap_diff m1 (keys m1) = amap_empty.
Proof.
  apply amap_ext.
  intros x. rewrite amap_empty_get.
  destruct (aset_mem_dec x (keys m1)).
  - apply amap_diff_in; auto.
  - rewrite amap_diff_notin; auto. apply amap_lookup_none; auto.
Qed.


Lemma alpha_equiv_t_extra_union r1 r2 m1 m2 t1 t2:
  aset_disj (keys r1) (tm_fv t1) ->
  aset_disj (keys r2) (tm_fv t2) ->
  alpha_equiv_t (aunion r1 m1) (aunion r2 m2) t1 t2 = alpha_equiv_t m1 m2 t1 t2.
Proof.
  intros Hdisj1 Hdisj2.
  rewrite <- (alpha_equiv_t_diff) with (s:=keys r2); auto.
  rewrite <- (alpha_equiv_t_diff _ _ (keys r2) m1 m2); auto.
  (*And do other side*)
  rewrite !(alpha_equiv_t_sym t1 t2).
  rewrite <- (alpha_equiv_t_diff) with (s:=keys r1); auto.
  rewrite <- (alpha_equiv_t_diff _ _ (keys r1) _ m1); auto.
  (*Now prove maps equal*)
  rewrite !amap_diff_aunion, !amap_diff_keys, !aunion_empty_l. reflexivity.
Qed.

(*Single version*)
Lemma alpha_equiv_t_extra_var x y m1 m2 t1 t2:
  ~ aset_mem x (tm_fv t1) ->
  ~ aset_mem y (tm_fv t2) ->
  alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t1 t2 = alpha_equiv_t m1 m2 t1 t2.
Proof.
  intros Hmem1 Hmem2. rewrite !amap_set_aunion. apply alpha_equiv_t_extra_union;
  rewrite !keys_singleton; apply aset_disj_singleton; auto.
Qed.

(*TODO: why didnt I prove in Alpha?*)
Lemma alpha_equiv_f_diff (f1 f2: formula) (s: aset vsymbol) (m1 m2: amap vsymbol vsymbol)
  (Hdisj: aset_disj s (fmla_fv f2)):
  alpha_equiv_f m1 (amap_diff m2 s) f1 f2 = alpha_equiv_f m1 m2 f1 f2.
Proof.
  rewrite amap_diff_remove. rewrite aset_disj_equiv in Hdisj.
  setoid_rewrite <- aset_to_list_in in Hdisj.
  induction (aset_to_list s); simpl; auto.
  simpl in Hdisj.
  rewrite alpha_equiv_f_remove; auto.
  - apply IHl. intros x [Hinx1 Hinx2]; apply (Hdisj x); auto.
  - intros Hmem. apply (Hdisj a); auto. split; auto; simpl_set; auto.
Qed.

Lemma alpha_equiv_f_extra_union r1 r2 m1 m2 f1 f2:
  aset_disj (keys r1) (fmla_fv f1) ->
  aset_disj (keys r2) (fmla_fv f2) ->
  alpha_equiv_f (aunion r1 m1) (aunion r2 m2) f1 f2 = alpha_equiv_f m1 m2 f1 f2.
Proof.
  intros Hdisj1 Hdisj2.
  rewrite <- (alpha_equiv_f_diff) with (s:=keys r2); auto.
  rewrite <- (alpha_equiv_f_diff _ _ (keys r2) m1 m2); auto.
  (*And do other side*)
  rewrite !(alpha_equiv_f_sym f1 f2).
  rewrite <- (alpha_equiv_f_diff) with (s:=keys r1); auto.
  rewrite <- (alpha_equiv_f_diff _ _ (keys r1) _ m1); auto.
  (*Now prove maps equal*)
  rewrite !amap_diff_aunion, !amap_diff_keys, !aunion_empty_l. reflexivity.
Qed.

(*Single version*)
Lemma alpha_equiv_f_extra_var x y m1 m2 f1 f2:
  ~ aset_mem x (fmla_fv f1) ->
  ~ aset_mem y (fmla_fv f2) ->
  alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2 = alpha_equiv_f m1 m2 f1 f2.
Proof.
  intros Hmem1 Hmem2. rewrite !amap_set_aunion. apply alpha_equiv_f_extra_union;
  rewrite !keys_singleton; apply aset_disj_singleton; auto.
Qed.


(*If tm1 and tm2 are alpha equivalent by m3 and m4
  and t1 and t2 are alpha equivalent by m1 and m2
  and x and y occur in t1 and t2 the same
  then t1[tm1/x] is alpha equivalent to t2[tm2/y] by (m1 U m3) and (m2 U m4) (I hope)*)
(*Could do for multiple sub, but dont need here*)
Lemma alpha_equiv_sub tm1 tm2  x y t1 f1:
  (forall t2 m1 m2 (Halpha2: alpha_equiv_t m1 m2 tm1 tm2) 
    (Halpha1: alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t1 t2) (Hsame: same_in_t t1 t2 x y)
    (*avoid capture*) 
    (Hdisj1: aset_disj (list_to_aset (tm_bnd t1)) (tm_fv tm1))
    (Hdisj2: aset_disj (list_to_aset (tm_bnd t2)) (tm_fv tm2))
    (*NOTE maybe cant assume this*)
    (* (Hnofv1: forall x, aset_mem x (tm_fv tm1) -> amap_lookup m1 x = None)
    (Hnofv2: forall x, aset_mem x (tm_fv tm2) -> amap_lookup m2 x = None) *),
    (*TODO: do we need any further restrictions*)
    alpha_equiv_t m1 m2 (sub_t tm1 x t1) (sub_t tm2 y t2)) /\
  (forall f2 m1 m2 (Halpha2: alpha_equiv_t m1 m2 tm1 tm2)  
    (Halpha1: alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2) (Hsame: same_in_f f1 f2 x y)
    (*avoid capture*) 
    (Hdisj1: aset_disj (list_to_aset (fmla_bnd f1)) (tm_fv tm1))
    (Hdisj2: aset_disj (list_to_aset (fmla_bnd f2)) (tm_fv tm2))
    (* (Hnofv1: forall x, aset_mem x (tm_fv tm1) -> amap_lookup m1 x = None)
    (Hnofv2: forall x, aset_mem x (tm_fv tm2) -> amap_lookup m2 x = None) *),
    (*TODO: do we need any further restrictions*)
    alpha_equiv_f m1 m2 (sub_f tm1 x f1) (sub_f tm2 y f2)).
Proof.
  revert t1 f1. apply term_formula_ind; simpl. (*TODO: try to do var and let case*)
  - intros c t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2; try discriminate. simpl. auto.
  - (*Tvar*)
    intros v1 t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2 as [| v2 | | | | |]; try discriminate.
    simpl. vsym_eq x v1.
    + vsym_eq v1 v1. simpl in Hsame. vsym_eq v2 y. vsym_eq y y.
    + vsym_eq v1 x. simpl in Hsame. vsym_eq v2 y. vsym_eq y v2.
      simpl. (*Now prove from [amap_set]*)
      rewrite !alpha_equiv_var_iff in Halpha |- *.
      rewrite !amap_set_lookup_diff in Halpha; auto.
  - (*Tfun*)
    intros f1 tys1 tms1 IHtms t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2 as [| | f2 tys2 tms2 | | | |]; try discriminate.
    simpl.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate]; simpl in Halpha. rewrite !length_map. 
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate]; simpl in *.
    destruct (list_eq_dec _ tys1 tys2); [|discriminate]; subst. simpl in *.
    rewrite all2_map.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IH]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true.
    intros [Halpha Hall] [Hsame1 Hsame2]. inversion IHtms as [| ? ? IH1 IH2]; subst; clear IHtms.
    revert Hd1. simpl. rewrite !list_to_aset_app. intros Hd1 Hd2 Hlen.
    split_disj_union. split; [apply IH1 | apply IH]; auto.
  - (*Tlet*)
    intros e1 v1 e2 IH1 IH2 t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2 as [| | | e3 v2 e4 | | |]; try discriminate.
    simpl.
    simpl in Hd2.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[Hty Ha1] Ha2].
    rewrite !andb_true in Hsame. destruct Hsame as [[Hsame1 Heqvar] Hsame2].
    rewrite !list_to_aset_cons, !list_to_aset_app in Hd1, Hd2.
    split_disj_union.
    apply IH1 in Ha1; auto.
    vsym_eq v1 x.
    + (*use same - crucial*)
      simpl in Heqvar. vsym_eq x x. vsym_eq v2 y. vsym_eq y y.
      rewrite !andb_true; split_all; auto.
      (*Just setting x and y twice - same*)
      rewrite !amap_set_twice in Ha2. auto.
    + simpl in Heqvar. vsym_eq x v1. vsym_eq v2 y. vsym_eq y v2.
      (*Here, nothing is equal - we can reorder*)
      rewrite !andb_true; split_all; auto.
      rewrite amap_set_reorder in Ha2; auto.
      rewrite (amap_set_reorder _ y v2) in Ha2; auto.
      apply IH2 in Ha2; auto.
      (*Now we can remove these vars because not free*)
      rewrite alpha_equiv_t_extra_var; auto; apply aset_disj_singleton; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 tm m1 m2 Halpha2 Halpha1 Hsame Hd1 Hd2.
    destruct tm; try discriminate. simpl.
    rewrite !andb_true in Halpha1, Hsame |- *.
    destruct Halpha1 as [[Ha1 Ha2] Ha3]. destruct Hsame as [[Hs1 Hs2] Hs3].
    simpl in Hd2. rewrite !list_to_aset_app in Hd1, Hd2. split_disj_union.
    split_all; [apply IH1 | apply IH2 | apply IH3]; auto.
  - (*Tmatch - generalizes let*)
    intros t1 ty1 ps1 IHt1 IHps1 t2 m1 m2 Halpha2 Halpha1 Hsame Hd1 Hd2.
    destruct t2 as [| | | | | t2 ty2 ps2 |]; try discriminate.
    simpl in *. rewrite !length_map.
    rewrite !andb_true in Halpha1, Hsame. (*Why doesn't this rewrite everything ugh*)
    rewrite andb_true in Halpha1.
    destruct Halpha1 as [[[Halpha1 Hlenps] Htyseq] Hall].
    destruct Hsame as [[_ Hsame] Hallsame]. rewrite Hlenps.
    apply Nat.eqb_eq in Hlenps. simpl_sumbool. simpl. rewrite !andb_true_r.
    rewrite list_to_aset_app in Hd1, Hd2. split_disj_union.
    rewrite andb_true; split; [auto|].
    (*Inductive case*)
    rewrite all2_map. simpl. clear IHt1 Halpha1 Hsame Hd1 Hd2 t1 t2 ty2.
    rename Hd into Hd2. rename Hd0 into Hd1.
    generalize dependent ps2. 
    induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; simpl; try discriminate; auto.
    inversion IHps1 as [| ? ? IH1 IH2]; subst; clear IHps1. specialize (IH IH2). clear IH2.
    rewrite !all2_cons. simpl.
    intros Hlenps. destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite !andb_true.
    intros [Halphat Hallalpha] [[Hsamep Hsamet] Hallsame].
    revert Hd1. simpl. rewrite !list_to_aset_app. intros Hd1 Hd2. split_disj_union.
    split; auto. (*IH case automatic*)
    (*Prove head case - like let*)
    assert (Hfviff:=Hsamep).
    apply same_in_p_fv in Hfviff.
    assert (Hvars:=Halphap).
    apply a_equiv_p_vars_iff in Hvars. simpl in Hvars. destruct Hvars as [Hr1 Hr2].
    (*Have to destruct - 2 cases*)
    destruct (aset_mem_dec x (pat_fv p1) ) as [Hxfv | Hxfv];
    destruct (aset_mem_dec y (pat_fv p2)) as [Hyfv | Hyfv]; [| tauto | tauto |]; simpl; rewrite Halphap.
    + rewrite !aunion_set_infst in Halphat; auto.
      * apply Hr2; auto.
      * apply Hr1; auto.
    + (*Idea: x not in r1 and y not in r2 so can rewrite as set*)
      rewrite !aunion_set_not_infst in Halphat; [| rewrite Hr2; auto | rewrite Hr1; auto].
      apply IH1 in Halphat; auto.
      (*And now know from disj that we can remove r1 and r2 because no pat fv in tm1 or tm2 *)
      rewrite alpha_equiv_t_extra_union; auto.
      * (*Prove nothing in r1 in tm1 fvs*)
        rewrite aset_to_list_to_aset_eq in Hd1.
        replace (keys r1) with (pat_fv p1); auto.
        apply aset_ext. intros v. rewrite <- Hr1. apply amap_mem_keys.
      * (*and for r2*)
        rewrite aset_to_list_to_aset_eq in Hd2.
        replace (keys r2) with (pat_fv p2); auto.
        apply aset_ext. intros v. rewrite <- Hr2. apply amap_mem_keys.
  - (*Teps*)
    intros f1 v1 IH t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2 as [| | | | | | f2 v2]; try discriminate.
    simpl.
    simpl in Hd2.
    rewrite !andb_true in Halpha.
    destruct Halpha as [Hty Ha].
    rewrite !andb_true in Hsame. destruct Hsame as [Heqvar Hsame].
    rewrite !list_to_aset_cons in Hd1, Hd2.
    split_disj_union.
    vsym_eq v1 x.
    + simpl in Heqvar. vsym_eq x x. vsym_eq v2 y. vsym_eq y y. simpl.
      rewrite !andb_true; split_all; auto.
      (*Just setting x and y twice - same*)
      rewrite !amap_set_twice in Ha. auto.
    + simpl in Heqvar. vsym_eq x v1. vsym_eq v2 y. vsym_eq y v2. simpl.
      (*Here, nothing is equal - we can reorder*)
      rewrite !andb_true; split_all; auto.
      rewrite amap_set_reorder in Ha; auto.
      rewrite (amap_set_reorder _ y v2) in Ha; auto.
      apply IH in Ha; auto.
      rewrite alpha_equiv_t_extra_var; auto; apply aset_disj_singleton; auto.
  - (*Fpred*)
    intros p1 tys1 tms1 IHtms t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2 as [p2 tys2 tms2 | | | | | | | | |]; try discriminate.
    simpl.
    destruct (predsym_eq_dec p1 p2); subst; [|discriminate]; simpl in Halpha. rewrite !length_map. 
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate]; simpl in *.
    destruct (list_eq_dec _ tys1 tys2); [|discriminate]; subst. simpl in *.
    rewrite all2_map.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IH]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true.
    intros [Halpha Hall] [Hsame1 Hsame2]. inversion IHtms as [| ? ? IH1 IH2]; subst; clear IHtms.
    revert Hd1. simpl. rewrite !list_to_aset_app. intros Hd1 Hd2 Hlen.
    split_disj_union. split; [apply IH1 | apply IH]; auto.
  - (*Fquant*)
    intros q1 v1 f1 IH t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2 as [| q2 v2 f2 | | | | | | | |]; try discriminate.
    simpl.
    simpl in Hd2.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[Hq Hty] Ha].
    rewrite !andb_true in Hsame. destruct Hsame as [Heqvar Hsame].
    rewrite !list_to_aset_cons in Hd1, Hd2.
    split_disj_union.
    vsym_eq v1 x.
    + simpl in Heqvar. vsym_eq x x. vsym_eq v2 y. vsym_eq y y. simpl.
      rewrite !andb_true; split_all; auto.
      rewrite !amap_set_twice in Ha. auto.
    + simpl in Heqvar. vsym_eq x v1. vsym_eq v2 y. vsym_eq y v2. simpl.
      rewrite !andb_true; split_all; auto.
      rewrite amap_set_reorder in Ha; auto.
      rewrite (amap_set_reorder _ y v2) in Ha; auto.
      apply IH in Ha; auto.
      rewrite alpha_equiv_t_extra_var; auto; apply aset_disj_singleton; auto.
  - (*Feq*)
    intros ty1 t1 t2 IH1 IH2 tm m1 m2 Halpha2 Halpha1 Hsame Hd1 Hd2.
    destruct tm; try discriminate. simpl.
    rewrite !andb_true in Halpha1; rewrite !andb_true in Hsame; rewrite !andb_true.
    destruct Halpha1 as [[ Htyeq Ha1] Ha2]. destruct Hsame as [Hs1 Hs2].
    simpl in Hd2. rewrite !list_to_aset_app in Hd1, Hd2. split_disj_union. auto.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2 tm m1 m2 Halpha2 Halpha1 Hsame Hd1 Hd2.
    destruct tm; try discriminate. simpl.
    rewrite !andb_true in Halpha1; rewrite !andb_true in Hsame; rewrite !andb_true.
    destruct Halpha1 as [[ Htyeq Ha1] Ha2]. destruct Hsame as [Hs1 Hs2].
    simpl in Hd2. rewrite !list_to_aset_app in Hd1, Hd2. split_disj_union. auto.
  - (*Fnot*)
    intros f1 IH f2 m1 m2 Halpha2 Halpha1 Hsame. destruct f2; try discriminate.
    simpl. intros. auto.
  - (*Ftrue*) intros f2; intros. destruct f2; try discriminate. auto.
  - (*Ffalse*) intros f2; intros. destruct f2; try discriminate. auto.
  - (*Flet*) intros e1 v1 e2 IH1 IH2 t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2 as [| | | | | | | e3 v2 e4 | |]; try discriminate.
    simpl.
    simpl in Hd2.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[Hty Ha1] Ha2].
    rewrite !andb_true in Hsame. destruct Hsame as [[Hsame1 Heqvar] Hsame2].
    rewrite !list_to_aset_cons, !list_to_aset_app in Hd1, Hd2.
    split_disj_union.
    apply IH1 in Ha1; auto.
    vsym_eq v1 x.
    + simpl in Heqvar. vsym_eq x x. vsym_eq v2 y. vsym_eq y y.
      rewrite !andb_true; split_all; auto.
      rewrite !amap_set_twice in Ha2. auto.
    + simpl in Heqvar. vsym_eq x v1. vsym_eq v2 y. vsym_eq y v2.
      rewrite !andb_true; split_all; auto.
      rewrite amap_set_reorder in Ha2; auto.
      rewrite (amap_set_reorder _ y v2) in Ha2; auto.
      apply IH2 in Ha2; auto.
      rewrite alpha_equiv_t_extra_var; auto; apply aset_disj_singleton; auto.
  - (*Fif*)
    intros f t1 t2 IH1 IH2 IH3 tm m1 m2 Halpha2 Halpha1 Hsame Hd1 Hd2.
    destruct tm; try discriminate. simpl.
    rewrite !andb_true in Halpha1, Hsame |- *.
    destruct Halpha1 as [[Ha1 Ha2] Ha3]. destruct Hsame as [[Hs1 Hs2] Hs3].
    simpl in Hd2. rewrite !list_to_aset_app in Hd1, Hd2. split_disj_union.
    split_all; [apply IH1 | apply IH2 | apply IH3]; auto.
  - (*Fmatch - exactly the same as Tmatch*)
    intros t1 ty1 ps1 IHt1 IHps1 t2 m1 m2 Halpha2 Halpha1 Hsame Hd1 Hd2.
    destruct t2 as [| | | | | | | | | t2 ty2 ps2]; try discriminate.
    simpl in *. rewrite !length_map.
    rewrite !andb_true in Halpha1, Hsame.
    rewrite andb_true in Halpha1.
    destruct Halpha1 as [[[Halpha1 Hlenps] Htyseq] Hall].
    destruct Hsame as [[_ Hsame] Hallsame]. rewrite Hlenps.
    apply Nat.eqb_eq in Hlenps. simpl_sumbool. simpl. rewrite !andb_true_r.
    rewrite list_to_aset_app in Hd1, Hd2. split_disj_union.
    rewrite andb_true; split; [auto|].
    rewrite all2_map. simpl. clear IHt1 Halpha1 Hsame Hd1 Hd2 t1 t2 ty2.
    rename Hd into Hd2. rename Hd0 into Hd1.
    generalize dependent ps2. 
    induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; simpl; try discriminate; auto.
    inversion IHps1 as [| ? ? IH1 IH2]; subst; clear IHps1. specialize (IH IH2). clear IH2.
    rewrite !all2_cons. simpl.
    intros Hlenps. destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite !andb_true.
    intros [Halphat Hallalpha] [[Hsamep Hsamet] Hallsame].
    revert Hd1. simpl. rewrite !list_to_aset_app. intros Hd1 Hd2. split_disj_union.
    split; auto. assert (Hfviff:=Hsamep).
    apply same_in_p_fv in Hfviff.
    assert (Hvars:=Halphap).
    apply a_equiv_p_vars_iff in Hvars. simpl in Hvars. destruct Hvars as [Hr1 Hr2].
    destruct (aset_mem_dec x (pat_fv p1) ) as [Hxfv | Hxfv];
    destruct (aset_mem_dec y (pat_fv p2)) as [Hyfv | Hyfv]; [| tauto | tauto |]; simpl; rewrite Halphap.
    + rewrite !aunion_set_infst in Halphat; auto.
      * apply Hr2; auto.
      * apply Hr1; auto.
    + rewrite !aunion_set_not_infst in Halphat; [| rewrite Hr2; auto | rewrite Hr1; auto].
      apply IH1 in Halphat; auto.
      rewrite alpha_equiv_t_extra_union; auto.
      * rewrite aset_to_list_to_aset_eq in Hd1.
        replace (keys r1) with (pat_fv p1); auto.
        apply aset_ext. intros v. rewrite <- Hr1. apply amap_mem_keys.
      * rewrite aset_to_list_to_aset_eq in Hd2.
        replace (keys r2) with (pat_fv p2); auto.
        apply aset_ext. intros v. rewrite <- Hr2. apply amap_mem_keys.
Qed.

Definition alpha_equiv_t_sub tm1 tm2 x y t1 t2 m1 m2 (Halpha1: alpha_equiv_t m1 m2 tm1 tm2)
  (Halpha2: alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t1 t2)
  (Hsame: same_in_t t1 t2 x y)
  (Hdisj1: aset_disj (list_to_aset (tm_bnd t1)) (tm_fv tm1))
  (Hdisj2: aset_disj (list_to_aset (tm_bnd t2)) (tm_fv tm2)):
  alpha_equiv_t m1 m2 (sub_t tm1 x t1) (sub_t tm2 y t2) :=
  proj_tm (alpha_equiv_sub tm1 tm2 x y) t1 t2 m1 m2 Halpha1 Halpha2 Hsame Hdisj1 Hdisj2.

Definition alpha_equiv_f_sub tm1 tm2 x y f1 f2 m1 m2 (Halpha1: alpha_equiv_t m1 m2 tm1 tm2)
  (Halpha2: alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2)
  (Hsame: same_in_f f1 f2 x y)
  (Hdisj1: aset_disj (list_to_aset (fmla_bnd f1)) (tm_fv tm1))
  (Hdisj2: aset_disj (list_to_aset (fmla_bnd f2)) (tm_fv tm2)):
  alpha_equiv_f m1 m2 (sub_f tm1 x f1) (sub_f tm2 y f2) :=
  proj_fmla (alpha_equiv_sub tm1 tm2 x y) f1 f2 m1 m2 Halpha1 Halpha2 Hsame Hdisj1 Hdisj2.

(*I hope this is true - if needed can assume in fv but that might make harder)*)
(*NOT true if x or y can be bound
  example: map x <-> z, terms x=x || forall x.x=x and z=z || forall y.y=y these are alpha equiv under x <-> z
  but NOT same_in_t for x and z *)
Lemma alpha_not_bnd_same x y t1 f1:
  (forall m1 m2 t2 (Halpha: alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t1 t2) 
    (Hbnd1: ~ In x (tm_bnd t1)) (Hbnd2: ~ In y (tm_bnd t2)) (*TODO: do we need other?*)
    (* (Hlook1: amap_lookup m1 x = Some y) *) (*(Hlook2: amap_lookup m2 y = Some x)*)
    (* (Hfv1: aset_mem x (tm_fv t1)) *) (*(Hfv2: aset_mem y (tm_fv t2)*),
    same_in_t t1 t2 x y) /\
  (forall m1 m2 f2 (Halpha: alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2) 
    (Hbnd1: ~ In x (fmla_bnd f1)) (Hbnd2: ~ In y (fmla_bnd f2)),
    same_in_f f1 f2 x y).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; auto.
  - intros c m1 m2 t2 Halpha. destruct t2; try discriminate. auto.
  - (*Tvar*) intros v1 m1 m2 t2 Halpha Hbnd1. (*Hlook Hfv.*)
    destruct t2 as [| v2 | | | | |]; try discriminate.
    rewrite !alpha_equiv_var_iff in Halpha.
    vsym_eq v1 x.
    + rewrite !amap_set_lookup_same in Halpha. destruct Halpha as [[Hsome _] | [Hsome _]]; inversion Hsome; subst.
      vsym_eq v2 v2.
    + vsym_eq v2 y. rewrite !amap_set_lookup_same in Halpha.
      destruct Halpha as [[_ Hsome] | [_ [Hsome _]]]; inversion Hsome; subst. contradiction.
  - (*Tfun*)
    intros f1 tys1 tms1 IH m1 m2 t2 Halpha Hbnd1 Hbnd2. destruct t2 as [| | f2 tys2 tms2 | | | | ]; try discriminate.
    simpl. rewrite !andb_true in Halpha.
    destruct Halpha as [[[ _ Hlen] _] Hall].
    rewrite Hlen. simpl. apply Nat.eqb_eq in Hlen.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true. intros Hlentms [Halpha Hall] Hbnd2. simpl in Hbnd1.
    rewrite in_app_iff in Hbnd1, Hbnd2.
    not_or Hbnd. inversion IH as [| ? ? IH1 IH2]; subst.
    split; auto. eapply IH1; eauto.
  - (*Tlet*)
    intros tm1 v1 tm2 IH1 IH2 m1 m2 t2 Halpha Hbnd1 Hbnd2.
    destruct t2 as [| | | tm3 v2 tm4 | | | ]; try discriminate.
    rewrite !andb_true in Halpha |- *.
    simpl in *. rewrite !in_app_iff in Hbnd1, Hbnd2. not_or Hbnd.
    vsym_eq v1 x. vsym_eq v2 y.  
    destruct Halpha as [[Htyeq Ha1] Ha2].
    apply IH1 in Ha1; auto. rewrite Ha1. simpl.
    split_all; auto.
    (*not equal, so reorder*)
    rewrite (amap_set_reorder _ x) in Ha2; auto.
    rewrite (amap_set_reorder _ y) in Ha2; auto.
    apply IH2 in Ha2; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 m1 m2 tm Halpha.
    destruct tm; try discriminate; simpl in *.
    rewrite !in_app_iff. intros Hbnd1 Hbnd2. not_or Hbnd.
    rewrite !andb_true in Halpha |- *. destruct_all. split; eauto.
  - (*Tmatch*)
    intros tm1 ty1 ps1 IHtm1 IHps m1 m2 t2 Halpha.
    destruct t2 as [| | | | | tm2 ty2 ps2 |]; try discriminate.
    simpl in *. rewrite !in_app_iff. intros Hbnd1 Hbnd2.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[[Halpha1 Hlenps] _] Hall].
    rewrite Hlenps. simpl.
    rewrite IHtm1 with (m1:=m1)(m2:=m2); auto. simpl.
    not_or Hbnd. clear IHtm1 Halpha1 Hbnd2 Hbnd tm1 tm2 ty1 ty2.
    rename Hbnd3 into Hbnd1. rename Hbnd0 into Hbnd2.
    apply Nat.eqb_eq in Hlenps.
    generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; try discriminate; auto.
    simpl in *.
    inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
    specialize (IHps1 IH2); clear IH2.
    rewrite !all2_cons. simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    intros Hlen. rewrite !andb_true. intros [Halphat Hall].
    revert Hbnd1. rewrite !in_app_iff. intros Hbnd1 Hbnd2.
    not_or Hbnd.
    rewrite IHps1; auto. split; auto; clear IHps1 Hall.
    (*Need to show if x and y not in free vars, then same_in_p*)
    (*Again, need to flip set order*)
    assert (Hvars:=Halphap).
    apply a_equiv_p_vars_iff in Hvars. simpl in Hvars. destruct Hvars as [Hr1 Hr2].
    rewrite aset_to_list_in in Hbnd1, Hbnd2.
    rewrite !aunion_set_not_infst in Halphat; [| rewrite Hr2; auto | rewrite Hr1; auto].
    apply IH1 in Halphat; auto. rewrite Halphat.
    (*Lastly: not in fv so same_in_p trivially true*)
    split; auto. apply a_equiv_p_or_cmp_iff in Halphap. destruct Halphap as [Hor _].
    simpl in Hor. apply same_in_p_notfv with (m1:=r1)(m2:=r2); auto.
  - (*Teps*)
    intros f1 v1 IH m1 m2 t2 Halpha. destruct t2 as [| | | | | | f2 v2]; try discriminate.
    simpl. intros. not_or Hbnd. vsym_eq v1 x. vsym_eq v2 y. simpl.
    rewrite andb_true in Halpha. destruct Halpha as [_ Ha].
    rewrite (amap_set_reorder _ x) in Ha; auto.
    rewrite (amap_set_reorder _ y) in Ha; auto.
    apply IH in Ha; auto.
  - (*Fpred*)
    intros p1 tys1 tms1 IH m1 m2 t2 Halpha Hbnd1 Hbnd2. destruct t2 as [p2 tys2 tms2 | | | | | | | | |]; try discriminate.
    simpl. rewrite !andb_true in Halpha.
    destruct Halpha as [[[ _ Hlen] _] Hall].
    rewrite Hlen. simpl. apply Nat.eqb_eq in Hlen.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true. intros Hlentms [Halpha Hall] Hbnd2. simpl in Hbnd1.
    rewrite in_app_iff in Hbnd1, Hbnd2.
    not_or Hbnd. inversion IH as [| ? ? IH1 IH2]; subst.
    split; auto. eapply IH1; eauto.
  - (*Fquant*)
    intros q1 v1 f1 IH m1 m2 t2 Halpha. destruct t2 as [| q2 v2 f2 | | | | | | | | ]; try discriminate.
    simpl. intros. not_or Hbnd. vsym_eq v1 x. vsym_eq v2 y. simpl.
    rewrite andb_true in Halpha. destruct Halpha as [_ Ha].
    rewrite (amap_set_reorder _ x) in Ha; auto.
    rewrite (amap_set_reorder _ y) in Ha; auto.
    apply IH in Ha; auto.
  - (*Feq*)
    intros ty t1 t2 IH1 IH2 m1 m2 f2 Halpha. destruct f2; try discriminate. simpl.
    rewrite !in_app_iff. intros. not_or Hbnd. rewrite !andb_true in Halpha.
    destruct Halpha as [[_ Ha1] Ha2]. rewrite andb_true; split; [eapply IH1 | eapply IH2]; eauto.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2 m1 m2 fm Halpha. destruct fm; try discriminate. simpl.
    rewrite !in_app_iff. intros. not_or Hbnd. rewrite !andb_true in Halpha.
    destruct Halpha as [[_ Ha1] Ha2]. rewrite andb_true; split; [eapply IH1 | eapply IH2]; eauto.
  - (*Fnot*)
    intros f IH m1 m2 f2 Halpha. destruct f2; try discriminate. simpl. intros; eauto.
  - (*Flet*)
    intros tm1 v1 tm2 IH1 IH2 m1 m2 f2 Halpha Hbnd1 Hbnd2.
    destruct f2 as [| | | | | | | tm3 v2 tm4 | | ]; try discriminate.
    rewrite !andb_true in Halpha |- *.
    simpl in *. rewrite !in_app_iff in Hbnd1, Hbnd2. not_or Hbnd.
    vsym_eq v1 x. vsym_eq v2 y.  
    destruct Halpha as [[Htyeq Ha1] Ha2].
    apply IH1 in Ha1; auto. rewrite Ha1. simpl.
    split_all; auto.
    rewrite (amap_set_reorder _ x) in Ha2; auto.
    rewrite (amap_set_reorder _ y) in Ha2; auto.
    apply IH2 in Ha2; auto.
  - (*Fif*)
    intros f t1 t2 IH1 IH2 IH3 m1 m2 tm Halpha.
    destruct tm; try discriminate; simpl in *.
    rewrite !in_app_iff. intros Hbnd1 Hbnd2. not_or Hbnd.
    rewrite !andb_true in Halpha |- *. destruct_all. split; eauto.
  - (*Fmatch*)
    intros tm1 ty1 ps1 IHtm1 IHps m1 m2 t2 Halpha.
    destruct t2 as [| | | | |  | | | | tm2 ty2 ps2]; try discriminate.
    simpl in *. rewrite !in_app_iff. intros Hbnd1 Hbnd2.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[[Halpha1 Hlenps] _] Hall].
    rewrite Hlenps. simpl.
    rewrite IHtm1 with (m1:=m1)(m2:=m2); auto. simpl.
    not_or Hbnd. clear IHtm1 Halpha1 Hbnd2 Hbnd tm1 tm2 ty1 ty2.
    rename Hbnd3 into Hbnd1. rename Hbnd0 into Hbnd2.
    apply Nat.eqb_eq in Hlenps.
    generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; try discriminate; auto.
    simpl in *.
    inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
    specialize (IHps1 IH2); clear IH2.
    rewrite !all2_cons. simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    intros Hlen. rewrite !andb_true. intros [Halphat Hall].
    revert Hbnd1. rewrite !in_app_iff. intros Hbnd1 Hbnd2.
    not_or Hbnd.
    rewrite IHps1; auto. split; auto; clear IHps1 Hall.
    assert (Hvars:=Halphap).
    apply a_equiv_p_vars_iff in Hvars. simpl in Hvars. destruct Hvars as [Hr1 Hr2].
    rewrite aset_to_list_in in Hbnd1, Hbnd2.
    rewrite !aunion_set_not_infst in Halphat; [| rewrite Hr2; auto | rewrite Hr1; auto].
    apply IH1 in Halphat; auto. rewrite Halphat.
    split; auto. apply a_equiv_p_or_cmp_iff in Halphap. destruct Halphap as [Hor _].
    simpl in Hor. apply same_in_p_notfv with (m1:=r1)(m2:=r2); auto.
Qed.

Definition alpha_not_bnd_same_in_t x y t1 t2 m1 m2 
  (Halpha: alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t1 t2) 
  (Hbnd1: ~ In x (tm_bnd t1)) (Hbnd2: ~ In y (tm_bnd t2)):
  same_in_t t1 t2 x y :=
  proj_tm (alpha_not_bnd_same x y) t1 m1 m2 t2 Halpha Hbnd1 Hbnd2.

Definition alpha_not_bnd_same_in_f x y f1 f2 m1 m2 
  (Halpha: alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2) 
  (Hbnd1: ~ In x (fmla_bnd f1)) (Hbnd2: ~ In y (fmla_bnd f2)):
  same_in_f f1 f2 x y :=
  proj_fmla (alpha_not_bnd_same x y) f1 m1 m2 f2 Halpha Hbnd1 Hbnd2.

(*And we can combine the two results: instead of assuming [same_in_t], we can just
  assume we the variable we substitute for is not bound*)

Corollary alpha_equiv_t_sub_not_bnd (tm1 tm2 : term) (x y : vsymbol) (t1 t2 : term) (m1 m2 : amap vsymbol vsymbol)
  (Halpha1: alpha_equiv_t m1 m2 tm1 tm2)
  (Halpha2: alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t1 t2)
  (Hbnd1: ~ In x (tm_bnd t1)) (Hbnd2: ~ In y (tm_bnd t2))
  (Hdisj1: aset_disj (list_to_aset (tm_bnd t1)) (tm_fv tm1))
  (Hdisj2: aset_disj (list_to_aset (tm_bnd t2)) (tm_fv tm2)):
  alpha_equiv_t m1 m2 (sub_t tm1 x t1) (sub_t tm2 y t2).
Proof.
  apply alpha_equiv_t_sub; auto.
  eapply alpha_not_bnd_same_in_t; eauto.
Qed.

Corollary alpha_equiv_f_sub_not_bnd (tm1 tm2 : term) (x y : vsymbol) (f1 f2 : formula) (m1 m2 : amap vsymbol vsymbol)
  (Halpha1: alpha_equiv_t m1 m2 tm1 tm2)
  (Halpha2: alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2)
  (Hbnd1: ~ In x (fmla_bnd f1)) (Hbnd2: ~ In y (fmla_bnd f2))
  (Hdisj1: aset_disj (list_to_aset (fmla_bnd f1)) (tm_fv tm1))
  (Hdisj2: aset_disj (list_to_aset (fmla_bnd f2)) (tm_fv tm2)):
  alpha_equiv_f m1 m2 (sub_f tm1 x f1) (sub_f tm2 y f2).
Proof.
  apply alpha_equiv_f_sub; auto.
  eapply alpha_not_bnd_same_in_f; eauto.
Qed.



(*Cannot use [safe_sub_t] because if we don't alpha convert, dont have
  the tm_bnd condition (and don't have [same_in_t] necessarily*)
Lemma safe_sub_t_alpha m1 m2 v1 v2 t1 t2 t3 t4
  (Halpha1: alpha_equiv_t m1 m2 t1 t2)
  (Halpha2: alpha_equiv_t (amap_set m1 v1 v2) (amap_set m2 v2 v1) t3 t4):
  alpha_equiv_t m1 m2 (safe_sub_t' t1 v1 t3) (safe_sub_t' t2 v2 t4).
Proof.
  unfold safe_sub_t'.
  (*Why we needed the previous: v1 in fv of t3 iff v2 in fv of t4*)
  assert (Hfvs: aset_mem v1 (tm_fv t3) <-> aset_mem v2 (tm_fv t4)). {
    eapply alpha_equiv_t_map_fv_iff; eauto.
    rewrite alpha_equiv_var_iff. rewrite !amap_set_lookup_same. auto.
  }
  (*Annoyingly, have to destruct by cases*)
  destruct (aset_mem_dec v1 (tm_fv t3)) as [Hv1 | Hv1]; 
  destruct (aset_mem_dec v2 (tm_fv t4)) as [Hv2 | Hv2]; [| tauto | tauto |].
  2: { (*In this case, can remove these from the map because free vars not present*) 
    rewrite alpha_equiv_t_extra_var in Halpha2; auto. }
  set (t3':=(a_convert_t t3 (aset_union (tm_fv t1) (tm_fv t3)))).
  set (t4':=(a_convert_t t4 (aset_union (tm_fv t2) (tm_fv t4)))).
  assert (Ht3: a_equiv_t t3 t3') by apply a_convert_t_equiv.
  assert (Ht4: a_equiv_t t4 t4') by apply a_convert_t_equiv.
  assert (Ht34: alpha_equiv_t (amap_set m1 v1 v2) (amap_set m2 v2 v1) t3' t4'). {
    pose proof (alpha_equiv_t_trans t3' t3 t4' amap_empty amap_empty (amap_set m1 v1 v2) (amap_set m2 v2 v1)) as Htrans.
    forward Htrans.
    { rewrite alpha_equiv_t_sym; auto. }
    forward Htrans.
    { pose proof (alpha_equiv_t_trans t3 t4 t4' (amap_set m1 v1 v2) (amap_set m2 v2 v1) amap_empty amap_empty Halpha2 Ht4) 
      as Htrans1.
      rewrite alpha_comp_empty_r, alpha_comp_empty_l in Htrans1. auto.
    }
    rewrite alpha_comp_empty_r, alpha_comp_empty_l in Htrans. auto.
  }
  (*Prove disj*)
  assert (Hdisj1: aset_disj (list_to_aset (tm_bnd t3')) (tm_fv t1)).
  { unfold t3'. clear. rewrite aset_disj_equiv. intros x [Hx1 Hx2].
    apply (a_convert_t_bnd t3 (aset_union (tm_fv t1) (tm_fv t3)) x); auto; simpl_set; auto. }
  assert (Hdisj2: aset_disj (list_to_aset (tm_bnd t4')) (tm_fv t2)).
  { unfold t4'. clear. rewrite aset_disj_equiv. intros x [Hx1 Hx2].
    apply (a_convert_t_bnd t4 (aset_union (tm_fv t2) (tm_fv t4)) x); auto; simpl_set; auto. }
  (*Now use previous*)
  apply alpha_equiv_t_sub_not_bnd; auto.
  - intros Hinv. apply a_convert_t_bnd in Hinv; auto. simpl_set; auto.
  - intros Hinv. apply a_convert_t_bnd in Hinv; auto. simpl_set; auto.
Qed.

Lemma safe_sub_f_alpha m1 m2 v1 v2 t1 t2 f3 f4
  (Halpha1: alpha_equiv_t m1 m2 t1 t2)
  (Halpha2: alpha_equiv_f (amap_set m1 v1 v2) (amap_set m2 v2 v1) f3 f4):
  alpha_equiv_f m1 m2 (safe_sub_f' t1 v1 f3) (safe_sub_f' t2 v2 f4).
Proof.
  unfold safe_sub_f'.
  assert (Hfvs: aset_mem v1 (fmla_fv f3) <-> aset_mem v2 (fmla_fv f4)). {
    eapply alpha_equiv_f_map_fv_iff; eauto.
    rewrite alpha_equiv_var_iff. rewrite !amap_set_lookup_same. auto.
  }
  (*Annoyingly, have to destruct by cases*)
  destruct (aset_mem_dec v1 (fmla_fv f3)) as [Hv1 | Hv1]; 
  destruct (aset_mem_dec v2 (fmla_fv f4)) as [Hv2 | Hv2]; [| tauto | tauto |].
  2: { (*In this case, can remove these from the map because free vars not present*) 
    rewrite alpha_equiv_f_extra_var in Halpha2; auto. }
  set (f3':=(a_convert_f f3 (aset_union (tm_fv t1) (fmla_fv f3)))).
  set (f4':=(a_convert_f f4 (aset_union (tm_fv t2) (fmla_fv f4)))).
  assert (Ht3: a_equiv_f f3 f3') by apply a_convert_f_equiv.
  assert (Ht4: a_equiv_f f4 f4') by apply a_convert_f_equiv.
  assert (Ht34: alpha_equiv_f (amap_set m1 v1 v2) (amap_set m2 v2 v1) f3' f4'). {
    pose proof (alpha_equiv_f_trans f3' f3 f4' amap_empty amap_empty (amap_set m1 v1 v2) (amap_set m2 v2 v1)) as Htrans.
    forward Htrans.
    { rewrite alpha_equiv_f_sym; auto. }
    forward Htrans.
    { pose proof (alpha_equiv_f_trans f3 f4 f4' (amap_set m1 v1 v2) (amap_set m2 v2 v1) amap_empty amap_empty Halpha2 Ht4) 
      as Htrans1.
      rewrite alpha_comp_empty_r, alpha_comp_empty_l in Htrans1. auto.
    }
    rewrite alpha_comp_empty_r, alpha_comp_empty_l in Htrans. auto.
  }
  (*Prove disj*)
  assert (Hdisj1: aset_disj (list_to_aset (fmla_bnd f3')) (tm_fv t1)).
  { unfold f3'. clear. rewrite aset_disj_equiv. intros x [Hx1 Hx2].
    apply (a_convert_f_bnd f3 (aset_union (tm_fv t1) (fmla_fv f3)) x); auto; simpl_set; auto. }
  assert (Hdisj2: aset_disj (list_to_aset (fmla_bnd f4')) (tm_fv t2)).
  { unfold f4'. clear. rewrite aset_disj_equiv. intros x [Hx1 Hx2].
    apply (a_convert_f_bnd f4 (aset_union (tm_fv t2) (fmla_fv f4)) x); auto; simpl_set; auto. }
  (*Now use previous*)
  apply alpha_equiv_f_sub_not_bnd; auto.
  - intros Hinv. apply a_convert_f_bnd in Hinv; auto. simpl_set; auto.
  - intros Hinv. apply a_convert_f_bnd in Hinv; auto. simpl_set; auto.
Qed.


Lemma elim_let_alpha_equiv b1 b2 t1 f1:
  (forall m1 m2 t2 (Halpha: alpha_equiv_t m1 m2 t1 t2), 
    alpha_equiv_t m1 m2 (elim_let_t b1 b2 t1) (elim_let_t b1 b2 t2)) /\
  (forall m1 m2 f2 (Halpha: alpha_equiv_f m1 m2 f1 f2), 
    alpha_equiv_f m1 m2 (elim_let_f b1 b2 f1) (elim_let_f b1 b2 f2)).
Proof.
  revert t1 f1; apply term_formula_ind; simpl.
  - intros c _ _ t2 Halpha. destruct t2; try discriminate. simpl. auto.
  - intros v m1 m2 t2 Halpha. destruct t2; try discriminate. simpl. auto.
  - (*Tfun*)
    intros f1 tys1 tms1 IH m1 m2 t2 Halpha. destruct t2 as [| | f2 tys2 tms2 | | | | ]; try discriminate.
    simpl. destruct (funsym_eq_dec f1 f2); subst; [|discriminate]; simpl in Halpha. simpl.
    rewrite !length_map. destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate]; simpl in *.
    destruct (list_eq_dec _ tys1 tys2); [|discriminate]; subst. simpl in *.
    rewrite !all2_map.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true.
    intros [Halpha Hall] Hlentms. inversion IH as [| ? ? IH1 IH2]; subst.
    split; auto.
  - (*Tlet - interesting case*)
    intros tm1 v1 tm2 IH1 IH2 m1 m2 t2 Halpha. destruct t2 as [| | | e1 v2 e3 | | | ]; try discriminate.
    destruct (vty_eq_dec (snd v1) (snd v2)) as [Htyeq|]; [|discriminate]; simpl in Halpha.
    rewrite andb_true in Halpha. destruct Halpha as [Halpha1 Halpha2].
    destruct b1; simpl; auto.
    2: { rewrite Htyeq. destruct (vty_eq_dec _ _); simpl; auto. rewrite andb_true; split; auto. }
    apply IH1 in Halpha1.
    apply IH2 in Halpha2.
    apply safe_sub_t_alpha; auto.
  - (*Tif*)
    intros f1 t1 t2 IH1 IH2 IH3 m1 m2 tm Halpha.
    destruct tm; try discriminate. simpl. rewrite !andb_true in Halpha |- *.
    destruct Halpha as [[Ha1 Ha2] Ha3]. split_all; auto.
  - (*Tmatch*)
    intros tm1 ty1 ps1 IHtm IHps m1 m2 t2 Halpha.
    destruct t2 as [| | | | | tm2 tys2 ps2 |]; try discriminate. simpl in *.
    rewrite !length_map.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Halphat Hlenps] Htys] Hall].
    rewrite Hlenps, Htys, !andb_true_r.
    rewrite IHtm; auto. simpl. clear IHtm Halphat Htys tm1 tm2 ty1 tys2.
    apply Nat.eqb_eq in Hlenps.
    generalize dependent ps2. 
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; simpl; try discriminate; auto.
    intros Hlenps. rewrite !all2_cons. simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite andb_true. intros [Halphat Hall].
    inversion IHps as [|? ? IH1 IH2]; subst; clear IHps. specialize (IHps1 IH2); clear IH2.
    rewrite IHps1; auto. clear IHps1 Hall. rewrite andb_true_r. auto.
  - (*Teps*)
    intros f1 v1 IH m1 m2 t2 Halpha. destruct t2; try discriminate. simpl.
    rewrite andb_true in Halpha |- *. destruct_all; split; auto.
  - (*Fpred*)
    intros p1 tys1 tms1 IH m1 m2 t2 Halpha. destruct t2 as [p2 tys2 tms2 | | | | | | | | | ]; try discriminate.
    simpl. destruct (predsym_eq_dec p1 p2); subst; [|discriminate]; simpl in Halpha. simpl.
    rewrite !length_map. destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate]; simpl in *.
    destruct (list_eq_dec _ tys1 tys2); [|discriminate]; subst. simpl in *.
    rewrite !all2_map.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true.
    intros [Halpha Hall] Hlentms. inversion IH as [| ? ? IH1 IH2]; subst.
    split; auto.
  - (*Fquant*)
    intros q1 v1 f1 IH m1 m2 t2 Halpha. destruct t2; try discriminate. simpl.
    rewrite andb_true in Halpha |- *. destruct_all; split; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2 m1 m2 f2 Halpha. destruct f2; try discriminate. simpl.
    bool_hyps. bool_to_prop. split_all; auto; [apply IH1 | apply IH2]; auto.
  - (*Fpred*) intros b t1 t2 IH1 IH2 m1 m2 f2 Halpha. destruct f2; try discriminate. simpl.
    bool_hyps. bool_to_prop. split_all; auto; [apply IH1 | apply IH2]; auto.
  - (*Fnot*) intros f IH m1 m2 f2 Halpha. destruct f2; try discriminate; simpl; auto.
  - (*Ftrue*) intros _ _ f2 Halpha; destruct f2; try discriminate; auto.
  - (*Ffalse*) intros _ _ f2 Halpha; destruct f2; try discriminate; auto.
  - (*Flet*) intros tm1 v1 tm2 IH1 IH2 m1 m2 t2 Halpha. destruct t2 as [| | | | | | | e1 v2 e3 | | ]; try discriminate.
    destruct (vty_eq_dec (snd v1) (snd v2)) as [Htyeq|]; [|discriminate]; simpl in Halpha.
    rewrite andb_true in Halpha. destruct Halpha as [Halpha1 Halpha2].
    destruct b2; simpl; auto.
    2: { rewrite Htyeq. destruct (vty_eq_dec _ _); simpl; auto. rewrite andb_true; split; auto. }
    apply IH1 in Halpha1.
    apply IH2 in Halpha2.
    apply safe_sub_f_alpha; auto.
  - (*Fif*)
    intros f1 t1 t2 IH1 IH2 IH3 m1 m2 tm Halpha.
    destruct tm; try discriminate. simpl. rewrite !andb_true in Halpha |- *.
    destruct Halpha as [[Ha1 Ha2] Ha3]. split_all; auto.
  - (*Fmatch*)
    intros tm1 ty1 ps1 IHtm IHps m1 m2 t2 Halpha.
    destruct t2 as [| | | | | | | | | tm2 tys2 ps2]; try discriminate. simpl in *.
    rewrite !length_map.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Halphat Hlenps] Htys] Hall].
    rewrite Hlenps, Htys, !andb_true_r.
    rewrite IHtm; auto. simpl. clear IHtm Halphat Htys tm1 tm2 ty1 tys2.
    apply Nat.eqb_eq in Hlenps.
    generalize dependent ps2. 
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; simpl; try discriminate; auto.
    intros Hlenps. rewrite !all2_cons. simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite andb_true. intros [Halphat Hall].
    inversion IHps as [|? ? IH1 IH2]; subst; clear IHps. specialize (IHps1 IH2); clear IH2.
    rewrite IHps1; auto. clear IHps1 Hall. rewrite andb_true_r. auto.
Qed.

(*Only need f version*)

Definition elim_let_f_alpha_equiv b1 b2 f1 f2 m1 m2 (Halpha: alpha_equiv_f m1 m2 f1 f2):
  alpha_equiv_f m1 m2 (elim_let_f b1 b2 f1) (elim_let_f b1 b2 f2) :=
  proj_fmla (elim_let_alpha_equiv b1 b2) f1 m1 m2 f2 Halpha.

(*And corollary for empty maps*)
Definition elim_let_f_a_equiv b1 b2 f1 f2 (Halpha: a_equiv_f f1 f2):
  a_equiv_f (elim_let_f b1 b2 f1) (elim_let_f b1 b2 f2) :=
  elim_let_f_alpha_equiv b1 b2 f1 f2 amap_empty amap_empty Halpha.

Lemma eval_task_ctx_change_tdecl tsk d d1 y x
  (Hhd : td_node_of (task_decl tsk) = Decl d1)
  (Hd1 : d_node d1 = Dprop y):
  (eval_task_ctx
     (change_tdecl_c tsk
        (change_tdecl_node (task_decl tsk) (Decl (change_decl_node d (Dprop x)))))) =
  eval_task_ctx tsk.
Proof.
  unfold eval_task_ctx. simpl.
  destruct tsk; simpl in *. destruct task_decl; simpl in *. 
  subst; simpl. unfold eval_decl. rewrite Hd1. simpl.
  destruct y as [[k1 pr1] f1]; simpl. destruct x as [[k2 pr2] f2]; simpl.
  destruct k1; destruct k2; auto.
Qed.

Lemma eval_task_hyps_change_tdecl tsk d d1 pr1 pr2 f1 f2
  (Hhd : td_node_of (task_decl tsk) = Decl d1)
  (Hd1 : d_node d1 = Dprop (Pgoal, pr1, f1)):
  (eval_task_hyps
     (change_tdecl_c tsk
        (change_tdecl_node (task_decl tsk) (Decl (change_decl_node d (Dprop (Pgoal, pr2, f2))))))) =
  eval_task_hyps tsk.
Proof.
  unfold eval_task_hyps. simpl.
  destruct tsk; simpl in *. destruct task_decl; simpl in *. 
  subst; simpl. unfold eval_decl. rewrite Hd1. reflexivity.
Qed.

Lemma eval_task_goal_change_tdecl tsk d d1 pr2 f2
  (Hhd : td_node_of (task_decl tsk) = Decl d1)
  (*(Hd1 : d_node d1 = Dprop (Pgoal, pr1, f1)) *):
  (eval_task_goal
     (change_tdecl_c tsk
        (change_tdecl_node (task_decl tsk) (Decl (change_decl_node d (Dprop (Pgoal, pr2, f2))))))) =
   eval_fmla f2.
Proof.
  unfold eval_task_goal. simpl.  destruct tsk; simpl in *. destruct task_decl; simpl in *.
  subst; simpl. unfold eval_tdecl_goal. simpl.
  unfold eval_decl_goal. simpl.
  destruct (eval_fmla f2); auto.
Qed.

(*TODO: move these*)

(*Inversion Lemmas for eval*)
Section EvalInv.

(*Const*)

Lemma eval_const_tm {f1 g1 c} 
  (Hn: t_node_of f1 = TermDefs.Tconst c)
  (Heval: eval_term f1 = Some g1):
  exists c1, g1 = Tconst c1 /\ eval_const c = Some c1.
Proof.
  destruct f1 as [n ? ? ? ]; destruct n; simpl in *; try discriminate.
  apply option_map_some in Heval. inversion Hn; subst. 
  destruct Heval as [c1 [Heval Hg1]]; subst. eauto.
Qed.

Lemma eval_const_fmla {f1 g1 c} 
  (Hn: t_node_of f1 = TermDefs.Tconst c)
  (Heval: eval_fmla f1 = Some g1):
  False.
Proof.
  destruct f1 as [n ? ? ? ]; destruct n; simpl in *; discriminate.
Qed.

(*var*)
Lemma eval_var_tm {f1 g1 v} 
  (Hn: t_node_of f1 = TermDefs.Tvar v)
  (Heval: eval_term f1 = Some g1):
  g1 = Tvar (eval_vsymbol v).
Proof.
  destruct f1 as [n ? ? ? ]; destruct n; simpl in *; try discriminate.
  inversion Heval; subst; auto. inversion Hn; subst; auto.
Qed.

Lemma eval_var_fmla {f1 g1 v} 
  (Hn: t_node_of f1 = TermDefs.Tvar v)
  (Heval: eval_fmla f1 = Some g1):
  False.
Proof.
  destruct f1 as [n ? ? ? ]; destruct n; simpl in *; discriminate.
Qed.

(*if*)

Lemma eval_if_tm {f1 g1 t1 t2 t3} 
  (Hn: t_node_of f1 = TermDefs.Tif t1 t2 t3)
  (Heval: eval_term f1 = Some g1):
  exists e1 e2 e3, g1 = Tif e1 e2 e3 /\ eval_fmla t1 = Some e1 /\ eval_term t2 = Some e2 /\
    eval_term t3 = Some e3.
Proof.
  destruct f1 as [n ? ? ? ]; destruct n; simpl in *; try discriminate. 
  inversion Hn; subst; clear Hn.
  apply option_bind_some in Heval. destruct Heval as [e1 [He1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e2 [He2 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e3 [He3 Hbind]].
  inversion Hbind; subst. eauto 10.
Qed.

Lemma eval_if_fmla {f1 g1 t1 t2 t3} 
  (Hn: t_node_of f1 = TermDefs.Tif t1 t2 t3)
  (Heval: eval_fmla f1 = Some g1):
  exists e1 e2 e3, g1 = Fif e1 e2 e3 /\ eval_fmla t1 = Some e1 /\ eval_fmla t2 = Some e2 /\
    eval_fmla t3 = Some e3.
Proof.
  destruct f1 as [n ? ? ? ]; destruct n; simpl in *; try discriminate. 
  inversion Hn; subst; clear Hn.
  apply option_bind_some in Heval. destruct Heval as [e1 [He1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e2 [He2 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e3 [He3 Hbind]].
  inversion Hbind; subst. eauto 10.
Qed.



(*app - trickier: can become Tfun, Fpred, or Feq*)

Lemma eval_app_tm {f1 g1 l ts}
  (Hn: t_node_of f1 = TermDefs.Tapp l ts)
  (Heval: eval_term f1 = Some g1):
  exists l1 tys' tys1 ts1,
    g1 = Tfun l1 tys1 ts1 /\ eval_funsym l = Some l1 /\
      fold_list_option (map term_type ts) = Some tys' /\
      funpred_ty_list l1 tys' = Some tys1 /\
      fold_list_option (map eval_term ts) = Some ts1.
Proof.
  destruct f1 as [n ? ? ? ]; destruct n; simpl in *; try discriminate.
  inversion Hn; subst; clear Hn.
  apply option_bind_some in Heval. destruct Heval as [l1 [Hl1 Hbind]]. exists l1.
  apply option_bind_some in Hbind. destruct Hbind as [ts1 [Hts1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [tys' [Htsys' Hbind]].
  apply option_map_some in Hbind. destruct Hbind as [tys1 [Htys1 Hg1]]; subst; eauto 10.
Qed.

Lemma eval_app_fmla {f1 g1 l ts}
  (Hn: t_node_of f1 = TermDefs.Tapp l ts)
  (Heval: eval_fmla f1 = Some g1):
  (l = ps_equ /\ exists t1 t2 t3 t4 ty1, ts = [t1 ; t2] /\ g1 = Feq ty1 t3 t4 /\
    eval_term t1 = Some t3 /\ eval_term t2 = Some t4 /\ term_type t1 = Some ty1) \/
  l <> ps_equ /\
  exists l1 tys' tys1 ts1,
    g1 = Fpred l1 tys1 ts1 /\ eval_predsym l = Some l1 /\
      fold_list_option (map term_type ts) = Some tys' /\
      funpred_ty_list l1 tys' = Some tys1 /\
      fold_list_option (map eval_term ts) = Some ts1.
Proof.
  destruct f1 as [n ? ? ? ]; destruct n; simpl in *; try discriminate.
  inversion Hn; subst; clear Hn.
  destruct (lsymbol_eqb l ps_equ) eqn : Heq.
  - assert (l = ps_equ). apply lsymbol_eqb_eq; auto. subst.
    left. destruct ts as [| t1 [| t2 [| ? ?]]]; try discriminate.
    split; auto. exists t1. exists t2. 
    apply option_bind_some in Heval. destruct Heval as [t3 [Ht3 Hbind]].
    apply option_bind_some in Hbind. destruct Hbind as [t4 [Ht4 Hbind]].
    apply option_bind_some in Hbind. destruct Hbind as [ty1 [Hty1 Hbind]].
    inversion Hbind; subst. eauto 10.
  - assert (l <> ps_equ).
    { intro C; subst. assert (Ht: lsymbol_eqb ps_equ ps_equ) by (apply lsymbol_eqb_eq; auto).
      rewrite Ht in Heq; discriminate.
    }
    right. split; auto.
    apply option_bind_some in Heval. destruct Heval as [l1 [Hl1 Hbind]]. exists l1.
    apply option_bind_some in Hbind. destruct Hbind as [ts1 [Hts1 Hbind]].
    apply option_bind_some in Hbind. destruct Hbind as [tys' [Htsys' Hbind]].
    apply option_map_some in Hbind. destruct Hbind as [tys1 [Htys1 Hg1]]; subst; eauto 10.
Qed.


End EvalInv.

(*TODO: move*)

Local Open Scope Z_scope.

Section Pres.

(*In general, if the state is *)

(*Preservation of states (move)*)
Print idents_of_term_wf.

(*1. If the counter only increases, everything that was wf is still wf (for idents)*)
Lemma idents_of_term_wf_pres {A: Type} (tm: term_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 =>(fst s1 <= fst s2)%Z) ->
  errst_spec (idents_of_term_wf tm) o (fun _ _ s2 => idents_of_term_wf tm s2).
Proof.
  intros Hspec.
  eapply errst_spec_weaken with (P1:= fun s => True /\ idents_of_term_wf tm s)
   (Q1:=fun s1 _ s2 => fst s1 <= fst s2 /\ idents_of_term_wf tm s1); auto.
  - intros s1 _ s2 [Hle Hwf].
    (*separate lemma?*)
    unfold idents_of_term_wf in *. intros i Hi. specialize (Hwf _ Hi). lia.
  - apply errst_spec_and; auto.
    apply errst_spec_init.
Qed.

(*2. If the type hash counter only increases and the hash table only grows larger,
  then [term_hash_wf] is preserved
  NOTE: this is NOT true of weak hashtables, which Why3 uses for hashing. Reasoning
  about garbage collection would be much trickier *)

Definition hashset_subset {key} (hash: key -> CoqBigInt.t) (eqb: key -> key -> bool) (h1 h2: CoqHashtbl.hashset key)
 : Prop := forall (k: key) v, CoqHashtbl.find_opt_hashset hash eqb h1 k = Some v ->  
  CoqHashtbl.find_opt_hashset hash eqb h2 k = Some v.

(*TODO: write definition for these*)
Lemma term_hash_wf_pres {A: Type} (tm: term_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) ->
  errst_spec (term_hash_wf tm) o (fun _ _ s2 => term_hash_wf tm s2).
Proof.
  intros Hspec.
  eapply errst_spec_weaken with (P1:= fun s => True /\ term_hash_wf tm s)
   (Q1:=fun s1 _ s2 => (hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) 
    /\ term_hash_wf tm s1); auto.
  - intros s1 _ s2 [[Hle Hhash] Hwf].
    (*separate lemma?*)
    unfold term_hash_wf in *.
    unfold gen_hash_wf in *. destruct Hwf as [Hwf1 Hwf2]. split.
    + unfold all_in_hashtable in *. intros x Hinx. specialize (Hwf1 _ Hinx).
      apply Hhash; auto.
    + unfold all_idents_smaller in *. intros x Hinx. specialize (Hwf2 _ Hinx).
      lia.
  - apply errst_spec_and; auto.
    apply errst_spec_init.
Qed.

Lemma ty_hash_wf_pres {A: Type} (t: option ty_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) ->
  errst_spec (ty_hash_wf t) o (fun _ _ s2 => ty_hash_wf t s2).
Proof.
  intros Hspec.
  eapply errst_spec_weaken with (P1:= fun s => True /\ ty_hash_wf t s)
   (Q1:=fun s1 _ s2 => (hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) 
    /\ ty_hash_wf t s1); auto.
  - intros s1 _ s2 [[Hle Hhash] Hwf].
    (*separate lemma?*)
    unfold ty_hash_wf, gen_hash_wf in *. destruct Hwf as [Hwf1 Hwf2]. split.
    + unfold all_in_hashtable in *. intros x Hinx. specialize (Hwf1 _ Hinx).
      apply Hhash; auto.
    + unfold all_idents_smaller in *. intros x Hinx. specialize (Hwf2 _ Hinx).
      lia.
  - apply errst_spec_and; auto.
    apply errst_spec_init.
Qed.

Definition term_wf_pres_cond (s1 s2: full_st) :=
  (fst s1 <= fst s2)%Z /\ 
  (hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
  hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))).

Lemma term_st_wf_pres {A: Type} (tm: term_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => term_wf_pres_cond s1 s2) ->
  errst_spec (term_st_wf tm) o (fun _ _ s2 => term_st_wf tm s2).
Proof.
  unfold term_st_wf, term_wf_pres_cond. intros Hspec.
  apply errst_spec_and.
  - apply idents_of_term_wf_pres. revert Hspec. apply errst_spec_weaken; auto.
    intros; destruct_all; auto.
  - apply term_hash_wf_pres. revert Hspec. apply errst_spec_weaken; auto.
    intros; destruct_all; split; auto.
Qed.

Lemma ty_st_wf_pres {A: Type} (t: option ty_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => term_wf_pres_cond s1 s2) ->
  errst_spec (ty_st_wf t) o (fun _ _ s2 => ty_st_wf t s2).
Proof.
  unfold ty_st_wf, term_wf_pres_cond. intros Hspec.
  apply ty_hash_wf_pres. revert Hspec. apply errst_spec_weaken_post. intros; destruct_all; auto.
Qed.

Lemma term_wf_pres_cond_refl s: term_wf_pres_cond s s.
Proof.
  unfold term_wf_pres_cond. split_all; try lia.
  unfold hashset_subset; auto.
Qed.

Lemma term_wf_pres_cond_trans s1 s2 s3: term_wf_pres_cond s1 s2 -> term_wf_pres_cond s2 s3 ->
  term_wf_pres_cond s1 s3.
Proof.
  unfold term_wf_pres_cond. intros; destruct_all; split_all; try lia.
  unfold hashset_subset in *. auto.
Qed.


End Pres.

(*TODO: move*)
Lemma errst_spec_tup1 {St1 St2 A: Type} (P: St1 -> A -> St1 -> Prop) (Q: St2 -> A -> St2 -> Prop) (o: errState St1 A)
  (Q_refl: forall s x, Q s x s):
  errst_spec (fun _ => True) o P ->
  errst_spec (fun _ => True) (errst_tup1 o) (fun s1 x s2 => P (fst s1) x (fst s2) /\ Q (snd s1) x (snd s2)).
Proof.
  unfold errst_spec. intros Hspec [i1 i2] b _ Hb.
  simpl.
  destruct o; simpl in *. unfold run_errState in *; simpl in *.
  specialize (Hspec i1).
  destruct (runState unEitherT i1 ) as [x1 x2] eqn : Hrun; simpl in *; subst.
  split; auto.
Qed.

Require Import StateHoareMonad.

(*Preserved through [t_open_bound]*)

Check prove_st_spec_bnd.
(*P1=P2, ignore ending - just give postcondition of A and B*)
(*TODO: move*)
Lemma prove_st_spec_bnd_invar {St A B: Type}
  (Q1: St -> St -> Prop) (Q2 Q3: St -> St -> Prop) (a: st St A) (b: A -> st St B):
  st_spec (fun _ => True) a (fun s1 _ s2 => Q1 s1 s2) ->
  (forall x, st_spec (fun _ => True) (b x) (fun s1 _ s2 => Q2 s1 s2)) ->
  (forall x1 x2 x3, Q1 x1 x2 -> Q2 x2 x3 -> Q3 x1 x3) ->
  st_spec (fun _ => True) (x <- a ;; b x)%state (fun s1 _ s2 => Q3 s1 s2).
Proof.
  intros Ha Hb Htrans. eapply prove_st_spec_bnd; [apply Ha | apply Hb | |]; simpl; auto.
  intros; eauto.
Qed.

(*Useful in multiple places*)
Lemma fresh_vsymbol_lt v:
  st_spec (fun _ : Z => True) (fresh_vsymbol v) (fun (s1 : Z) (_ : TermDefs.vsymbol) (s2 : Z) => s1 < s2).
Proof.
  unfold fresh_vsymbol, create_vsymbol.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
  2: { intros x. apply prove_st_spec_ret. intros; lia. }
  (*Prove [id_register]*)
  unfold id_register.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
  - (*incr*) apply IdCtr.st_spec_incr. intros.
    (*TODO: bad*) Transparent CoqBigInt.succ. unfold CoqBigInt.succ. lia. Opaque CoqBigInt.succ.
  - (*rest of function*) intros _.
    apply prove_st_spec_bnd_invar with (Q1:=fun i j => i <= j)(Q2:=fun i j => i <= j); [| | intros; lia].
    + (*get*) apply IdCtr.st_spec_get. intros; lia.
    + intros x. apply prove_st_spec_ret. intros; lia.
Qed.

Lemma vs_rename_lt m v:
  st_spec (fun _ : Z => True) (vs_rename m v)
  (fun (s1 : Z) (_ : Mvs.t term_c * TermDefs.vsymbol) (s2 : Z) => s1 < s2).
Proof.
  unfold vs_rename.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
  2: { intros x. apply prove_st_spec_ret. intros; lia. }
  (*Prove [fresh_vsymbol]*)
  apply fresh_vsymbol_lt.
Qed.


(*NOTE: it is important that it increases the state*)
Lemma t_open_bound_lt b:
  st_spec (fun _ : Z => True) (t_open_bound b)
  (fun (s1 : Z) (_ : TermDefs.vsymbol * term_c) (s2 : Z) => (s1 < s2)%Z).
Proof.
  unfold t_open_bound.
  destruct b as [[v ?] t].
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
  2: { intros [m t1]. apply prove_st_spec_ret. intros; lia. }
  (*Prove [vs_rename]*)
  apply vs_rename_lt.
Qed.

Lemma t_open_bound_pres tb:
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
  (fun (s1 : full_st) (_ : TermDefs.vsymbol * term_c) (s2 : full_st) => term_wf_pres_cond s1 s2).
Proof.
  unfold term_wf_pres_cond.
  apply errst_spec_tup1 with (P:=fun s1 _ s2 => (s1 <= s2)%Z)(Q:=fun s1 _ s2 =>
    ((hashcons_ctr (fst (fst (fst s1))) <= hashcons_ctr (fst (fst (fst s2))))%Z /\
   hashset_subset ty_hash ty_eqb (hashcons_hash (fst (fst (fst s1)))) (hashcons_hash (fst (fst (fst s2)))))).
  - intros s _. split; try lia. unfold hashset_subset. auto.
  - (*separate lemma?*)
    apply errst_spec_st. eapply st_spec_weaken_post. 2: apply t_open_bound_lt.
    simpl. intros; lia.
Qed.

(*And for [t_open_branch]*)

(*NOTE: 2 possible specs here: if the pattern has at least one variable, we get <.
  In all cases, get <=*)
Lemma t_open_branch_lt b:
  st_spec (fun _ : Z => True) (t_open_branch b)
  (fun (s1 : Z) (_ : pattern_c * term_c) (s2 : Z) =>
    if null (Svs.elements (pat_vars_of (fst (fst b)))) then (s1 <= s2) else (s1 < s2)%Z).
Proof.
  unfold t_open_branch.
  destruct b as [[p ?] t]. simpl.
  apply prove_st_spec_bnd_invar with 
  (Q1:=fun i j => if null (Svs.elements (pat_vars_of p)) then i <= j else i < j)
  (Q2:=fun i j => i <= j).
  3: { destruct (null (Svs.elements (pat_vars_of p))); auto; intros; lia. }
  2: { intros [m t1]. apply prove_st_spec_ret. intros; lia. }
  (*Prove [pat_rename]*)
  unfold pat_rename.
  apply prove_st_spec_bnd_invar with 
  (Q1:=fun i j => if null (Svs.elements (pat_vars_of p)) then i <= j else i < j)
  (Q2:=fun i j => i <= j).
  3: { destruct (null (Svs.elements (pat_vars_of p))); auto; intros; lia. }
  2: { intros [m t1]. apply prove_st_spec_ret. intros; lia. }
  (*Prove [add_vars]*)
  induction (Svs.elements (pat_vars_of p)) as [| h tl IH]; simpl; auto.
  - apply prove_st_spec_ret. intros; lia.
  - (*bind with [fresh_vsymbol]*)
    apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
    + apply fresh_vsymbol_lt.
    + intros s1.
      (*Now either way get <= result*)
      apply prove_st_spec_bnd_invar with (Q1:=fun i j => i <= j)(Q2:=fun i j => i <= j); [| | intros; lia]; auto.
      * eapply st_spec_weaken_post. 2: apply IH. simpl. intros. destruct (null tl); lia.
      * intros. apply prove_st_spec_ret. intros; lia.
Qed.

Lemma t_open_branch_pres b:
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_branch b)))
  (fun (s1 : full_st) (_ : pattern_c * term_c) (s2 : full_st) => term_wf_pres_cond s1 s2).
Proof.
  unfold term_wf_pres_cond.
  apply errst_spec_tup1 with (P:=fun s1 _ s2 => (s1 <= s2)%Z)(Q:=fun s1 _ s2 =>
    ((hashcons_ctr (fst (fst (fst s1))) <= hashcons_ctr (fst (fst (fst s2))))%Z /\
   hashset_subset ty_hash ty_eqb (hashcons_hash (fst (fst (fst s1)))) (hashcons_hash (fst (fst (fst s2)))))).
  - intros s _. split; try lia. unfold hashset_subset. auto.
  - (*separate lemma?*)
    apply errst_spec_st. eapply st_spec_weaken_post. 2: apply t_open_branch_lt.
    simpl. intros; destruct (null _); lia.
Qed.

(*And [t_open_quant1]*)

Print term_quant.
Lemma t_open_quant1_lt tq:
  st_spec (fun _ : Z => True) (t_open_quant1 tq)
  (fun (s1 : Z) (_ : (list TermDefs.vsymbol * trigger * term_c)) (s2 : Z) => 
    if null (fst (fst (fst tq))) then s1 <= s2 else (s1 < s2)%Z).
Proof.
  unfold t_open_quant1.
  destruct tq as [[[vs ?] tr] t]. simpl.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => if null vs then i <= j else i < j)
  (Q2:=fun i j => i <= j).
  3: { destruct (null vs); intros; lia. }
  2: { intros [m t1]. apply prove_st_spec_ret. intros; lia. }
  (*Prove [vs_rename]*)
  unfold vs_rename.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => if null vs then i <= j else i < j)
  (Q2:=fun i j => i <= j).
  3: { destruct (null vs); intros; lia. }
  2: { intros x. apply prove_st_spec_ret. intros; lia. }
  (*[vl_rename_aux*)
  (*NOTE: this is really annoying to work with*)
  remember (st_ret (Mvs.empty, [])) as base.
  assert (Hbase: st_spec (fun _ => True) base (fun s1 _ s2 => s1 <= s2)).
  { rewrite Heqbase. apply prove_st_spec_ret. intros; lia. }
  clear Heqbase. generalize dependent base.
  induction vs as [| h tl IH]; simpl; auto.
  intros base Hbase.
  (*bind base*)
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i <= j)(Q2:=fun i j => i < j); [| | intros; lia]; auto.
  intros [m vls]. 
  (*bind rename*)
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia]; auto.
  + (*vs_rename*) apply vs_rename_lt.
  + intros [m1 v1]. eapply st_spec_weaken_post. 2: apply IH.
    * simpl. intros. destruct (null tl); lia.
    * apply prove_st_spec_ret. intros; lia.
Qed.

Lemma t_open_quant1_pres tq:
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_quant1 tq)))
  (fun (s1 : full_st) (_ : list TermDefs.vsymbol * trigger * term_c) (s2 : full_st) =>
   term_wf_pres_cond s1 s2).
Proof.
  unfold term_wf_pres_cond.
  apply errst_spec_tup1 with (P:=fun s1 _ s2 => (s1 <= s2)%Z)(Q:=fun s1 _ s2 =>
    ((hashcons_ctr (fst (fst (fst s1))) <= hashcons_ctr (fst (fst (fst s2))))%Z /\
   hashset_subset ty_hash ty_eqb (hashcons_hash (fst (fst (fst s1)))) (hashcons_hash (fst (fst (fst s2)))))).
  - intros s _. split; try lia. unfold hashset_subset. auto.
  - (*separate lemma?*)
    apply errst_spec_st. eapply st_spec_weaken_post. 2: apply t_open_quant1_lt.
    simpl. destruct (null _); intros; lia.
Qed.


(*TODO move*)
Lemma prove_errst_spec_bnd_invar {St A B: Type}
  (Q1: St -> St -> Prop) (Q2 Q3: St -> St -> Prop) (a: errState St A) (b: A -> errState St B):
  errst_spec (fun _ => True) a (fun s1 _ s2 => Q1 s1 s2) ->
  (forall x, errst_spec (fun _ => True) (b x) (fun s1 _ s2 => Q2 s1 s2)) ->
  (forall x1 x2 x3, Q1 x1 x2 -> Q2 x2 x3 -> Q3 x1 x3) ->
  errst_spec (fun _ => True) (x <- a ;; b x) (fun s1 _ s2 => Q3 s1 s2).
Proof.
  intros Ha Hb Htrans. eapply prove_errst_spec_bnd; [apply Ha | apply Hb | |]; simpl; auto.
  intros; eauto.
Qed.

(*dep version*)
Lemma prove_errst_spec_dep_bnd_invar {St A B: Type}
  (Q1: St -> St -> Prop) (Q2 Q3: St -> St -> Prop) (a: errState St A) 
  (b : forall (s : St) (b : A), fst (run_errState a s) = inr b -> errState St B):
  errst_spec (fun _ => True) a (fun s1 _ s2 => Q1 s1 s2) ->
  (forall s x Heq, errst_spec (fun _ => True) (b s x Heq) (fun s1 _ s2 => Q2 s1 s2)) ->
  (forall x1 x2 x3, Q1 x1 x2 -> Q2 x2 x3 -> Q3 x1 x3) ->
  errst_spec (fun _ => True) (errst_bind_dep' a b) (fun s1 _ s2 => Q3 s1 s2).
Proof.
  intros Ha Hb Htrans. eapply prove_errst_spec_dep_bnd; [apply Ha | apply Hb | |]; simpl; auto.
  intros; eauto.
Qed.

(*Loops are trickier. We prove 2 different rules: 1 for invariants that only depend on the states
  (and are transitive) e.g. well-formed conditions and 1 for propositions that do not
  depend on the initial state. Things gets much harder when the postcondtiion depends on all*)

(*A Hoare-like loop rule - give loop invariant - in pre and post*)
Lemma prove_errst_spec_list_invar {St A: Type} (I1: St -> Prop) (I2: St -> St -> Prop) 
  (*(P1: St -> Prop)*) (* (Q1: St -> A -> St -> Prop) (Q2: St -> list A -> St -> Prop) *)  (l: list (errState St A)):
  (*Loop invariant implied on beginning*)
  (*(forall s, P1 s -> I1 s) ->*)
  (*Loop invariant preserved through loop*)
  Forall (fun a => errst_spec I1 a (fun x _ y => I2 x y)) l ->
  (*Ending implies beginning again*)
  (forall s1 s2, I2 s1 s2 -> I1 s2) ->
  (*Reflexivity*)
  (forall s, I1 s -> I2 s s) ->
  (*Transitivity*)
  (forall s1 s2 s3, I2 s1 s2 -> I2 s2 s3 -> I2 s1 s3) ->
  (*Exiting implies postcondition*)
  (* (forall s1 x s2, I2 s1 x s2 -> Q1 s1 x s2) -> *)
  (*Then post holds for all list*)
  (*TODO: is this the right direction?*)
  (* (forall s1 l s2, Forall (fun y => Q1 s1 y s2) l -> Q2 s1 l s2 ) ->  *)
  errst_spec I1 (errst_list l) (fun s1 _ s2 => I2 s1 s2).
Proof.
  unfold errst_list. intros Hinvar Hi12 Hrefl Htrans.
  induction l as [| h t IH]; simpl; auto.
  - apply prove_errst_spec_ret. auto.
  - inversion Hinvar as [| ? ? Hinvar1 Hinvar2]; subst; clear Hinvar. specialize (IH Hinvar2).
    eapply prove_errst_spec_bnd with (Q1:=fun s1 _ s2 => I2 s1 s2) (Q2:=fun _ s1 _ s2 => I2 s1 s2)(P2:=fun _ => I1); eauto.
    intros x.
    (*use IH, but need another bind*)
    eapply prove_errst_spec_bnd with (Q2:=fun _ s1 _ s2 => I2 s1 s2) (P2:=fun _ => I1). 1: apply IH. all: simpl; eauto.
    intros y. apply prove_errst_spec_ret. auto.
Qed.

(*TODO: see what other version we need (not sure yet)*)

(*And a version for monotonic predicate that does not depend on state (e.g. *)

(**)
(* 
(*And a version for monotonic predicates that do not depend on the initial state*)
Lemma prove_errst_spec_list_mono {St A: Type} (I1: St -> Prop) (I2: A -> St -> Prop) 
  (*(P1: St -> Prop)*) (* (Q1: St -> A -> St -> Prop) (Q2: St -> list A -> St -> Prop) *)  (l: list (errState St A)):
  (*Loop invariant implied on beginning*)
  (*(forall s, P1 s -> I1 s) ->*)
  (*Loop invariant preserved through loop*)
  Forall (fun a => errst_spec I1 a (fun _ x y => I2 x y)) l ->
  (*Ending implies beginning again*)
  (forall x s2, I2 x s2 -> I1 s2) ->
  (*Monotonicity: TODO*)
  Forall (fun a => errst_spec I1 a (fun _ _ s2 => I1 s2)) l ->
  (*Reflexivity*)
  (forall s, I1 s -> I2 s s) ->
  (*Transitivity*)
  (forall s1 s2 s3, I2 s1 s2 -> I2 s2 s3 -> I2 s1 s3) -> 
  (*Exiting implies postcondition*)
  (* (forall s1 x s2, I2 s1 x s2 -> Q1 s1 x s2) -> *)
  (*Then post holds for all list*)
  (*TODO: is this the right direction?*)
  (* (forall s1 l s2, Forall (fun y => Q1 s1 y s2) l -> Q2 s1 l s2 ) ->  *)
  errst_spec I1 (errst_list l) (fun _ x s2 => Forall (fun y => I2 y s2) x).
Proof.
  unfold errst_list. intros Hinvar Hi12 Hmono.
  induction l as [| h t IH]; simpl; auto.
  - apply prove_errst_spec_ret. intros i Hi. constructor.
  - inversion Hinvar as [| ? ? Hinvar1 Hinvar2]; subst; clear Hinvar.
    inversion Hmono as [| ? ? Hm1 Hm2]; subst; clear Hmono. specialize (IH Hinvar2 Hm2).
    eapply prove_errst_spec_bnd with (Q1:=fun x s1 y s2 => I2 s1 y s2 /\ Forall (fun z => Q1 s1 z s2) y). (P2:=fun _ => I1); auto.
    (Q2:=fun x s1 y s2 =>  Forall (fun z : A => Q1 s1 z s2) y); auto.




 with



 (Q1:=fun x s1 y s2 => I2 s1 y s2 /\ Forall (fun z => Q1 s1 z s2) y). (P2:=fun _ => I1); auto.
    (Q2:=fun x s1 y s2 =>  Forall (fun z : A => Q1 s1 z s2) y); auto. *)




(*Now prove preservation for substitution*)
(*TODO: should reduce duplication by proving generically for traverse, prove for default cases*)

(*Useful for these lemmas*)
Ltac refl_case := intros; apply term_wf_pres_cond_refl.
Ltac trans_case := intros ? ? ?; apply term_wf_pres_cond_trans.

Lemma t_make_wf_pres t:
errst_spec (fun _ : full_st => True) (t_make_wf t)
  (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_wf_pres_cond s1 s2).
Proof.
 apply tm_traverse_ind with (P:= fun f1 t1 =>
  errst_spec (fun _ : full_st => True) t1
    (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_wf_pres_cond s1 s2)); clear; auto.
  - (*const*)
    intros. apply prove_errst_spec_ret. refl_case.
  - (*var*) intros. apply prove_errst_spec_ret. refl_case.
  - (*if*) intros t t1 t2 t3 Hnode IH1 IH2 IH3.
    (*By transitivity*)
    unfold tmap_if_default.
    repeat (
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| trans_case]; intros).
    apply errst_spec_err. refl_case.
  - (*let*)
    intros t t1 tb Hnode IH1 IH2.
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| trans_case ]. intros e1.
    (*Now dependent bind*)
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_bound*) apply t_open_bound_pres.
    + (*rest*) intros s2 y Hy. (*bind - first from IH*) 
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      auto; [eapply IH2; eauto | | trans_case]. intros.
      apply errst_spec_err. refl_case.
  - (*app*) intros t l ts Hnode IH.
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| | trans_case].
    2: { intros. unfold tmap_app_default. apply prove_errst_spec_ret. refl_case. }
    (*use loop invariant*)
    apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case]. 
    rewrite Forall_map. auto.
  - (*case*) intros t t1 tbs Hnode IH1 IH2.
    (*do 1st term*)
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); auto; [| trans_case].
    intros s1.
    (*last part*)
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| | trans_case].
    2: { intros. unfold tmap_match_default. apply errst_spec_err. refl_case. }
    (*loop invariant again*)
    apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
    rewrite Forall_map.
    (*This one is not quite trivial, need dependent bind*)
    revert IH2. clear. apply Forall_impl. intros b Hb.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case]; auto.
    + apply t_open_branch_pres.
    + intros s1 b1 Hb1.
      (*easy bind and return*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case].
      * eapply Hb; eauto.
      * intros. apply prove_errst_spec_ret. refl_case.
  - (*eps*)
    intros t b Hnode IH.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_bound*) apply t_open_bound_pres.
    + (*rest*) intros s2 y Hy. (*bind - first from IH*) 
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      auto; [eapply IH; eauto | | trans_case]. intros.
      apply errst_spec_err. refl_case.
  - (*quant*) intros t q tq Hnode IH.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_quant1 *) apply t_open_quant1_pres.
    + intros s1 [[vs1 tr1] t1] Hrun. simpl.
      specialize (IH _ _ Hrun). simpl in IH. destruct IH as [IH1 IHtr].
      (*first one*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case]; auto.
      intros t2. 
      (*Do final*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case].
      2: { intros x. apply errst_spec_err. refl_case. }
      (*now do list - doubly nested so trickier*)
      apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
      rewrite Forall_map.
      revert IHtr. clear. apply Forall_impl. intros l Hall.
      apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
      rewrite Forall_map. auto.
  - (*tbinop*) intros t b t1 t2 Hnode IH1 IH2.
    repeat (apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      [| | trans_case]; auto; intros).
    apply errst_spec_err. refl_case.
  - (*tnot*) intros t t1 Hnode IH. 
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case]; auto.
    intros; apply errst_spec_err. refl_case.
  - (*Ttrue*) intros. apply prove_errst_spec_ret. refl_case.
  - (*Tfalse*) intros. apply prove_errst_spec_ret. refl_case.
Qed.

(*TODO*)
(*stuff to add to thesis
  1. dependent bind (maybe) in st monad
  2. mention loop rule w invariants in hoare state monad*)

(*Therefore [t_subst_single1] preserves the invariant*)
Lemma t_subst_single1_pres v t1 t2:
errst_spec (fun _ : full_st => True) (t_subst_single1 v t1 t2)
  (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_wf_pres_cond s1 s2).
Proof.
  unfold t_subst_single1, t_subst1.
  apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
  [| | trans_case].
  1: { apply errst_spec_err. refl_case. }
  intros _.
  (*t_make_wf is interesting part*)
  apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
  [apply t_make_wf_pres | | trans_case].
  intros. apply prove_errst_spec_ret. refl_case.
Qed.

(*Now show invariant preservation through [elim_let]*)

(*TODO BAD: all cases but "let" are identical to wf lemma - should factor out*)
Lemma elim_let_rewrite_pres (f1: term_c):
  errst_spec 
    (fun (_: full_st) => True) 
      (elim_let_rewrite f1) 
    (fun (s1: full_st) _ (s2: full_st) => term_wf_pres_cond s1 s2).
Proof.
  apply tm_traverse_ind with (P:= fun f1 t1 =>
    errst_spec (fun _ : full_st => True) t1
      (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_wf_pres_cond s1 s2)); clear; auto.
  - (*const*) intros. apply prove_errst_spec_ret. refl_case.
  - (*var*) intros. apply prove_errst_spec_ret. refl_case.
  - (*if*) intros t t1 t2 t3 Hnode IH1 IH2 IH3.
    (*By transitivity*)
    unfold tmap_if_default.
    repeat (
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| trans_case]; intros).
    apply errst_spec_err. refl_case.
  - (*let*)
    intros t t1 tb Hnode IH1 IH2.
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| trans_case ]. intros e1.
    (*Now dependent bind*)
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_bound*) apply t_open_bound_pres.
    + (*substitution*) intros s2 y Hy. (*bind - first from IH*) 
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      auto; [eapply IH2; eauto | | trans_case].
      intros e2. apply t_subst_single1_pres.
  - (*app*) intros t l ts Hnode IH.
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| | trans_case].
    2: { intros. unfold tmap_app_default. apply prove_errst_spec_ret. refl_case. }
    (*use loop invariant*)
    apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case]. 
    rewrite Forall_map. auto.
  - (*case*) intros t t1 tbs Hnode IH1 IH2.
    (*do 1st term*)
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); auto; [| trans_case].
    intros s1.
    (*last part*)
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| | trans_case].
    2: { intros. unfold tmap_match_default. apply errst_spec_err. refl_case. }
    (*loop invariant again*)
    apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
    rewrite Forall_map.
    (*This one is not quite trivial, need dependent bind*)
    revert IH2. clear. apply Forall_impl. intros b Hb.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case]; auto.
    + apply t_open_branch_pres.
    + intros s1 b1 Hb1.
      (*easy bind and return*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case].
      * eapply Hb; eauto.
      * intros. apply prove_errst_spec_ret. refl_case.
  - (*eps*)
    intros t b Hnode IH.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_bound*) apply t_open_bound_pres.
    + (*rest*) intros s2 y Hy. (*bind - first from IH*) 
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      auto; [eapply IH; eauto | | trans_case]. intros.
      apply errst_spec_err. refl_case.
  - (*quant*) intros t q tq Hnode IH.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_quant1 *) apply t_open_quant1_pres.
    + intros s1 [[vs1 tr1] t1] Hrun. simpl.
      specialize (IH _ _ Hrun). simpl in IH. destruct IH as [IH1 IHtr].
      (*first one*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case]; auto.
      intros t2. 
      (*Do final*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case].
      2: { intros x. apply errst_spec_err. refl_case. }
      (*now do list - doubly nested so trickier*)
      apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
      rewrite Forall_map.
      revert IHtr. clear. apply Forall_impl. intros l Hall.
      apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
      rewrite Forall_map. auto.
  - (*tbinop*) intros t b t1 t2 Hnode IH1 IH2.
    repeat (apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      [| | trans_case]; auto; intros).
    apply errst_spec_err. refl_case.
  - (*tnot*) intros t t1 Hnode IH. 
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case]; auto.
    intros; apply errst_spec_err. refl_case.
  - (*Ttrue*) intros. apply prove_errst_spec_ret. refl_case.
  - (*Tfalse*) intros. apply prove_errst_spec_ret. refl_case.
Qed.
      


(*spec for other: counter increases and hash table only grows larger - NOTE
  that this is not true of weak hashtables*)



(*Any term that was already wf is still wf*)
Lemma elim_let_rewrite_wf (t: term_c) (f1: term_c):
  errst_spec (term_st_wf t) (elim_let_rewrite f1) (fun _ _ s2 =>term_st_wf t s2).
Proof.
  apply term_st_wf_pres.
  apply elim_let_rewrite_pres.
Qed.

(*same for ty*)
Lemma elim_let_rewrite_ty_wf (t: option ty_c) (f1: term_c):
  errst_spec (ty_st_wf t) (elim_let_rewrite f1) (fun _ _ s2 =>ty_st_wf t s2).
Proof.
  apply ty_st_wf_pres.
  apply elim_let_rewrite_pres.
Qed.

(*I believe for induction purposes I need both the term and formula result*)

(*TODO: move*)

Ltac destruct_term_node t:=
  let n := fresh "n" in
  destruct t as [n ? ? ?]; destruct n; try discriminate; simpl in *; subst; simpl in *.

Lemma idents_of_term_eq t1 t2 (Hn: t_node_of t1 = t_node_of t2):
  idents_of_term t1 = idents_of_term t2.
Proof.
  destruct_term_node t1; destruct_term_node t2; auto; inversion Hn; subst; auto.
Qed.

(*Need type wf also - TODO: move*)


(*Decompose wf*)
Lemma term_st_wf_if {t t1 t2 t3} (Ht: t_node_of t = TermDefs.Tif t1 t2 t3):
  forall s,
  term_st_wf t s <-> term_st_wf t1 s /\ term_st_wf t2 s /\ term_st_wf t3 s /\  ty_st_wf (t_ty_of t) s.
Proof.
  intros s.
  unfold term_st_wf, ty_st_wf.
  (*Easier to separate - can we generalize?*)
  assert (Hidents: idents_of_term_wf t s <-> idents_of_term_wf t1 s /\ idents_of_term_wf t2 s /\
    idents_of_term_wf t3 s).
  {
    destruct_term_node t. inversion Ht; subst. unfold idents_of_term_wf; simpl.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros Hin. split_all; intros i Hini; apply Hin; auto.
    - intros [Hin1 [Hin2 Hin3]] i Hini. destruct_all; eauto.
  }
  assert (Hhash: term_hash_wf t s <-> term_hash_wf t1 s /\ term_hash_wf t2 s /\ term_hash_wf t3 s /\ ty_hash_wf (t_ty_of t) s).
  {
    unfold term_hash_wf, ty_hash_wf, gen_hash_wf. destruct_term_node t; inversion Ht; subst; simpl.
    rewrite !map_app, !concat_app. unfold all_in_hashtable, all_idents_smaller.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros [Hi1 Hi2]. split_all; eauto.
    - intros; destruct_all; split; intros; destruct_all; eauto.
  }
  rewrite Hidents, Hhash.
  split; intros; destruct_all; split_all; auto.
Qed.

(*TODO: move*)

Lemma errst_spec_err' {A B : Type} (P : A -> Prop) (Q : A -> B -> A -> Prop) c:
  (forall (i : A) (x : B), c = inr x -> P i -> Q i x i) ->
  errst_spec P (errst_lift2 c) Q.
Proof.
  intros Hc. destruct c.
  - eapply errst_spec_err1; eauto.
  - (*need stronger lemma than [errst_spec_err2]*)
    unfold errst_spec, errst_lift2. simpl. auto.
Qed.

Lemma err_bnd_inr {A B: Type} (f: A -> errorM B) (x: errorM A) y:
  err_bnd f x = inr y ->
  exists z, x = inr z /\ f z = inr y.
Proof.
  unfold err_bnd. destruct x; simpl; try discriminate.
  intros Hf. eauto.
Qed.

Lemma fmla_related_fif t1 t2 t3 e1 e2 e3:
  fmla_related t1 e1 ->
  fmla_related t2 e2 ->
  fmla_related t3 e3 ->
  fmla_related (t_if1 t1 t2 t3) (Fif e1 e2 e3).
Proof.
  intros Hrel1 Hrel2 Hrel3.
  unfold fmla_related in *.
  simpl. destruct Hrel1 as [f1 [He1 Ha1]].
  destruct Hrel2 as [f2 [He2 Ha2]].
  destruct Hrel3 as [f3 [He3 Ha3]].
  exists (Fif f1 f2 f3). rewrite He1, He2, He3. simpl.
  split; auto.
  (*TODO: prove separately*)
  unfold a_equiv_f. simpl.
  bool_to_prop; split_all; auto.
Qed.

Check prove_errst_spec_bnd_nondep.

(*A version where *)
(*Version where intermediate assertion does not depend on initial state*)
Lemma prove_errst_spec_bnd_nondep' {St A B: Type} (P1 : St -> Prop)
  Q1 Q3 a (b: A -> errState St B):
  (*Hmm, what if Q1 does not use initial state?*)
  (errst_spec P1 a (fun _ => Q1)) ->
  (forall x, errst_spec (Q1 x) (b x) (fun _ => Q3)) ->
  (*Weaken rest*)
  (* (forall s2 s3 x y, Q1 x s2 -> Q3 y s3) -> *)
  errst_spec P1 (errst_bind b a) (fun _ => Q3).
Proof.
  intros Ha Hb. eapply prove_errst_spec_bnd with (Q2:=fun _ _ => Q3); eauto.
Qed.

(*TODO: move*)
Lemma term_ty_wf_aux t s:
  term_hash_wf t s ->
  ty_st_wf (t_ty_of t) s.
Proof.
  unfold term_hash_wf, ty_st_wf, ty_hash_wf, gen_hash_wf.
  destruct t; simpl. 
  rewrite !map_app, !concat_app.
  unfold all_in_hashtable, all_idents_smaller.
  setoid_rewrite in_app_iff.
  intros [Hin1 Hin2]; split; intros x Hinx; [apply Hin1 | apply Hin2]; auto.
Qed.

Lemma term_ty_wf t s:
  term_st_wf t s ->
  ty_st_wf (t_ty_of t) s.
Proof.
  intros [_ Hhash]. apply term_ty_wf_aux; auto.
Qed.

(*Prove related for formulas (main part)*)
Theorem elim_let_rewrite_related_aux (f1: term_c) :
  (forall (g1: formula)
    (Heval: eval_fmla f1 = Some g1),
    errst_spec (term_st_wf f1) (elim_let_rewrite f1)
    (fun (_ : full_st) (f2 : term_c) (s2 : full_st) =>
     term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true g1))) /\
  (forall (g1: term)
    (Heval: eval_term f1 = Some g1),
    errst_spec (term_st_wf f1) (elim_let_rewrite f1)
    (fun (_ : full_st) (f2 : term_c) (s2 : full_st) =>
     term_st_wf f2 s2 /\ term_related f2 (elim_let_t true true g1))).
Proof.
  (*Use induction principle *)
  apply tm_traverse_ind with (P:= fun f1 t1 =>
    (forall g1 : formula,
       eval_fmla f1 = Some g1 ->
       errst_spec (term_st_wf f1) t1
         (fun (_ : full_st) (f2 : term_c) (s2 : full_st) =>
          term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true g1))) /\
      (forall g1 : term,
       eval_term f1 = Some g1 ->
       errst_spec (term_st_wf f1) t1
         (fun (_ : full_st) (f2 : term_c) (s2 : full_st) =>
          term_st_wf f2 s2 /\ term_related f2 (elim_let_t true true g1)))).
  - (*const*)
    intros t c Ht. split; intros g1 Heval.
    + exfalso. apply (eval_const_fmla Ht Heval).
    + destruct (eval_const_tm Ht Heval) as [c1 [Hg1 Hc1]]; subst. simpl.
      apply prove_errst_spec_ret.
      intros i Hwf. split; auto.
      unfold term_related. exists (Tconst c1). split; auto.
      apply a_equiv_t_refl.
  - (*var*)
    intros t c Ht. split; intros g1 Heval.
    + exfalso. apply (eval_var_fmla Ht Heval).
    + rewrite (eval_var_tm Ht Heval) in Heval |- *.
      simpl. apply prove_errst_spec_ret.
      intros i Hwf. split; auto.
      unfold term_related. eexists. split; eauto.
      apply a_equiv_t_refl.
  - (*if*)
    intros t t1 t2 t3 Ht IH1 IH2 IH3. split.
    + (*Tif*)
      intros g1 Heval.
      destruct (eval_if_fmla Ht Heval) as [e1 [e2 [e3 [Hg1 [He1 [He2 He3]]]]]]. subst.
      simpl. destruct IH1 as [IH1 _]. destruct IH2 as [IH2 _]. destruct IH3 as [IH3 _].
      specialize (IH1 e1 He1). specialize (IH2 e2 He2). specialize (IH3 e3 He3).
      (*Idea: use bind result 3 times: first by IH gives that r1 related to [elim_let e1],
        second. The wfs are annoying: we have the push them through *)
      (*First, break down st*)
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ term_st_wf t3 s
      /\ ty_st_wf (t_ty_of t) s)).
      { intros s.  rewrite (term_st_wf_if Ht). auto. }
      (*Now bind first*)
      eapply prove_errst_spec_bnd_nondep' with
      (Q1:=fun f2 s2 => (term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true e1)) /\
        (term_st_wf t2 s2 /\ term_st_wf t3 s2 /\ ty_st_wf (t_ty_of t) s2)).
      1: { (*Prove first*) 
        apply errst_spec_and; [apply IH1|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      intros ta.
      (*Pull pure out*)
      apply errst_spec_weaken_pre with (P1:=fun s2 =>
        (term_st_wf t2 s2 /\
        (term_st_wf ta s2 /\ term_st_wf t3 s2 /\ ty_st_wf (t_ty_of t) s2)) /\ 
        fmla_related ta (elim_let_f true true e1));
      [intros; destruct_all; split_all; auto|].
      apply errst_spec_pure_pre. intros Hrel1.
      (*Now use second IH*)
      eapply prove_errst_spec_bnd_nondep' with (Q1:=fun f3 s3 =>
        (term_st_wf f3 s3 /\ fmla_related f3 (elim_let_f true true e2)) /\
        (term_st_wf ta s3 /\ term_st_wf t3 s3 /\ ty_st_wf (t_ty_of t) s3)).
      1: { (*Prove second*)
        apply errst_spec_and; [apply IH2|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      intros tb.
      (*Again, pull pure out*)
      apply errst_spec_weaken_pre with (P1:=fun s3 => ((term_st_wf t3 s3 /\
        (term_st_wf ta s3 /\ term_st_wf tb s3 /\ ty_st_wf (t_ty_of t) s3)) /\ 
        (fmla_related tb (elim_let_f true true e2))));
      [intros; destruct_all; split_all; auto|].
      apply errst_spec_pure_pre. intros Hrel2.
      (*Use third IH*)
      eapply prove_errst_spec_bnd_nondep' with (Q1:=fun f4 s4 =>
        (term_st_wf f4 s4 /\ fmla_related f4 (elim_let_f true true e3)) /\
        (term_st_wf ta s4 /\ term_st_wf tb s4 /\ ty_st_wf (t_ty_of t) s4)).
      1: { (*Prove third*)
        apply errst_spec_and; [apply IH3|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      (*Finally, put it all together*)
      intros tc. unfold tmap_if_default. apply errst_spec_err'.
      intros s4 x Hx. (*Get info about [t_if] - kinda breaks abstraction which isn't great*)
      intros [[Hwfc Hrel3] [Hwfa [Hwfb Hwfty]]].
      unfold t_if in Hx.
      apply err_bnd_inr in Hx. destruct Hx as [u [_ Hbind]].
      apply err_bnd_inr in Hbind. destruct Hbind as [fa [Hta Hif]]. 
      unfold err_ret in Hif. inversion Hif; subst; clear Hif.
      unfold t_prop in Hta. (*TODO: prop should be separate probably*)
      destruct (negb (isSome (t_ty_of ta)) ); inversion Hta; subst; auto.
      split.
      * (*prove wf*) eapply term_st_wf_if. reflexivity. split_all; auto.
        simpl. apply term_ty_wf in Hwfc. auto.
      * (*Now prove related*)
        apply fmla_related_fif; auto.
    + (*Tif - very similar*)
Admitted.




(*Then lift result to transformation. This is not trivial*)
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
  (*Now decompose bind again: first just gives us (alpha equiv to) [elim_let_f goal], second
    builds the task*)
  eapply prove_errst_spec_bnd with (Q1:=fun _ f2 _ => fmla_related f2 (elim_let_f true true goal))
  (Q2:=fun x _ y _ => task_related (Some y) (gamma1, delta1, elim_let_f true true goal1))
  (P2:=fun x _ => fmla_related x (elim_let_f true true goal)) (*TODO: see*); auto.
  2: { (*Prove ending spec assuming [elim_let] correct*) intros f2. apply prove_errst_spec_ret. intros _ Hf2.
    unfold task_related.
    unfold fmla_related in Hf2. destruct Hf2 as [f3 [Hf23 Halphaf]].
    exists (gamma, delta, f3). 
    split.
    - unfold eval_task. simpl. erewrite eval_task_ctx_change_tdecl; eauto. rewrite Hgamma. simpl.
      erewrite eval_task_hyps_change_tdecl; eauto. rewrite Hdelta. simpl.
      erewrite eval_task_goal_change_tdecl; eauto. rewrite Hf23. reflexivity.
    - unfold a_equiv_task. simpl_task. bool_to_prop; split_all; auto.
      eapply a_equiv_f_trans. apply Halphaf.
      (*Why we needed that a_equiv_f is preserved by elim_let_f*)
      apply elim_let_f_a_equiv; auto.
  }
  (*We need to change the precondition*)
  apply errst_spec_weaken with (P1:=term_st_wf f1)(Q1:=fun _ f2 s2 => term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true goal)).
  - intros i. eapply prop_wf; eauto.
  - intros _ x f [_ Hrel]; auto.
  - (*The main result*)
    apply (proj1 (elim_let_rewrite_related_aux f1)); auto.
Qed.

(*Put it all together with decomp theorem*)
Theorem elim_let_sound: trans_errst_sound elim_let.
Proof.
  apply prove_trans_errst_decompose with (tr1:=single_goal (elim_let_f true true)).
  - (*already proved soundness*) apply elim_let_sound. 
  - (*Now prove related*) apply elim_let_related.
Qed.


