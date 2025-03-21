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

(*TODO: formula version*)

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
  - admit.
  - (*Tlet*)
    intros e1 v1 e2 IH1 IH2 t2 m1 m2 Halpha2 Halpha Hsame Hd1 Hd2.
    destruct t2 as [| | | e3 v2 e4 | | |]; try discriminate.
    simpl.
    simpl in Hd2.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[Hty Ha1] Ha2].
    rewrite !andb_true in Hsame. destruct Hsame as [[Hsame1 Heqvar] Hsame2].
    rewrite !list_to_aset_cons, !list_to_aset_app in Hd1, Hd2.
    apply IH1 in Ha1; auto.
    2: { apply aset_disj_union_r, aset_disj_union_l in Hd1. auto. }
    2: { apply aset_disj_union_r, aset_disj_union_l in Hd2. auto. }
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
      2: { apply aset_disj_union_r, aset_disj_union_r in Hd1. auto. }
      2: { apply aset_disj_union_r, aset_disj_union_r in Hd2. auto. }
      (*Now we can remove these vars because not free*)
      assert (Hv1: ~ aset_mem v1 (tm_fv tm1)).
      { apply aset_disj_union_l in Hd1. apply aset_disj_singleton; auto. }
      assert (Hv2: ~ aset_mem v2 (tm_fv tm2)).
      { apply aset_disj_union_l in Hd2. apply aset_disj_singleton; auto. }
      (*separate lemma?*)
      rewrite <- alpha_equiv_t_remove with (y2:=v2) in Halpha2 |- *; auto.
      rewrite amap_remove_set_same.
      (*And remove the other side*)
      rewrite alpha_equiv_t_sym in Halpha2 |- *.
      rewrite <- alpha_equiv_t_remove with (y2:=v1) in Halpha2 |- *; auto.
      rewrite amap_remove_set_same.
      apply Halpha2.
  - 
Admitted.

(*TODO: prove rest of cases but should be doable*)


(*TODO: need type equality?*)
Lemma safe_sub_t_alpha m1 m2 v1 v2 t1 t2 t3 t4
  (Halpha1: alpha_equiv_t m1 m2 t1 t2)
  (Halpha2: alpha_equiv_t (amap_set m1 v1 v2) (amap_set m2 v2 v1) t3 t4):
  alpha_equiv_t m1 m2 (safe_sub_t t1 v1 t3) (safe_sub_t t2 v2 t4).
Proof.
  unfold safe_sub_t.
  (*Why we needed the previous: v1 in fv of t3 iff v2 in fv of t4*)
  assert (Hfvs: aset_mem v1 (tm_fv t3) <-> aset_mem v2 (tm_fv t4)). {
    eapply alpha_equiv_t_map_fv_iff; eauto.
    rewrite alpha_equiv_var_iff. rewrite !amap_set_lookup_same. auto.
  }
  (*Annoyingly, have to destruct by cases*)
  destruct (aset_mem_dec v1 (tm_fv t3)) as [Hv1 | Hv1]; 
  destruct (aset_mem_dec v2 (tm_fv t4)) as [Hv2 | Hv2]; [| tauto | tauto |].
  2: {
    (*In this case, can remove these from the map because free vars not present*)
    rewrite <- alpha_equiv_t_remove with (y2:=v2) in Halpha2 |- *; auto.
    rewrite amap_remove_set_same in Halpha2.
    (*And remove the other side*)
    rewrite alpha_equiv_t_sym in Halpha2 |- *.
    rewrite <- alpha_equiv_t_remove with (y2:=v1) in Halpha2 |- *; auto.
    rewrite amap_remove_set_same in Halpha2.
    apply Halpha2.
  }
  (*It doesn't actually matter which we substitute. But the result is alpha equivalent to t3*)
  set (t3':=(if existsb (fun x : vsymbol => in_bool vsymbol_eq_dec x (tm_bnd t3)) (aset_to_list (tm_fv t1))
      then a_convert_t t3 (tm_fv t1)
      else t3)).
  set (t4':=(if existsb (fun x : vsymbol => in_bool vsymbol_eq_dec x (tm_bnd t4)) (aset_to_list (tm_fv t2))
      then a_convert_t t4 (tm_fv t2)
      else t4)).
  assert (Ht3: a_equiv_t t3 t3'). {
    unfold t3'. destruct (existsb _). 
    - apply a_convert_t_equiv.
    - apply a_equiv_t_refl.
  }
  assert (Ht4: a_equiv_t t4 t4'). {
    unfold t4'. clear. destruct (existsb _). 
    - apply a_convert_t_equiv.
    - apply a_equiv_t_refl.
  }
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
  (*Should be provable with previous*)
Admitted.



(* alpha_equiv_sub_var_t_full:
  forall (t t2 : term) (x y : vsymbol) (m1 m2 : amap vsymbol vsymbol),
  snd x = snd y ->
  ~ In y (tm_bnd t2) ->
  ~ aset_mem y (tm_fv t2) ->
  same_in_t t t2 x ->
  ~ amap_mem y m2 ->
  alpha_equiv_t m1 m2 t t2 -> alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t (sub_var_t x y t2)
 *)

(*TODO: generalize, define previous by this*)




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
    set (t1 := (elim_let_t true b2 tm1) ) in *.
    set (t2:=(elim_let_t true b2 e1)) in *.
    set (t3:=(elim_let_t true b2 tm2)) in *.
    set (t4:=(elim_let_t true b2 e3)) in *.
    (*Could assume: tm1 and tm2 with m3 and m4, then t1 and t2 with m1 U m3 and m2 U m4
      then want to show safe_sub_t with  *)
    apply safe_sub_t_alpha; auto.
Admitted.


    Search elim_let_t tm_fv.



    unfold safe_sub_t.
    (*TODO: should do [safe_sub_t] in different lemma*)
    (*oh btw I already have the free var optimization but only in [safe_sub_t]*)

    Search alpha_equiv_t safe_sub_t.
 

    Search all2 combine.
    Search all2 "impl".




all2_Forall2
    Search all2 Forall2.


 auto.
    Search all2 map.


    rewrite !map_length.

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


