Require Import Vars.
Set Bullet Behavior "Strict Subproofs".

(*If we know that the bound variable names are unique and do
  not conflict with the free variable names, we can prove the
  correctness of many transformations. We define such a notion
  and provide a function (not necessarily the most efficient one)
  to alpha-convert our term/formula into this form. The function
  and proofs are in Alpha.v*)
Definition term_name_wf (t: term) : Prop :=
  NoDup (map fst (tm_bnd t)) /\ disj (map fst (tm_fv t)) (map fst (tm_bnd t)).
Definition fmla_name_wf (f: formula) : Prop :=
  NoDup (map fst (fmla_bnd f)) /\ disj (map fst (fmla_fv f)) (map fst (fmla_bnd f)).
Definition gen_name_wf {b: bool} (t: gen_term b) : Prop :=
  match b return gen_term b -> Prop with
  | true => term_name_wf
  | false => fmla_name_wf
  end t.

Lemma gen_name_wf_eq {b: bool} (t: gen_term b) :
  gen_name_wf t <->
  NoDup (map fst (gen_bnd t)) /\ disj (map fst (gen_fv t)) (map fst (gen_bnd t)).
Proof.
  destruct b; reflexivity.
Qed.

Lemma wf_genfun (b: bool) {s: gen_sym b} {tys: list vty} {tms: list term}
  (Hwf: gen_name_wf (gen_fun s tys tms)):
  Forall term_name_wf tms.
Proof.
  rewrite gen_name_wf_eq in Hwf. unfold term_name_wf.
  rewrite gen_fun_bnd, gen_fun_fv in Hwf.
  rewrite Forall_forall. intros t Hint.
  destruct Hwf as [Hnodup Hfb].
  rewrite concat_map in Hnodup.
  split.
  - eapply in_concat_NoDup; [apply string_dec | apply Hnodup |].
    rewrite in_map_iff. exists (tm_bnd t); rewrite in_map_iff; eauto.
  - intros x [Hinx1 Hinx2].
    apply (Hfb x).
    split; [rewrite in_map_big_union|].
    + simpl_set. eauto. Unshelve. exact string_dec.
    + rewrite concat_map, !map_map. 
      rewrite in_concat. eexists. split; [| apply Hinx2].
      rewrite in_map_iff. eauto.
Qed.

Lemma wf_genlet (b: bool) {tm1: term} {tm2: gen_term b} {x} 
  (Hwf: gen_name_wf (gen_let x tm1 tm2)):
  term_name_wf tm1 /\ gen_name_wf tm2.
Proof.
  rewrite gen_name_wf_eq in Hwf |- *. unfold term_name_wf.
  rewrite gen_let_bnd, gen_let_fv in Hwf.
  destruct Hwf as [Hnodup Hfb].
  inversion Hnodup as [| ? ? Hnotin Hn2]; subst.
  rewrite map_app in Hn2.
  apply NoDup_app in Hn2. destruct Hn2 as [Hn1 Hn2].
  split_all; auto; intros y [Hiny1 Hiny2]; apply (Hfb y);
  rewrite in_map_union; simpl_set; simpl; rewrite map_app, in_app_iff; auto.
  split; auto. right. apply in_map_remove. split; auto.
  intro C; subst. apply Hnotin. rewrite map_app, in_app_iff; auto.
Qed.

Lemma wf_genif (b : bool) {f} {t1 t2 : gen_term b} 
  (Hwf: gen_name_wf (gen_if f t1 t2)):
  fmla_name_wf f /\ gen_name_wf t1 /\ gen_name_wf t2.
Proof.
  rewrite !gen_name_wf_eq in Hwf |- *.
  rewrite gen_name_wf_eq. unfold fmla_name_wf.
  rewrite gen_if_bnd, gen_if_fv in Hwf.
  destruct Hwf as [Hnodup Hfb].
  rewrite !map_app in Hnodup, Hfb.
  apply NoDup_app in Hnodup.
  destruct Hnodup as [Hn1 Hn2].
  apply NoDup_app in Hn2.
  destruct Hn2 as [Hn2 Hn3].
  unfold disj in Hfb.
  do 2 (setoid_rewrite in_app_iff in Hfb).
  split_all; auto; intros x [Hinx1 Hinx2]; apply (Hfb x);
  rewrite !in_map_union; simpl_set; auto.
Qed.

Lemma wf_genmatch (b: bool) {tm ty} {ps: list (pattern * gen_term b)} 
  (Hwf: gen_name_wf (gen_match tm ty ps)):
  term_name_wf tm /\ Forall (fun x => gen_name_wf (snd x)) ps.
Proof.
  rewrite gen_name_wf_eq in Hwf.
  unfold term_name_wf. 
  rewrite gen_match_bnd, gen_match_fv in Hwf.
  rewrite !map_app in Hwf.
  destruct Hwf as [Hn Hdisj].
  apply NoDup_app_iff in Hn.
  destruct Hn as [Hn1 [Hn2  [Hn12 _]]].
  split_all; auto.
  - eapply disj_sublist_lr. apply Hdisj.
    intros x Hinx. rewrite in_map_union. auto.
    apply sublist_app_l.
  - rewrite Forall_forall. intros x Hinx.
    rewrite gen_name_wf_eq.
    rewrite concat_map in Hn2.
    assert (Hn3:
      NoDup (map fst (pat_fv (fst x)) ++ map fst (gen_bnd (snd x)))).
    {
      eapply in_concat_NoDup; [apply string_dec | apply Hn2 |].
      rewrite in_map_iff. eexists.
      rewrite <- map_app. split; [reflexivity|]. 
      rewrite in_map_iff; eauto.
    }
    split.
    + apply NoDup_app in Hn3. apply Hn3.
    + intros y [Hiny1 Hiny2].
      (*Because in [tm_bnd], cannot be in [pat_fv]*)
      assert (Hnotin: ~ In y (map fst (pat_fv (fst x)))). {
        intro C.
        apply NoDup_app_iff in Hn3.
        apply Hn3 in C; auto; contradiction.
      }
      apply (Hdisj y). split.
      * rewrite in_map_union. right.
        rewrite in_map_big_union with (eq_dec1:=string_dec).
        simpl_set. exists x. split; auto.
        apply in_map_remove_all. auto.
      * rewrite in_app_iff. right. rewrite concat_map, map_map, in_concat.
        eexists. split; [rewrite in_map_iff; eexists; split; [| apply Hinx]; reflexivity |].
        rewrite map_app, in_app_iff; auto.
Qed.

Lemma wf_teps {f v} (Hwf: term_name_wf (Teps f v)):
  fmla_name_wf f.
Proof.
  unfold term_name_wf in Hwf; unfold fmla_name_wf. simpl in *.
  destruct Hwf as [Hn1 Hdisj].
  inversion Hn1; subst. split; auto.
  intros x [Hinx1 Hinx2].
  assert (x <> fst v) by (intro C; subst; contradiction).
  apply (Hdisj x); split.
  - apply in_map_remove. auto.
  - simpl. auto.
Qed.

Lemma wf_fquant {q v f} (Hwf: fmla_name_wf (Fquant q v f)):
  fmla_name_wf f.
Proof.
  unfold fmla_name_wf in *; simpl in *.
  destruct Hwf as [Hn1 Hdisj].
  inversion Hn1; subst. split; auto.
  intros x [Hinx1 Hinx2].
  assert (x <> fst v) by (intro C; subst; contradiction).
  apply (Hdisj x); split.
  - apply in_map_remove. auto.
  - simpl. auto.
Qed.

Lemma wf_feq {ty t1 t2} (Hwf: fmla_name_wf (Feq ty t1 t2)):
  term_name_wf t1 /\ term_name_wf t2.
Proof.
  unfold term_name_wf, fmla_name_wf in *; simpl in *.
  rewrite map_app in Hwf.
  destruct Hwf as [Hn1 Hdisj].
  apply NoDup_app in Hn1. destruct Hn1 as [Hn1 Hn2]. split_all; auto;
  eapply disj_sublist_lr; try solve[apply Hdisj];
  try solve[apply sublist_app_r]; try solve[apply sublist_app_l];
  intros x Hinx; apply in_map_union; auto.
Qed.

Lemma wf_fbinop {b f1 f2} (Hwf: fmla_name_wf (Fbinop b f1 f2)):
  fmla_name_wf f1 /\ fmla_name_wf f2.
Proof.
  unfold fmla_name_wf in *; simpl in *.
  rewrite map_app in Hwf.
  destruct Hwf as [Hn1 Hdisj].
  apply NoDup_app in Hn1. destruct Hn1 as [Hn1 Hn2]. split_all; auto;
  eapply disj_sublist_lr; try solve[apply Hdisj];
  try solve[apply sublist_app_r]; try solve[apply sublist_app_l];
  intros x Hinx; apply in_map_union; auto.
Qed.

Lemma wf_fnot {f} (Hwf: fmla_name_wf (Fnot f)):
  fmla_name_wf f.
Proof.
  unfold fmla_name_wf in *; simpl in *; auto.
Qed.

(*For legacy reasons (TODO remove)*)
Definition term_wf (t: term) : Prop :=
  NoDup (tm_bnd t) /\ forall x, ~ (In x (tm_fv t) /\ In x (tm_bnd t)).
Definition fmla_wf (f: formula) : Prop :=
  NoDup (fmla_bnd f) /\ forall x, ~ (In x (fmla_fv f) /\ In x (fmla_bnd f)).

Lemma term_name_wf_wf (t: term):
  term_name_wf t ->
  term_wf t.
Proof.
  unfold term_name_wf, term_wf.
  intros [Hn Hdisj].
  split.
  - apply NoDup_map_inv in Hn; auto.
  - intros x [Hinx1 Hinx2].
    apply (Hdisj (fst x)).
    rewrite !in_map_iff; split; eauto.
Qed.

Lemma fmla_name_wf_wf (f: formula):
  fmla_name_wf f ->
  fmla_wf f.
Proof.
  unfold fmla_name_wf, fmla_wf.
  intros [Hn Hdisj].
  split.
  - apply NoDup_map_inv in Hn; auto.
  - intros x [Hinx1 Hinx2].
    apply (Hdisj (fst x)).
    rewrite !in_map_iff; split; eauto.
Qed.


Lemma wf_quant (q: quant) (v: vsymbol) (f: formula) :
  fmla_wf (Fquant q v f) ->
  fmla_wf f.
Proof.
  unfold fmla_wf. simpl. intros. split_all.
  - inversion H; auto.
  - intros x C. split_all.
    apply (H0 x).
    destruct (vsymbol_eq_dec x v); subst; auto.
    + inversion H; subst. contradiction.
    + split; auto. simpl_set; auto. 
Qed. 

Lemma wf_binop (b: binop) (f1 f2: formula) :
  fmla_wf (Fbinop b f1 f2) ->
  fmla_wf f1 /\ fmla_wf f2.
Proof.
  unfold fmla_wf. simpl. rewrite NoDup_app_iff.
  intros. split_all; auto; intros x C; split_all.
  - apply (H0 x).
    split_all. apply union_elts. auto. 
    apply in_or_app. auto.
  - apply (H0 x).
    split_all. apply union_elts. auto.
    apply in_or_app. auto. 
Qed.

Lemma wf_let (t: term) (v: vsymbol) (f: formula) :
  fmla_wf (Flet t v f) ->
  fmla_wf f.
Proof.
  unfold fmla_wf. simpl. intros; split_all; auto; 
  inversion H; subst; auto.
  - rewrite NoDup_app_iff in H4; apply H4.
  - intros x C. split_all.
    apply (H0 x). split.
    + simpl_set; right. split; auto. intro Heq; subst.
      inversion H; subst.
      apply H7. apply in_or_app. auto. 
    + right. apply in_or_app. auto.
Qed.
