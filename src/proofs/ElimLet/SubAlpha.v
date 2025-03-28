(*Results about how Alpha equivalence/relations interact with substitution
  TODO: move*)
From Proofs Require Import Alpha eliminate_let (*for [safe_sub_t'] TODO move*).

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

Set Bullet Behavior "Strict Subproofs".

Lemma safe_sub_t_notin' tm1 x t:
  ~ aset_mem x (tm_fv t) ->
  a_equiv_t (safe_sub_t' tm1 x t) t.
Proof.
  intros Hmem.
  unfold safe_sub_t'.
  rewrite sub_t_notin.
  - rewrite a_equiv_t_sym. apply a_convert_t_equiv.
  - erewrite <- a_equiv_t_fv; eauto. apply a_convert_t_equiv.
Qed.

Lemma safe_sub_f_notin' tm1 x f:
  ~ aset_mem x (fmla_fv f) ->
  a_equiv_f (safe_sub_f' tm1 x f) f.
Proof.
  intros Hmem.
  unfold safe_sub_f'.
  rewrite sub_f_notin.
  - rewrite a_equiv_f_sym. apply a_convert_f_equiv.
  - erewrite <- a_equiv_f_fv; eauto. apply a_convert_f_equiv.
Qed.

(*TODO: move*)
(*Transitivity is awkward to work with, but things are much easier if 1 is alpha-equivalent
  rather than related*)
Lemma alpha_trans_eq_rel_t {t1 t2 m1 m2 t3}
  (Heq: a_equiv_t t1 t2) (Halpha: alpha_equiv_t m1 m2 t2 t3):
  alpha_equiv_t m1 m2 t1 t3.
Proof.
  unfold a_equiv_t in Heq.
  pose proof (alpha_equiv_t_trans _ _ _ _ _ _ _ Heq Halpha) as Ha.
  rewrite alpha_comp_empty_l, alpha_comp_empty_r in Ha. auto.
Qed.

Lemma alpha_trans_rel_eq_t {t1 t2 m1 m2 t3}
  (Halpha: alpha_equiv_t m1 m2 t1 t2) (Heq: a_equiv_t t2 t3):
  alpha_equiv_t m1 m2 t1 t3.
Proof.
  unfold a_equiv_t in Heq.
  pose proof (alpha_equiv_t_trans _ _ _ _ _ _ _ Halpha Heq) as Ha.
  rewrite alpha_comp_empty_l, alpha_comp_empty_r in Ha. auto.
Qed.

Lemma alpha_trans_eq_rel_f {f1 f2 m1 m2 f3}
  (Heq: a_equiv_f f1 f2) (Halpha: alpha_equiv_f m1 m2 f2 f3):
  alpha_equiv_f m1 m2 f1 f3.
Proof.
  unfold a_equiv_f in Heq.
  pose proof (alpha_equiv_f_trans _ _ _ _ _ _ _ Heq Halpha) as Ha.
  rewrite alpha_comp_empty_l, alpha_comp_empty_r in Ha. auto.
Qed.

Lemma alpha_trans_rel_eq_f {f1 f2 m1 m2 f3}
  (Halpha: alpha_equiv_f m1 m2 f1 f2) (Heq: a_equiv_f f2 f3):
  alpha_equiv_f m1 m2 f1 f3.
Proof.
  unfold a_equiv_f in Heq.
  pose proof (alpha_equiv_f_trans _ _ _ _ _ _ _ Halpha Heq) as Ha.
  rewrite alpha_comp_empty_l, alpha_comp_empty_r in Ha. auto.
Qed.

(*Cannot use [safe_sub_t] because if we don't alpha convert, dont have
  the tm_bnd condition (and don't have [same_in_t] necessarily*)
Lemma safe_sub_t_alpha m1 m2 v1 v2 t1 t2 t3 t4
  (Halpha1: alpha_equiv_t m1 m2 t1 t2)
  (Halpha2: alpha_equiv_t (amap_set m1 v1 v2) (amap_set m2 v2 v1) t3 t4):
  alpha_equiv_t m1 m2 (safe_sub_t' t1 v1 t3) (safe_sub_t' t2 v2 t4).
Proof.
  pose proof (safe_sub_t_notin' t1 v1 t3) as Hfv1.
  pose proof (safe_sub_t_notin' t2 v2 t4) as Hfv2.
  unfold safe_sub_t' in *.
  (*Why we needed the previous: v1 in fv of t3 iff v2 in fv of t4*)
  (*NOTE: don't need anymore, but still good to know*)
  assert (Hfvs: aset_mem v1 (tm_fv t3) <-> aset_mem v2 (tm_fv t4)). {
    eapply alpha_equiv_t_map_fv_iff; eauto.
    rewrite alpha_equiv_var_iff. rewrite !amap_set_lookup_same. auto.
  }
  (*Annoyingly, have to destruct by cases*)
  destruct (aset_mem_dec v1 (tm_fv t3)) as [Hv1 | Hv1]; 
  destruct (aset_mem_dec v2 (tm_fv t4)) as [Hv2 | Hv2]; [| tauto | tauto |].
  2: { (*In this case, can remove these from the map because free vars not present*) 
    rewrite alpha_equiv_t_extra_var in Halpha2; auto.
    specialize (Hfv1 Hv1). specialize (Hfv2 Hv2).
    eapply alpha_trans_eq_rel_t; [apply Hfv1|].
    eapply alpha_trans_rel_eq_t; [apply Halpha2|].
    rewrite a_equiv_t_sym. auto.
  }
  set (t3':=(a_convert_t t3 (aset_union (tm_fv t1) (tm_fv t3)))).
  set (t4':=(a_convert_t t4 (aset_union (tm_fv t2) (tm_fv t4)))).
  assert (Ht3: a_equiv_t t3 t3') by apply a_convert_t_equiv.
  assert (Ht4: a_equiv_t t4 t4') by apply a_convert_t_equiv.
  assert (Ht34: alpha_equiv_t (amap_set m1 v1 v2) (amap_set m2 v2 v1) t3' t4'). {
    eapply alpha_trans_eq_rel_t; [rewrite a_equiv_t_sym; apply Ht3|].
    eapply alpha_trans_rel_eq_t; [apply Halpha2|]; auto.
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
  pose proof (safe_sub_f_notin' t1 v1 f3) as Hfv1.
  pose proof (safe_sub_f_notin' t2 v2 f4) as Hfv2.
  unfold safe_sub_f'.
  assert (Hfvs: aset_mem v1 (fmla_fv f3) <-> aset_mem v2 (fmla_fv f4)). {
    eapply alpha_equiv_f_map_fv_iff; eauto.
    rewrite alpha_equiv_var_iff. rewrite !amap_set_lookup_same. auto.
  }
  (*Annoyingly, have to destruct by cases*)
  destruct (aset_mem_dec v1 (fmla_fv f3)) as [Hv1 | Hv1]; 
  destruct (aset_mem_dec v2 (fmla_fv f4)) as [Hv2 | Hv2]; [| tauto | tauto |].
  2: { (*In this case, can remove these from the map because free vars not present*) 
    rewrite alpha_equiv_f_extra_var in Halpha2; auto.
    specialize (Hfv1 Hv1). specialize (Hfv2 Hv2).
    eapply alpha_trans_eq_rel_f; [apply Hfv1|].
    eapply alpha_trans_rel_eq_f; [apply Halpha2|].
    rewrite a_equiv_f_sym. auto. }
  set (f3':=(a_convert_f f3 (aset_union (tm_fv t1) (fmla_fv f3)))).
  set (f4':=(a_convert_f f4 (aset_union (tm_fv t2) (fmla_fv f4)))).
  assert (Ht3: a_equiv_f f3 f3') by apply a_convert_f_equiv.
  assert (Ht4: a_equiv_f f4 f4') by apply a_convert_f_equiv.
  assert (Ht34: alpha_equiv_f (amap_set m1 v1 v2) (amap_set m2 v2 v1) f3' f4'). {
    eapply alpha_trans_eq_rel_f; [rewrite a_equiv_f_sym; apply Ht3|].
    eapply alpha_trans_rel_eq_f; [apply Halpha2|]; auto.
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