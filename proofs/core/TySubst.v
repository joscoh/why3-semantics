(*Type substitution*)
Require Import Denotational.
Require Import CommonSSR Typechecker.

(*We can substitute types for type variables just as we 
  substitute terms for term variables. We would like to
  say similarly that this is equivalent to adjusting
  the type variable valuation accoringly. But, there are 2 main
  complications:
  1. The type of [term_rep] depends on the type variable
    valuation, so we need lots of tricky casting (even more than
    _change_vt in Denotational.v)
  2. Our variables are typed, so under a type substitution, 2
    variables which were not equal may be. Ex:
      let x : 'a = y in let x : int = z in x : 'a
      has a different meaning if 'a -> int
    The problem comes from different (free) 
    variables with the same name.
    But this is not exactly a problem for us: we only deal with
    closed terms and formulas and formulas (in the body of a
    recursive fn or pred) with distinct free variable names.
    So we can always alpha-convert.
    But it is a lot of work to show that all of this works.
    We do so here.*)

From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*To prove that patterns are well-typed,
  we need a condition that the names of pattern variables
  are unique (not just the vsymbols). Really, this should
  be in typing, but it makes alpha equvialence much harder.
  For now, we have a separate condition, which we can check.
  We could alpha convert if needed to make this condition true*)
(*We don't need the bool version, but we include anyway*)
Section PatUniq.

Fixpoint pat_names_uniq (p:pattern) : Prop :=
  match p with
  | Pconstr f args ps =>
    Forall id (map pat_names_uniq ps) /\
    forall i j, (i < length ps)%coq_nat -> (j < length ps)%coq_nat ->
    i <> j ->
    forall x, ~ (In x (map fst (pat_fv (List.nth i ps Pwild))) /\
      In x (map fst (pat_fv (List.nth j ps Pwild))))
  | Por p1 p2 => pat_names_uniq p1 /\ pat_names_uniq p2 /\
    (forall x, In x (map fst (pat_fv p1)) <-> In x (map fst (pat_fv p2)))
  | Pbind p x => pat_names_uniq p /\ ~ In (fst x) (map fst (pat_fv p))
  | _ => true
  end.

Fixpoint pat_names_uniqb (p: pattern) : bool :=
  match p with
  | Pconstr f args ps => 
    all id (map pat_names_uniqb ps) &&
    [forall x in 'I_(length ps), forall y in 'I_(length ps),
    (x != y) ==>  
    null (seqI (map fst (pat_fv (nth Pwild ps x))) 
      (map fst (pat_fv (nth Pwild ps y))))]
  | Por p1 p2 => pat_names_uniqb p1 && pat_names_uniqb p2 &&
    (eq_memb (map fst (pat_fv p2)) (map fst (pat_fv p1)))
  | Pbind p x => pat_names_uniqb p && 
    ((fst x) \notin (map fst (pat_fv p)))
  | _ => true
  end.

Lemma all_Forall_idP {A: Type} (P: A -> Prop) (b: A -> bool)
  (l: list A):
  (forall x, In x l -> reflect (P x) (b x)) ->
  reflect (Forall id (map P l)) (all id (map b l)).
Proof.
  move=>Hrefl.
  apply iff_reflect. rewrite Forall_map all_map.
  apply reflect_iff.
  apply forallb_ForallP => x Hinx.
  by apply Hrefl.
Qed.

Lemma pat_names_uniqb_correct p:
  reflect (pat_names_uniq p) (pat_names_uniqb p).
Proof.
  apply 
    (pattern_rect (fun (p: pattern) => 
      reflect (pat_names_uniq p) (pat_names_uniqb p)))=>//=.
  - move=> _. by reflT.
  - (*The hard case*)
    move=> f vs ps Hall.
    have Hallr: reflect (Forall id [seq pat_names_uniq i | i <- ps])
      (all id [seq pat_names_uniqb i | i <- ps]).
    {
      apply all_Forall_idP.
      apply ForallT_In=>//. apply pattern_eq_dec. 
    }
    case: Hallr => Halluniq; last by reflF.
    case: [forall x in 'I_(Datatypes.length ps),
    forall y in 'I_(Datatypes.length ps),
    (x != y) ==>
    null (seqI (map fst(pat_fv (nth Pwild ps x))) 
      (map fst (pat_fv (nth Pwild ps y))))] 
    /forallP => Hforallx/=; last first.
    + apply ReflectF => [[_ C]]. apply Hforallx. move=> x.
      apply /implyP => _. apply /forallP => y.
      apply /implyP=>_. apply /implyP => Hneq.
      apply /nullP. apply /eqP. 
      rewrite /seqI -(negbK (_ == _)) -has_filter. 
      apply /negP => /hasP [z] /inP Hzin1 /inP Hzin2.
      apply (C x y (ltac:(by apply /ltP)) (ltac:(by apply /ltP))
        (ltac:(by apply /eqP)) z).
      by rewrite !nth_eq.
    + apply ReflectT. split=>//. move => i j /ltP Hi /ltP Hj /eqP Hij x.
      rewrite !nth_eq => [[Hinxi Hinxj]].
      move: Hforallx => /(_ (Ordinal Hi))/= /forallP 
        /(_ (Ordinal Hj))/= /implyP.
      have Hneq: (Ordinal (n:=Datatypes.length ps) (m:=i) Hi
        != Ordinal (n:=Datatypes.length ps) (m:=j) Hj).
      apply /eqP=> C. inversion C; subst. by rewrite eq_refl in Hij.
      move=>/(_ Hneq) /nullP /eqP. 
      rewrite /seqI -(negbK (_ == _)) -has_filter => /hasP.
      apply. by exists x; apply /inP.
  - by reflT.
  - move=> p1 p2 Hr1 Hr2. rewrite -andbA. apply andPP=>//.
    apply andPP=>//.
    case: (eq_memb (map fst (pat_fv p2)) (map fst (pat_fv p1))) /eq_memb_spec => Heq/=.
    + apply ReflectT. by rewrite eq_mem_In.
    + apply ReflectF => C.
      symmetry in C. 
      by rewrite eq_mem_In in C.
  - move=> p1 v Hr.
    apply andPP=>//.
    apply negPP. apply inP.
Qed.

(*Push through terms and formulas*)
Fixpoint pat_names_uniq_t (t: term) : Prop :=
  match t with
  | Tfun f tys tms => Forall id (map pat_names_uniq_t tms)
  | Tlet t1 v t2 => pat_names_uniq_t t1 /\ pat_names_uniq_t t2
  | Tif f t1 t2 => pat_names_uniq_f f /\ pat_names_uniq_t t1 /\
    pat_names_uniq_t t2
  | Tmatch t ty ps => pat_names_uniq_t t /\
    Forall id (map (fun x => pat_names_uniq (fst x) /\ pat_names_uniq_t (snd x)) ps)
  | Teps f x => pat_names_uniq_f f
  | _ => True
  end
with pat_names_uniq_f (f: formula) : Prop :=
  match f with
  | Fpred p tys tms => Forall id (map pat_names_uniq_t tms)
  | Fquant q v f => pat_names_uniq_f f
  | Feq ty t1 t2 => pat_names_uniq_t t1 /\ pat_names_uniq_t t2
  | Fbinop b f1 f2 => pat_names_uniq_f f1 /\ pat_names_uniq_f f2
  | Fnot f => pat_names_uniq_f f
  | Flet t1 v f => pat_names_uniq_t t1 /\ pat_names_uniq_f f
  | Fif f1 f2 f3 => pat_names_uniq_f f1 /\ pat_names_uniq_f f2 /\
    pat_names_uniq_f f3
  | Fmatch t ty ps => pat_names_uniq_t t /\
    Forall id (map (fun x => pat_names_uniq (fst x) /\ pat_names_uniq_f (snd x)) ps)
  | _ => True
  end.

Fixpoint pat_names_uniq_tb (t: term) : bool :=
  match t with
  | Tfun f tys tms => all id (map pat_names_uniq_tb tms)
  | Tlet t1 v t2 => pat_names_uniq_tb t1 && pat_names_uniq_tb t2
  | Tif f t1 t2 => pat_names_uniq_fb f && pat_names_uniq_tb t1 &&
    pat_names_uniq_tb t2
  | Tmatch t ty ps => pat_names_uniq_tb t &&
    all id (map (fun x => pat_names_uniqb (fst x) && pat_names_uniq_tb (snd x)) ps)
  | Teps f x => pat_names_uniq_fb f
  | _ => true
  end
with pat_names_uniq_fb (f: formula) : bool :=
  match f with
  | Fpred p tys tms => all id (map pat_names_uniq_tb tms)
  | Fquant q v f => pat_names_uniq_fb f
  | Feq ty t1 t2 => pat_names_uniq_tb t1 && pat_names_uniq_tb t2
  | Fbinop b f1 f2 => pat_names_uniq_fb f1 && pat_names_uniq_fb f2
  | Fnot f => pat_names_uniq_fb f
  | Flet t1 v f => pat_names_uniq_tb t1 && pat_names_uniq_fb f
  | Fif f1 f2 f3 => pat_names_uniq_fb f1 && pat_names_uniq_fb f2 &&
    pat_names_uniq_fb f3
  | Fmatch t ty ps => pat_names_uniq_tb t &&
    all id (map (fun x => pat_names_uniqb (fst x) && pat_names_uniq_fb (snd x)) ps)
  | _ => true
  end.

Lemma pat_names_uniq_b_correct (t: term) (f: formula):
  (reflect (pat_names_uniq_t t) (pat_names_uniq_tb t)) *
  (reflect (pat_names_uniq_f f) (pat_names_uniq_fb f)).
Proof.
  revert t f. apply term_formula_rect=>//=.
  - move=>_. by reflT.
  - move=>_. by reflT.
  - move=>_ _ tms Hall.
    apply all_Forall_idP.
    apply ForallT_In=>//. apply term_eq_dec.
  - move=>tm1 _ tm2 Hr1 Hr2.
    by apply andPP.
  - move=> f t1 t2 Hr1 Hr2 Hr3.
    rewrite -andbA.
    apply andPP=>//.
    by apply andPP.
  - move=> t _ ps Hr Hall.
    apply andPP=>//.
    apply all_Forall_idP=> x Hinx.
    apply andPP.
    + apply pat_names_uniqb_correct.
    + apply ForallT_In with(x:=snd x) in Hall=>//.
      apply term_eq_dec. rewrite in_map_iff.
      by exists x. 
  - move=>_ _ tms Hall.
    apply all_Forall_idP.
    apply ForallT_In=>//. apply term_eq_dec.
  - move=>_ t1 t2 Hr1 Hr2.
    by apply andPP.
  - move=>_ f1 f2 Hr1 Hr2.
    by apply andPP.
  - by reflT.
  - by reflT.
  - move=>t _ f Hr1 Hr2.
    by apply andPP.
  - move=>f1 f2 f3 Hr1 Hr2 Hr3.
    rewrite -andbA. by repeat apply andPP=>//.
  - move=> t _ ps Hr Hall.
    apply andPP=>//.
    apply all_Forall_idP=> x Hinx.
    apply andPP.
    + apply pat_names_uniqb_correct.
    + apply ForallT_In with(x:=snd x) in Hall=>//.
      apply formula_eq_dec. rewrite in_map_iff.
      by exists x.
Qed. 

(*[pat_names_uniq] is a complicated (recursive) condition, but really
    it is just well-typed+unique names*)
Lemma pat_names_uniq_nodup gamma (p: pattern) ty:
  pattern_has_type gamma p ty ->
  NoDup (map fst (pat_fv p)) ->
  pat_names_uniq p.
Proof.
  revert ty. induction p; simpl; intros; auto.
  - split.
    { rewrite -> Forall_map, Forall_forall. intros.
      apply nodup_map_big_union_inv with(x:=x) in H1; auto.
      rewrite Forall_forall in H.
      2: {intros; apply NoDup_pat_fv. }
      inversion H0; subst.
      destruct (In_nth _ _ Pwild H2) as [i [Hi Hx]]; subst.
      apply specialize_combine with(d1:=Pwild)(d2:=vty_int)(i:=i) in H12; auto;
      [| rewrite map_length; auto].
      simpl in H12.
      eapply H; auto. apply H12.
    }
    inversion H0; subst. intros.
    eapply nodup_map_big_union_inv' in H1. apply H1.
    all: auto. intros. apply NoDup_pat_fv.
  - inversion H; subst.
    apply nodup_map_union_inv in H0; try apply NoDup_pat_fv.
    destruct H0.
    split_all; eauto.
    intros.
    rewrite !in_map_iff. setoid_rewrite H7. reflexivity.
  - inversion H; subst. 
    assert (Hn:=H0).
    apply nodup_map_union_inv in H0; destruct_all;
    [| apply NoDup_pat_fv | repeat (constructor; auto)].
    split; eauto.
    eapply nodup_map_union_inv' in Hn;
    [| apply NoDup_pat_fv | repeat (constructor; auto)|].
    intro C.
    apply Hn. split. apply C. simpl; auto.
    simpl. 
    intros. intro C; destruct_all; subst; try contradiction.
Qed.

End PatUniq.

(*We use ty_subst' because not all type variables may be substituted*)

Require Import Alpha.

Section TySubst.

Variable (params: list typevar) (tys: list vty).

Notation ty_subst_var := (ty_subst_var params tys).

(*Substitute types in patterns, terms, and formulas*)

Fixpoint ty_subst_p (p: pattern) : pattern :=
  match p with
  | Pvar x => Pvar (ty_subst_var x)
  | Pconstr f args ps => Pconstr f (ty_subst_list' params tys args)
    (map ty_subst_p ps)
  | Pwild => Pwild
  | Por p1 p2 => Por (ty_subst_p p1) (ty_subst_p p2)
  | Pbind p x => Pbind (ty_subst_p p) (ty_subst_var x)
  end.

Fixpoint ty_subst_tm  (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => Tvar (ty_subst_var v)
  | Tfun f args tms =>
    Tfun f (ty_subst_list' params tys args) (map ty_subst_tm tms)
  | Tlet t1 x t2 =>
    Tlet (ty_subst_tm  t1) (ty_subst_var x)
      (ty_subst_tm t2)
  | Tif f t1 t2 =>
    Tif (ty_subst_fmla f) (ty_subst_tm t1) (ty_subst_tm t2)
  | Tmatch t ty ps =>
    Tmatch (ty_subst_tm t) (ty_subst' params tys ty)
    (map (fun x => (ty_subst_p (fst x), ty_subst_tm (snd x))) ps)
  | Teps f x => Teps (ty_subst_fmla f) (ty_subst_var x)
  end
with ty_subst_fmla (f: formula) : formula :=
  match f with
  | Fpred p args tms => Fpred p (ty_subst_list' params tys args)
    (map ty_subst_tm tms)
  | Fquant q x f => Fquant q (ty_subst_var x) (ty_subst_fmla f)
  | Feq ty t1 t2 => Feq (ty_subst' params tys ty) (ty_subst_tm t1)
    (ty_subst_tm t2)
  | Fbinop b f1 f2 => Fbinop b (ty_subst_fmla f1) (ty_subst_fmla f2)
  | Fnot f => Fnot (ty_subst_fmla f)
  | Ftrue => Ftrue
  | Ffalse => Ffalse 
  | Flet t x f => Flet (ty_subst_tm t) (ty_subst_var x) (ty_subst_fmla f)
  | Fif f1 f2 f3 => Fif (ty_subst_fmla f1) (ty_subst_fmla f2)
    (ty_subst_fmla f3)
  | Fmatch t ty ps =>
   Fmatch (ty_subst_tm t) (ty_subst' params tys ty)
   (map (fun x => (ty_subst_p (fst x), ty_subst_fmla (snd x))) ps)
  end.

(*Typing*)
(*We show that if term t has type ty, then (ty_subst_t t)
  has type (ty_subst' params tys ty)*)

Context {gamma: context} (gamma_valid: valid_context gamma).
Variable (*(Hnodup: NoDup params) (Hlen: length params = length tys)*)
  (Hval: Forall (valid_type gamma) tys).

Lemma ty_subst_var_valid (v: vsymbol):
  valid_type gamma (snd v) ->
  valid_type gamma (snd (ty_subst_var v)).
Proof.
  destruct v; simpl. intros.
  apply valid_type_ty_subst'; auto.
Qed.

Lemma ty_subst_p_fv (p: pattern):
(forall x, In x (pat_fv (ty_subst_p p)) <-> In x (map ty_subst_var (pat_fv p))).
Proof.
  intros. induction p; simpl; auto; try reflexivity.
  - simpl_set. rewrite in_map_iff.
    split.
    + intros [p [Hinp Hinx]].
      revert Hinp; rewrite in_map_iff.
      intros [p' [Hpeq Hinp']]; subst.
      rewrite Forall_forall in H.
      specialize (H _ Hinp').
      destruct H. specialize (H Hinx); clear H0.
      rewrite in_map_iff in H.
      destruct H as [x' [Hx Hinx']]; subst.
      exists x'. split; auto. simpl_set.
      exists p'; auto.
    + intros [x' [Hx Hinx']]; subst.
      revert Hinx'. simpl_set. intros [p [Hinp Hinx']].
      rewrite Forall_forall in H.
      specialize (H _ Hinp). destruct H.
      clear H. rewrite in_map_iff in H0.
      prove_hyp H0.
      { exists x'. split; auto. }
      exists (ty_subst_p p); split; auto.
      rewrite in_map_iff. exists p; auto.
  - simpl_set. rewrite IHp1 IHp2.
    rewrite !in_map_iff. split; intros; destruct_all; subst.
    + exists x0. split; auto; simpl_set; auto.
    + exists x0. split; auto; simpl_set; auto.
    + simpl_set. destruct H0; [left | right]; exists x0; auto.
  - simpl_set. rewrite IHp. rewrite !in_map_iff;
    split; intros; destruct_all; subst.
    + exists x0; simpl_set; auto.
    + exists v; simpl_set; auto.
    + simpl_set. destruct H0 as [Hinx1 | [Hxv | []]]; subst;
      [left | right]; auto.
      exists x0; auto.
Qed.

Lemma ty_subst_var_fst v1 v2:
  ty_subst_var v1 = ty_subst_var v2 ->
  fst v1 = fst v2.
Proof.
  unfold ty_subst_var; intros. inversion H; subst; auto.
Qed.

(*Because patterns have the no-duplicate fv requirement in 
  constructors, we need the [pat_names_uniq] assumption*)
Lemma ty_subst_p_ty (p: pattern) (ty: vty)
  (Hp: pattern_has_type gamma p ty)
  (Hp2: pat_names_uniq p):
  pattern_has_type gamma (ty_subst_p p) (ty_subst' params tys ty).
Proof.
  generalize dependent ty.
  induction p; simpl; intros; inversion Hp; subst.
  - constructor. apply ty_subst_var_valid; auto.
  - subst sigma. rewrite ty_subst_twice; auto; [| apply s_params_Nodup].
    constructor; auto.
    + rewrite Forall_forall. intros x. rewrite in_map_iff.
      intros [y [Hy Hiny]]; subst.
      apply valid_type_ty_subst'; auto.
      rewrite Forall_forall in H4. apply H4; auto.
    + rewrite map_length; auto.
    + rewrite map_length; auto.
    + intros x. rewrite in_combine_iff; rewrite !map_length; auto.
      intros [i [Hi Hx]]. specialize (Hx Pwild vty_int); subst; simpl.
      rewrite -> !map_nth_inbound with(d2:=vty_int); try lia.
      rewrite -> map_nth_inbound with (d2:=Pwild); auto.
      rewrite Forall_forall in H.
      rewrite <- ty_subst_twice; auto; [| apply s_params_Nodup].
      apply H; [apply nth_In; auto| |].
      * simpl in Hp2. destruct Hp2.
        rewrite Forall_map in H0.
        rewrite Forall_forall in H0. apply H0. apply nth_In; auto.
      * apply (H9 (List.nth i ps Pwild,  (ty_subst (s_params f) vs (List.nth i (s_args f) vty_int)))).
        rewrite in_combine_iff; try rewrite !map_length; auto.
        exists i. split; auto. intros.
        f_equal; try apply nth_indep; auto.
        rewrite -> map_nth_inbound with (d2:=vty_int); auto; lia.
    + rewrite !map_length. intros.
      rewrite -> !map_nth_inbound with (d2:=Pwild); auto.
      rewrite !ty_subst_p_fv.
      rewrite -> !in_map_iff; intros [Hex1 Hex2]; destruct_all; subst.
      (*Here, we need the assumption - types may be same but names cannot*)
      apply ty_subst_var_fst in H8.
      simpl in Hp2.
      destruct Hp2 as [_ Hdisj].
      apply (Hdisj i j H0 H1 H2 (fst x0)).
      split; rewrite in_map_iff; [exists x1 | exists x0]; auto.
  - constructor. apply valid_type_ty_subst'; auto.
  - simpl in Hp2. destruct Hp2. destruct H0. constructor.
    + apply IHp1; auto.
    + apply IHp2; auto.
    + intros. rewrite !ty_subst_p_fv.
      rewrite !in_map_iff; split; intros; destruct_all; exists x0;
      split; auto; apply H5; auto.
  - simpl in Hp2. destruct Hp2.
    constructor.
    + rewrite ty_subst_p_fv in_map_iff; intros C; destruct_all.
      apply H0. rewrite in_map_iff. exists x; split; auto.
      apply ty_subst_var_fst; auto.
    + apply IHp; auto.
Qed.

Require Import PatternProofs.

(*Why we need [ty_rel] - it holds under substitution*)
Definition ty_rel_subst' ty ps args:
  ty_rel ty (ty_subst' ps args ty).
Proof.
  destruct ty; simpl; auto.
Qed.

(*And show that [ty_subst_p] preserves [shape_p]*)
Lemma subst_p_shape p:
  shape_p p (ty_subst_p p).
Proof.
  induction p as [| f tys1 ps1 | | |]; simpl; auto; [| rewrite IHp1 IHp2; auto].
  destruct (funsym_eq_dec f f); [| contradiction]; simpl.
  unfold ty_subst_list' at 1. rewrite !map_length !Nat.eqb_refl. simpl.
  rewrite andb_true_r.
  apply andb_true_iff. split.
  - clear. induction tys1 as [| ty1 tl1 IH]; auto.
    simpl. rewrite all2_cons ty_rel_subst' IH. reflexivity.
  - revert H. clear. induction ps1 as [| p1 t1 IH]; simpl; auto.
    intros Hall. inversion Hall; subst. rewrite all2_cons H1. auto.
Qed. 

(*Typing for terms and formulas*)
Lemma ty_subst_tf_ty (t: term) (f: formula):
  (forall ty (Hty: term_has_type gamma t ty)
    (Hp: pat_names_uniq_t t),
    term_has_type gamma (ty_subst_tm t) (ty_subst' params tys ty)) /\
  (forall (Hty: formula_typed gamma f)
    (Hp: pat_names_uniq_f f),
    formula_typed gamma (ty_subst_fmla f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  inversion Hty; subst; try solve[unfold ty_subst; simpl; constructor];
  try solve[destruct_all; constructor; auto;
    try apply ty_subst_var_valid; auto; solve[intuition auto with *]].
  (*Only Fun/Pred, Match are nontrivial*)
  - (*Function is tricky case, but simpler than pattern constr*) 
    rewrite ty_subst_twice; auto; [| apply s_params_Nodup].
    constructor; auto.
    + rewrite Forall_forall; intros.
      unfold ty_subst_list in H0.
      rewrite in_map_iff in H0. destruct H0 as [ty [Hx Hinty]]; subst.
      apply valid_type_ty_subst'; auto. rewrite Forall_forall in H4.
      apply H4; auto.
    + rewrite map_length; auto.
    + rewrite map_length; auto.
    + revert H10 H. rewrite !Forall_forall; intros.
      revert H0.
      rewrite in_combine_iff; rewrite !map_length; auto.
      intros [i [Hi Hx]]; subst. specialize (Hx tm_d vty_int); subst;
      simpl.
      rewrite -> !map_nth_inbound with (d2:=vty_int); try lia.
      rewrite -> !map_nth_inbound with (d2:=tm_d); auto.
      rewrite <- ty_subst_twice; auto; [| apply s_params_Nodup].
      apply H; auto.
      * apply nth_In; auto.
      * apply (H10 ((List.nth i l1 tm_d), (ty_subst (s_params f1) l (List.nth i (s_args f1) vty_int)))).
        rewrite in_combine_iff; [| rewrite map_length; auto].
        exists i. split; auto.
        intros. rewrite -> !map_nth_inbound with (d2:=vty_int); try lia.
        f_equal. apply nth_indep; auto.
      * rewrite Forall_map in Hp.
        rewrite Forall_forall in Hp. apply Hp. apply nth_In; auto.
  -(*Match relies on pattern typing, rest is easy - except exhaustiveness*) 
    destruct Hp as [Hpt Hallp].
    constructor; auto.
    + intros x. rewrite in_map_iff. intros [x1 [Hx Hinx1]]; subst. simpl.
      apply ty_subst_p_ty; auto. rewrite Forall_map in Hallp.
      rewrite Forall_forall in Hallp. apply Hallp; auto.
    + intros x. rewrite in_map_iff. intros [x1 [Hx Hinx1]]; subst; simpl.
      rewrite Forall_forall in H0.
      apply H0; auto.
      * rewrite in_map_iff. exists x1; auto.
      * rewrite Forall_map Forall_forall in Hallp.
        apply Hallp; auto.
    + revert H9. apply compile_bare_single_ext.
      * rewrite map_length; reflexivity.
      * apply ty_rel_subst'.
      * rewrite map_map.
        clear. induction ps as [| phd ptl IH]; simpl; auto.
        rewrite all2_cons subst_p_shape. auto.
  - (*Pred almost same as Fun*) constructor; auto.
    + rewrite Forall_forall; intros.
      unfold ty_subst_list in H0.
      rewrite in_map_iff in H0. destruct H0 as [ty [Hx Hinty]]; subst.
      apply valid_type_ty_subst'; auto. rewrite Forall_forall in H4.
      apply H4; auto.
    + rewrite map_length; auto.
    + rewrite map_length; auto.
    + revert H8 H. rewrite !Forall_forall; intros.
      revert H0.
      rewrite in_combine_iff; rewrite !map_length; auto.
      intros [i [Hi Hx]]; subst. specialize (Hx tm_d vty_int); subst;
      simpl.
      rewrite -> !map_nth_inbound with (d2:=vty_int); try lia.
      rewrite -> !map_nth_inbound with (d2:=tm_d); auto.
      rewrite <- ty_subst_twice; auto; [| apply s_params_Nodup].
      apply H; auto.
      * apply nth_In; auto.
      * apply (H8 ((nth i tms tm_d), (ty_subst (s_params p) tys0 (nth i (s_args p) vty_int)))).
        rewrite in_combine_iff; [| rewrite map_length; auto].
        exists i. split; auto.
        intros. rewrite -> !map_nth_inbound with (d2:=vty_int); try lia.
        f_equal. apply nth_indep; auto.
      * rewrite Forall_map in Hp.
        rewrite Forall_forall in Hp. apply Hp. apply nth_In; auto.
  - (*Exact same proof*) destruct Hp as [Hpt Hallp].
    constructor; auto.
    + intros x. rewrite in_map_iff. intros [x1 [Hx Hinx1]]; subst. simpl.
      apply ty_subst_p_ty; auto. rewrite Forall_map in Hallp.
      rewrite Forall_forall in Hallp. apply Hallp; auto.
    + intros x. rewrite in_map_iff. intros [x1 [Hx Hinx1]]; subst; simpl.
      rewrite Forall_forall in H0.
      apply H0; auto.
      * rewrite in_map_iff. exists x1; auto.
      * rewrite Forall_map Forall_forall in Hallp.
        apply Hallp; auto.
    + revert H8. apply compile_bare_single_ext.
      * rewrite map_length; reflexivity.
      * apply ty_rel_subst'.
      * rewrite map_map.
        clear. induction ps as [| phd ptl IH]; simpl; auto.
        rewrite all2_cons subst_p_shape. auto.
Qed.

Definition ty_subst_t_ty t := proj_tm ty_subst_tf_ty t.
Definition ty_subst_f_ty f := proj_fmla ty_subst_tf_ty f.

(*Before we can prove the reps lemma, we need a stronger
  notion of well-formedeness: no variables have any names in
  common (both bound and free).
  We call this condition [tm_wf_strong] and [fmla_wf_strong]
  *)
Definition tm_wf_strong t :=
  NoDup (map fst (tm_fv t)) /\
  NoDup (map fst (tm_bnd t)) /\
  disj (map fst (tm_fv t)) (map fst (tm_bnd t)).

Definition fmla_wf_strong f :=
  NoDup (map fst (fmla_fv f)) /\
  NoDup (map fst (fmla_bnd f)) /\
  disj (map fst (fmla_fv f)) (map fst (fmla_bnd f)).

(*However, this definition is not very useful to use in proofs,
  because it says nothing about subterms and formulas.
  Instead, we would like a stronger notion: the term/fmla is
  wf, and, for all subterms, this property holds recursively.
  Then, our proofs become much easier.
  We later show that in fact, this condition implies the
  recursive variant, so it is not really any stronger.
  Specifically, we do the following:
  1. Define the notion of a predicate holding recursively
    over patterns, terms, and formulas
  2. Define subterms and subformulas and prove that a predicate
    holding recursively is equivalent to saying that the predicate
    holds of all subterms and subformulas
  3. Define [tm_wf_strong_rec] and [fmla_wf_strong_rec], the recursive
    versions of strong wf
  4. Prove the rep lemma assuming [tm_wf_strong_rec] (the recursive
    structure makes it simpler)
  5. Prove that [tm_wf_strong] implies [tm_wf_strong_rec] by
    using (2) and proving that the wf strong property holds of all
    subterms
  6. Prove that a_convert_all_t produces a strongly wf term, if given
    a term with no duplicate free variables names
  7. Give a function that checks if the term is wf, and if not, alpha
    converts.
  8. Combine all of the above to prove that type substitution on
    the result of this function results in the rep under a change
    of type variable valuation.
    All of the wf predicates disappear from the final theorem statement.*)

(*Part 1: Define the notion of a predicate holding recursively
    over patterns, terms, and formulas*)

Ltac simpl_forall :=
  repeat match goal with
  | H: Forall ?P nil |- _ => clear H
  | H: Forall ?P (?x :: ?y) |- _ => inversion H; subst; clear H
  | H: Forall ?P (concat ?l) |- _ => rewrite Forall_concat in H
  | H: Forall ?P (map ?f ?l) |- _ => rewrite Forall_map in H
  | H: Forall ?P (?l1 ++ ?l2) |- _ => rewrite Forall_app in H;
    destruct H
  | H: Forall ?P (?l1 ++ ?l2)%list |- _ => rewrite Forall_app in H;
    destruct H
  | |- Forall ?P (map ?f ?l) => rewrite Forall_map
  end.

Notation id := Datatypes.id.

Section RecHolds.
  
Variable P_p: pattern -> Prop.
Variable P_t: term -> Prop.
Variable P_f: formula -> Prop.

(*A condition recursively holds on all subterms and subformulas*)

Fixpoint P_subpat (p: pattern) : Prop :=
  P_p p /\
  match p with
  | Pconstr _ _ ps => Forall id (map P_subpat ps)
  | Por p1 p2 => P_subpat p1 /\ P_subpat p2
  | Pbind p v => P_subpat p
  | _ => True
  end.

Fixpoint P_subtm (t: term) : Prop :=
  P_t t /\
  match t with
  | Tfun _ _ tms => Forall id (map P_subtm tms)
  | Tlet t1 _ t2 => P_subtm t1 /\ P_subtm t2
  | Tif f t1 t2 => P_subfmla f /\ P_subtm t1 /\ P_subtm t2
  | Tmatch t _ ps =>
    P_subtm t /\
    Forall id (map (fun x => P_subpat (fst x) /\ P_subtm (snd x)) ps)
  | Teps f _ => P_subfmla f
  | _ => True
  end
with P_subfmla (f: formula) : Prop :=
  P_f f /\
  match f with
  | Fpred _ _ tms => Forall id (map P_subtm tms)
  | Fquant _ _ f => P_subfmla f
  | Feq _ t1 t2 => P_subtm t1 /\ P_subtm t2
  | Fbinop _ f1 f2 => P_subfmla f1 /\ P_subfmla f2
  | Fnot f => P_subfmla f
  | Flet t1 _ f2 => P_subtm t1 /\ P_subfmla f2
  | Fif f1 f2 f3 => P_subfmla f1 /\ P_subfmla f2 /\ P_subfmla f3
  | Fmatch t _ ps =>
    P_subtm t /\
    Forall id (map (fun x => P_subpat (fst x) /\ P_subfmla (snd x)) ps)
  | _ => True
  end.

(*Part 2: Define subterms and subformulas and prove that a predicate
  holding recursively is equivalent to saying that the predicate
  holds of all subterms and subformulas*)
  
Fixpoint subpats (p: pattern) : list pattern :=
  p ::
  match p with
  | Pconstr _ _ ps => concat (map subpats ps)
  | Por p1 p2 => subpats p1 ++ subpats p2
  | Pbind p _ => subpats p
  | _ => nil
  end.

Fixpoint subterms_t (t: term) : list term :=
  t :: 
  match t with
  | Tfun _ _ tms => concat (map subterms_t tms)
  | Tlet t1 _ t2 => subterms_t t1 ++ subterms_t t2
  | Tif f t1 t2 => subterms_f f ++ subterms_t t1 ++ subterms_t t2
  | Tmatch t _ ps => subterms_t t ++ 
    concat (map (fun x => subterms_t (snd x)) ps)
  | Teps f _ => subterms_f f
  | _ => nil
  end
with subterms_f (f: formula) : list term :=
  match f with
  | Fpred _ _ tms => concat (map subterms_t tms)
  | Fquant _ _ f => subterms_f f
  | Feq _ t1 t2 => subterms_t t1 ++ subterms_t t2
  | Fbinop _ f1 f2 => subterms_f f1 ++ subterms_f f2
  | Fnot f => subterms_f f
  | Flet t1 _ f2 => subterms_t t1 ++ subterms_f f2
  | Fif f1 f2 f3 => subterms_f f1 ++ subterms_f f2 ++ subterms_f f3
  | Fmatch t _ ps =>
    subterms_t t ++
    concat (map (fun x => subterms_f (snd x)) ps)
  | _ => nil
  end.

Fixpoint subfmla_t (t: term) : list formula :=
  match t with
  | Tfun _ _ tms => concat (map subfmla_t tms)
  | Tlet t1 _ t2 => subfmla_t t1 ++ subfmla_t t2
  | Tif f t1 t2 => subfmla_f f ++ subfmla_t t1 ++ subfmla_t t2
  | Tmatch t _ ps => subfmla_t t ++ 
    concat (map (fun x => subfmla_t (snd x)) ps)
  | Teps f _ => subfmla_f f
  | _ => nil
  end
with subfmla_f (f: formula) : list formula :=
  f ::
  match f with
  | Fpred _ _ tms => concat (map subfmla_t tms)
  | Fquant _ _ f => subfmla_f f
  | Feq _ t1 t2 => subfmla_t t1 ++ subfmla_t t2
  | Fbinop _ f1 f2 => subfmla_f f1 ++ subfmla_f f2
  | Fnot f => subfmla_f f
  | Flet t1 _ f2 => subfmla_t t1 ++ subfmla_f f2
  | Fif f1 f2 f3 => subfmla_f f1 ++ subfmla_f f2 ++ subfmla_f f3
  | Fmatch t _ ps =>
    subfmla_t t ++
    concat (map (fun x => subfmla_f (snd x)) ps)
  | _ => nil
  end.

Fixpoint subpat_t (t: term) : list pattern :=
  match t with
  | Tfun _ _ tms => concat (map subpat_t tms)
  | Tlet t1 _ t2 => subpat_t t1 ++ subpat_t t2
  | Tif f t1 t2 => subpat_f f ++ subpat_t t1 ++ subpat_t t2
  | Tmatch t _ ps => subpat_t t ++ 
    concat (map (fun x => subpats (fst x) ++ subpat_t (snd x)) ps)
  | Teps f _ => subpat_f f
  | _ => nil
  end
with subpat_f (f: formula) : list pattern :=
  match f with
  | Fpred _ _ tms => concat (map subpat_t tms)
  | Fquant _ _ f => subpat_f f
  | Feq _ t1 t2 => subpat_t t1 ++ subpat_t t2
  | Fbinop _ f1 f2 => subpat_f f1 ++ subpat_f f2
  | Fnot f => subpat_f f
  | Flet t1 _ f2 => subpat_t t1 ++ subpat_f f2
  | Fif f1 f2 f3 => subpat_f f1 ++ subpat_f f2 ++ subpat_f f3
  | Fmatch t _ ps =>
    subpat_t t ++
    concat (map (fun x => subpats (fst x) ++ subpat_f (snd x)) ps)
  | _ => nil
  end.
  
Lemma Forall_apply {A: Type} {P Q: A -> Prop} {l}:
  Forall P l ->
  Forall (fun x => P x -> Q x) l ->
  Forall Q l.
Proof.
  rewrite !Forall_forall; intros; auto.
Qed.

Lemma Forall_impl_in  {A: Type} {P Q: A -> Prop} {l}:
(forall x, In x l -> P x -> Q x) ->
Forall P l ->
Forall Q l.
Proof.
  rewrite !Forall_forall; intros; auto.
Qed.

Lemma P_sub_pat_equiv1 p (Hsub: P_subpat p):
  Forall P_p (subpats p).
Proof.
  induction p; simpl in *; destruct_all; try solve[repeat (constructor; auto)].
  - constructor; auto. rewrite -> Forall_concat, Forall_map.
    rewrite Forall_map in H1.
    apply Forall_apply in H; auto.
  - constructor; auto. rewrite Forall_app; split; auto.
Qed.

Lemma P_sub_equiv1 t f: 
  (forall (Hsub: P_subtm t), Forall P_t (subterms_t t) /\
  Forall P_f (subfmla_t t) /\ Forall P_p (subpat_t t)) /\
  (forall (Hsub: P_subfmla f), Forall P_t (subterms_f f) /\
  Forall P_f (subfmla_f f) /\ Forall P_p (subpat_f f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros;
  destruct_all; try solve[split_all; repeat (constructor; auto)];
  try solve[intuition; try constructor; auto; rewrite !Forall_app; auto ].
  - rewrite Forall_map in H1.
    apply Forall_apply in H; auto; split_all; [constructor; auto | |];
    rewrite -> !Forall_concat, !Forall_map;
    revert H; apply Forall_impl; intros a Hall; apply Hall.
  - rewrite Forall_map in H3.
    apply Forall_apply in H0; [|revert H3; rewrite Forall_map; apply Forall_impl;
      intros a Ha; apply Ha].
    intuition; try constructor; auto; rewrite !Forall_app; split_all; auto;
    rewrite -> Forall_concat, Forall_map; revert H0; rewrite Forall_map; 
    apply Forall_impl_in;
    intros a Hina Ha; try rewrite Forall_app; try split; auto; try apply Ha.
    apply P_sub_pat_equiv1. rewrite Forall_forall in H3; apply H3; auto.
  - rewrite Forall_map in H1.
    apply Forall_apply in H; auto; split_all; [|constructor; auto |];
    rewrite -> !Forall_concat, !Forall_map;
    revert H; apply Forall_impl; intros a Hall; apply Hall.
  - rewrite Forall_map in H3.
    apply Forall_apply in H0; [|revert H3; rewrite Forall_map; apply Forall_impl;
      intros a Ha; apply Ha].
    intuition; try constructor; auto; rewrite !Forall_app; split_all; auto;
    rewrite -> Forall_concat, Forall_map; revert H0; rewrite Forall_map; 
    apply Forall_impl_in;
    intros a Hina Ha; try rewrite Forall_app; try split; auto; try apply Ha.
    apply P_sub_pat_equiv1. rewrite Forall_forall in H3; apply H3; auto.
Qed.



Lemma P_sub_pat_equiv2 p (Hp: Forall P_p (subpats p)):
  P_subpat p.
Proof.
  induction p; simpl in *; simpl_forall; split; auto; simpl_forall.
  repeat (apply Forall_apply in H; auto).
Qed.

Lemma P_sub_equiv2 t f: 
  (forall (Ht: Forall P_t (subterms_t t))
    (Hf: Forall P_f (subfmla_t t))
    (Hp: Forall P_p (subpat_t t)),
    P_subtm t) /\
  (forall (Ht: Forall P_t (subterms_f f))
    (Hf: Forall P_f (subfmla_f f))
    (Hp: Forall P_p (subpat_f f)),
    P_subfmla f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros;
  simpl_forall; split; auto; simpl_forall.
  (*Much easier to automate*)
  - simpl_forall.
    repeat (apply Forall_apply in H; auto).
  - split; simpl_forall; auto.
    apply Forall_and.
    + revert H5. apply Forall_impl. intros. simpl_forall.
      apply P_sub_pat_equiv2; auto.
    + do 3(apply Forall_apply in H0; auto); auto.
      revert H5. apply Forall_impl. intros. simpl_forall; auto.
  - simpl_forall.
    repeat (apply Forall_apply in H; auto).
  - split; simpl_forall; auto.
    apply Forall_and.
    + revert H5. apply Forall_impl. intros. simpl_forall.
      apply P_sub_pat_equiv2; auto.
    + do 3(apply Forall_apply in H0; auto); auto.
      revert H5. apply Forall_impl. intros. simpl_forall; auto.
Qed.

(*And the corollaries*)
Lemma P_subterms_equiv t:
  P_subtm t <-> 
  Forall P_t (subterms_t t) /\
  Forall P_f (subfmla_t t) /\ 
  Forall P_p (subpat_t t).
Proof.
  split.
  - apply (proj_tm P_sub_equiv1 t).
  - intros [Ht [Hf Hp]]. apply (proj_tm P_sub_equiv2 t); auto.
Qed.

Lemma P_subfmlas_equiv f:
  P_subfmla f <-> 
  Forall P_t (subterms_f f) /\
  Forall P_f (subfmla_f f) /\ 
  Forall P_p (subpat_f f).
Proof.
  split.
  - apply (proj_fmla P_sub_equiv1 f).
  - intros [Ht [Hf Hp]]. apply (proj_fmla P_sub_equiv2 f); auto.
Qed.

End RecHolds.

(*Part 3: Define [tm_wf_strong_rec] and [fmla_wf_strong_rec], 
  the recursive versions of strong wf*)

Definition tm_wf_strong_rec := P_subtm
  (fun _ => True) tm_wf_strong fmla_wf_strong.

Definition fmla_wf_strong_rec := P_subfmla
(fun _ => True) tm_wf_strong fmla_wf_strong.

(*These imply [pat_names_uniq_t/f]*)

Lemma wf_strong_pat_names t f:
  (forall (ty: vty) (Hty: term_has_type gamma t ty)
    (Hwf: tm_wf_strong_rec t), pat_names_uniq_t t) /\
  (forall (Hty: formula_typed gamma f)
    (Hwf: fmla_wf_strong_rec f), pat_names_uniq_f f).
Proof.
  unfold tm_wf_strong_rec, fmla_wf_strong_rec.
  revert t f; apply term_formula_ind; simpl; auto;
  cbn; intros; inversion Hty; subst; destruct_all; simpl_forall; 
  split_all; eauto.
  - rewrite Forall_map.
    revert H. apply Forall_impl_in; intros.
    destruct (In_nth _ _ tm_d H) as [i [Hi Hx]]; subst.
    rewrite Forall_forall in H10.
    apply specialize_combine with(d1:=tm_d)(d2:=vty_int)(i:=i) in H10;
    auto; [| rewrite map_length; auto].
    simpl in H10.
    eapply H2. apply H10. rewrite Forall_forall in H1; apply H1;
    auto.
  - rewrite Forall_map.
    apply Forall_and. 
    + (*Lots of unfolding to show that the pat fvs are actually NoDup*) 
      unfold tm_wf_strong in H1. simpl in H1. 
      destruct_all. rewrite map_app in H5.
      rewrite NoDup_app_iff in H5.
      destruct_all.
      rewrite concat_map in H10.
      rewrite NoDup_concat_iff in H10.
      destruct_all.
      rewrite Forall_forall. intros.
      eapply pat_names_uniq_nodup.
      apply H6; auto.
      rewrite !map_map in H10.
      specialize (H10 (map fst (pat_fv x.1 ++ tm_bnd x.2)%list)).
      prove_hyp H10.
      {
        rewrite in_map_iff. eexists; split; [reflexivity | auto].
      }
      rewrite map_app in H10.
      rewrite NoDup_app_iff in H10.
      apply H10.
    + (*easier*)
      revert H0. apply Forall_impl_in; intros.
      eapply H5. apply H8; auto.
      rewrite Forall_forall in H3; apply H3; auto.
  - (*pred same as fun*)
    rewrite Forall_map.
    revert H. apply Forall_impl_in; intros.
    destruct (In_nth _ _ tm_d H) as [i [Hi Hx]]; subst.
    rewrite Forall_forall in H8.
    apply specialize_combine with(d1:=tm_d)(d2:=vty_int)(i:=i) in H8;
    auto; [| rewrite map_length; auto].
    simpl in H8.
    eapply H2. apply H8. rewrite Forall_forall in H1; apply H1;
    auto.
  - (*Match same*)
    rewrite Forall_map.
    apply Forall_and.
    + (*Lots of unfolding to show that the pat fvs are actually NoDup*) 
      unfold fmla_wf_strong in H1. simpl in H1. 
      destruct_all. rewrite map_app in H5.
      rewrite NoDup_app_iff in H5.
      destruct_all.
      rewrite concat_map in H10.
      rewrite NoDup_concat_iff in H10.
      destruct_all.
      rewrite Forall_forall. intros.
      eapply pat_names_uniq_nodup.
      apply H6; auto.
      rewrite !map_map in H10.
      specialize (H10 (map fst (pat_fv x.1 ++ fmla_bnd x.2)%list)).
      prove_hyp H10.
      {
        rewrite in_map_iff. eexists; split; [reflexivity | auto].
      }
      rewrite map_app in H10.
      rewrite NoDup_app_iff in H10.
      apply H10.
    + (*easier*)
      revert H0. apply Forall_impl_in; intros.
      eapply H5. apply H7; auto.
      rewrite Forall_forall in H3; apply H3; auto.
Qed.
  
Definition wf_strong_pat_names_t t := proj_tm wf_strong_pat_names t.
Definition wf_strong_pat_names_f f := proj_fmla wf_strong_pat_names f.

(*Part 4 (the most difficult part):
  Prove the rep lemma assuming [tm_wf_strong_rec]*)

Variable (params_len: length params = length tys)
  (params_nodup: NoDup params).

(*First, we need to prove the lemmas for [match_val_single].
  These are annoyingly different than the lemmas we need
  for [_change_vt]. They are hard to prove*)

Lemma is_vty_adt_cons_none ts a1 a2:
  is_vty_adt gamma (vty_cons ts a1) = None <->
  is_vty_adt gamma (vty_cons ts a2) = None.
Proof.
  unfold is_vty_adt.
  destruct (find_ts_in_ctx gamma ts); try reflexivity.
  destruct p. split; discriminate.
Qed.

Lemma constr_pat_is_vty_adt_none {f tys1 tys2 ps1 ps2 ty1 ty2}
  (Hp1: pattern_has_type gamma (Pconstr f tys1 ps1) ty1)
  (Hp2: pattern_has_type gamma (Pconstr f tys2 ps2) ty2):
  is_vty_adt gamma ty1 = None <->
  is_vty_adt gamma ty2 = None.
Proof.
  inversion Hp1; inversion Hp2; subst.
  destruct H11 as [m [a [m_in [a_in f_in]]]].
  pose proof (adt_constr_ret gamma_valid m_in a_in f_in).
  rewrite H.
  subst sigma sigma0.
  rewrite !ty_subst_cons. apply is_vty_adt_cons_none.
Qed.

Lemma constr_pat_is_vty_adt_some {f tys1 ps1 ps2 ty1 ty2}
  m a vs
  (Hp1: pattern_has_type gamma (Pconstr f tys1 ps1) ty1)
  (Hp2: pattern_has_type gamma 
    (Pconstr f (ty_subst_list' params tys tys1) ps2) ty2):
  is_vty_adt gamma ty1 = Some (m, a, vs)  ->
  is_vty_adt gamma ty2 = Some (m, a, ty_subst_list' params tys vs).
Proof.
  inversion Hp1; inversion Hp2; subst.
  destruct H11 as [m1 [a1 [m_in1 [a_in1 f_in1]]]].
  pose proof (adt_constr_ret gamma_valid m_in1 a_in1 f_in1).
  rewrite H.
  subst sigma sigma0.
  rewrite !ty_subst_cons.
  simpl.
  destruct (find_ts_in_ctx gamma (adt_name a1)) eqn : Hts; try discriminate.
  destruct p as [m2 a2].
  intros. inversion H0; subst.
  f_equal. f_equal.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  unfold ty_subst_list'.
  rewrite -map_comp.
  rewrite -> !map_nth_inbound with (d2:=vty_int);
  try rewrite map_length; auto.
  rewrite -> !map_nth_inbound with (d2:=EmptyString); auto. simpl.
  rewrite ty_subst_twice; auto.
  apply s_params_Nodup.
Qed.

Lemma constr_pat_adt_args {f tys1 ps1 ty1}
  m a vs
  (Hp1: pattern_has_type gamma (Pconstr f tys1 ps1) ty1):
  is_vty_adt gamma ty1 = Some (m, a, vs) ->
  vs = tys1.
Proof.
  inversion Hp1; subst.
  destruct H11 as [m1 [a1 [m_in1 [a_in1 f_in1]]]].
  pose proof (adt_constr_ret gamma_valid m_in1 a_in1 f_in1).
  rewrite H.
  subst sigma.
  rewrite !ty_subst_cons.
  intros.
  apply is_vty_adt_some in H0.
  destruct_all.
  inversion H0; subst.
  pose proof (adt_constr_params gamma_valid m_in1 a_in1 f_in1).
  rewrite H9.
  apply list_eq_ext'; rewrite !map_length; rewrite <- H9; auto.
  intros n d Hn.
  rewrite -> !map_nth_inbound with (d2 := vty_int); [| rewrite map_length; auto].
  rewrite -> map_nth_inbound with (d2:=EmptyString); auto.
  unfold ty_subst; simpl.
  rewrite -> ty_subst_fun_nth with(s:=s_int); auto. apply nth_indep; lia.
  apply s_params_Nodup.
Qed.

Lemma match_val_single_change_ty pd vt (ty1 ty2: vty) 
  (p: pattern)
  (Hp1: pattern_has_type gamma p ty1)
  (Hp2: pattern_has_type gamma p ty2)
  (Heq: ty1 = ty2)
  d:
  match_val_single gamma_valid pd vt ty1 p Hp1 d =
  match_val_single gamma_valid pd vt ty2 p Hp2 (dom_cast (dom_aux pd) (f_equal (v_subst vt) Heq) d).
Proof.
  subst. simpl. unfold dom_cast. simpl. apply match_val_single_irrel.
Qed.

(*First:if we cast d, it does not change whether the
  match succeeds or not. The dependent types make this
  very difficult to prove*)   
(*NEED to use regular rewrite (rewrite ->) - ssreflect
  rewrite gives additional shelved goals and leads to Qed that
  doesn't work*)
Lemma match_val_single_ty_subst_none pd vt (ty: vty) 
  (p: pattern)
  (Hp1: pattern_has_type gamma p ty)
  (Hp2: pattern_has_type gamma (ty_subst_p p) (ty_subst' params tys ty))
  (Heq: v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty = 
    v_subst vt (ty_subst' params tys ty))
  (d: domain (dom_aux pd) (v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty)):
  match_val_single gamma_valid pd vt (ty_subst' params tys ty) 
    (ty_subst_p p) Hp2
    (dom_cast (dom_aux pd) Heq d) = None <->
  match_val_single gamma_valid pd 
    (vt_with_args vt params (map (v_subst vt) tys)) ty p Hp1 d = None.
Proof.
  revert ty vt Hp1 Hp2 Heq d.
  induction p; intros; auto; try reflexivity.
  - split; intros C; inversion C.
  - (*constructor case is hard*)
    rewrite -> !match_val_single_rewrite.
    revert Hp2. cbn. intros.
    generalize dependent (@is_vty_adt_some gamma (ty_subst' params tys ty)).
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq gamma gamma_valid (ty_subst' params tys ty)).
    generalize dependent (@adt_vty_length_eq gamma gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid (ty_subst' params tys ty)).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt1.
    2: {
      (*Show that both are none from constr assumption*)
      assert (Hisadt2: is_vty_adt gamma (ty_subst' params tys ty) = None); [|rewrite -> Hisadt2; intros; reflexivity].
      apply (constr_pat_is_vty_adt_none Hp1 Hp2). apply Hisadt1.
    }
    destruct p as [[m1 a1] vs1].
    assert (Hvs1: vs1 = vs). {
      apply (constr_pat_adt_args _ _ _ Hp1) in Hisadt1. auto.
    }
    (*Now show that other is Some with same m , a, related vs*)
    assert (Hisadt2:=Hisadt1).
    apply (constr_pat_is_vty_adt_some _ _ _ Hp1 Hp2) in Hisadt2.
    rewrite -> Hisadt2.
    intros Hvslen1 Hvslen2 Hvslen3 Hvslen4 Hadtspec1 Hadtspec2.
    destruct (Hadtspec1 m1 a1 vs1 Logic.eq_refl) as [Hty1 [a_in m_in]].
    destruct (Hadtspec2 m1 a1 (ty_subst_list' params tys vs1) Logic.eq_refl)
    as [Hty2 [a_in' m_in']].
    (*We can do a bit of simplification*)
    assert (a_in = a_in') by (apply bool_irrelevance).
    assert (m_in = m_in') by (apply bool_irrelevance).
    subst m_in' a_in'; simpl.
    generalize dependent (eq_trans (map_length (v_subst vt) (ty_subst_list' params tys vs1))
    (Hvslen4 m1 a1 (ty_subst_list' params tys vs1) erefl
       (pat_has_type_valid gamma
          (Pconstr f (ty_subst_list' params tys vs) (map ty_subst_p ps))
          (ty_subst' params tys ty) Hp2))).
    generalize dependent (eq_trans
    (map_length (v_subst (vt_with_args vt params (map (v_subst vt) tys))) vs1)
    (Hvslen3 m1 a1 vs1 erefl
       (pat_has_type_valid gamma (Pconstr f vs ps) ty Hp1))) .
    intros.
    clear Hvslen3 Hvslen4.
    (*We need to know things about the [find_constr_rep]. *)
    case_find_constr.
    intros [f1 [[x_in1 args1] Hcast1]] [f2 [[x_in2 args2] Hcast2]]; simpl in *;
    subst.
    (*Finally, a reasonable goal*)
    rewrite dom_cast_compose in Hcast2.
    rewrite -> !eq_trans_refl_l in Hcast1.
    assert (Heq2: map (v_subst vt) (ty_subst_list' params tys vs) =
    map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) vs). {
      unfold ty_subst_list'.
      apply list_eq_ext'; rewrite -> !map_length; auto.
      intros n d' Hn.
      rewrite -> !map_nth_inbound with (d2:=vty_int); try rewrite -> map_length; auto.
      apply v_subst_vt_with_args'; auto.
    }
    (*Now we can relate the two constr_reps*)
    assert (
      constr_rep gamma_valid m1 m_in
           (map (v_subst vt) (ty_subst_list' params tys vs)) e0 
           (dom_aux pd) a1 a_in f2 x_in2
           (adts pd m1 (map (v_subst vt) (ty_subst_list' params tys vs))) args2 =
      scast (f_equal 
      (fun x => adt_rep m1 x (dom_aux pd) a1 a_in) (Logic.eq_sym Heq2)) 
      (constr_rep gamma_valid m1 m_in
      (map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) vs) e
      (dom_aux pd) a1 a_in f1 x_in1
      (adts pd m1
         (map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) vs))
      args1)
    ).
    {
      rewrite <- Hcast1, <- Hcast2. unfold dom_cast.
      rewrite -> !scast_scast.
      apply scast_eq_uip.
    }
    clear Hcast1 Hcast2.
    (*Now, we first show that f1 = f2*)
    assert (f1 = f2). {
      (*Get rid of cast in H0 - cant' do in general bc of dep types*)
      generalize dependent (map (v_subst vt) (ty_subst_list' params tys vs)).
      intros; subst; simpl in H0.
      assert (e = e0). apply UIP_dec. apply Nat.eq_dec.
      subst.
      (*Now, we show that if x <> x0, this contradicts disjointness*)
      destruct (funsym_eq_dec f1 f2); subst; auto.
      exfalso. 
      apply (constr_rep_disjoint gamma_valid m1 m_in _ e0 (dom_aux pd) a1
      a_in _ args1 args2 (ltac:(auto)) (Logic.eq_sym H0)).
    }
    subst.
    assert (x_in2 = x_in1) by (apply bool_irrelevance); subst.
    (*And now we can show that a1 = a2 (with casting)*)
    assert (args1 = cast_arg_list (f_equal (sym_sigma_args f2) Heq2) args2). {
      (*Get rid of cast in H0 - cant' do in general bc of dep types*)
      generalize dependent (map (v_subst vt) (ty_subst_list' params tys vs)).
      intros; subst; simpl in H0.
      assert (e = e0). apply UIP_dec. apply Nat.eq_dec.
      subst.
      (*Now we use injectivity of constructors (knowing that f1 = f2)*)
      simpl. unfold cast_arg_list. simpl.
      apply (constr_rep_inj) in H0; auto.
      apply (gamma_all_unif gamma_valid); auto.
    }
    subst.
    (*Now that we know all of this information, we can simplify for induction*)
    destruct (funsym_eq_dec f2 f); try reflexivity. subst.
    (*Deal with Hvslen1*)
    repeat match goal with
    | |- context [sym_sigma_args_map ?vt ?f ?vs ?H] => generalize dependent H
    end.
    intros.
    clear Hvslen1 Hvslen2. simpl.
    rewrite -> cast_arg_list_compose.
    (*Only want 1 cast in induction*)
    repeat match goal with
    | |- context [cast_arg_list ?H ?a] => generalize dependent H
    end.
    intros.
    assert (cast_arg_list e4 args2 = cast_arg_list (eq_trans (Logic.eq_sym e3) e4) (cast_arg_list e3 args2)).
    {  rewrite -> !cast_arg_list_compose. apply cast_arg_list_eq. }
    rewrite -> H1. clear H1.
    generalize dependent (cast_arg_list e3 args2).
    generalize dependent (eq_trans (Logic.eq_sym e3) e4).
    clear e3 e4 e1 e2. intros ? a3. clear H0 args2.
    (*Now generalize for induction*)
    match goal with
    | |- (iter_arg_list ?val ?pd ?l1 ?a1 ?ps1 ?H1 = None) <->
      iter_arg_list ?val ?pd ?l2 ?a2 ?ps2 ?H2 = None =>
      generalize dependent H1;
      generalize dependent H2
    end.
    unfold sym_sigma_args in *.
    assert (Hlenvs: length vs = length (s_params f)). {
      inversion Hp1; subst; auto.
    }
    clear Hadtspec1 Hadtspec2 Hisadt1 Hisadt2 Hp1 Hp2.
    generalize dependent ps.
    generalize dependent a3.
    clear -Hlenvs params_len params_nodup.
    generalize dependent (s_args f).
    induction l; intros; simpl.
    + destruct ps; reflexivity.
    + destruct ps; try reflexivity.
      simpl.
      inversion H; subst.
      symmetry. split; case_match_hyp; try solve[intro C; inversion C];
      intros _; case_match_goal.
      * exfalso. rewrite -> hlist_tl_cast in Hmatch2.
        inversion f0; subst.
        (*Why doesn't Coq let me name this: has f and*)
        rewrite <- (IHl (cons_inj_tl e1) (hlist_tl a3) ps (Forall_inv_tail H)
          (Forall_inv_tail f0) (Forall_inv_tail f1)) in Hmatch0.
        assert (Some l2 = None); [|discriminate].
        rewrite <- Hmatch2, <- Hmatch0. (*rewriting directly doesn't work*) 
        reflexivity.
        
      * exfalso.
        rewrite -> hlist_hd_cast with (Heq2:=cons_inj_hd e1) in Hmatch0.
        rewrite -> rewrite_dom_cast in Hmatch0.
        (*Need one more typecast*)
        assert (Heqty: (ty_subst' params tys (ty_subst (s_params f) vs a)) =
        (ty_subst (s_params f) (ty_subst_list' params tys vs) a) ). {
          apply ty_subst_twice; auto. apply s_params_Nodup.
        }
        assert (Htyp: pattern_has_type gamma (ty_subst_p p)
        (ty_subst' params tys (ty_subst (s_params f) vs a))).
        {
          inversion f1; subst; auto. simpl in *.
          rewrite -> ty_subst_twice; auto. apply s_params_Nodup.
        }
        rewrite <- H2 with(Heq:=
        (eq_trans (cons_inj_hd e1) (f_equal (v_subst vt) 
          (Logic.eq_sym Heqty)))) (Hp2:=Htyp) in Hmatch.
        rewrite -> match_val_single_change_ty with 
          (Heq:=(Logic.eq_sym (Heqty)))(Hp2:=Htyp) in Hmatch0.
        rewrite -> !dom_cast_compose in Hmatch0.
        assert (Some l0 = None);[|discriminate].
        rewrite <- Hmatch0, <- Hmatch; reflexivity.
      * exfalso. 
        rewrite -> hlist_tl_cast in Hmatch0.
        inversion f0; subst.
        rewrite -> IHl in Hmatch0; auto.
        assert (C: Some l2 = None); [|inversion C].
        rewrite <- Hmatch2, <- Hmatch0. (*Why can't I rewrite directly?*) 
        reflexivity.
      * exfalso. rewrite -> hlist_hd_cast with (Heq2:=cons_inj_hd e1) in Hmatch.
        rewrite -> rewrite_dom_cast in Hmatch.
        assert (Heqty: (ty_subst' params tys (ty_subst (s_params f) vs a)) =
        (ty_subst (s_params f) (ty_subst_list' params tys vs) a) ). {
          apply ty_subst_twice; auto. apply s_params_Nodup.
        }
        assert (Hpty: pattern_has_type gamma (ty_subst_p p)
        (ty_subst' params tys (ty_subst (s_params f) vs a))).
        {
          inversion f1; subst; simpl in H4.
          rewrite -> ty_subst_twice; auto.
          apply s_params_Nodup.
        }
        rewrite -> match_val_single_change_ty with 
          (Heq:=(Logic.eq_sym (Heqty)))(Hp2:=Hpty) in Hmatch.
        rewrite -> !dom_cast_compose in Hmatch.
        rewrite -> H2 with(Hp2:=Hpty) in Hmatch.
        assert (C: Some l0 = None); [|inversion C].
        rewrite <- Hmatch0, <- Hmatch. reflexivity.
  - (*Por case*)
    simpl. 
    split; case_match_hyp; try solve[intro C; inversion C].
    + rewrite -> IHp2. intros Hm; rewrite -> Hm.
      rewrite -> IHp1 in Hmatch. rewrite -> Hmatch. reflexivity.
      Unshelve. all: inversion Hp1; subst; auto.
    + rewrite <- IHp2. intros Hm; rewrite -> Hm.
      rewrite <- IHp1 in Hmatch. rewrite -> Hmatch. reflexivity.
      Unshelve. all: inversion Hp2; subst; auto.
  - (*Pbind case*)
    simpl.
    split; case_match_hyp; try solve[intro C; inversion C]; intros _.
    + rewrite -> IHp in Hmatch. rewrite -> Hmatch. reflexivity.
    + rewrite <- IHp in Hmatch. rewrite -> Hmatch. reflexivity.
Qed. 

Ltac inv H := inversion H; subst; clear H.

Lemma match_val_single_ty_subst_some pd vt (ty: vty) 
  (p: pattern)
  (Hp1: pattern_has_type gamma p ty)
  (Hp2: pattern_has_type gamma (ty_subst_p p) (ty_subst' params tys ty))
  (Heq: v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty = 
    v_subst vt (ty_subst' params tys ty))
  (d: domain (dom_aux pd) (v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty))
  l1 l2:
  match_val_single gamma_valid pd vt (ty_subst' params tys ty) 
    (ty_subst_p p) Hp2
    (dom_cast (dom_aux pd) Heq d) = Some l1 ->
  match_val_single gamma_valid pd 
    (vt_with_args vt params (map (v_subst vt) tys)) ty p Hp1 d = Some l2 ->
  forall x y,
  In (x, y) l2 ->
  exists z Heq,
    In (ty_subst_var x, z) l1 /\
    projT2 z = dom_cast (dom_aux pd) Heq (projT2 y).
Proof.
  revert ty vt Hp1 Hp2 Heq d l1 l2.
  induction p; intros ty vt Hp1 Hp2 Heq d l1 l2; auto.
  - (*Pvar (base case)*) simpl; intros.
    inv H; inv H0. simpl in *. destruct H1 as [Hxy | []]. inv Hxy.
    simpl. exists ( existT (domain (dom_aux pd)) (v_subst vt (ty_subst' params tys ty))
    (dom_cast (dom_aux pd) Heq d)).
    simpl.
    exists (Logic.eq_sym (v_subst_vt_with_args' params tys params_len params_nodup vt ty)).
    split; auto. apply dom_cast_eq.
  - (*Pconstr - hard case*)
     (*constructor case is hard*)
    rewrite -> !match_val_single_rewrite.
    revert Hp2. cbn. intros Hp2. 
    generalize dependent (@is_vty_adt_some gamma (ty_subst' params tys ty)).
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq gamma gamma_valid (ty_subst' params tys ty)).
    generalize dependent (@adt_vty_length_eq gamma gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid (ty_subst' params tys ty)).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt1.
    2: {
      (*Show that both are none from constr assumption*)
      assert (Hisadt2: is_vty_adt gamma (ty_subst' params tys ty) = None); [|discriminate].
      apply (constr_pat_is_vty_adt_none Hp1 Hp2). apply Hisadt1.
    }
    destruct p as [[m1 a1] vs1].
    assert (Hvs1: vs1 = vs). {
      apply (constr_pat_adt_args _ _ _ Hp1) in Hisadt1. auto.
    }
    (*Now show that other is Some with same m , a, related vs*)
    assert (Hisadt2:=Hisadt1).
    apply (constr_pat_is_vty_adt_some _ _ _ Hp1 Hp2) in Hisadt2.
    rewrite -> Hisadt2.
    intros Hvslen1 Hvslen2 Hvslen3 Hvslen4 Hadtspec1 Hadtspec2.
    destruct (Hadtspec1 m1 a1 vs1 Logic.eq_refl) as [Hty1 [a_in m_in]].
    destruct (Hadtspec2 m1 a1 (ty_subst_list' params tys vs1) Logic.eq_refl)
    as [Hty2 [a_in' m_in']].
    (*We can do a bit of simplification*)
    assert (a_in = a_in') by (apply bool_irrelevance).
    assert (m_in = m_in') by (apply bool_irrelevance).
    subst m_in' a_in'; simpl.
    generalize dependent (eq_trans (map_length (v_subst vt) (ty_subst_list' params tys vs1))
    (Hvslen4 m1 a1 (ty_subst_list' params tys vs1) erefl
       (pat_has_type_valid gamma
          (Pconstr f (ty_subst_list' params tys vs) (map ty_subst_p ps))
          (ty_subst' params tys ty) Hp2))).
    generalize dependent (eq_trans
    (map_length (v_subst (vt_with_args vt params (map (v_subst vt) tys))) vs1)
    (Hvslen3 m1 a1 vs1 erefl
       (pat_has_type_valid gamma (Pconstr f vs ps) ty Hp1))) .
    intros ? ?.
    clear Hvslen3 Hvslen4.
    (*We need to know things about the [find_constr_rep]. *)
    case_find_constr.
    intros [f1 [[x_in1 args1] Hcast1]] [f2 [[x_in2 args2] Hcast2]]; simpl in *;
    subst.
    (*Finally, a reasonable goal*)
    rewrite dom_cast_compose in Hcast2.
    rewrite -> !eq_trans_refl_l in Hcast1.
    assert (Heq2: map (v_subst vt) (ty_subst_list' params tys vs) =
    map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) vs). {
      unfold ty_subst_list'.
      apply list_eq_ext'; rewrite -> !map_length; auto.
      intros n d' Hn.
      rewrite -> !map_nth_inbound with (d2:=vty_int); try rewrite -> map_length; auto.
      apply v_subst_vt_with_args'; auto.
    }
    (*Now we can relate the two constr_reps*)
    assert (
      constr_rep gamma_valid m1 m_in
           (map (v_subst vt) (ty_subst_list' params tys vs)) e0 
           (dom_aux pd) a1 a_in f2 x_in2
           (adts pd m1 (map (v_subst vt) (ty_subst_list' params tys vs))) args2 =
      scast (f_equal 
      (fun x => adt_rep m1 x (dom_aux pd) a1 a_in) (Logic.eq_sym Heq2)) 
      (constr_rep gamma_valid m1 m_in
      (map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) vs) e
      (dom_aux pd) a1 a_in f1 x_in1
      (adts pd m1
         (map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) vs))
      args1)
    ).
    {
      rewrite <- Hcast1, <- Hcast2. unfold dom_cast.
      rewrite -> !scast_scast.
      apply scast_eq_uip.
    }
    clear Hcast1 Hcast2.
    (*Now, we first show that f1 = f2*)
    assert (f1 = f2). {
      (*Get rid of cast in H0 - cant' do in general bc of dep types*)
      generalize dependent (map (v_subst vt) (ty_subst_list' params tys vs)).
      intros; subst; simpl in H0.
      assert (e = e0). apply UIP_dec. apply Nat.eq_dec.
      subst.
      (*Now, we show that if x <> x0, this contradicts disjointness*)
      destruct (funsym_eq_dec f1 f2); subst; auto.
      exfalso. 
      apply (constr_rep_disjoint gamma_valid m1 m_in _ e0 (dom_aux pd) a1
      a_in _ args1 args2 (ltac:(auto)) (Logic.eq_sym H0)).
    }
    subst.
    assert (x_in2 = x_in1) by (apply bool_irrelevance); subst.
    (*And now we can show that a1 = a2 (with casting)*)
    assert (args1 = cast_arg_list (f_equal (sym_sigma_args f2) Heq2) args2). {
      (*Get rid of cast in H0 - cant' do in general bc of dep types*)
      generalize dependent (map (v_subst vt) (ty_subst_list' params tys vs)).
      intros; subst; simpl in H0.
      assert (e = e0). apply UIP_dec. apply Nat.eq_dec.
      subst.
      (*Now we use injectivity of constructors (knowing that f1 = f2)*)
      simpl. unfold cast_arg_list. simpl.
      apply (constr_rep_inj) in H0; auto.
      apply (gamma_all_unif gamma_valid); auto.
    }
    subst.
    (*Now that we know all of this information, we can simplify for induction*)
    destruct (funsym_eq_dec f2 f); [|discriminate]. subst.
    (*Deal with Hvslen1*)
    repeat match goal with
    | |- context [sym_sigma_args_map ?vt ?f ?vs ?H] => generalize dependent H
    end.
    intros ? ?.
    clear Hvslen1 Hvslen2. simpl.
    rewrite -> cast_arg_list_compose.
    (*Only want 1 cast in induction*)
    repeat match goal with
    | |- context [cast_arg_list ?H ?a] => generalize dependent H
    end.
    intros ? ?.
    assert (cast_arg_list e4 args2 = cast_arg_list (eq_trans (Logic.eq_sym e3) e4) (cast_arg_list e3 args2)).
    {  rewrite -> !cast_arg_list_compose. apply cast_arg_list_eq. }
    rewrite -> H1. clear H1.
    generalize dependent (cast_arg_list e3 args2).
    generalize dependent (eq_trans (Logic.eq_sym e3) e4).
    clear e3 e4 e1 e2. intros ? a3. clear H0 args2.
    (*Now generalize for induction*)
    match goal with
    | |- (iter_arg_list ?val ?pd ?l1 ?a1 ?ps1 ?H1 = Some _) ->
      iter_arg_list ?val ?pd ?l2 ?a2 ?ps2 ?H2 = Some _ -> _ =>
      generalize dependent H1;
      generalize dependent H2
    end.
    unfold sym_sigma_args in *.
    assert (Hlenvs: length vs = length (s_params f)). {
      inversion Hp1; subst; auto.
    }
    clear Hadtspec1 Hadtspec2 Hisadt1 Hisadt2 Hp1 Hp2.
    generalize dependent ps.
    generalize dependent a3.
    clear -Hlenvs params_len params_nodup.
    revert l1 l2.
    generalize dependent (s_args f).
    induction l; intros; revert H0 H1.
    + destruct ps; try discriminate.
      intros. inversion H0; inversion H1; subst. destruct H2. 
    + destruct ps; try discriminate. simpl.
      inversion H; subst.
      case_match_hyp; try discriminate. intro Hl; inv Hl.
      case_match_hyp; try discriminate. intro Hl; inv Hl. 
      (*Here, we actually prove the claim via the IHs. It is not hard*)
      rewrite -> in_app_iff in H2. destruct H2.
      * rewrite -> hlist_hd_cast with (Heq2:=cons_inj_hd e1) in Hmatch.
        rewrite -> rewrite_dom_cast in Hmatch.
        (*Need a cast*)
        assert (Heqty: ty_subst (s_params f) (ty_subst_list' params tys vs) a =
        ty_subst' params tys (ty_subst (s_params f) vs a)).
        {
          rewrite ty_subst_twice; auto. apply s_params_Nodup.
        }
        assert (Hp2': pattern_has_type gamma (ty_subst_p p) (ty_subst' params tys (ty_subst (s_params f) vs a))).
        {
          rewrite <- Heqty. inversion f1; subst; auto.
        }
        erewrite -> match_val_single_change_ty with
          (ty2:=(ty_subst' params tys (ty_subst (s_params f) vs a)))
          (Heq:=Heqty)  (Hp2:=Hp2')in Hmatch.
        rewrite dom_cast_compose in Hmatch.
        destruct (H3 _ _ _ _ _ _ _ _ Hmatch Hmatch1 x y H0) as [z [Heq [Hinxz Hz2]]].
        exists z. exists Heq. split; auto. rewrite in_app_iff; auto.
      * rewrite hlist_tl_cast in Hmatch0.
        destruct (IHl _ _ _ _ _ H4 _ _ Hmatch0 Hmatch2 x y H0) as [z [Heq [Hinxz Hz2]]].
        exists z. exists Heq. split; auto.
        rewrite in_app_iff; auto.
  - (*Pwild is trivial*)
    simpl. intros H1 H2; inv H1; inv H2; contradiction.
  - (*Por - just from induction and using previous lemma*) 
    simpl. case_match_hyp.
    + intros Hl; inv Hl.
      case_match_hyp.
      * intros Hl; inv Hl.
        eapply IHp1. apply Hmatch. apply Hmatch0.
      * (*Here, use contradiction from previous lemma*)
        rewrite <- match_val_single_ty_subst_none in Hmatch0.
        rewrite -> Hmatch0 in Hmatch. inversion Hmatch.
    + intros Hmatch1. case_match_hyp.
      * (*Another contradiction*) 
        rewrite -> match_val_single_ty_subst_none in Hmatch.
        rewrite -> Hmatch in Hmatch0. inversion Hmatch0.
      * eapply IHp2. apply Hmatch1.
  - (*Pbind*)
    simpl. case_match_hyp; try discriminate.
    intros Hl; inv Hl.
    case_match_hyp; try discriminate.
    intros Hl; inv Hl. simpl.
    intros x y [Hxy | Hinxy].
    + inv Hxy. simpl.
      exists (existT (domain (dom_aux pd)) (v_subst vt (ty_subst' params tys ty))
      (dom_cast (dom_aux pd) Heq d)).
      simpl.
      exists Heq. split; auto.
    + destruct (IHp _ _ _ _ _ _ _ _ Hmatch Hmatch0 x y Hinxy) as [z [Heq1 [Hinxz Hz2]]].
      exists z. exists Heq1. split; auto.
Qed.

(*And now, the rep lemma. This is hard to prove*)

(*The above works because v is bound and x is free, so
  name cannot overlap*)
  Lemma ty_subst_tf_rep {pd: pi_dom} {pf: pi_funpred gamma_valid pd}
  (t: term) (f: formula):
  (forall (vt: val_typevar) (vv1: val_vars pd vt)
    (vv2: val_vars pd (vt_with_args vt params (map (v_subst vt) tys)))
    (ty1 ty2: vty)
    (Hwf: tm_wf_strong_rec t)
    (Hty1: term_has_type gamma t ty1)
    (Hty2: term_has_type gamma (ty_subst_tm t) ty2)
    (Hvv: forall x Heq, In x (tm_fv t) -> vv2 x = dom_cast (dom_aux pd) Heq 
      (vv1 (ty_subst_var x)))
    Heq,
    (*[term_rep] version is ugly because of cast, but we mostly
      need formula version (or maybe not, see)*)
    term_rep gamma_valid pd vt pf vv1 (ty_subst_tm t) ty2 Hty2 =
    dom_cast (dom_aux pd) Heq (term_rep gamma_valid pd 
      (vt_with_args vt params (map (v_subst vt) tys)) pf
      vv2
      t ty1 Hty1)) /\
  (forall (vt: val_typevar) (vv1: val_vars pd vt) 
  (vv2: val_vars pd (vt_with_args vt params (map (v_subst vt) tys)))
    (Hwf: fmla_wf_strong_rec f)
    (Hty1: formula_typed gamma f)
    (Hty2: formula_typed gamma (ty_subst_fmla f))
    (Hvv: forall x Heq, In x (fmla_fv f) -> vv2 x = dom_cast (dom_aux pd) Heq 
      (vv1 (ty_subst_var x))),
    formula_rep gamma_valid pd vt pf vv1 (ty_subst_fmla f) Hty2 =
    formula_rep gamma_valid pd 
      (vt_with_args vt params (map (v_subst vt) tys)) pf
      vv2
      f Hty1).
Proof.
  unfold tm_wf_strong_rec, fmla_wf_strong_rec.
  revert t f. apply term_formula_ind; simpl; intros; simpl_rep_full; auto.
  - destruct c; inversion Hty1; inversion Hty2; subst; simpl_rep_full;
    unfold cast_dom_vty.
    + generalize dependent ((Logic.eq_sym (ty_constint_inv Hty1))); intros.
      assert (e = Logic.eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl. unfold dom_cast; simpl.
      generalize dependent (Logic.eq_sym (ty_constint_inv Hty2)); intros.
      assert (e = Logic.eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl.
      assert ((f_equal (domain (dom_aux pd)) Heq) = Logic.eq_refl). {
        (*NOTE: relies on UIP*)
        apply UIP.
      }
      rewrite H. reflexivity.
    + generalize dependent ((Logic.eq_sym (ty_constreal_inv Hty1))); intros.
      assert (e = Logic.eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl. unfold dom_cast; simpl.
      generalize dependent (Logic.eq_sym (ty_constreal_inv Hty2)); intros.
      assert (e = Logic.eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl.
      assert ((f_equal (domain (dom_aux pd)) Heq) = Logic.eq_refl). {
        (*NOTE: relies on UIP*)
        apply UIP.
      }
      rewrite H. reflexivity.
  - (*Variable case - more casting*)
    unfold var_to_dom.
    inversion Hty1; inversion Hty2; subst.
    rewrite Hvv. auto. intros.
    rewrite !dom_cast_compose.
    (*If we do not use upd_vv_args'', this is not provable*)
    apply dom_cast_eq. auto.
  - (*Function case - hard because of casting already and
    need nested inductive lemma for get_arg_list*)
    unfold cast_dom_vty. rewrite !dom_cast_compose.
    assert (Hmap: (map (v_subst vt) (ty_subst_list' params tys l)) =
    (map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) l)). {
      apply list_eq_ext'; rewrite !map_length; auto.
      intros n d Hn. unfold ty_subst_list'.
      rewrite !map_map.
      rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
      apply v_subst_vt_with_args'; auto.
    }
    match goal with
    | |- dom_cast ?d ?H ?x = dom_cast ?d ?H1 ?x1 =>
      generalize dependent H; 
      generalize dependent H1
    end.
    
    assert (Hargs:
    cast_arg_list (f_equal (sym_sigma_args f1) Hmap)
    (fun_arg_list pd vt f1 (ty_subst_list' params tys l) (map ty_subst_tm l1)
    (term_rep gamma_valid pd vt pf vv1) Hty2) =
    (fun_arg_list pd (vt_with_args vt params (map (v_subst vt) tys)) f1 l l1
        (term_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf
           vv2) Hty1)).
    {
      unfold fun_arg_list.
      apply get_arg_list_vt_ext with(Heq:=Hmap);
      rewrite map_length; auto.
      revert H; rewrite Forall_forall; intros.
      revert Hty0. rewrite -> map_nth_inbound with (d2:=tm_d); auto.
      intros.
      erewrite H; [|apply nth_In; auto | |].
      rewrite !dom_cast_compose. apply dom_cast_refl.
      cbn in Hwf; destruct_all.
      simpl_forall. rewrite Forall_forall in H2; apply H2; apply nth_In; auto.
      intros. apply Hvv. simpl_set.
      exists (nth i l1 tm_d); split; auto; apply nth_In; auto.
      Unshelve.
      auto.
    }
    rewrite <- Hargs.
    intros.
    rewrite <- funs_cast_eq.
    rewrite !dom_cast_compose. apply dom_cast_eq.
  - (*Tlet case*)
    assert (Heq1: v_subst (vt_with_args vt params (map (v_subst vt) tys)) v.2 =
    v_subst vt (ty_subst' params tys v.2)).
    {
      symmetry; apply v_subst_vt_with_args'; auto.
    }
    cbn in Hwf. destruct_all.
    erewrite -> H with(vv2:=vv2)(ty1:=snd v)(Heq:=Heq1)(Hty1:=(proj1' (ty_let_inv Hty1))); auto.
    assert (Heq2: v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty1 = v_subst vt ty2).
    {
      inversion Hty1; subst; inversion Hty2; subst.
      (*Use typing*)
      assert (ty2 = ty_subst' params tys ty1). {
        eapply term_has_type_unique. apply H12.
        apply ty_subst_t_ty; auto.
        eapply wf_strong_pat_names_t.
        apply H10. auto.
      }
      subst. rewrite v_subst_vt_with_args'; auto.
    }
    2: intros; apply Hvv; simpl_set; auto.
    apply H0; auto.
    intros.
    unfold tm_wf_strong in H1; simpl in H1.
    destruct_all.
    unfold substi.
    vsym_eq x v.
    {
      vsym_eq (ty_subst_var v) (ty_subst_var v).
      simpl. assert (e =Logic.eq_refl). apply UIP_dec. apply vsymbol_eq_dec.
      subst. simpl. symmetry.
      rewrite !dom_cast_compose.
      apply dom_cast_refl.
    }
    (*Idea: if x not v, cannot have same name, or else
      it contradicts strong wf assumption*)
    vsym_eq (ty_subst_var x) (ty_subst_var v).
    2: {
      rewrite Hvv; auto. simpl_set. auto.
    }
    exfalso. apply ty_subst_var_fst in e.
    apply (H6 (fst x)); split; simpl; auto.
    rewrite in_map_iff. exists x; simpl_set; auto.
  - (*Tif*)
    inversion Hty1; subst.
    inversion Hty2; subst.
    cbn in Hwf. destruct_all.
    rewrite -> H with(vv2:=vv2)(Hty1:=(proj2' (proj2' (ty_if_inv Hty1)))); auto; 
    [| intros; apply Hvv; simpl_set; auto].
    (*Ltac is being annoying and not letting me match*)
    destruct (formula_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf vv2 f
    (proj2' (proj2' (ty_if_inv Hty1))));
    [apply H0 | apply H1]; auto;
    intros; apply Hvv; simpl_set; auto.
  - (*Tmatch*)
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    cbn in Hwf. destruct Hwf as [Hwf [Hptm Hpall]].
    (*From Hwf, get info we need about bnd and free vars*)
    assert (Hbndfree: forall p t x y,
      In (p, t) ps ->
      In x (pat_fv p) ->
      In y (tm_fv t) ->
      fst x = fst y ->
      x = y).
    {
      intros p t x y Hinpt Hinx Hiny Hxy. 
      unfold tm_wf_strong in Hwf; simpl in Hwf.
      vsym_eq x y.
      destruct (in_dec vsymbol_eq_dec y (pat_fv p)).
      {
        destruct Hwf as [_ [Hwf _]].
        revert Hwf.
        rewrite -> map_app, NoDup_app_iff.
        intros [_ [Hwf _]].
        eapply NoDup_map_in. apply Hwf. all: auto;
        rewrite in_concat; eexists;
        split; try (rewrite in_map_iff);
        try (eexists; split; [reflexivity | auto]);
        try apply Hinpt;
        rewrite !in_app_iff; auto.
      }
      (*Now y not in, so can use 3rd part of Hwf*)
      destruct Hwf as [_ [_ Hwf]].
      exfalso.
      apply (Hwf (fst x)).
      rewrite map_app. split.
      - rewrite !in_map_iff. exists y.
        split; auto. simpl_set. right. exists (p, t); split; auto.
        simpl_set; auto.
      - rewrite in_app_iff. right.
        rewrite in_map_iff. exists x. split; auto.
        rewrite in_concat. eexists.
        split. rewrite in_map_iff. eexists; split; [reflexivity | auto].
        apply Hinpt. rewrite in_app_iff; auto.
    }
    clear Hwf. rewrite Forall_map in Hpall.
    induction ps; simpl; intros.
    {
      (*Trivial case*)
      generalize dependent (v_subst vt ty2).
      intros. subst. unfold dom_cast; simpl. reflexivity.
    }
    destruct a.
    inversion H0; subst.
    (*First step: handle term_rep in case*)
    assert (Heq1: v_subst (vt_with_args vt params (map (v_subst vt) tys)) v =
    v_subst vt (ty_subst' params tys v)).
    {
      symmetry; apply v_subst_vt_with_args'; auto.
    }
    erewrite -> H with(vv2:=vv2)(ty1:=v)(Hty1:=Hty1)(Heq:=Heq1);
    auto.
    2: { intros; rewrite Hvv; auto; simpl_set; auto. }
    simpl.
    case_match_goal.
    2: {
      rewrite -> match_val_single_ty_subst_none in Hmatch.
      rewrite -> Hmatch.
      rewrite <- H with(vv1:=vv1)(Hty2:=Hty2). auto. simpl. 
      apply IHps. all: auto.
      - intros. apply Hvv. simpl; simpl_set_small; auto.
        destruct H1; auto.
      - intros. apply (Hbndfree p0 t0 x y); simpl; auto.  
      - inversion Hpall; subst; auto.
      - intros. apply Hvv. simpl; simpl_set_small; auto.
    }
    symmetry.
    destruct (match_val_single gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) v p
    (Forall_inv Hpat1)
    (term_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf vv2
       tm v Hty1)) eqn : Hmatch1.
    2: {
      rewrite <- match_val_single_ty_subst_none in Hmatch1.
      rewrite -> Hmatch1 in Hmatch. inversion Hmatch.
      (*Contradiction from [match_val_single_ty_subst_none]*)
    }
    symmetry.
    apply H3.
    { apply (Forall_inv Hpall). }
    intros x Hinx Heq'.
    destruct (in_dec vsymbol_eq_dec x (pat_fv p)).
    2: {
      (*Not in: follows from Hvv*)
      rewrite !extend_val_notin; auto.
      - erewrite Hvv. reflexivity.
        simpl. simpl_set; auto.
      - rewrite <- (match_val_single_free_var gamma_valid pd vt). 
        2: apply Hmatch.
        rewrite ty_subst_p_fv.
        rewrite in_map_iff.
        intros C. destruct C as [y [Hxy Hiny]].
        (*Contradicts fact that no names shared between bnd and free vars*)
        assert (x = y). {
          symmetry.
          apply (Hbndfree p t y x); simpl; auto.
          apply ty_subst_var_fst in Hxy; auto.
        }
        subst. contradiction.
      - rewrite <- (match_val_single_free_var gamma_valid pd 
        (vt_with_args vt params (map (v_subst vt) tys))).
        2: apply Hmatch1. apply n.
    }
    (*So now we know that x is in (pat_fv p), and
      therefore we know that it is in (map fst l0)*)
    assert (In x (map fst l0)). {
      rewrite <- (match_val_single_free_var gamma_valid pd 
        (vt_with_args vt params (map (v_subst vt) tys))).
      apply i. apply Hmatch1.
    }
    rewrite in_map_iff in H1.
    destruct H1 as [[x1 y1] [Hx Hinx1]]; subst; simpl in *.
    rewrite -> extend_val_lookup with (t:=y1); auto.
    2:  apply match_val_single_nodup in Hmatch1; auto.
    assert (projT1 y1 = (v_subst (vt_with_args vt params (map (v_subst vt) tys)) x1.2)).
    {
      eapply match_val_single_typs. apply Hmatch1. auto.
    }
    destruct (sort_eq_dec (v_subst (vt_with_args vt params (map (v_subst vt) tys)) x1.2) (projT1 y1));
    try (exfalso; apply n; auto).
    assert (exists z Heq,
      In (ty_subst_var x1, z) l /\
      projT2 z = dom_cast (dom_aux pd) Heq (projT2 y1)
    ).
    { eapply match_val_single_ty_subst_some. apply Hmatch. 
      apply Hmatch1. auto. }
    destruct H2 as [z [Hz1 [Hinz Hz2]]].
    rewrite -> extend_val_lookup with (t:=z); auto.
    2: apply match_val_single_nodup in Hmatch; auto.
    assert (projT1 z = (v_subst vt (ty_subst_var x1).2)). {
      rewrite <- Hz1, <- e. symmetry.
      apply v_subst_vt_with_args'; auto.
    }
    destruct (sort_eq_dec (v_subst vt (ty_subst_var x1).2) (projT1 z));
    [| exfalso; apply n; auto].
    rewrite Hz2. rewrite !dom_cast_compose. apply dom_cast_eq.
    (*So all that remains is to prove [match_val_single] Some lemma*)
  - (*Teps*)
    (*First, cast inhabited*)
    assert (match domain_ne pd (v_subst vt ty2) with
    | @DE _ _ x => x
    end = dom_cast (dom_aux pd) Heq
    (match domain_ne pd (v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty1) with
    | @DE _ _ x => x
    end)). {
      generalize dependent (v_subst vt ty2); intros; subst.
      unfold dom_cast; reflexivity.
    }
    generalize dependent (match domain_ne pd (v_subst vt ty2) with
    | @DE _ _ x => x
    end).
    generalize dependent (match domain_ne pd (v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty1) with
    | @DE _ _ x => x
    end).
    intros i1 i2 Hi; subst.
    (*We need to "cast" the function*)
    match goal with
    | |- ClassicalEpsilon.epsilon ?i1 ?f = dom_cast ?d ?Heq (ClassicalEpsilon.epsilon ?i2 ?g) => 
      let H := fresh in
      assert (H: g = (fun (z: domain (dom_aux pd) (v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty1)) =>
        f (dom_cast (dom_aux pd) Heq z))); [| generalize dependent f;
        intros; rewrite H]
    end.
    {
      apply functional_extensionality_dep; intros.
      rewrite !dom_cast_compose. symmetry. erewrite H.
      reflexivity.
      apply Hwf.
      intros.
      unfold substi. vsym_eq x0 v.
      - vsym_eq (ty_subst_var v) (ty_subst_var v).
        simpl. assert (e=Logic.eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        subst; simpl. rewrite dom_cast_compose. apply dom_cast_eq.
      - vsym_eq (ty_subst_var x0) (ty_subst_var v); [|apply Hvv; simpl_set; auto].
        (*Contradiction from bnd/free assumption*)
        exfalso. apply ty_subst_var_fst in e.
        destruct Hwf as [Hwf _].
        unfold tm_wf_strong in Hwf.
        destruct Hwf as [_ [_ Hwf]].
        apply (Hwf (fst x0)); split; auto;
        rewrite in_map_iff; [exists x0 | exists v]; simpl; simpl_set; auto.
    }
    clear H0.
    (*Now, we can generalize*)
    generalize dependent (v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty1); intros; subst; 
    unfold dom_cast; simpl.
    reflexivity.
  - (*Fpred*)
    assert (Hmap: (map (v_subst vt) (ty_subst_list' params tys tys0)) =
    (map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) tys0)). {
      apply list_eq_ext'; rewrite !map_length; auto.
      intros n d Hn. unfold ty_subst_list'.
      rewrite !map_map.
      rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
      apply v_subst_vt_with_args'; auto.
    }
    assert (Hargs:
    cast_arg_list (f_equal (sym_sigma_args p) Hmap)
    (pred_arg_list pd vt p (ty_subst_list' params tys tys0) (map ty_subst_tm tms)
    (term_rep gamma_valid pd vt pf vv1) Hty2) =
    (pred_arg_list pd (vt_with_args vt params (map (v_subst vt) tys)) p tys0 tms
        (term_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf
          vv2) Hty1)).
    {
      unfold pred_arg_list.
      apply get_arg_list_vt_ext with(Heq:=Hmap);
      rewrite map_length; auto.
      revert H; rewrite Forall_forall; intros.
      revert Hty0. rewrite -> map_nth_inbound with (d2:=tm_d); auto.
      intros.
      erewrite H; [|apply nth_In; auto | |].
      rewrite !dom_cast_compose. apply dom_cast_refl.
      cbn in Hwf; destruct_all.
      simpl_forall. rewrite Forall_forall in H2; apply H2; apply nth_In; auto.
      intros. apply Hvv. simpl_set.
      exists (nth i tms tm_d); split; auto; apply nth_In; auto.
      Unshelve.
      auto.
    }
    rewrite <- Hargs.
    rewrite <- preds_cast_eq. reflexivity.
  - (*Fquant*)
    assert (Heq: v_subst vt (ty_subst_var v).2 =
    v_subst (vt_with_args vt params (map (v_subst vt) tys)) v.2).
    {
      simpl. apply v_subst_vt_with_args'; auto.
    }
    assert (forall d1 d2,
      d1 = dom_cast (dom_aux pd) Heq d2 ->
      formula_rep gamma_valid pd vt pf (substi pd vt vv1 (ty_subst_var v) d2) 
      (ty_subst_fmla f) (typed_quant_inv Hty2) =
    formula_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf
      (substi pd (vt_with_args vt params (map (v_subst vt) tys)) vv2 v d1) f
      (typed_quant_inv Hty1)).
    {
      intros. subst. apply H; auto. apply Hwf.
      intros. unfold substi.
      vsym_eq x v.
      - vsym_eq (ty_subst_var v) (ty_subst_var v). simpl.
        assert (e = Logic.eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec); subst.
        apply dom_cast_eq.
      - vsym_eq (ty_subst_var x) (ty_subst_var v); [| apply Hvv; simpl_set; auto].
        exfalso. destruct Hwf as [Hwf _].
        unfold fmla_wf_strong in Hwf.
        destruct Hwf as [_ [_ Hwf]].
        apply ty_subst_var_fst in e.
        apply (Hwf (fst x)); split; rewrite in_map_iff; simpl;
        [exists x | exists v]; simpl_set; auto.
    }
    destruct q; simpl_rep_full;
    apply all_dec_eq; split; intros.
    + erewrite <- H0. apply H1.
      Unshelve.
      2: exact (dom_cast (dom_aux pd) (Logic.eq_sym Heq) d).
      rewrite !dom_cast_compose. symmetry. apply dom_cast_refl.
    + erewrite H0. apply H1. reflexivity.
    + destruct H1 as [d Hd]. exists (dom_cast (dom_aux pd) Heq d).
      erewrite <- H0. apply Hd. reflexivity.
    + destruct H1 as [d Hd]. exists (dom_cast (dom_aux pd) (Logic.eq_sym Heq) d).
      erewrite H0. apply Hd. rewrite !dom_cast_compose. symmetry.
      apply dom_cast_refl.
  - (*Feq*)
    apply all_dec_eq. 
    assert (Heq1: v_subst (vt_with_args vt params (map (v_subst vt) tys)) v =
    v_subst vt (ty_subst' params tys v)).
    {
      symmetry.
      apply v_subst_vt_with_args'; auto.
    }
    rewrite -> H with(vv2:=vv2)(ty1:=v)(Hty1:=proj1' (typed_eq_inv Hty1))(Heq:=Heq1);
    [| apply Hwf | intros; apply Hvv; simpl_set; auto].
    rewrite -> H0 with(vv2:=vv2)(ty1:=v)(Hty1:=proj2' (typed_eq_inv Hty1))(Heq:=Heq1);
    [| apply Hwf | intros; apply Hvv; simpl_set; auto].
    split; intros Heq.
    + apply dom_cast_inj in Heq. auto.
    + rewrite Heq. apply dom_cast_eq.
  - (*Fbinop - easier bc no casts*)
    rewrite -> H with(vv2:=vv2)(Hty1:=proj1' (typed_binop_inv Hty1));
    [|apply Hwf | intros; apply Hvv; simpl_set; auto].
    rewrite -> H0 with (vv2:=vv2)(Hty1:=proj2' (typed_binop_inv Hty1));
    [|apply Hwf | intros; apply Hvv; simpl_set; auto].
    reflexivity.
  - (*Fnot*)
    rewrite -> H with (vv2:=vv2)(Hty1:=typed_not_inv Hty1); auto.
    apply Hwf.
  - (*Flet*)
    assert (Heq1: v_subst (vt_with_args vt params (map (v_subst vt) tys)) v.2 =
    v_subst vt (ty_subst' params tys v.2)).
    {
      symmetry; apply v_subst_vt_with_args'; auto.
    }
    rewrite -> H with(vv2:=vv2)(ty1:=snd v)(Heq:=Heq1)(Hty1:=(proj1' (typed_let_inv Hty1))); auto;
    [|apply Hwf | intros; apply Hvv; simpl_set; auto].
    apply H0; [apply Hwf |].
    intros.
    (*separate lemma?*)
    unfold substi.
    vsym_eq x v.
    + vsym_eq (ty_subst_var v) (ty_subst_var v).
      simpl. assert (e = Logic.eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec);
      subst; simpl. rewrite dom_cast_compose. symmetry. apply dom_cast_refl.
    + vsym_eq (ty_subst_var x) (ty_subst_var v); 
      [| apply Hvv; intros; simpl_set; auto].
      exfalso. destruct Hwf as [Hwf _].
      destruct Hwf as [_ [_ Hwf]].
      apply (Hwf (fst x)).
      apply ty_subst_var_fst in e.
      split; rewrite in_map_iff; simpl; [exists x | exists v];
      simpl_set; auto.
  - (*Fif*)
    rewrite -> H with (vv2:=vv2)(Hty1:=proj1' (typed_if_inv Hty1));
    [| apply Hwf | intros; apply Hvv; simpl_set; auto].
    rewrite -> H0 with (vv2:=vv2)(Hty1:=proj1' (proj2' (typed_if_inv Hty1)));
    [| apply Hwf | intros; apply Hvv; simpl_set; auto].
    rewrite -> H1 with (vv2:=vv2)(Hty1:=proj2' (proj2' (typed_if_inv Hty1)));
    [| apply Hwf | intros; apply Hvv; simpl_set; auto].
    reflexivity.
  -(*Fmatch*)
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    cbn in Hwf. destruct Hwf as [Hwf [Hptm Hpall]].
    (*From Hwf, get info we need about bnd and free vars*)
    assert (Hbndfree: forall p f x y,
      In (p, f) ps ->
      In x (pat_fv p) ->
      In y (fmla_fv f) ->
      fst x = fst y ->
      x = y).
    {
      intros p f x y Hinpt Hinx Hiny Hxy. 
      unfold fmla_wf_strong in Hwf; simpl in Hwf.
      vsym_eq x y.
      destruct (in_dec vsymbol_eq_dec y (pat_fv p)).
      {
        destruct Hwf as [_ [Hwf _]].
        revert Hwf.
        rewrite -> map_app, NoDup_app_iff.
        intros [_ [Hwf _]].
        eapply NoDup_map_in. apply Hwf. all: auto;
        rewrite in_concat; eexists;
        split; try (rewrite in_map_iff);
        try (eexists; split; [reflexivity | auto]);
        try apply Hinpt;
        rewrite !in_app_iff; auto.
      }
      (*Now y not in, so can use 3rd part of Hwf*)
      destruct Hwf as [_ [_ Hwf]].
      exfalso.
      apply (Hwf (fst x)).
      rewrite map_app. split.
      - rewrite !in_map_iff. exists y.
        split; auto. simpl_set. right. exists (p, f); split; auto.
        simpl_set; auto.
      - rewrite in_app_iff. right.
        rewrite in_map_iff. exists x. split; auto.
        rewrite in_concat. eexists.
        split. rewrite in_map_iff. eexists; split; [reflexivity | auto].
        apply Hinpt. rewrite in_app_iff; auto.
    }
    clear Hwf. rewrite Forall_map in Hpall.
    induction ps; simpl; intros; auto.
    destruct a.
    inversion H0; subst.
    (*First step: handle term_rep in case*)
    assert (Heq1: v_subst (vt_with_args vt params (map (v_subst vt) tys)) v =
    v_subst vt (ty_subst' params tys v)).
    {
      symmetry; apply v_subst_vt_with_args'; auto.
    }
    erewrite -> H with(vv2:=vv2)(ty1:=v)(Hty1:=Hty1)(Heq:=Heq1);
    auto.
    2: { intros; rewrite Hvv; auto; simpl_set; auto. }
    simpl.
    case_match_goal.
    2: {
      rewrite -> match_val_single_ty_subst_none in Hmatch.
      rewrite -> Hmatch.
      rewrite <- H with(vv1:=vv1)(Hty2:=Hty2). auto. simpl. 
      apply IHps. all: auto.
      - intros. apply Hvv. simpl; simpl_set_small; auto.
        destruct H1; auto.
      - intros. apply (Hbndfree p0 f0 x y); simpl; auto.  
      - inversion Hpall; subst; auto.
      - intros. apply Hvv. simpl; simpl_set_small; auto.
    }
    symmetry.
    destruct (match_val_single gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) v p
    (Forall_inv Hpat1)
    (term_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf vv2
      tm v Hty1)) eqn : Hmatch1.
    2: {
      rewrite <- match_val_single_ty_subst_none in Hmatch1.
      rewrite -> Hmatch1 in Hmatch. inversion Hmatch.
      (*Contradiction from [match_val_single_ty_subst_none]*)
    }
    symmetry.
    apply H3.
    { apply (Forall_inv Hpall). }
    intros x Hinx Heq'.
    destruct (in_dec vsymbol_eq_dec x (pat_fv p)).
    2: {
      (*Not in: follows from Hvv*)
      rewrite !extend_val_notin; auto.
      - erewrite Hvv. reflexivity.
        simpl. simpl_set; auto.
      - rewrite <- (match_val_single_free_var gamma_valid pd vt). 
        2: apply Hmatch.
        rewrite ty_subst_p_fv.
        rewrite in_map_iff.
        intros C. destruct C as [y [Hxy Hiny]].
        (*Contradicts fact that no names shared between bnd and free vars*)
        assert (x = y). {
          symmetry.
          apply (Hbndfree p f y x); simpl; auto.
          apply ty_subst_var_fst in Hxy; auto.
        }
        subst. contradiction.
      - rewrite <- (match_val_single_free_var gamma_valid pd 
        (vt_with_args vt params (map (v_subst vt) tys))).
        2: apply Hmatch1. apply n.
    }
    (*So now we know that x is in (pat_fv p), and
      therefore we know that it is in (map fst l0)*)
    assert (In x (map fst l0)). {
      rewrite <- (match_val_single_free_var gamma_valid pd 
        (vt_with_args vt params (map (v_subst vt) tys))).
      apply i. apply Hmatch1.
    }
    rewrite in_map_iff in H1.
    destruct H1 as [[x1 y1] [Hx Hinx1]]; subst; simpl in *.
    rewrite -> extend_val_lookup with (t:=y1); auto.
    2:  apply match_val_single_nodup in Hmatch1; auto.
    assert (projT1 y1 = (v_subst (vt_with_args vt params (map (v_subst vt) tys)) x1.2)).
    {
      eapply match_val_single_typs. apply Hmatch1. auto.
    }
    destruct (sort_eq_dec (v_subst (vt_with_args vt params (map (v_subst vt) tys)) x1.2) (projT1 y1));
    try (exfalso; apply n; auto).
    assert (exists z Heq,
      In (ty_subst_var x1, z) l /\
      projT2 z = dom_cast (dom_aux pd) Heq (projT2 y1)
    ).
    { eapply match_val_single_ty_subst_some. apply Hmatch. 
      apply Hmatch1. auto. }
    destruct H2 as [z [Hz1 [Hinz Hz2]]].
    rewrite -> extend_val_lookup with (t:=z); auto.
    2: apply match_val_single_nodup in Hmatch; auto.
    assert (projT1 z = (v_subst vt (ty_subst_var x1).2)). {
      rewrite <- Hz1, <- e. symmetry.
      apply v_subst_vt_with_args'; auto.
    }
    destruct (sort_eq_dec (v_subst vt (ty_subst_var x1).2) (projT1 z));
    [| exfalso; apply n; auto].
    rewrite Hz2. rewrite !dom_cast_compose. apply dom_cast_eq.
Qed.

Definition ty_subst_t_rep {pd} t (pf: pi_funpred gamma_valid pd) := 
    proj_tm (@ty_subst_tf_rep pd pf) t.
Definition ty_subst_f_rep {pd} f (pf: pi_funpred gamma_valid pd) := 
  proj_fmla (@ty_subst_tf_rep pd pf) f.

(*Part 5: Prove that [tm_wf_strong] implies [tm_wf_strong_rec] by
  using (2) and proving that the wf strong property holds of all
  subterms*)


(*Idea:
  1. Prove that all free vars in subterm are free or bound in original term
  2. Prove if Nodup names of bnd, then NoDup names of bnd for all subterms/fmlas
  3. Prove that no overlap in subterm fv
  4. Prove that if strong condition holds, no free variable dups in any
    subterm (from previous)
  5. put together*)

(*1. All free vars in subterms and subfmlas are 
  free or bound in the original term*)

(*Subterm formulation makes it easier to reason about
  free variables*)

Ltac simpl_in :=
  repeat(match goal with
  | H: In ?x (concat ?l) |- _ => rewrite in_concat in H
  | H: In ?x (map ?f ?l) |- _ => rewrite in_map_iff in H
  | H: In ?x ?l |- In (?f ?x) (map ?f ?l) => rewrite in_map_iff;
    exists x; auto
  end; destruct_all; subst); try rewrite -> !in_app_iff in *.

Ltac auto_hyp :=
  repeat match goal with
  | H: ?P -> ?Q, H1 : ?P |- _ => specialize (H H1)
  end; auto.
  
Lemma subterm_fv_in x tm t f:
  (In tm (subterms_t t) -> 
    In x (tm_fv tm) -> In x (tm_fv t) \/
    In x (tm_bnd t)) /\
  (In tm (subterms_f f) -> 
  In x (tm_fv tm) -> In x (fmla_fv f) \/
  In x (fmla_bnd f)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; 
  destruct_all; try contradiction; simpl in *;
  destruct_all; try contradiction; subst; auto.
  - simpl_in. simpl_set. rewrite in_concat.
    rewrite Forall_forall in H. specialize (H _ H3 H2 H1).
    destruct H; [left | right]; [exists x1 | exists (tm_bnd x1) ]; split; auto.
    simpl_in.
  - simpl_set. simpl_in. vsym_eq x v. 
    repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set.
    repeat (destruct_all; auto_hyp).
  - simpl_set. simpl_in.
    rewrite in_concat.
    destruct H1; [auto_hyp; destruct_all; auto_hyp| simpl_in].
    simpl_forall. rewrite Forall_forall in H0.
    specialize (H0 _ H4).
    destruct (in_dec vsymbol_eq_dec x (pat_fv x1.1)).
    + right. right. eexists. rewrite in_map_iff.
      split. eexists. split;[reflexivity |]. apply H4.
      simpl_in; auto.
    + repeat (destruct_all; auto_hyp); [left | right]; right.
      * exists x1. split; auto. simpl_set. auto.
      * eexists. split. rewrite in_map_iff.
        eexists. split;[reflexivity |]. apply H4.
        simpl_in; auto.
  - simpl_set. vsym_eq x v. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. rewrite in_concat.
    rewrite Forall_forall in H. specialize (H _ H3 H2 H1).
    destruct H; [left | right]; [exists x1 | exists (tm_bnd x1) ]; split; auto.
    simpl_in.
  - simpl_set. vsym_eq x v. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. vsym_eq x v. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_set. simpl_in.
    rewrite in_concat.
    destruct H1; [auto_hyp; destruct_all; auto_hyp| simpl_in].
    simpl_forall. rewrite Forall_forall in H0.
    specialize (H0 _ H4).
    destruct (in_dec vsymbol_eq_dec x (pat_fv x1.1)).
    + right. right. eexists. rewrite in_map_iff.
      split. eexists. split;[reflexivity |]. apply H4.
      simpl_in; auto.
    + repeat (destruct_all; auto_hyp); [left | right]; right.
      * exists x1. split; auto. simpl_set. auto.
      * eexists. split. rewrite in_map_iff.
        eexists. split;[reflexivity |]. apply H4.
        simpl_in; auto.
Qed.

Definition subterm_t_fv_in t tm x := proj_tm (subterm_fv_in x tm) t.
Definition subterm_f_fv_in f tm x := proj_fmla (subterm_fv_in x tm) f.
  
(*And for subformulas (the same proof, should reduce dup)*)
Lemma subfmla_fv_in x f1 t f:
  (In f1 (subfmla_t t) -> 
    In x (fmla_fv f1) -> In x (tm_fv t) \/
    In x (tm_bnd t)) /\
  (In f1 (subfmla_f f) -> 
  In x (fmla_fv f1) -> In x (fmla_fv f) \/
  In x (fmla_bnd f)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; 
  destruct_all; try contradiction; simpl in *;
  destruct_all; try contradiction; subst; auto.
  - simpl_in. simpl_set. rewrite in_concat.
    rewrite Forall_forall in H. specialize (H _ H3 H2 H1).
    destruct H; [left | right]; [exists x1 | exists (tm_bnd x1) ]; split; auto.
    simpl_in.
  - simpl_set. simpl_in. vsym_eq x v. 
    repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set.
    repeat (destruct_all; auto_hyp).
  - simpl_set. simpl_in.
    rewrite in_concat.
    destruct H1; [auto_hyp; destruct_all; auto_hyp| simpl_in].
    simpl_forall. rewrite Forall_forall in H0.
    specialize (H0 _ H4).
    destruct (in_dec vsymbol_eq_dec x (pat_fv x1.1)).
    + right. right. eexists. rewrite in_map_iff.
      split. eexists. split;[reflexivity |]. apply H4.
      simpl_in; auto.
    + repeat (destruct_all; auto_hyp); [left | right]; right.
      * exists x1. split; auto. simpl_set. auto.
      * eexists. split. rewrite in_map_iff.
        eexists. split;[reflexivity |]. apply H4.
        simpl_in; auto.
  - simpl_set. vsym_eq x v. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. rewrite in_concat.
    rewrite Forall_forall in H. specialize (H _ H3 H2 H1).
    destruct H; [left | right]; [exists x1 | exists (tm_bnd x1) ]; split; auto.
    simpl_in.
  - simpl_set. vsym_eq x v. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. vsym_eq x v. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_set. simpl_in.
    rewrite in_concat.
    destruct H1; [auto_hyp; destruct_all; auto_hyp| simpl_in].
    simpl_forall. rewrite Forall_forall in H0.
    specialize (H0 _ H4).
    destruct (in_dec vsymbol_eq_dec x (pat_fv x1.1)).
    + right. right. eexists. rewrite in_map_iff.
      split. eexists. split;[reflexivity |]. apply H4.
      simpl_in; auto.
    + repeat (destruct_all; auto_hyp); [left | right]; right.
      * exists x1. split; auto. simpl_set. auto.
      * eexists. split. rewrite in_map_iff.
        eexists. split;[reflexivity |]. apply H4.
        simpl_in; auto.
Qed.

Definition subfmla_t_fv_in t f1 x := proj_tm (subfmla_fv_in x f1) t.
Definition subfmla_f_fv_in f f1 x := proj_fmla (subfmla_fv_in x f1) f.
  
(*2. If the names of bound variables are unique,
  then the names of all bound vars in all subterms are unique*)
Lemma bnd_nodup_subterm t f:
  (forall (Hbnd: NoDup (map fst (tm_bnd t))),
    forall tm, In tm (subterms_t t) ->
      NoDup (map fst (tm_bnd tm))) /\
  (forall (Hbnd: NoDup (map fst (fmla_bnd f))),
    forall tm, In tm (subterms_f f) ->
      NoDup (map fst (tm_bnd tm))).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - destruct H; try contradiction. subst. auto.
  - destruct H; try contradiction. subst. auto.
  - destruct H0; subst; auto.
    rewrite Forall_forall in H.
    rewrite in_concat in H0.
    destruct_all. rewrite in_map_iff in H0. destruct_all.
    eapply H. apply H2. all: auto.
    rewrite concat_map in Hbnd.
    rewrite map_map in Hbnd.
    rewrite NoDup_concat_iff in Hbnd.
    destruct Hbnd as [Hnodup _].
    apply Hnodup. rewrite in_map_iff.
    exists x0; auto.
  - destruct H1; subst; auto.
    rewrite in_app_iff in H1.
    inversion Hbnd; subst.
    rewrite map_app in H5.
    rewrite NoDup_app_iff in H5. destruct_all; auto.
  - destruct H2; subst; auto.
    rewrite !in_app_iff in H2.
    rewrite !map_app in Hbnd.
    rewrite NoDup_app_iff in Hbnd.
    destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite NoDup_app_iff in Hn2. destruct_all; auto.
  - destruct H1; subst; auto.
    rewrite map_app in Hbnd.
    rewrite NoDup_app_iff in Hbnd. destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1. destruct H1; auto.
    rewrite -> concat_map, map_map in Hn2.
    rewrite NoDup_concat_iff in Hn2.
    destruct Hn2 as [Hn2 _].
    rewrite in_concat in H1; destruct_all.
    rewrite in_map_iff in H1; destruct_all.
    rewrite -> Forall_map, Forall_forall in H0.
    eapply H0. apply H3. all: auto.
    specialize (Hn2 (map fst (pat_fv (fst x0) ++ tm_bnd (snd x0)))).
    prove_hyp Hn2.
    { rewrite in_map_iff. exists x0; auto. }
    rewrite -> map_app, NoDup_app_iff in Hn2.
    apply Hn2.
  - destruct H0; subst; auto.
    inversion Hbnd; subst. auto.
  - rewrite Forall_forall in H.
    rewrite in_concat in H0.
    destruct_all. rewrite in_map_iff in H0. destruct_all.
    eapply H. apply H2. all: auto.
    rewrite concat_map in Hbnd.
    rewrite map_map in Hbnd.
    rewrite NoDup_concat_iff in Hbnd.
    destruct Hbnd as [Hnodup _].
    apply Hnodup. rewrite in_map_iff.
    exists x0; auto.
  - inversion Hbnd; auto.
  - rewrite -> map_app, NoDup_app_iff in Hbnd.
    destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1. destruct_all; auto.
  - rewrite -> map_app, NoDup_app_iff in Hbnd.
    destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1. destruct_all; auto.
  - contradiction.
  - contradiction.
  - inversion Hbnd; subst.
    rewrite -> map_app, NoDup_app_iff in H5.
    destruct H5 as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1; destruct_all; auto.
  - rewrite -> !map_app, NoDup_app_iff in Hbnd.
    destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite NoDup_app_iff in Hn2.
    destruct Hn2 as [Hn2 [Hn3 _]].
    rewrite !in_app_iff in H2.
    destruct_all; auto.
  - rewrite map_app in Hbnd.
    rewrite NoDup_app_iff in Hbnd. destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1. destruct H1; auto.
    rewrite -> concat_map, map_map in Hn2.
    rewrite NoDup_concat_iff in Hn2.
    destruct Hn2 as [Hn2 _].
    rewrite in_concat in H1; destruct_all.
    rewrite in_map_iff in H1; destruct_all.
    rewrite -> Forall_map, Forall_forall in H0.
    eapply H0. apply H3. all: auto.
    specialize (Hn2 (map fst (pat_fv (fst x0) ++ fmla_bnd (snd x0)))).
    prove_hyp Hn2.
    { rewrite in_map_iff. exists x0; auto. }
    rewrite -> map_app, NoDup_app_iff in Hn2.
    apply Hn2.
Qed.

Definition bnd_nodup_subterm_t t := proj_tm bnd_nodup_subterm t.
Definition bnd_nodup_subterm_f f := proj_fmla bnd_nodup_subterm f.
  
(*subformula version (this really isn't very good - the same proof)*)
Lemma bnd_nodup_subfmla t f:
  (forall (Hbnd: NoDup (map fst (tm_bnd t))),
    forall f1, In f1 (subfmla_t t) ->
      NoDup (map fst (fmla_bnd f1))) /\
  (forall (Hbnd: NoDup (map fst (fmla_bnd f))),
    forall f1, In f1 (subfmla_f f) ->
      NoDup (map fst (fmla_bnd f1))).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto; try contradiction.
  - rewrite Forall_forall in H.
    rewrite in_concat in H0.
    destruct_all. rewrite in_map_iff in H0. destruct_all.
    eapply H. apply H2. all: auto.
    rewrite concat_map in Hbnd.
    rewrite map_map in Hbnd.
    rewrite NoDup_concat_iff in Hbnd.
    destruct Hbnd as [Hnodup _].
    apply Hnodup. rewrite in_map_iff.
    exists x0; auto.
  - rewrite in_app_iff in H1.
    inversion Hbnd; subst.
    rewrite map_app in H5.
    rewrite NoDup_app_iff in H5. destruct_all; auto.
  - rewrite !in_app_iff in H2.
    rewrite !map_app in Hbnd.
    rewrite NoDup_app_iff in Hbnd.
    destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite NoDup_app_iff in Hn2. destruct_all; auto.
  - rewrite map_app in Hbnd.
    rewrite NoDup_app_iff in Hbnd. destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1. destruct H1; auto.
    rewrite -> concat_map, map_map in Hn2.
    rewrite NoDup_concat_iff in Hn2.
    destruct Hn2 as [Hn2 _].
    rewrite in_concat in H1; destruct_all.
    rewrite in_map_iff in H1; destruct_all.
    rewrite -> Forall_map, Forall_forall in H0.
    eapply H0. apply H3. all: auto.
    specialize (Hn2 (map fst (pat_fv (fst x0) ++ tm_bnd (snd x0)))).
    prove_hyp Hn2.
    { rewrite in_map_iff. exists x0; auto. }
    rewrite -> map_app, NoDup_app_iff in Hn2.
    apply Hn2.
  - inversion Hbnd; subst. auto.
  - destruct H0; subst; auto. 
    rewrite Forall_forall in H.
    rewrite in_concat in H0.
    destruct_all. rewrite in_map_iff in H0. destruct_all.
    eapply H. apply H2. all: auto.
    rewrite concat_map in Hbnd.
    rewrite map_map in Hbnd.
    rewrite NoDup_concat_iff in Hbnd.
    destruct Hbnd as [Hnodup _].
    apply Hnodup. rewrite in_map_iff.
    exists x0; auto.
  - destruct H0; subst; auto. inversion Hbnd; auto.
  - destruct H1; subst; auto. rewrite -> map_app, NoDup_app_iff in Hbnd.
    destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1. destruct_all; auto.
  - destruct H1; subst; auto. rewrite -> map_app, NoDup_app_iff in Hbnd.
    destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1. destruct_all; auto.
  - destruct H0; subst; auto.
  - destruct H; subst; auto. contradiction.
  - destruct H; subst; auto. contradiction.
  - destruct H1; subst; auto. inversion Hbnd; subst.
    rewrite -> map_app, NoDup_app_iff in H5.
    destruct H5 as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1; destruct_all; auto.
  - destruct H2; subst; auto. rewrite -> !map_app, NoDup_app_iff in Hbnd.
    destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite NoDup_app_iff in Hn2.
    destruct Hn2 as [Hn2 [Hn3 _]].
    rewrite !in_app_iff in H2.
    destruct_all; auto.
  - destruct H1; subst; auto. rewrite map_app in Hbnd.
    rewrite NoDup_app_iff in Hbnd. destruct Hbnd as [Hn1 [Hn2 _]].
    rewrite in_app_iff in H1. destruct H1; auto.
    rewrite -> concat_map, map_map in Hn2.
    rewrite NoDup_concat_iff in Hn2.
    destruct Hn2 as [Hn2 _].
    rewrite in_concat in H1; destruct_all.
    rewrite in_map_iff in H1; destruct_all.
    rewrite -> Forall_map, Forall_forall in H0.
    eapply H0. apply H3. all: auto.
    specialize (Hn2 (map fst (pat_fv (fst x0) ++ fmla_bnd (snd x0)))).
    prove_hyp Hn2.
    { rewrite in_map_iff. exists x0; auto. }
    rewrite -> map_app, NoDup_app_iff in Hn2.
    apply Hn2.
Qed.
  
Definition bnd_nodup_subfmla_t t := proj_tm bnd_nodup_subfmla t.
Definition bnd_nodup_subfmla_f f := proj_fmla bnd_nodup_subfmla f.
  
(*3. From these, we show that there is no overlap in subterms*)

(*This is tricky to prove, and actually does not
  follow from previous - we need induction*)
Lemma subterm_disj tm t f:
  (forall (Hn: NoDup (map fst (tm_bnd t)))
    (Hd: disj (map fst (tm_fv t)) (map fst (tm_bnd t)))
    (Hsub: In tm (subterms_t t)),
    disj (map fst (tm_fv tm)) (map fst (tm_bnd tm))) /\
  (forall (Hn: NoDup (map fst (fmla_bnd f)))
    (Hd: disj (map fst (fmla_fv f)) (map fst (fmla_bnd f)))
    (Hsub: In tm (subterms_f f)),
    disj (map fst (tm_fv tm)) (map fst (tm_bnd tm))).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try contradiction.
  - destruct_all; subst; auto. contradiction.
  - destruct_all; subst; auto. contradiction.
  - destruct Hsub as [Hsub | Hsub]; subst; auto.
    rewrite in_concat in Hsub.
    destruct Hsub as [ts [Hints Hin]].
    rewrite in_map_iff in Hints.
    destruct Hints as [t1 [Hts Hint1]]; subst.
    rewrite Forall_forall in H.
    rewrite -> concat_map, map_map in Hn.
    apply (H _ Hint1); auto.
    + rewrite -> NoDup_concat_iff in Hn.
      destruct Hn as [Hn _].
      apply Hn; rewrite in_map_iff. exists t1; auto.
    + apply (disj_sublist_lr Hd); apply sublist_map;
      [apply sublist_big_union | apply sublist_concat_map]; auto. 
  - (*Tlet*) destruct Hsub as [Hsub | Hsub]; subst; auto.
    inversion Hn; subst.
    rewrite -> map_app, NoDup_app_iff in H4.
    destruct H4 as [Hn1 [Hn2 _]].
    rewrite in_app_iff in Hsub; destruct Hsub;
    [apply H | apply H0]; auto.
    + apply (disj_sublist_lr Hd).
      * apply sublist_map. apply union_sublist_l.
      * apply incl_tl. apply sublist_map. apply sublist_app_l.
    + clear -Hd H3. (*need nodups for bound vars*)
      unfold disj in *.
      intros x [Hinx1 Hinx2].
      rewrite -> !in_map_iff in Hinx1 , Hinx2.
      destruct Hinx1 as [v1 [Hx Hinv1]]; subst.
      destruct Hinx2 as [v2 [Hv Hinv2]]; subst.
      apply (Hd (fst v1)).
      split.
      * rewrite in_map_iff. exists v1. split; auto. simpl_set; auto.
        vsym_eq v1 v.
        exfalso. apply H3. rewrite -> map_app, in_app_iff.
        right. rewrite in_map_iff. exists v2; auto.
      * simpl. right. rewrite -> map_app, in_app_iff; right.
        rewrite in_map_iff; exists v2; auto.
  - (*Tif*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    rewrite !in_app_iff in Hsub.
    rewrite -> !map_app, !NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [[Hn2 [Hn3 _]] _]].
    destruct_all; [apply H | apply H0 | apply H1]; auto;
    apply (disj_sublist_lr Hd); apply sublist_map.
    + apply union_sublist_l.
    + apply sublist_app_l.
    + eapply sublist_trans. apply union_sublist_l.
      apply union_sublist_r.
    + eapply sublist_trans. apply sublist_app_l.
      apply sublist_app_r.
    + eapply sublist_trans. apply union_sublist_r.
      apply union_sublist_r.
    + eapply sublist_trans. apply sublist_app_r.
      apply sublist_app_r.
  - (*Tmatch case*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    rewrite in_app_iff in Hsub.
    rewrite -> !map_app, NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [Hn2 _]].
    destruct Hsub as [Hsub | Hsub].
    + apply H; auto.
      apply (disj_sublist_lr Hd); apply sublist_map.
      * apply union_sublist_l.
      * apply sublist_app_l.
    + clear H Hn1. rewrite in_concat in Hsub.
      rewrite -> Forall_map, Forall_forall in H0.
      destruct Hsub as [ts [Hints Hintm]].
      rewrite in_map_iff in Hints.
      destruct Hints as [pt [Hts Hinpt]]; subst.
      rewrite -> concat_map, !map_map, NoDup_concat_iff in Hn2.
      destruct Hn2 as [Hn2 _].
      specialize (Hn2 (map fst (pat_fv pt.1 ++ tm_bnd pt.2))).
      prove_hyp Hn2.
      {  rewrite in_map_iff. exists pt; auto. }
      rewrite -> map_app, NoDup_app_iff in Hn2.
      destruct Hn2 as [Hn1 [Hn2 [Hnotin _]]]. 
      apply (H0 _ Hinpt); auto.
      (*Prove manually*)
      intros x [Hinxfv Hinxbnd].
      destruct (in_dec string_dec x (map fst (pat_fv pt.1))).
      * (*If in pat_fv contradicts nodup*)
        apply (Hnotin _ i Hinxbnd).
      * (*Otherwise, use disj assumption*)
        apply (Hd x).
        rewrite -> !in_map_iff in Hinxfv, Hinxbnd.
        destruct Hinxfv as [v1 [Hx Hinv1]]; subst.
        destruct Hinxbnd as [v2 [Hvs Hinv2]].
        split.
        -- rewrite in_map_iff. exists v1. split; auto.
          simpl_set. right. exists pt. split; auto.
          simpl_set. split; auto. intro C.
          apply n. rewrite in_map_iff. exists v1. auto.
        -- rewrite in_map_iff. exists v2. split; auto.
          rewrite in_app_iff. right. rewrite in_concat.
          exists (pat_fv pt.1 ++ tm_bnd pt.2).
          split; auto.
          ++ rewrite in_map_iff. exists pt; auto.
          ++ rewrite in_app_iff; auto.
  - (*Teps*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    inversion Hn; subst.
    apply H; auto.
    intros x [Hinx1 Hinx2].
    rewrite -> !in_map_iff in Hinx1, Hinx2.
    destruct Hinx1 as [v1 [Hx Hinv1]]; subst.
    destruct Hinx2 as [v2 [Hv Hinv2]].
    destruct (string_dec v2.1 v.1).
    + apply H2. rewrite in_map_iff. exists v2; auto.
    + apply (Hd (v1.1)); simpl; split; auto.
      * rewrite in_map_iff. exists v1; split; auto.
        simpl_set. split; auto. intro C; subst; contradiction.
      * right. rewrite in_map_iff. exists v2; auto.
  - (*Fpred - same as Tfun*)
    rewrite in_concat in Hsub.
    destruct Hsub as [ts [Hints Hin]].
    rewrite in_map_iff in Hints.
    destruct Hints as [t1 [Hts Hint1]]; subst.
    rewrite Forall_forall in H.
    rewrite -> concat_map, map_map in Hn.
    apply (H _ Hint1); auto.
    + rewrite -> NoDup_concat_iff in Hn.
      destruct Hn as [Hn _].
      apply Hn; rewrite in_map_iff. exists t1; auto.
    + apply (disj_sublist_lr Hd); apply sublist_map;
      [apply sublist_big_union | apply sublist_concat_map]; auto. 
  - (*Fquant - same as Teps*)
    inversion Hn; subst.
    apply H; auto.
    intros x [Hinx1 Hinx2].
    rewrite -> !in_map_iff in Hinx1, Hinx2.
    destruct Hinx1 as [v1 [Hx Hinv1]]; subst.
    destruct Hinx2 as [v2 [Hv Hinv2]].
    destruct (string_dec v2.1 v.1).
    + apply H2. rewrite in_map_iff. exists v2; auto.
    + apply (Hd (v1.1)); simpl; split; auto.
      * rewrite in_map_iff. exists v1; split; auto.
        simpl_set. split; auto. intro C; subst; contradiction.
      * right. rewrite in_map_iff. exists v2; auto.
  - (*Feq*)
    rewrite -> map_app, NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [Hn2 _]].
    rewrite in_app_iff in Hsub.
    destruct Hsub; [apply H | apply H0]; auto;
    apply (disj_sublist_lr Hd); apply sublist_map;
    [apply union_sublist_l | apply sublist_app_l |
      apply union_sublist_r | apply sublist_app_r].
  - (*Fbinop*)
    rewrite -> map_app, NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [Hn2 _]].
    rewrite in_app_iff in Hsub.
    destruct Hsub; [apply H | apply H0]; auto;
    apply (disj_sublist_lr Hd); apply sublist_map;
    [apply union_sublist_l | apply sublist_app_l |
    apply union_sublist_r | apply sublist_app_r].
  - (*Flet*)
    inversion Hn; subst.
    rewrite -> map_app, NoDup_app_iff in H4.
    destruct H4 as [Hn1 [Hn2 _]].
    rewrite in_app_iff in Hsub; destruct Hsub;
    [apply H | apply H0]; auto.
    + apply (disj_sublist_lr Hd).
      * apply sublist_map. apply union_sublist_l.
      * apply incl_tl. apply sublist_map. apply sublist_app_l.
    + clear -Hd H3. (*need nodups for bound vars*)
      unfold disj in *.
      intros x [Hinx1 Hinx2].
      rewrite -> !in_map_iff in Hinx1 , Hinx2.
      destruct Hinx1 as [v1 [Hx Hinv1]]; subst.
      destruct Hinx2 as [v2 [Hv Hinv2]]; subst.
      apply (Hd (fst v1)).
      split.
      * rewrite in_map_iff. exists v1. split; auto. simpl_set; auto.
        vsym_eq v1 v.
        exfalso. apply H3. rewrite -> map_app, in_app_iff.
        right. rewrite in_map_iff. exists v2; auto.
      * simpl. right. rewrite -> map_app, in_app_iff; right.
        rewrite in_map_iff; exists v2; auto.
  - (*Fif*)
    rewrite !in_app_iff in Hsub.
    rewrite -> !map_app, !NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [[Hn2 [Hn3 _]] _]].
    destruct_all; [apply H | apply H0 | apply H1]; auto;
    apply (disj_sublist_lr Hd); apply sublist_map.
    + apply union_sublist_l.
    + apply sublist_app_l.
    + eapply sublist_trans. apply union_sublist_l.
      apply union_sublist_r.
    + eapply sublist_trans. apply sublist_app_l.
      apply sublist_app_r.
    + eapply sublist_trans. apply union_sublist_r.
      apply union_sublist_r.
    + eapply sublist_trans. apply sublist_app_r.
      apply sublist_app_r.
  - (*Tmatch case*)
    rewrite in_app_iff in Hsub.
    rewrite -> !map_app, NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [Hn2 _]].
    destruct Hsub as [Hsub | Hsub].
    + apply H; auto.
      apply (disj_sublist_lr Hd); apply sublist_map.
      * apply union_sublist_l.
      * apply sublist_app_l.
    + clear H Hn1. rewrite in_concat in Hsub.
      rewrite -> Forall_map, Forall_forall in H0.
      destruct Hsub as [ts [Hints Hintm]].
      rewrite in_map_iff in Hints.
      destruct Hints as [pt [Hts Hinpt]]; subst.
      rewrite -> concat_map, !map_map, NoDup_concat_iff in Hn2.
      destruct Hn2 as [Hn2 _].
      specialize (Hn2 (map fst (pat_fv pt.1 ++ fmla_bnd pt.2))).
      prove_hyp Hn2.
      {  rewrite in_map_iff. exists pt; auto. }
      rewrite -> map_app, NoDup_app_iff in Hn2.
      destruct Hn2 as [Hn1 [Hn2 [Hnotin _]]]. 
      apply (H0 _ Hinpt); auto.
      (*Prove manually*)
      intros x [Hinxfv Hinxbnd].
      destruct (in_dec string_dec x (map fst (pat_fv pt.1))).
      * (*If in pat_fv contradicts nodup*)
        apply (Hnotin _ i Hinxbnd).
      * (*Otherwise, use disj assumption*)
        apply (Hd x).
        rewrite -> !in_map_iff in Hinxfv, Hinxbnd.
        destruct Hinxfv as [v1 [Hx Hinv1]]; subst.
        destruct Hinxbnd as [v2 [Hvs Hinv2]].
        split.
        -- rewrite in_map_iff. exists v1. split; auto.
          simpl_set. right. exists pt. split; auto.
          simpl_set. split; auto. intro C.
          apply n. rewrite in_map_iff. exists v1. auto.
        -- rewrite in_map_iff. exists v2. split; auto.
          rewrite in_app_iff. right. rewrite in_concat.
          exists (pat_fv pt.1 ++ fmla_bnd pt.2).
          split; auto.
          ++ rewrite in_map_iff. exists pt; auto.
          ++ rewrite in_app_iff; auto.
Qed.

Definition subterm_t_disj t Hn Hd tm :=
  (proj_tm (subterm_disj tm) t) Hn Hd.
Definition subterm_f_disj f Hn Hd tm :=
  (proj_fmla (subterm_disj tm) f) Hn Hd.

(*Subformula (lots of repetition bad)*)
Lemma subfmla_disj f1 t f:
  (forall (Hn: NoDup (map fst (tm_bnd t)))
    (Hd: disj (map fst (tm_fv t)) (map fst (tm_bnd t)))
    (Hsub: In f1 (subfmla_t t)),
    disj (map fst (fmla_fv f1)) (map fst (fmla_bnd f1))) /\
  (forall (Hn: NoDup (map fst (fmla_bnd f)))
    (Hd: disj (map fst (fmla_fv f)) (map fst (fmla_bnd f)))
    (Hsub: In f1 (subfmla_f f)),
    disj (map fst (fmla_fv f1)) (map fst (fmla_bnd f1))).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try contradiction.
  - rewrite in_concat in Hsub.
    destruct Hsub as [ts [Hints Hin]].
    rewrite in_map_iff in Hints.
    destruct Hints as [t1 [Hts Hint1]]; subst.
    rewrite Forall_forall in H.
    rewrite -> concat_map, map_map in Hn.
    apply (H _ Hint1); auto.
    + rewrite -> NoDup_concat_iff in Hn.
      destruct Hn as [Hn _].
      apply Hn; rewrite in_map_iff. exists t1; auto.
    + apply (disj_sublist_lr Hd); apply sublist_map;
      [apply sublist_big_union | apply sublist_concat_map]; auto. 
  - (*Tlet*)
    inversion Hn; subst.
    rewrite -> map_app, NoDup_app_iff in H4.
    destruct H4 as [Hn1 [Hn2 _]].
    rewrite in_app_iff in Hsub; destruct Hsub;
    [apply H | apply H0]; auto.
    + apply (disj_sublist_lr Hd).
      * apply sublist_map. apply union_sublist_l.
      * apply incl_tl. apply sublist_map. apply sublist_app_l.
    + clear -Hd H3. (*need nodups for bound vars*)
      unfold disj in *.
      intros x [Hinx1 Hinx2].
      rewrite -> !in_map_iff in Hinx1 , Hinx2.
      destruct Hinx1 as [v1 [Hx Hinv1]]; subst.
      destruct Hinx2 as [v2 [Hv Hinv2]]; subst.
      apply (Hd (fst v1)).
      split.
      * rewrite in_map_iff. exists v1. split; auto. simpl_set; auto.
        vsym_eq v1 v.
        exfalso. apply H3. rewrite -> map_app, in_app_iff.
        right. rewrite in_map_iff. exists v2; auto.
      * simpl. right. rewrite -> map_app, in_app_iff; right.
        rewrite in_map_iff; exists v2; auto.
  - (*Tif*)
    rewrite !in_app_iff in Hsub.
    rewrite -> !map_app, !NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [[Hn2 [Hn3 _]] _]].
    destruct_all; [apply H | apply H0 | apply H1]; auto;
    apply (disj_sublist_lr Hd); apply sublist_map.
    + apply union_sublist_l.
    + apply sublist_app_l.
    + eapply sublist_trans. apply union_sublist_l.
      apply union_sublist_r.
    + eapply sublist_trans. apply sublist_app_l.
      apply sublist_app_r.
    + eapply sublist_trans. apply union_sublist_r.
      apply union_sublist_r.
    + eapply sublist_trans. apply sublist_app_r.
      apply sublist_app_r.
  - (*Tmatch case*)
    rewrite in_app_iff in Hsub.
    rewrite -> !map_app, NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [Hn2 _]].
    destruct Hsub as [Hsub | Hsub].
    + apply H; auto.
      apply (disj_sublist_lr Hd); apply sublist_map.
      * apply union_sublist_l.
      * apply sublist_app_l.
    + clear H Hn1. rewrite in_concat in Hsub.
      rewrite -> Forall_map, Forall_forall in H0.
      destruct Hsub as [ts [Hints Hintm]].
      rewrite in_map_iff in Hints.
      destruct Hints as [pt [Hts Hinpt]]; subst.
      rewrite -> concat_map, !map_map, NoDup_concat_iff in Hn2.
      destruct Hn2 as [Hn2 _].
      specialize (Hn2 (map fst (pat_fv pt.1 ++ tm_bnd pt.2))).
      prove_hyp Hn2.
      {  rewrite in_map_iff. exists pt; auto. }
      rewrite -> map_app, NoDup_app_iff in Hn2.
      destruct Hn2 as [Hn1 [Hn2 [Hnotin _]]]. 
      apply (H0 _ Hinpt); auto.
      (*Prove manually*)
      intros x [Hinxfv Hinxbnd].
      destruct (in_dec string_dec x (map fst (pat_fv pt.1))).
      * (*If in pat_fv contradicts nodup*)
        apply (Hnotin _ i Hinxbnd).
      * (*Otherwise, use disj assumption*)
        apply (Hd x).
        rewrite -> !in_map_iff in Hinxfv, Hinxbnd.
        destruct Hinxfv as [v1 [Hx Hinv1]]; subst.
        destruct Hinxbnd as [v2 [Hvs Hinv2]].
        split.
        -- rewrite in_map_iff. exists v1. split; auto.
          simpl_set. right. exists pt. split; auto.
          simpl_set. split; auto. intro C.
          apply n. rewrite in_map_iff. exists v1. auto.
        -- rewrite in_map_iff. exists v2. split; auto.
          rewrite in_app_iff. right. rewrite in_concat.
          exists (pat_fv pt.1 ++ tm_bnd pt.2).
          split; auto.
          ++ rewrite in_map_iff. exists pt; auto.
          ++ rewrite in_app_iff; auto.
  - (*Teps*)
    inversion Hn; subst.
    apply H; auto.
    intros x [Hinx1 Hinx2].
    rewrite -> !in_map_iff in Hinx1, Hinx2.
    destruct Hinx1 as [v1 [Hx Hinv1]]; subst.
    destruct Hinx2 as [v2 [Hv Hinv2]].
    destruct (string_dec v2.1 v.1).
    + apply H2. rewrite in_map_iff. exists v2; auto.
    + apply (Hd (v1.1)); simpl; split; auto.
      * rewrite in_map_iff. exists v1; split; auto.
        simpl_set. split; auto. intro C; subst; contradiction.
      * right. rewrite in_map_iff. exists v2; auto.
  - (*Fpred - same as Tfun*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    rewrite in_concat in Hsub.
    destruct Hsub as [ts [Hints Hin]].
    rewrite in_map_iff in Hints.
    destruct Hints as [t1 [Hts Hint1]]; subst.
    rewrite Forall_forall in H.
    rewrite -> concat_map, map_map in Hn.
    apply (H _ Hint1); auto.
    + rewrite -> NoDup_concat_iff in Hn.
      destruct Hn as [Hn _].
      apply Hn; rewrite in_map_iff. exists t1; auto.
    + apply (disj_sublist_lr Hd); apply sublist_map;
      [apply sublist_big_union | apply sublist_concat_map]; auto. 
  - (*Fquant - same as Teps*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    inversion Hn; subst.
    apply H; auto.
    intros x [Hinx1 Hinx2].
    rewrite -> !in_map_iff in Hinx1, Hinx2.
    destruct Hinx1 as [v1 [Hx Hinv1]]; subst.
    destruct Hinx2 as [v2 [Hv Hinv2]].
    destruct (string_dec v2.1 v.1).
    + apply H2. rewrite in_map_iff. exists v2; auto.
    + apply (Hd (v1.1)); simpl; split; auto.
      * rewrite in_map_iff. exists v1; split; auto.
        simpl_set. split; auto. intro C; subst; contradiction.
      * right. rewrite in_map_iff. exists v2; auto.
  - (*Feq*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    rewrite -> map_app, NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [Hn2 _]].
    rewrite in_app_iff in Hsub.
    destruct Hsub; [apply H | apply H0]; auto;
    apply (disj_sublist_lr Hd); apply sublist_map;
    [apply union_sublist_l | apply sublist_app_l |
      apply union_sublist_r | apply sublist_app_r].
  - (*Fbinop*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    rewrite -> map_app, NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [Hn2 _]].
    rewrite in_app_iff in Hsub.
    destruct Hsub; [apply H | apply H0]; auto;
    apply (disj_sublist_lr Hd); apply sublist_map;
    [apply union_sublist_l | apply sublist_app_l |
    apply union_sublist_r | apply sublist_app_r].
  - destruct Hsub; subst; auto.
  - destruct Hsub; subst; auto; contradiction.
  - destruct Hsub; subst; auto; contradiction.
  - (*Flet*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    inversion Hn; subst.
    rewrite -> map_app, NoDup_app_iff in H4.
    destruct H4 as [Hn1 [Hn2 _]].
    rewrite in_app_iff in Hsub; destruct Hsub;
    [apply H | apply H0]; auto.
    + apply (disj_sublist_lr Hd).
      * apply sublist_map. apply union_sublist_l.
      * apply incl_tl. apply sublist_map. apply sublist_app_l.
    + clear -Hd H3. (*need nodups for bound vars*)
      unfold disj in *.
      intros x [Hinx1 Hinx2].
      rewrite -> !in_map_iff in Hinx1 , Hinx2.
      destruct Hinx1 as [v1 [Hx Hinv1]]; subst.
      destruct Hinx2 as [v2 [Hv Hinv2]]; subst.
      apply (Hd (fst v1)).
      split.
      * rewrite in_map_iff. exists v1. split; auto. simpl_set; auto.
        vsym_eq v1 v.
        exfalso. apply H3. rewrite -> map_app, in_app_iff.
        right. rewrite in_map_iff. exists v2; auto.
      * simpl. right. rewrite -> map_app, in_app_iff; right.
        rewrite in_map_iff; exists v2; auto.
  - (*Fif*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    rewrite !in_app_iff in Hsub.
    rewrite -> !map_app, !NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [[Hn2 [Hn3 _]] _]].
    destruct_all; [apply H | apply H0 | apply H1]; auto;
    apply (disj_sublist_lr Hd); apply sublist_map.
    + apply union_sublist_l.
    + apply sublist_app_l.
    + eapply sublist_trans. apply union_sublist_l.
      apply union_sublist_r.
    + eapply sublist_trans. apply sublist_app_l.
      apply sublist_app_r.
    + eapply sublist_trans. apply union_sublist_r.
      apply union_sublist_r.
    + eapply sublist_trans. apply sublist_app_r.
      apply sublist_app_r.
  - (*Tmatch case*)
    destruct Hsub as [Hsub | Hsub]; subst; auto.
    rewrite in_app_iff in Hsub.
    rewrite -> !map_app, NoDup_app_iff in Hn.
    destruct Hn as [Hn1 [Hn2 _]].
    destruct Hsub as [Hsub | Hsub].
    + apply H; auto.
      apply (disj_sublist_lr Hd); apply sublist_map.
      * apply union_sublist_l.
      * apply sublist_app_l.
    + clear H Hn1. rewrite in_concat in Hsub.
      rewrite -> Forall_map, Forall_forall in H0.
      destruct Hsub as [ts [Hints Hintm]].
      rewrite in_map_iff in Hints.
      destruct Hints as [pt [Hts Hinpt]]; subst.
      rewrite -> concat_map, !map_map, NoDup_concat_iff in Hn2.
      destruct Hn2 as [Hn2 _].
      specialize (Hn2 (map fst (pat_fv pt.1 ++ fmla_bnd pt.2))).
      prove_hyp Hn2.
      {  rewrite in_map_iff. exists pt; auto. }
      rewrite -> map_app, NoDup_app_iff in Hn2.
      destruct Hn2 as [Hn1 [Hn2 [Hnotin _]]]. 
      apply (H0 _ Hinpt); auto.
      (*Prove manually*)
      intros x [Hinxfv Hinxbnd].
      destruct (in_dec string_dec x (map fst (pat_fv pt.1))).
      * (*If in pat_fv contradicts nodup*)
        apply (Hnotin _ i Hinxbnd).
      * (*Otherwise, use disj assumption*)
        apply (Hd x).
        rewrite -> !in_map_iff in Hinxfv, Hinxbnd.
        destruct Hinxfv as [v1 [Hx Hinv1]]; subst.
        destruct Hinxbnd as [v2 [Hvs Hinv2]].
        split.
        -- rewrite in_map_iff. exists v1. split; auto.
          simpl_set. right. exists pt. split; auto.
          simpl_set. split; auto. intro C.
          apply n. rewrite in_map_iff. exists v1. auto.
        -- rewrite in_map_iff. exists v2. split; auto.
          rewrite in_app_iff. right. rewrite in_concat.
          exists (pat_fv pt.1 ++ fmla_bnd pt.2).
          split; auto.
          ++ rewrite in_map_iff. exists pt; auto.
          ++ rewrite in_app_iff; auto.
Qed.

Definition subfmla_t_disj t Hn Hd f1 :=
  (proj_tm (subfmla_disj f1) t) Hn Hd.
Definition subfmla_f_disj f Hn Hd f1 :=
  (proj_fmla (subfmla_disj f1) f) Hn Hd.
  
  
(*4. Finally, want to show that no free variable duplicate
  names in all subterms (assuming previous conditions).
  This is easy because of previous lemmas*)

Lemma fv_nodup_subterm tm t f:
  (forall (Hbnd: NoDup (map fst (tm_bnd t))) 
    (Hfv: NoDup (map fst (tm_fv t)))
    (Hdisj: disj (map fst (tm_fv t)) (map fst (tm_bnd t)))
    (Hsub: In tm (subterms_t t)),
    NoDup (map fst (tm_fv tm))) /\
  (forall (Hbnd: NoDup (map fst (fmla_bnd f))) 
    (Hfv: NoDup (map fst (fmla_fv f)))
    (Hdisj: disj (map fst (fmla_fv f)) (map fst (fmla_bnd f)))
    (Hsub: In tm (subterms_f f)),
    NoDup (map fst (tm_fv tm))).
Proof.
  split; intros;
  apply NoDup_map_inj; try apply tm_fv_nodup;
  intros x y Hinx Hiny Hxy;
  [apply subterm_t_fv_in with(t:=t) in Hinx, Hiny |
    apply subterm_f_fv_in with(f:=f) in Hinx, Hiny]; auto;
  destruct Hinx; destruct Hiny;
  try solve[apply (NoDup_map_in Hbnd); auto];
  try solve[apply (NoDup_map_in Hfv); auto];
  exfalso; apply (Hdisj (fst x));
  split; rewrite in_map_iff;
  try solve[exists x; auto];
  solve[exists y; auto].
Qed.
  
Definition fv_nodup_subterm_t t Hbnd Hfv Hdisj tm :=
  (proj_tm (fv_nodup_subterm tm) t) Hbnd Hfv Hdisj.
Definition fv_nodup_subterm_f f Hbnd Hfv Hdisj tm :=
  (proj_fmla (fv_nodup_subterm tm) f) Hbnd Hfv Hdisj.

Lemma fv_nodup_subfmla f1 t f:
  (forall (Hbnd: NoDup (map fst (tm_bnd t))) 
    (Hfv: NoDup (map fst (tm_fv t)))
    (Hdisj: disj (map fst (tm_fv t)) (map fst (tm_bnd t)))
    (Hsub: In f1 (subfmla_t t)),
    NoDup (map fst (fmla_fv f1))) /\
  (forall (Hbnd: NoDup (map fst (fmla_bnd f))) 
    (Hfv: NoDup (map fst (fmla_fv f)))
    (Hdisj: disj (map fst (fmla_fv f)) (map fst (fmla_bnd f)))
    (Hsub: In f1 (subfmla_f f)),
    NoDup (map fst (fmla_fv f1))).
Proof.
  split; intros;
  apply NoDup_map_inj; try apply fmla_fv_nodup;
  intros x y Hinx Hiny Hxy;
  [apply subfmla_t_fv_in with(t:=t) in Hinx, Hiny |
    apply subfmla_f_fv_in with(f:=f) in Hinx, Hiny]; auto;
  destruct Hinx; destruct Hiny;
  try solve[apply (NoDup_map_in Hbnd); auto];
  try solve[apply (NoDup_map_in Hfv); auto];
  exfalso; apply (Hdisj (fst x));
  split; rewrite in_map_iff;
  try solve[exists x; auto];
  solve[exists y; auto].
Qed.
  
Definition fv_nodup_subfmla_t t Hbnd Hfv Hdisj tm :=
  (proj_tm (fv_nodup_subfmla tm) t) Hbnd Hfv Hdisj.
Definition fv_nodup_subfmla_f f Hbnd Hfv Hdisj tm :=
  (proj_fmla (fv_nodup_subfmla tm) f) Hbnd Hfv Hdisj.
  
(*And now, finally, we can prove the result that we want*)
Theorem wf_strong_rec_holds t f:
  (forall (Hwf: tm_wf_strong t), tm_wf_strong_rec t) /\
  (forall (Hwf: fmla_wf_strong f), fmla_wf_strong_rec f).
Proof.
  unfold tm_wf_strong_rec, fmla_wf_strong_rec.
  rewrite -> P_subterms_equiv, P_subfmlas_equiv. split;
  intros; unfold tm_wf_strong, fmla_wf_strong in *;
  destruct Hwf as [Hfv [Hbnd Hdisj]];
  split_all; auto; rewrite Forall_forall; auto.
  - intros tm Hsub. split_all.
    + apply (fv_nodup_subterm_t t); auto.
    + apply (bnd_nodup_subterm_t t); auto.
    + apply (subterm_t_disj t); auto.
  - intros f1 Hsub. split_all.
    + apply (fv_nodup_subfmla_t t); auto.
    + apply (bnd_nodup_subfmla_t t); auto.
    + apply (subfmla_t_disj t); auto.
  - intros tm Hsub. split_all.
    + apply (fv_nodup_subterm_f f); auto.
    + apply (bnd_nodup_subterm_f f); auto.
    + apply (subterm_f_disj f); auto.
  - intros f1 Hsub. split_all.
    + apply (fv_nodup_subfmla_f f); auto.
    + apply (bnd_nodup_subfmla_f f); auto.
    + apply (subfmla_f_disj f); auto.
Qed.

Definition tm_wf_strong_rec_holds t :=
  proj_tm wf_strong_rec_holds t.
Definition fmla_wf_strong_rec_holds f :=
  proj_fmla wf_strong_rec_holds f.
(*And therefore, the recursive structure adds nothing - but it
  helps us in our proofs above*)

(*Part 6: Prove that a_convert_all_t produces a strongly wf term, 
  if given a term with no duplicate free variables names*)

Lemma a_convert_all_t_strong_wf t l:
  NoDup (map fst (tm_fv t)) ->
  tm_wf_strong (a_convert_all_t t l).
Proof.
  intros Hnodup.
  unfold tm_wf_strong.
  split_all.
  - erewrite <- a_equiv_t_fv. apply Hnodup.
    apply a_convert_all_t_equiv.
  - apply a_convert_all_t_bnd_nodup.
  - intros x [Hinfv Hinbnd].
    apply a_convert_all_t_bnd_notin in Hinbnd.
    destruct Hinbnd.
    apply H. clear -Hinfv.
    rewrite -> !in_map_iff in *.
    destruct_all. exists x0. split; auto.
    erewrite alpha_equiv_t_fv.
    apply H0.
    apply a_convert_all_t_equiv.
Qed.

Lemma a_convert_all_f_strong_wf f l:
  NoDup (map fst (fmla_fv f)) ->
  fmla_wf_strong (a_convert_all_f f l).
Proof.
  intros Hnodup.
  unfold fmla_wf_strong.
  split_all.
  - erewrite <- a_equiv_f_fv. apply Hnodup.
    apply a_convert_all_f_equiv.
  - apply a_convert_all_f_bnd_nodup.
  - intros x [Hinfv Hinbnd].
    apply a_convert_all_f_bnd_notin in Hinbnd.
    destruct Hinbnd.
    apply H. clear -Hinfv.
    rewrite -> !in_map_iff in *.
    destruct_all. exists x0. split; auto.
    erewrite alpha_equiv_f_fv.
    apply H0.
    apply a_convert_all_f_equiv.
Qed.

(*Part 7: Give a function that checks if the term is wf, and if not, 
  alpha converts*)

(*Decide disjointness*)
Definition disjb {A: eqType} (l1 l2: list A) : bool :=
  (all (fun x => x \notin l2) l1).

Lemma disjP {A: eqType} (l1 l2: list A) :
  reflect (disj l1 l2) (disjb l1 l2).
Proof.
  rewrite /disjb/disj.
  case: (all (fun x : A => x \notin l2) l1) /allP => Hl1/=; last first.
  - move: Hl1 => /allP. rewrite -has_predC => /hasP/= Hex.
    apply ReflectF => C.
    case: Hex => [x] /inP Hinl1. rewrite negbK => /inP Hinl2.
    by apply (C x).
  - apply ReflectT => x [/inP Hinx1 /inP Hinx2].
    move: Hl1 => /(_ _ Hinx1). by rewrite Hinx2.
Qed.

(*Now, we give a function that transforms a term, alpha converting
  if needed if we don't already have new and distinct bound variables*)
Definition make_tm_wf (t: term) : term :=
  if uniq (map fst (tm_bnd t)) && disjb (map fst (tm_fv t)) (map fst (tm_bnd t))
  then t else a_convert_all_t t nil.

Lemma make_tm_wf_wf t:
  NoDup (map fst (tm_fv t)) ->
  tm_wf_strong (make_tm_wf t).
Proof.
  intros.
  unfold make_tm_wf.
  case: (uniq (map fst (tm_bnd t))) /Typechecker.uniqP => Hbnd/=;
  last by apply a_convert_all_t_strong_wf.
  case: (disjb (map fst (tm_fv t)) (map fst (tm_bnd t))) /disjP => Hdisj/=;
  last by apply a_convert_all_t_strong_wf.
  rewrite /tm_wf_strong; split_all; auto.
Qed.

(*And this is well-typed and has the same rep*)
Lemma make_tm_wf_typed {t ty}:
  term_has_type gamma t ty ->
  term_has_type gamma (make_tm_wf t) ty.
Proof.
  unfold make_tm_wf.
  destruct (uniq (map fst (tm_bnd t)) && disjb (map fst (tm_fv t)) (map fst (tm_bnd t))); auto.
  intros. apply a_convert_all_t_ty; auto.
Qed.

Lemma make_tm_wf_rep (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt) t ty
  (Hty1: term_has_type gamma t ty)
  (Hty2: term_has_type gamma (make_tm_wf t) ty):
  term_rep gamma_valid pd vt pf vv (make_tm_wf t) ty Hty2 =
  term_rep gamma_valid pd vt pf vv t ty Hty1.
Proof.
  revert Hty2.
  unfold make_tm_wf.
  destruct (uniq (map fst (tm_bnd t)) && disjb (map fst (tm_fv t)) (map fst (tm_bnd t)));
  intros.
  apply term_rep_irrel.
  erewrite term_rep_irrel.
  erewrite <- a_convert_all_t_rep. reflexivity.
Qed.


Definition make_fmla_wf (f: formula) : formula :=
  if uniq (map fst (fmla_bnd f)) && 
    disjb (map fst (fmla_fv f)) (map fst (fmla_bnd f))
  then f else a_convert_all_f f nil.

Lemma make_fmla_wf_wf f:
  NoDup (map fst (fmla_fv f)) ->
  fmla_wf_strong (make_fmla_wf f).
Proof.
  intros.
  unfold make_fmla_wf.
  case: (uniq (map fst (fmla_bnd f))) /Typechecker.uniqP => Hbnd/=;
  last by apply a_convert_all_f_strong_wf.
  case: (disjb (map fst (fmla_fv f)) (map fst (fmla_bnd f))) /disjP => Hdisj/=;
  last by apply a_convert_all_f_strong_wf.
  rewrite /fmla_wf_strong; split_all; auto.
Qed.

(*And this is well-typed and has the same rep*)
Lemma make_fmla_wf_typed {f}:
  formula_typed gamma f ->
  formula_typed gamma (make_fmla_wf f).
Proof.
  unfold make_fmla_wf.
  destruct (uniq (map fst (fmla_bnd f)) && 
    disjb (map fst (fmla_fv f)) (map fst (fmla_bnd f))); auto.
  intros. apply a_convert_all_f_typed; auto.
Qed.

Lemma make_fmla_wf_rep (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt) f
  (Hty1: formula_typed gamma f)
  (Hty2: formula_typed gamma (make_fmla_wf f)):
  formula_rep gamma_valid pd vt pf vv (make_fmla_wf f) Hty2 =
  formula_rep gamma_valid pd vt pf vv f Hty1.
Proof.
  revert Hty2.
  unfold make_fmla_wf.
  destruct (uniq (map fst (fmla_bnd f)) &&
  disjb (map fst (fmla_fv f)) (map fst (fmla_bnd f)));
  intros.
  apply fmla_rep_irrel.
  erewrite fmla_rep_irrel.
  erewrite <- a_convert_all_f_rep. reflexivity.
Qed.

(*Part 8: Combine all of the above to prove that type substitution on
  the result of this function results in the rep under a change
  of type variable valuation.
  All of the wf predicates disappear from the final theorem statement;
  we just need the term to have no duplicate free variable names
  (which is true for all terms and formulas we deal with)*)

(*And finally, we can type substitute for a term*)

Definition ty_subst_wf_tm (t: term) : term :=
  ty_subst_tm (make_tm_wf t).

Lemma ty_subst_wf_tm_typed t ty:
  NoDup (map fst (tm_fv t)) ->
  term_has_type gamma t ty ->
  term_has_type gamma (ty_subst_wf_tm t) (ty_subst' params tys ty).
Proof.
  intros Hn Hty. unfold ty_subst_wf_tm.
  apply ty_subst_t_ty.
  apply make_tm_wf_typed. auto.
  eapply wf_strong_pat_names_t.
  apply make_tm_wf_typed. apply Hty.
  apply tm_wf_strong_rec_holds.
  apply make_tm_wf_wf. auto.
Qed.

(*And now the full spec: given a term with no duplicate
  free variables, if we substitute with the given type
  substitution, this is the same as changing the type
  variable valuation accordingly and evaluating the original term*)
Theorem ty_subst_wf_tm_rep (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt) t ty
  (Hty1: term_has_type gamma t ty)
  (Hty2: term_has_type gamma (ty_subst_wf_tm t) (ty_subst' params tys ty)):
  NoDup (map fst (tm_fv t)) ->
  term_rep gamma_valid pd vt pf vv (ty_subst_wf_tm t) 
    (ty_subst' params tys ty) Hty2 =
  dom_cast (dom_aux pd) (Logic.eq_sym (v_subst_vt_with_args' 
    params tys params_len params_nodup vt ty))
    (term_rep gamma_valid pd 
      (vt_with_args vt params (map (v_subst vt) tys))
      pf (upd_vv_args params tys params_len params_nodup pd vt vv) t ty Hty1).
Proof.
  intros Hn.
  unfold ty_subst_wf_tm.
  erewrite ty_subst_t_rep.
  - rewrite make_tm_wf_rep. apply Hty1.
    intros. erewrite term_rep_irrel. reflexivity.
    Unshelve. apply make_tm_wf_typed; auto.
  - apply tm_wf_strong_rec_holds.  apply make_tm_wf_wf. auto.
  - intros. apply dom_cast_eq.
Qed.

Definition ty_subst_wf_fmla (f: formula) : formula :=
  ty_subst_fmla (make_fmla_wf f).

Lemma ty_subst_wf_fmla_typed f:
  NoDup (map fst (fmla_fv f)) ->
  formula_typed gamma f ->
  formula_typed gamma (ty_subst_wf_fmla f).
Proof.
  intros Hn Hty. unfold ty_subst_wf_fmla.
  apply ty_subst_f_ty.
  apply make_fmla_wf_typed. auto.
  eapply wf_strong_pat_names_f.
  apply make_fmla_wf_typed. apply Hty.
  apply fmla_wf_strong_rec_holds.
  apply make_fmla_wf_wf. auto.
Qed.

(*And now the full spec: given a formula with no duplicate
  free variables, if we substitute with the given type
  substitution, this is the same as changing the type
  variable valuation accordingly and evaluating the original term*)
Theorem ty_subst_wf_fmla_rep (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt) f 
  (Hty1: formula_typed gamma f)
  (Hty2: formula_typed gamma (ty_subst_wf_fmla f)):
  NoDup (map fst (fmla_fv f)) ->
  formula_rep gamma_valid pd vt pf vv (ty_subst_wf_fmla f) Hty2 =
  formula_rep gamma_valid pd 
    (vt_with_args vt params (map (v_subst vt) tys))
    pf (upd_vv_args params tys params_len params_nodup pd vt vv) f Hty1.
Proof.
  intros Hn.
  unfold ty_subst_wf_fmla.
  erewrite ty_subst_f_rep.
  - apply make_fmla_wf_rep.
    Unshelve. apply make_fmla_wf_typed; auto.
  - apply fmla_wf_strong_rec_holds. apply make_fmla_wf_wf. auto.
  - intros. apply dom_cast_eq.
Qed.

(*Type Vars of result*)

Lemma type_vars_subst_sort ty:
  (forall x, In x (type_vars ty) -> In x params) ->
  (forall t, In t tys -> is_sort t) ->
  null (type_vars (ty_subst' params tys ty)).
Proof.
  intros. induction ty; simpl; auto.
  - simpl in H. specialize (H _ (ltac:(auto))).
    destruct (in_dec typevar_eq_dec v params); try contradiction.
    simpl. unfold ty_subst; simpl.
    destruct (ty_subst_fun_cases params tys vty_int v).
    + apply H0. auto.
    + rewrite H1. reflexivity.
  - rewrite null_nil. apply big_union_nil_eq.
    rewrite Forall_forall in H1.
    intros. rewrite in_map_iff in H2.
    destruct H2 as [ty [Hx Hinty]]; subst.
    rewrite <- null_nil. apply H1; auto.
    intros. apply H. simpl.
    simpl_set. exists ty; auto.
Qed.

Lemma tm_type_vars_tmatch t ty ps:
  tm_type_vars (Tmatch t ty ps) =
  union typevar_eq_dec 
    (union typevar_eq_dec (tm_type_vars t)
      (big_union typevar_eq_dec pat_type_vars (map fst ps)))
    (union typevar_eq_dec (big_union typevar_eq_dec (fun x => tm_type_vars (snd x)) ps)
      (type_vars ty)).
Proof.
  simpl.
  f_equal.
  f_equal. induction ps; simpl; auto.
  destruct a; simpl. f_equal. auto.
Qed.

Lemma tm_type_vars_fmatch t ty ps:
  fmla_type_vars (Fmatch t ty ps) =
  union typevar_eq_dec 
    (union typevar_eq_dec (tm_type_vars t)
      (big_union typevar_eq_dec pat_type_vars (map fst ps)))
    (union typevar_eq_dec (big_union typevar_eq_dec (fun x => fmla_type_vars (snd x)) ps)
      (type_vars ty)).
Proof.
  simpl.
  f_equal.
  f_equal. induction ps; simpl; auto.
  destruct a; simpl. f_equal. auto.
Qed.

(*Two lists with the same elements have equal null*)
Lemma same_elts_null {A: Type} (l1 l2: list A):
  (forall x, In x l1 <-> In x l2) ->
  null l1 = null l2.
Proof.
  intros. destruct l1; destruct l2; simpl in *; auto; exfalso;
  apply (H a); auto.
Qed.

Lemma pat_type_vars_null p:
  null (pat_type_vars p) =
  null (match p with
| Pvar v => type_vars (snd v)
| Pconstr f tys ps => big_union typevar_eq_dec pat_type_vars ps
| Por p1 p2 => union typevar_eq_dec (pat_type_vars p1) (pat_type_vars p2)
| Pwild => nil
| Pbind p x => union typevar_eq_dec (pat_type_vars p) (type_vars (snd x))
end).
Proof.
  apply same_elts_null, pat_type_vars_rewrite.
Qed.

Lemma ty_subst_srts_vars_p p
  (Hallin: forall x, In x (pat_type_vars p) -> In x params)
  (Hsrts: forall t, In t tys -> is_sort t):
  null (pat_type_vars (ty_subst_p p)).
Proof.
  induction p; simpl; auto.
  - rewrite pat_type_vars_null. 
    apply type_vars_subst_sort; auto.
    intros. apply Hallin.
    apply pat_type_vars_rewrite. auto.
  - rewrite pat_type_vars_null.
    apply big_union_null_eq.
    intros p.
    rewrite in_map_iff.
    intros [p1 [Hp Hinp1]]; subst.
    rewrite Forall_forall in H.
    apply H; auto.
    intros.
    apply Hallin.
    apply pat_type_vars_rewrite. simpl_set.
    exists p1; auto.
  - rewrite pat_type_vars_null.
    apply union_null_eq; 
    [apply IHp1 | apply IHp2]; intros; apply Hallin, pat_type_vars_rewrite;
    simpl_set; auto.
  - rewrite pat_type_vars_null.
    apply union_null_eq.
    + apply IHp; intros; apply Hallin, pat_type_vars_rewrite;
      simpl_set; auto.
    + apply type_vars_subst_sort; auto; intros; apply Hallin,
      pat_type_vars_rewrite; simpl_set; auto.
Qed.

(*Could prove stronger theorem but this is ok*)
Lemma ty_subst_srts_vars
  (Hsrts: forall t, In t tys -> is_sort t) t f:
  (forall (Hallin: forall x, In x (tm_type_vars t) -> In x params),
    null (tm_type_vars (ty_subst_tm t))) /\
  (forall (Hallin: forall x, In x (fmla_type_vars f) -> In x params),
    null (fmla_type_vars (ty_subst_fmla f))).
Proof.
  revert t f; apply term_formula_ind; intros; auto.
  - apply type_vars_subst_sort; auto.
  - cbn. apply union_null_eq.
    + apply big_union_null_eq.
      unfold ty_subst_list'.
      intros ty. rewrite in_map_iff.
      intros [ty' [Hty Hinty']]; subst.
      apply type_vars_subst_sort; auto.
      intros. apply Hallin. simpl. simpl_set.
      left. exists ty'; auto.
    + apply big_union_null_eq.
      intros tm. rewrite in_map_iff.
      intros [tm1 [Htm Hintm1]]; subst.
      rewrite Forall_forall in H.
      apply H; auto.
      intros.
      apply Hallin; simpl; simpl_set.
      right. exists tm1; auto.
  - apply union_null_eq; [apply union_null_eq |];
    [apply H | apply H0 | apply type_vars_subst_sort]; auto;
    intros; apply Hallin; simpl; simpl_set; auto.
  - apply union_null_eq; [| apply union_null_eq];
    [apply H | apply H0 | apply H1]; intros;
    apply Hallin; simpl; simpl_set; auto.
  - setoid_rewrite tm_type_vars_tmatch in Hallin.
    rewrite tm_type_vars_tmatch. 
    apply union_null_eq.
    + apply union_null_eq.
      * apply H; auto; intros; apply Hallin; intros; simpl_set; auto.
      * apply big_union_null_eq.
        intros p.
        rewrite in_map_iff.
        intros [p1 [Hp1 Hinp1]]; subst.
        rewrite in_map_iff in Hinp1.
        destruct Hinp1 as [pt [Hp1 Hinpt]]; subst; simpl.
        apply ty_subst_srts_vars_p; auto.
        intros; apply Hallin; simpl_set; left.
        right. exists (fst pt); split; auto.
        rewrite in_map_iff. exists pt; auto.
    + apply union_null_eq.
      * apply big_union_null_eq.
        intros pt.
        rewrite in_map_iff.
        intros [pt1 [Hpt Inpt1]]; subst; simpl.
        rewrite -> Forall_map, Forall_forall in H0.
        apply H0; auto.
        intros. apply Hallin; simpl_set.
        right. left. exists pt1. auto.
      * apply type_vars_subst_sort; auto.
        intros. apply Hallin; simpl_set; auto.
  - cbn in *.
    apply union_null_eq.
    + apply H. intros; apply Hallin; simpl_set; auto.
    + apply type_vars_subst_sort; auto; intros; apply Hallin;
      simpl_set; auto.
  - cbn. apply union_null_eq.
    + apply big_union_null_eq.
      unfold ty_subst_list'.
      intros ty. rewrite in_map_iff.
      intros [ty' [Hty Hinty']]; subst.
      apply type_vars_subst_sort; auto.
      intros. apply Hallin. simpl. simpl_set.
      left. exists ty'; auto.
    + apply big_union_null_eq.
      intros tm. rewrite in_map_iff.
      intros [tm1 [Htm Hintm1]]; subst.
      rewrite Forall_forall in H.
      apply H; auto.
      intros.
      apply Hallin; simpl; simpl_set.
      right. exists tm1; auto.
  - apply union_null_eq.
    + apply type_vars_subst_sort; auto;
      intros; apply Hallin; simpl; simpl_set; auto.
    + apply H; intros; apply Hallin; simpl; simpl_set; auto.
  - apply union_null_eq; [| apply union_null_eq];
    [apply type_vars_subst_sort | apply H | apply H0];
    auto; intros; apply Hallin; simpl; simpl_set; auto.
  - apply union_null_eq; [apply H | apply H0]; auto;
    intros; apply Hallin; simpl; simpl_set; auto.
  - apply union_null_eq; [apply union_null_eq |];
    [apply H | apply H0 | apply type_vars_subst_sort];
    auto; intros; apply Hallin; simpl; simpl_set; auto.
  - apply union_null_eq; [|apply union_null_eq];
    [apply H | apply H0 | apply H1]; intros;
    apply Hallin; simpl; simpl_set; auto.
  - setoid_rewrite tm_type_vars_fmatch in Hallin.
    rewrite tm_type_vars_fmatch. 
    apply union_null_eq.
    + apply union_null_eq.
      * apply H; auto; intros; apply Hallin; intros; simpl_set; auto.
      * apply big_union_null_eq.
        intros p.
        rewrite in_map_iff.
        intros [p1 [Hp1 Hinp1]]; subst.
        rewrite in_map_iff in Hinp1.
        destruct Hinp1 as [pt [Hp1 Hinpt]]; subst; simpl.
        apply ty_subst_srts_vars_p; auto.
        intros; apply Hallin; simpl_set; left.
        right. exists (fst pt); split; auto.
        rewrite in_map_iff. exists pt; auto.
    + apply union_null_eq.
      * apply big_union_null_eq.
        intros pt.
        rewrite in_map_iff.
        intros [pt1 [Hpt Inpt1]]; subst; simpl.
        rewrite -> Forall_map, Forall_forall in H0.
        apply H0; auto.
        intros. apply Hallin; simpl_set.
        right. left. exists pt1. auto.
      * apply type_vars_subst_sort; auto.
        intros. apply Hallin; simpl_set; auto.
Qed.

Definition ty_subst_srts_vars_t Hsrts t :=
  proj_tm (ty_subst_srts_vars Hsrts) t.
Definition ty_subst_srts_vars_f Hsrts f :=
  proj_fmla (ty_subst_srts_vars Hsrts) f.


Lemma make_fmla_wf_type_vars f:
  fmla_type_vars (make_fmla_wf f) = fmla_type_vars f.
Proof.
  unfold make_fmla_wf.
  destruct ( uniq (map fst (fmla_bnd f)) && disjb (map fst (fmla_fv f)) (map fst (fmla_bnd f)));
  auto.
  symmetry.
  apply a_equiv_f_type_vars.
  apply a_convert_all_f_equiv.
Qed.

End TySubst.