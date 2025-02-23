Require Import Relations.
From Proofs Require Import Task.
Set Bullet Behavior "Strict Subproofs".

(*Maybe move elsewhere not sure*)

(*Reason about relations (of terms, tasks, etc) and how properties (typing, semantics, soundess) preserved*)

Section Typing.

(*Lots to prove about context*)

(*1. Signatures*)
Lemma a_equiv_syms_of_def (d1 d2: def):
  a_equiv_def d1 d2 ->
  funsyms_of_def d1 = funsyms_of_def d2 /\
  predsyms_of_def d1 = predsyms_of_def d2 /\
  typesyms_of_def d1 = typesyms_of_def d2.
Proof.
  unfold a_equiv_def. unfold funsyms_of_def. destruct d1 as [m1 | l1 | l1 | fd1 | t1 | f1 | p1 ]; 
  destruct d2 as [m2 | l2 | l2 | fd2 | t2 | f2 |  p2]; try discriminate; simpl.
  - destruct (mut_adt_eqb_spec m1 m2); subst; auto. discriminate.
  - rewrite andb_true. intros [Hlen Hall]. apply Nat.eqb_eq in Hlen.
    apply and_assoc. split; auto.
    generalize dependent l2. induction l1 as [| x1 t1 IH]; intros [| x2 t2]; simpl; try discriminate; auto.
    intros Hlen. rewrite all2_cons, andb_true. intros [Halpha Hall].
    specialize (IH t2 ltac:(auto) Hall). destruct_all.
    destruct x1; destruct x2; auto; try discriminate.
    + simpl in Halpha. destruct (funsym_eqb_spec f f0); subst; auto; [|discriminate].
      split; auto; f_equal; auto.
    + simpl in Halpha. destruct (predsym_eqb_spec p p0); subst; auto; [|discriminate].
      split; auto; f_equal; auto.
  - rewrite andb_true. intros [Hlen Hall]. apply Nat.eqb_eq in Hlen. split_all; auto.
    generalize dependent l2. induction l1 as [| x1 t1 IH]; intros [| x2 t2]; simpl; try discriminate; auto.
    intros Hlen. rewrite all2_cons, andb_true. intros [Halpha Hall]. destruct x1; destruct x2; auto.
    simpl in Halpha. destruct (predsym_eqb_spec p p0); subst; f_equal; auto. discriminate.
  - destruct fd1; destruct fd2; simpl; try discriminate; rewrite andb_true; intros [Heq _]; split_all; auto.
    + destruct (funsym_eqb_spec f f0); subst; auto. discriminate.
    + destruct (predsym_eqb_spec p p0); subst; auto. discriminate.
  - destruct (typesym_eqb_spec t1 t2); subst; auto. discriminate.
  - destruct (funsym_eqb_spec f1 f2); subst; auto. discriminate.
  - destruct (predsym_eqb_spec p1 p2); subst; auto. discriminate.
Qed.

(*Corollary: idents*)
Lemma a_equiv_idents_of_def (d1 d2: def):
  a_equiv_def d1 d2 ->
  idents_of_def d1 = idents_of_def d2.
Proof.
  intros Halpha.
  unfold idents_of_def. 
  apply a_equiv_syms_of_def in Halpha.
  destruct Halpha as [Hfuns [Hpreds Htys]].
  rewrite Hfuns, Hpreds, Htys. reflexivity.
Qed.

(*And now, signatures are equal*)

Lemma a_equiv_sig (g1 g2: context) :
  a_equiv_ctx g1 g2 ->
  sig_f g1 = sig_f g2 /\ sig_p g1 = sig_p g2 /\ sig_t g1 = sig_t g2 /\
  mut_of_context g1 = mut_of_context g2.
Proof.
  unfold a_equiv_ctx. rewrite andb_true.
  intros [Hlen Halpha]. apply Nat.eqb_eq in Hlen.
  generalize dependent g2. induction g1 as [| d1 g1 IH]; intros [| d2 g2]; try discriminate; auto.
  simpl. intros Hlen. rewrite all2_cons. rewrite andb_true; intros [Hdef Halpha].
  rewrite !sig_f_cons, !sig_p_cons, !sig_t_cons.
  pose proof (a_equiv_syms_of_def _ _ Hdef) as [Hfuns [Hpreds Htys]].
  rewrite Hfuns, Hpreds, Htys.
  specialize (IH g2 ltac:(auto) Halpha).
  destruct IH as [Hf [Hp [Ht Hmut]]].
  rewrite Hf, Hp, Ht. split_all; try reflexivity.
  (*Now prove mut*)
  destruct d1; destruct d2; try discriminate; auto.
  simpl in Hdef. destruct (mut_adt_eqb_spec m m0); subst; f_equal; auto; discriminate.
Qed.

(*Nonempty def is preserved*)
Lemma a_equiv_nonempty_def (d1 d2: def):
  a_equiv_def d1 d2 ->
  nonempty_def d1 ->
  nonempty_def d2.
Proof.
  unfold a_equiv_def. unfold funsyms_of_def. destruct d1 as [m1 | l1 | l1 | fd1 | t1 | f1 | p1 ]; 
  destruct d2 as [m2 | l2 | l2 | fd2 | t2 | f2 |  p2]; try discriminate; simpl; auto.
  - destruct (mut_adt_eqb_spec m1 m2); try discriminate. subst. auto.
  - destruct l1; destruct l2; simpl; auto.
  - rewrite !andb_true. intros [Hlen Hall] [Hnotnull Hall1].
    split. { destruct l1; destruct l2; auto. }
    clear Hnotnull. generalize dependent l2.
    induction l1 as [| x1 t1 IH]; intros [| x2 t2]; simpl; auto; try discriminate.
    intros Hlen. rewrite !all2_cons, !andb_true. intros [Halpha Hall].
    destruct x1; destruct x2; simpl in *. destruct (predsym_eqb p p0); [|discriminate].
    destruct l; destruct l0; auto.
Qed.

(*As is [valid_constrs_def]*)
Lemma a_equiv_valid_constrs_def (d1 d2: def):
  a_equiv_def d1 d2 ->
  valid_constrs_def d1 ->
  valid_constrs_def d2.
Proof.
  unfold a_equiv_def. unfold funsyms_of_def. destruct d1 as [m1 | l1 | l1 | fd1 | t1 | f1 | p1 ]; 
  destruct d2 as [m2 | l2 | l2 | fd2 | t2 | f2 |  p2]; try discriminate; auto; simpl.
  - destruct (mut_adt_eqb_spec m1 m2); try discriminate. subst. auto.
  - intros Hall. 
    assert (Hfuns: funsyms_of_def (recursive_def l1) = funsyms_of_def (recursive_def l2)). {
      apply a_equiv_syms_of_def; auto. }
    simpl in Hfuns. rewrite Hfuns. auto.
  - intros Hall. 
    assert (Hfuns: funsyms_of_def (nonrec_def fd1) = funsyms_of_def (nonrec_def fd2)). {
      apply a_equiv_syms_of_def; auto. }
    simpl in Hfuns. rewrite Hfuns. auto.
  - rewrite !andb_true_r. destruct (funsym_eqb_spec f1 f2); subst; auto.
Qed.

Import Alpha.

(*TODO: move*)
Lemma list_to_amap_none {A B: Type} `{countable.Countable A} (l: list (A * B)) x:
  amap_lookup (list_to_amap l) x = None <-> ~ In x (map fst l).
Proof.
  induction l as [| [x1 y1] t IH]; simpl.
  - rewrite amap_empty_get. split; auto.
  - rewrite amap_set_lookup_none_iff, IH. tauto.
Qed.

(*This all comes from properties of alpha equivalence*)
Lemma a_equiv_funpred_def_valid_type gamma (fd1 fd2: funpred_def):
  a_equiv_funpred_def fd1 fd2 ->
  funpred_def_valid_type gamma fd1 ->
  funpred_def_valid_type gamma fd2.
Proof.
  unfold a_equiv_funpred_def. 
  (*Useful in both cases*)
  assert (Hmaptys: forall (vs1 vs2: list vsymbol)
    (Hlen : length vs1 = length vs2)
    (Hnodup : NoDup (map fst vs1))
    (Heq : map snd vs1 = map snd vs2),
    forall x y : vsymbol, amap_lookup (list_to_amap (combine vs1 vs2)) x = Some y -> snd x = snd y).
  {
    intros vs1 vs2 Hlen Hnodup Heq x y.
    rewrite list_to_amap_lookup.
    2: { rewrite map_fst_combine; auto. eapply NoDup_map_inv; eauto. }
    rewrite in_combine_iff by auto. intros [i [Hi Hxy]].
    specialize (Hxy vs_d vs_d). inversion Hxy; subst; clear Hxy.
    apply (f_equal (fun l => nth i l vty_int)) in Heq.
    rewrite !map_nth_inbound with (d2:=vs_d) in Heq; try lia. auto.
  }
  (*And prove the free var case: it is complicated*)
  assert (Hfvs: forall (A: Type) (fv: A -> aset vsymbol) (vs1 vs2: list vsymbol) (b1 b2: A)
    (Hlen: length vs1 = length vs2)
    (Halpha: aset_filter (fun x : vsymbol => negb (amap_mem x (list_to_amap (combine vs1 vs2)))) (fv b1) =
             aset_filter (fun x : vsymbol => negb (amap_mem x (list_to_amap (combine vs2 vs1)))) (fv b2))
    (Hsubfv: asubset (fv b1) (list_to_aset vs1))
    (Hnodup2: NoDup (map fst vs2)),
    asubset (fv b2) (list_to_aset vs2)).
  {
    (*Free vars a bit more complicated: have filter condition for everything else*)
    (*Idea: we know that free vars of b1 \ vs1 = fv of b2 \ vs2 - but by condition LHS is empty
      so RHS also empty, so all free vars of b2 in vs2*)
    intros.
    rewrite !asubset_def in *. intros x Hmemx.
    destruct (aset_mem_dec x (list_to_aset vs2)) as [| Hnotin]; auto.
    exfalso. assert (Hnotin': ~ In x vs2). { revert Hnotin. simpl_set. auto. }
    assert (Hin: aset_mem x (aset_filter 
      (fun x => negb (amap_mem x (list_to_amap (combine vs2 vs1)))) (fv b2))).
    {
      simpl_set. split; auto. rewrite amap_mem_spec.
      destruct (amap_lookup (list_to_amap (combine vs2 vs1)) x) as [y|] eqn : Hget; simpl; auto.
      apply list_to_amap_lookup in Hget.
      2: { apply map_fst_combine_nodup; eapply NoDup_map_inv; eauto. }
      apply in_combine_l in Hget. contradiction.
    }
    rewrite <- Halpha in Hin. simpl_set. destruct Hin as [Hinfv Hnotin1].
    (*Now contradicts subset of vs1*)
    specialize (Hsubfv _ Hinfv). simpl_set. 
    rewrite amap_mem_spec in Hnotin1.
    destruct (amap_lookup (list_to_amap (combine vs1 vs2)) x) as [y|] eqn : Hget; auto.
    rewrite list_to_amap_none in Hget. rewrite map_fst_combine in Hget; auto.
  }
  (*Now all goals are easy*)
  destruct fd1 as [f1 vs1 b1 | p1 vs1 b1]; destruct fd2 as [f2 vs2 b2 | p2 vs2 b2];
  simpl; auto; try discriminate.
  - rewrite !andb_true. intros [[[[[Hf12 Hlen] Hmap2] _] Hn2] Halpha] [Hty [Hsubfv [Hsubty [Hnodup Hmapsnd]]]].
    destruct (nodup_NoDup string_dec (map fst vs2)) as [Hnodup2|]; [|discriminate].
    destruct (funsym_eqb_spec f1 f2); [subst | discriminate].
    destruct (list_eqb_spec _ vty_eq_spec (map snd vs1) (map snd vs2)) as [Heq|]; [subst | discriminate].
    apply Nat.eqb_eq in Hlen.
    split_all; auto.
    + eapply alpha_equiv_t_type; eauto.
    + apply alpha_t_fv_filter in Halpha. eauto.
    + eapply alpha_equiv_t_type_vars in Halpha; auto. rewrite <- Halpha; auto. apply Hmaptys; auto.
    + congruence.
  - (*predsyms symmetric*)
    rewrite !andb_true. intros [[[[[Hf12 Hlen] Hmap2] _] Hn2] Halpha] [Hty [Hsubfv [Hsubty [Hnodup Hmapsnd]]]].
    destruct (nodup_NoDup string_dec (map fst vs2)) as [Hnodup2|]; [|discriminate].
    destruct (predsym_eqb_spec p1 p2); [subst | discriminate].
    destruct (list_eqb_spec _ vty_eq_spec (map snd vs1) (map snd vs2)) as [Heq|]; [subst | discriminate].
    apply Nat.eqb_eq in Hlen.
    split_all; auto.
    + eapply alpha_equiv_f_typed; eauto.
    + apply alpha_f_fv_filter in Halpha. eauto.
    + eapply alpha_equiv_f_type_vars in Halpha; auto. rewrite <- Halpha; auto. apply Hmaptys; auto.
    + congruence.
Qed.

(*Termination is very tricky, since we rely on the syntactic bound pattern variables.
  We can prove a more general lemma (TODO: can we?): as long as small and hd are
  consistent with the alpha maps, then the two terms are termination-equivalent.
  And this property is inductive.
  In the end, small is empty and hd is just the corresponding var, which is
  alpha equivalent by the condition*)

(*Basically, (later) just prove we can change bodies of fn and pn and still OK*)
(*temp*)
Require Import eliminate_algebraic_typing.
(*NOTE: I DO need the condition of alpha equivalence*)
(*We need typing here because we need to know things about lengths*)
Lemma a_equiv_decrease_fun gamma (fs: list fn) (ps: list pn)
  (Hwf1: Forall fn_wf fs) (Hwf2: Forall pn_wf ps) (*only need wf for index*) 
    (m: mut_adt) (vs: list vty) t1 f1:
  (forall (ty: vty) (Hty: term_has_type gamma t1 ty) 
      (small1 small2: aset vsymbol) (hd1 hd2: option vsymbol) (t2: term) (ty: vty)
      (m1 m2: amap vsymbol vsymbol)
      (*Think we need: m1(small1) = small2 and m2(small2) = small1 - OK because we only
        ever care when we add matched vars, which have nice properties*)
      (Hsmall1: forall x y, amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> aset_mem x small1 -> aset_mem y small2)
      (* (Hsmall2: forall x y, amap_lookup m2 y = Some x -> aset_mem y small2 -> aset_mem x small1) *)
      (*NOTE: dont know if I need iff, just trying to prove strongest thing i can*)
      (* (Hhdn: hd1 = None <-> hd2 = None) *) (*TODO: is this inductive? Can we ever change one but not other?*)
      (Hhd1: forall x y, amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> hd1 = Some x <-> hd2 = Some y)
      (* (Hhd2: forall x y, amap_lookup m2 y = Some x -> hd2 = Some y -> hd1 = Some x) *)
      (*All small variables need to be in the map*)
      (Hallin1: forall x, aset_mem x small1 -> amap_mem x m1)
      (* (Hallin2: forall x, aset_mem x small2 -> amap_mem x m2) *)
      (Halpha: alpha_equiv_t m1 m2 t1 t2)
      (Hdec: decrease_fun fs ps small1 hd1 m vs t1),
      decrease_fun fs ps small2 hd2 m vs t2) /\
  (forall (Hty: formula_typed gamma f1) (small1 small2: aset vsymbol) (hd1 hd2: option vsymbol) (f2: formula)
      (m1 m2: amap vsymbol vsymbol)
      (*Think we need: m1(small1) = small2 and m2(small2) = small1 - OK because we only
        ever care when we add matched vars, which have nice properties*)
      (Hsmall1: forall x y, amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> aset_mem x small1 -> aset_mem y small2)
      (* (Hsmall2: forall x y, amap_lookup m2 y = Some x -> aset_mem y small2 -> aset_mem x small1) *)
      (Hhd1: forall x y, amap_lookup m1 x = Some y -> hd1 = Some x -> hd2 = Some y)
     (*  (Hhd2: forall x y, amap_lookup m2 y = Some x -> hd2 = Some y -> hd1 = Some x) *)
      (*All small variables need to be in the map*)
      (Hallin1: forall x, aset_mem x small1 -> amap_mem x m1)
      (* (Hallin2: forall x, aset_mem x small2 -> amap_mem x m2) *)
      (Halpha: alpha_equiv_f m1 m2 f1 f2)
      (Hdec: decrease_pred fs ps small1 hd1 m vs f1),
      decrease_pred fs ps small2 hd2 m vs f2).
Proof.
  revert t1 f1. apply term_formula_ind_typed; simpl.
  - intros. destruct t2; try discriminate. constructor.
  - intros. destruct t2; try discriminate. constructor.
  - intros. destruct t2; try discriminate. constructor.
  - (*Tfun - interesting case 1*)
    intros f1 tys1 tms1 IH Hty small1 small2 hd1 hd2 t2 ty m1 m2 Hsmall1 (*Hsmall2 *) Hhd1 (*Hhd2*) Hallin1 Halpha Hdec.
    destruct t2 as [| | f2 tys2 tms2 | | | |]; try discriminate.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Hfs Hlen] Htys] Hall].
    repeat simpl_sumbool. apply Nat.eqb_eq in Hlen. 
    (*inductive case is same*)
    assert (Hold: Forall (decrease_fun fs ps small1 hd1 m vs) tms1). {
      inversion Hdec; subst; auto.
      rewrite Forall_forall; auto.
    }
    assert (Hind: Forall (decrease_fun fs ps small2 hd2 m vs) tms2). {
      apply forall2_snd_irrel in IH.
      2: { unfold ty_subst_list; inversion Hty; subst; solve_len. }
      rewrite Forall_forall in IH, Hold |- *.
      intros tm Hintm. 
      rewrite all2_forall with (d1:=tm_d)(d2:=tm_d) in Hall by auto.
      destruct (In_nth _ _ tm_d Hintm) as [i [Hi Htm]]. subst.
      specialize (Hall i (ltac:(lia))).
      apply IH with (x:=(nth i tms1 tm_d))(small1:=small1)(hd1:=hd1)(m1:=m1)(m2:=m2); auto.
      { apply nth_In; auto. lia. }
      apply Hold, nth_In; lia.
    }
    inversion Hdec; subst.
    + (*In case*)
      (*Idea: we know that idxth element ot tms1 is x, so we know there is var y alpha equivalent to x
        By the allin condition, we know that m1(x) = y and m2(y) = x, so
        by the Hsmall condition, we know that y is in small, as we wanted*)
      assert (Halpha: alpha_equiv_t m1 m2 (nth (sn_idx f_decl) tms1 tm_d) (nth (sn_idx f_decl) tms2 tm_d)).
      {
        rewrite all2_forall in Hall by auto. apply Hall.
        rewrite Forall_forall in Hwf1. apply Hwf1 in H2. unfold fn_wf in H2.
        unfold sn_wf in H2. destruct H2 as [[Hidx [Hlen' _]]Hsym].
        inversion Hty; subst. clear -H7 Hidx Hlen' Hsym.
        rewrite H7, Hsym, <- Hlen'. auto.
      }
      rewrite H9 in Halpha.
      simpl in Halpha.
      destruct (nth (sn_idx f_decl) tms2 tm_d) as [| y| | | | |] eqn : Hnth2; try discriminate.
      assert (Hinsmall: aset_mem y small2).
      {
        unfold alpha_equiv_var in Halpha. assert (Hinsmall1:=H4).
        apply Hallin1 in H4. rewrite amap_mem_spec in H4. 
        destruct (amap_lookup m1 x) as [z|] eqn : Hget1; [|discriminate].
        destruct (amap_lookup m2 y) as [z1|] eqn : Hget2; [|discriminate].
        vsym_eq y z; try discriminate. vsym_eq x z1; try discriminate.
        specialize (Hsmall1 _ _ Hget1 Hget2 Hinsmall1). auto.
      }
      eapply Dec_fun_in; eauto.
    + (*Now notin*)
      apply Dec_fun_notin; eauto. rewrite Forall_forall in Hind; auto.
  - (*Tlet*)
    intros tm1 v1 tm2 _ IH1 IH2 small1 small2 hd1 hd2 t2 _ m1 m2 Hsmall1 Hhd1 Hallin1 Halpha Hdec.
    destruct t2 as [| | | tm3 v2 tm4 | | |]; try discriminate.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[Hty Halpha1] Halpha2].
    inversion Hdec; subst.
    constructor; auto.
    + eapply IH1; eauto. exact vty_int.
    + eapply IH2. 5: apply Halpha2. 5: eauto. exact vty_int.
      * intros x y. rewrite !amap_set_lookup_iff.
        intros [[Hx Hy] | [Hx Hlook]]; subst.
        -- (*Idea: get contradiction: remove both at once*)
          simpl_set. intros; destruct_all; contradiction.
        -- simpl_set. (*Need both to get the contradiction here for y and v2*)
          intros [[Hy' Hx'] | [Hy' Hlook']]; subst; try contradiction.
          intros [Hmemx _].
          specialize (Hsmall1 _ _ Hlook Hlook' Hmemx). auto.
      * unfold upd_option.
        intros x y. rewrite !amap_set_lookup_iff. 
        intros [[Hx Hy] | [Hx Hlook]]; subst.
        -- intros _. unfold upd_option. split.
          ++ destruct hd1; try discriminate. vsym_eq x v; try discriminate. inv Hsome.
            contradiction.
          ++ destruct hd2; try discriminate. vsym_eq y v; try discriminate. inv Hsome.
            contradiction.
        -- intros [[Hy' Hx'] | [Hy' Hlook']]; subst; try contradiction.
          specialize (Hhd1 _ _ Hlook Hlook').
          split.
          ++ destruct hd1; try discriminate. vsym_eq v1 v; try discriminate. inv Hsome.
            replace hd2 with (Some y) by (symmetry; apply Hhd1; auto). vsym_eq v2 y.
          ++ destruct hd2; try discriminate. vsym_eq v2 v; try discriminate. inv Hsome.
            replace hd1 with (Some x) by (symmetry; apply Hhd1; auto). vsym_eq v1 x. 
      * (*This is easy - strictly easier to satisfy*)
        intros x Hmemx. simpl_set. destruct Hmemx as [Hmemx Hnotv1].
        apply Hallin1 in Hmemx. rewrite amap_mem_set_iff. auto.
  - admit.
  - (*Tmatch is hard case*)
    (*START*)


    Print decrease_fun.


      *

 Search amap_mem amap_set.

        --
            destruct hd2.
            destruct hd2 


 unfold upd_option.


 (*How do we know that y is not v2?*)



 Search amap_lookup amap_set.

 eauto.

    Print decrease_fun.


| Dec_tlet : forall (small : aset vsymbol) (hd : option vsymbol) (m : mut_adt) 
                 (vs : list vty) (t1 : term) (v : vsymbol) (t2 : term),
               decrease_fun fs0 ps0 small hd m vs t1 ->
               decrease_fun fs0 ps0 (aset_remove v small) (upd_option hd v) m vs t2 ->
               decrease_fun fs0 ps0 small hd m vs (Tlet t1 v t2)



      (*Now only inductive case left*) 
      



      Print decrease_fun.




 Print decrease_fun. 
    inversion Hdec; subst.


decrease_fun (fs : list fn) (ps : list pn)
  : aset vsymbol -> option vsymbol -> mut_adt -> list vty -> term -> Prop :=
*)

(*The more interesting one: [valid_def] is preserved*)
Lemma a_equiv_valid_def gamma (d1 d2: def):
  a_equiv_def d1 d2 ->
  valid_def gamma d1 ->
  valid_def gamma d2.
Proof.
  unfold a_equiv_def. unfold funsyms_of_def. destruct d1 as [m1 | l1 | l1 | fd1 | t1 | f1 | p1 ]; 
  destruct d2 as [m2 | l2 | l2 | fd2 | t2 | f2 |  p2]; try discriminate; auto; simpl.
  - destruct (mut_adt_eqb_spec m1 m2); subst; auto. discriminate.
  - (*Need to split: 1 needs induction, other does not*)
    rewrite andb_true. intros [Hlen Hall].
    unfold funpred_valid. intros [Hallval Hterm].
    (*First prove valid*)
    assert (Hval2: Forall (funpred_def_valid_type gamma) l2).
    {
      (*This one is more straightforward: TODO: single case in other lemma for nonrec*)
      clear Hterm. 
      generalize dependent l2. induction l1 as [| fd1 l1 IH]; intros [| fd2 l2]; simpl; try discriminate; auto.
      intros Hlen. rewrite all2_cons, andb_true. intros [Halpha Hall]. 
      inversion Hallval; subst.
      constructor; auto.
      eapply a_equiv_funpred_def_valid_type; eauto.
    }
    split; auto.  (*Tricky part: termination*)
    unfold funpred_def_term_exists in *.
    destruct Hterm as [m [params [vs [is Hterm]]]].
    exists m. exists params. exists vs. exists is.
    unfold funpred_def_term in *.
    destruct Hterm as [Hl1 [Hlenvs [m_in [Hlenis [Hargs [Htys1 [Htys2 [Hparams1 [Hparams2 [Hdec1 Hdec2]]]]]]]]]].
    split_all; auto.
    * intro C; subst. destruct l1; auto.
    * apply Nat.eqb_eq in Hlen; congruence.
    * (*TODO: prove equivalence of [split_funpred_defs] - each is pairwise equiv/alpha equiv*)
      admit.
    * Print funpred_defs_to_sns. (*And likewise prove for [funpred_defs_to_sns]*)
      admit.
    * admit.
    * admit.
    * admit.
    * (*Here is the challenging part*)
      unfold funpred_def_valid_type in Hval2.


rewrite Forall_forall in Hval2.
      unfold funpred
      Print decrease_fun.
      (*Maybe we can say: 
        1. suppose all vars in small and hd are free in term (do we need this?). 
          Then if two terms are alpha equivalent,
          then they are also termination-equivalent under small and hd
        2. If fn and fn' (and likewise for pn) are equal mod alpha equiv, then
          termination-equivalent

suppose alll vars are in *)


 Print split_funpred_defs.


      
      Search funpred_def_term.
      Print funpred_def_term.




(*TODO: funpred_def in new lemma i think*)
    rewrite andb_true. intros [Hlen Hall]. 
    generalize dependent l2. induction l1 as [| fd1 l1 IH]; intros [| fd2 l2]; try discriminate; auto; simpl.
    intros Hlen. rewrite all2_cons, andb_true. intros [Halpha Hall].
    unfold funpred_valid.
    specialize (IH _ Hlen Hall). unfold funpred_valid in IH.
    intros [Hval1 Hval2].
    inversion Hval1 as [| ? ? Hvalfd1 Hvall1]; subst.
    Print funpred_def_term_exists.
    split. { inversion Hval1; subst. constructor; auto.

 
    Search funpred_valid.

 simpl.
    




Print valid_constrs_def.
(**)


Lemma a_equiv_valid_context (g1 g2: context):
  a_equiv_ctx g1 g2 ->
  valid_context g1 ->
  valid_context g2. 
Proof.
  unfold a_equiv_ctx. rewrite andb_true.
  intros [Hlen Halpha]. apply Nat.eqb_eq in Hlen.
  generalize dependent g2. induction g1 as [| d1 g1 IH]; intros [| d2 g2]; try discriminate; auto.
  simpl. intros Hlen. rewrite all2_cons. rewrite andb_true; intros [Hdef Halpha].
  intros Hval. inversion Hval; subst.
  constructor; auto. Search valid_def.
  - Search wf_funsym. Print wf_funsym.


(*Prove 1. signatures are the same if alpha equivalent
2. funsym_of_def (and others) same if alpha_equiv for def
3. idents are the same if alpha_equiv for def
4. nonempty same if alpha equiv for def
5. valid_constrs_def (not sure)
6. prove mut_of_context equal
7. prove sig_t equal (really just prove each equal in 1
8. prove valid_def equiv for def
6. (BIG ON) valid_def is true for def - and need context change*)



wf_funsym_sublist:
  forall (g1 g2 : context) (f : funsym),
  sublist (sig_t g1) (sig_t g2) -> wf_funsym g1 f -> wf_funsym g2 f








(*Alpha equivalent tasks have the same typing*)
Lemma a_equiv_task_typed (t1 t2: task) :
  a_equiv_task t1 t2 ->
  task_typed t1 ->
  task_typed t2.
Proof.
  unfold a_equiv_task.
  destruct t1 as [[gamma1 delta1] goal1].
  destruct t2 as [[gamma2 delta2] goal2].
  simpl_task.
  rewrite !andb_true. intros [[[Hgamma Hlendelta] Hdelta] Hgoal].
  intros Hty. inversion Hty; simpl_task.
  constructor; simpl_task.
  -




  unfold task_typed.
  unfold task_valid, TaskGen.task_valid.
  intros [Hty Hsem]. split.
  
  

(*Alpha equivalent tasks have the same validity*)
Lemma a_equiv_task_valid (t1 t2: Task.task) :
  a_equiv_task t1 t2 ->
  task_valid t1 ->
  task_valid t2.
Proof.
  unfold a_equiv_task.
  destruct t1 as [[gamma1 delta1] goal1].
  destruct t2 as [[gamma2 delta2] goal2].
  simpl_task.
  rewrite !andb_true. intros [[[Hgamma Hlendelta] Hdelta] Hgoal].
  unfold task_valid, TaskGen.task_valid.
  intros [Hty Hsem]. split.
  -
(*NOTE: should be possible to prove but annoying, full interp would be hardest bc of
  recfun - see if we need*)
Admitted.

Lemma task_related_valid (t1: task) (t2: Task.task):
  task_related t1 t2 ->
  Task.task_valid t2 ->
  valid_task t1.
Proof.
  unfold task_related, valid_task.
  intros [t [Heval Halpha]] Hval.
  exists t. split; auto.
  (*Need to prove [a_equiv_task] symmetric*)
  (* apply a_equiv_task_valid. *)
  (*TODO: would have to prove that a_equiv_task preserves validity - might be annoying
    see if we need this or we should just define in terms of related*)
Admitted.