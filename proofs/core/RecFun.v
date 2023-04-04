(*Recursive Functions*)
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import Semantics.
Require Import IndTypes.
Require Import Hlist.
Require Import ADTInd.
Require Import Denotational.
From Equations Require Import Equations.
Require Import Coq.Logic.Eqdep_dec.

Set Bullet Behavior "Strict Subproofs".

(*TODO: move*)
Inductive Either (A B: Set) : Set :=
  | Left: A -> Either A B
  | Right: B -> Either A B. 

Section FunDef.


Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
{pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m).

(*First, we assume we have our fs and ps lists and that
  they satisfy all of the well-founded conditions which follow
  from typing*)

Variable (fs: list fn) (ps: list pn).

Definition sns : list sn :=
  map fn_sn fs ++ map pn_sn ps.

Variable fs_uniq: NoDup (map fn_sym fs).
Variable ps_uniq: NoDup (map pn_sym ps).
Variable fs_typed: Forall 
  (fun f => term_has_type sigma (fn_body f) (f_ret (fn_sym f))) fs.
Variable ps_typed: Forall
  (fun p => valid_formula sigma (pn_body p)) ps.

Variable funs_args_agree: forall f, In f fs ->
  map snd (sn_args f) = s_args (fn_sym f).
Variable preds_args_agree: forall p, In p ps ->
  map snd (sn_args p) = s_args (pn_sym p).

Lemma args_agree: forall s, In s sns ->
  map snd (sn_args s) = s_args (sn_sym s).
Proof.
  intros. unfold sns in H. rewrite in_app_iff in H.
  destruct H; auto; rewrite in_map_iff in H;
  destruct H as [x [Heq Hinx]]; subst.
  - rewrite funs_args_agree; auto.
    destruct x; simpl. rewrite fn_wf.
    reflexivity.
  - rewrite preds_args_agree; auto.
    destruct x; simpl. rewrite pn_wf.
    reflexivity.
Qed.

(*Since vt is fixed through everything (we are requiring all
  mutually recursive functions to have the same params)
  This is a restriction on why3 (maybe), but I am OK with that
  we can assume some property of it, then build it up later
  *)
Variable params: list typevar.
Variable funs_params_eq: forall f, In f fs -> s_params (fn_sym f) = params.
Variable preds_params_eq: forall p, In p ps -> s_params (pn_sym p) = params.

Lemma params_eq: forall s, In s sns -> s_params (sn_sym s) = params.
Proof.
  intros. unfold sns in H. rewrite in_app_iff in H.
  destruct H; auto; rewrite in_map_iff in H;
  destruct H as [x [Heq Hinx]]; subst.
  - replace (sn_sym x) with (f_sym (fn_sym x)).
    rewrite funs_params_eq; auto.
    destruct x; simpl. rewrite fn_wf.
    reflexivity.
  - replace (sn_sym x) with (p_sym (pn_sym x)). 
    rewrite preds_params_eq; auto.
    destruct x; simpl. rewrite pn_wf.
    reflexivity.
Qed.

Variable f_typevars: forall f, In f fs -> 
  forall ty, In ty (f_ret (fn_sym f) :: s_args (fn_sym f)) ->
  forall x, In x (type_vars ty) ->
  In x params.

Variable p_typevars: forall p, In p ps ->
  forall ty, In ty (s_args (pn_sym p)) ->
  forall x, In x (type_vars ty) ->
  In x params.

(*Here we lose info for funsyms*)
Lemma s_typevars: forall s, In s sns ->
  forall ty, In ty (s_args (sn_sym s)) ->
  forall x, In x (type_vars ty) ->
  In x params.
Proof.
  intros. unfold sns in H. rewrite in_app_iff in H.
  destruct H; rewrite in_map_iff in H;
  destruct H as [x' [Heq Hinx']]; subst.
  - apply (f_typevars x' Hinx' ty); auto. right.
    destruct x'; simpl in *.
    rewrite fn_wf. auto.
  - apply (p_typevars x' Hinx' ty); auto. 
    destruct x'; simpl in *.
    rewrite pn_wf. auto.
Qed.

Notation domain := (domain (dom_aux pd)).

Section Smaller.

Context  {vt: val_typevar} {pf: pi_funpred gamma_valid pd}.

Notation val x :=  (v_subst vt x).

Section WellFounded.

(*The [adt_smaller] relation is conceptually simple:
  both types are instances of ADTs from mut adt m, the second
  is c(args), and the first is in the args of the second*)
Inductive adt_smaller: 
  {s: sort &  domain s} -> {s: sort & domain s} -> Prop :=
  | ADT_small: forall 
    (x1 x2: {s: sort &  domain s})
    s1 s2 (*(Hval1: valid_type sigma ty1)
    (Hval2: valid_type sigma ty2)*) (d1: domain s1) 
    (d2: domain s2) m a1 a2 srts c args
    (Hx1_1: projT1 x1 = s1)
    (Hx1_2: d1 = (dom_cast (dom_aux pd) 
       Hx1_1 (projT2 x1)))
    (Hx2_1: projT1 x2 = s2)
    (Hx2_2: d2 = (dom_cast (dom_aux pd) 
       Hx2_1 (projT2 x2)))
    (Hty1: s1 = typesym_to_sort (adt_name a1) srts)
    (Hty2: s2 = typesym_to_sort (adt_name a2) srts) (*TODO: srts same?*)
    (a_in1: adt_in_mut a1 m)
    (a_in2: adt_in_mut a2 m)
    (m_in: mut_in_ctx m gamma)
    (c_in: constr_in_adt c a2)
    (lengths_eq: length srts = length (m_params m)),
    let adt2 : adt_rep m srts (dom_aux pd) a2 a_in2 :=
      scast (Semantics.adts pd m srts a2 a_in2) (dom_cast _ Hty2 d2) in
    let adt1: adt_rep m srts (dom_aux pd) a1 a_in1 :=
      scast (Semantics.adts pd m srts a1 a_in1) (dom_cast _ Hty1 d1) in
    forall (Hadt2: adt2 = constr_rep gamma_valid m m_in srts
      lengths_eq (dom_aux pd) a2 a_in2 c c_in (Semantics.adts pd m srts) args),
    (exists i Heq, 
    i < length (s_args c) /\
    adt1 = scast (Semantics.adts pd m srts a1 a_in1) 
      (dom_cast (dom_aux pd) Heq (hnth i args s_int (dom_int pd)))) ->
    adt_smaller x1 x2.

(*TODO: move*)
(*We show that [is_sort_adt] is Some for adts*)
Lemma is_sort_adt_adt a srts m:
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  @is_sort_adt gamma (typesym_to_sort (adt_name a) srts) =
    Some (m, a, (adt_name a), srts).
Proof.
  intros m_in a_in.
  unfold is_sort_adt. simpl.
  assert (@find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
    apply (@find_ts_in_ctx_iff sigma); auto.
  }
  rewrite H. simpl. 
  f_equal. f_equal.
  apply is_sort_cons_sorts_eq.
Qed.

Lemma scast_rev {A B: Set} (H: A = B) {x y} (Heq: x = scast H y) :
  y = scast (eq_sym H) x.
Proof.
subst. reflexivity.
Qed.

Lemma typesym_to_sort_inj t1 t2 s1 s2:
  typesym_to_sort t1 s1 = typesym_to_sort t2 s2 ->
  t1 = t2 /\ s1 = s2.
Proof.
  unfold typesym_to_sort. intros. inversion H; subst.
  split; auto.
  apply seq.inj_map in H2; auto.
  unfold ssrfun.injective. intros.
  apply sort_inj. auto.
Qed.

(*TODO: move*)
Lemma scast_eq_sym {A B: Set} (Heq: A = B) x:
  scast (eq_sym Heq) (scast Heq x) = x.
Proof.
  subst. reflexivity.
Qed.

(*Now we prove that this is well_founded. Basically our proof
  consists of 3 parts:
  1. Show that the second element of the relation has to be
  an ADT
  2. Apply our induction principle from above and do
  various inversions and to show that the generated variables
  are equivalent, allowing us to apply the IH
  3. Apply the IH
  This requires UIP (and funext from adt_rep_ind)*)
Lemma adt_smaller_wf: well_founded adt_smaller.
Proof.
  unfold well_founded. 
  intros a. destruct a as [s d].
  simpl in *.
  destruct (@is_sort_adt gamma s) eqn : Hisadt.
  (*Can't be None, contradiction*)
  2: {
    constructor. intros.
    inversion H; subst.
    simpl in Hty2.
    rewrite Hty2 in Hisadt.
    rewrite (is_sort_adt_adt _ _ _ m_in a_in2) in Hisadt.
    inversion Hisadt.
  }
  destruct p as [[[m a] ts] srts].
  (*We need to know about the length of the srts list*)
  destruct (Nat.eq_dec (length srts) (length (m_params m))).
  2: {
    constructor. intros. inversion H; subst.
    simpl in Hty2.
    rewrite Hty2 in Hisadt.
    rewrite (is_sort_adt_adt _ _ _ m_in a_in2) in Hisadt.
    inversion Hisadt; subst.
    rewrite lengths_eq in n. contradiction.
  }
  rename e into Hlen.
  (*Need an adt_rep to do induction on*)
  set (adt_spec := (is_sort_adt_spec gamma_valid _ _ _ _ _ Hisadt)).
  pose proof (proj1 adt_spec) as Hseq.
  pose proof (proj1 (proj2 adt_spec)) as a_in.
  pose proof (proj1 (proj2 (proj2 adt_spec))) as m_in.
  clear adt_spec.
  remember (scast (Semantics.adts pd m srts a a_in) (dom_cast _ Hseq d)) as adt.
  revert Heqadt.
  unfold dom_cast. rewrite scast_scast. intros Hd.
  apply scast_rev in Hd.
  generalize dependent ((eq_sym
  (eq_trans (f_equal domain Hseq) (Semantics.adts pd m srts a a_in)))).
  intros Heqadt Hd. subst d.
  (*Here, we use induction*)
  apply (adt_rep_ind gamma_valid all_unif m m_in srts Hlen (fun t t_in x =>
    forall s Heq, s = typesym_to_sort (adt_name t) srts ->
    Acc adt_smaller (existT (fun s => domain s) s 
      (scast Heq x)))); auto.
  intros t t_in x c Hc args Hx IH ty1 Heq Hty1.
  constructor.
  intros y Hsmall.
  remember (scast Heq x) as x2. inversion Hsmall. subst.
  simpl in *. unfold dom_cast in adt1, adt2. simpl in adt1, adt2.

  destruct H as [i [Heqith [Hi Hadt1]]].
  (*Need to prove lots of equalities before applying the IH. First,
    a2's name and srts*)
  assert (adt_name a2 = adt_name t /\ srts0 = srts). {
    apply typesym_to_sort_inj; rewrite <- Hty2; auto.
  }
  destruct H;subst srts0.
  (*Now prove m equal*)
  assert (m = m0) by
    (apply (@mut_adts_inj _ _ gamma_valid) with(a1:=t)(a2:=a2); auto).
  subst m0.
  (*Now prove a2 and t equal*)
  assert (a2 = t) by
    (apply (adt_names_inj' gamma_valid a_in2); auto).
  subst t.
  clear H.
  (*Now we need to deal with adt1 and adt2*)
  subst adt1. apply scast_inj in Hadt1.
  unfold dom_cast in Hadt1.
  destruct y as [ty2 d2]. simpl in *.
  symmetry in Hadt1.
  apply scast_rev in Hadt1. subst.
  (*From adt2, get info about c*)
  subst adt2. rewrite !scast_scast in Hadt2.
  assert (m_in = m_in0) by apply bool_irrelevance.
  subst m_in0.
  assert (Hlen = lengths_eq). {
    clear. generalize dependent (length srts); intros.
    subst. apply UIP_dec. apply Nat.eq_dec.
  }
  subst lengths_eq. 
  assert (a_in2 = t_in). {
    apply bool_irrelevance.
  }
  subst a_in2.
  assert (eq_trans Heq
  (eq_trans (f_equal domain Hty2)
     (Semantics.adts pd m srts a2 t_in)) = eq_refl). {
  (*HERE, we need UIP*)
    clear. apply IndTypes.UIP. }
  rewrite H in Hadt2. simpl in Hadt2.
  clear H.
  (*Now we use injectivity*)
  destruct (funsym_eq_dec c c0). 2: {
    exfalso. 
    apply (constr_rep_disjoint gamma_valid _ _ _ _ _ _ _ _ _ _ n Hadt2).
  }
  subst c0.
  assert (Hc = c_in). apply bool_irrelevance. subst Hc.
  apply constr_rep_inj in Hadt2. 2: apply all_unif; auto.
  subst args0.
  (*Now, we can apply the IH*)
  specialize (IH _ _ a_in1 Heqith Hi (typesym_to_sort (adt_name a1) srts)
    (eq_sym ((Semantics.adts pd m srts a1 a_in1))) eq_refl).
  (*We don't need UIP here if we build a proof term carefully*)
  match goal with
  | H: Acc ?y (existT ?g1 ?ty1 ?x1) |- Acc ?y (existT ?g ?ty2 ?x2) =>
    let Heq := fresh "Heq" in
    assert (Heq: x1 = x2); [|rewrite <- Heq; auto]
  end. clear.
  unfold dom_cast. simpl. rewrite scast_eq_sym.
  reflexivity.
Qed.

(*Now, transitive closure*)
Inductive R_trans {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
  | Rtrans_once: forall x y,
    R x y ->
    R_trans R x y
  | Rtrans_multi: forall x y z,
    R_trans R x y ->
    R y z ->
    R_trans R x z.

Lemma R_trans_trans {A: Type} {R: A -> A -> Prop} {x y z: A}:
  R_trans R x y ->
  R_trans R y z ->
  R_trans R x z.
Proof.
  intros.
  induction H0.
  - eapply Rtrans_multi. apply H. auto.
  - eapply Rtrans_multi. apply IHR_trans. auto. auto.
Qed.

(*Need reflexive closure*)
Inductive R_refl {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
  | Rrefl_R: forall x y,
    R x y ->
    R_refl R x y
  | Rrefl_refl: forall x,
    R_refl R x x.

(*Reflexive transitive closure*)
Definition R_refl_trans {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
  R_refl (R_trans R).

(*Now we prove: if we have R_refl_trans R x y and we have R_trans y z,
  then we have R_trans x z. In other words, we can repeat R
  0 or more times, then repeat R 1 or more times*)
Lemma R_refl_trans_trans {A: Type} (R: A -> A -> Prop) x y z:
  R_refl_trans R x y ->
  R_trans R y z ->
  R_trans R x z.
Proof.
  intros. unfold R_refl_trans in H.
  inversion H; subst; auto.
  eapply R_trans_trans. apply H1. auto.
Qed.

(*Proof of transitive closure wf from 
  [https://madiot.fr/pso/tp6.html]*)
Lemma Acc_inv {A : Type} (R : A -> A -> Prop) x y: 
  R x y -> Acc R y -> Acc R x.
Proof.
  intros. apply H0. auto.
Qed.

Lemma Acc_trans {A : Type} (R : A -> A -> Prop) :
  forall x, Acc R x -> Acc (R_trans R) x.
Proof.
  intros. induction H.
  constructor. intros.
  inversion H1; subst.
  - apply H0; auto.
  - eapply Acc_inv. apply H2. apply H0. auto.
Qed.

Lemma R_trans_wf {A: Type} (R: A -> A -> Prop):
  well_founded R ->
  well_founded (R_trans R).
Proof.
  intros Hr.
  unfold well_founded.
  intros. apply Acc_trans. apply Hr.
Qed.

(*The transitive closure of [adt_smaller]*)
Definition adt_smaller_trans := R_trans adt_smaller.
Definition adt_smaller_trans_wf := R_trans_wf adt_smaller adt_smaller_wf.

(*Part 2: lift to [arg_list]*)

(*This is why we need sort, not 
  {x: vty & domain (v_subst vt x)}
  This definition is unusable when we have types who are not
  equal but their valuations are*)
Definition hide_ty {s: sort} (d: domain s) : {s: sort & domain s} :=
  existT _ s d.

End WellFounded.
End Smaller.


(*The mut adt we are recursing on*)
Variable m: mut_adt.
Variable vs: list vty.

Variable vs_len: length vs = length (m_params m).
  
Variable funs_recurse_on_adt: forall f, In f fs ->
  vty_in_m m vs (snd (nth (sn_idx f) (sn_args f) vs_d)).
Variable preds_recurse_on_adt: forall p, In p ps ->
  vty_in_m m vs (snd (nth (sn_idx p) (sn_args p) vs_d)).

Lemma recurse_on_adt: forall s, In s sns ->
  vty_in_m m vs (snd (nth (sn_idx s) (sn_args s) vs_d)).
Proof.
  intros. unfold sns in H. rewrite in_app_iff in H.
  destruct H; auto; rewrite in_map_iff in H;
  destruct H as [x [Heq Hinx]]; subst;
  [apply funs_recurse_on_adt | apply preds_recurse_on_adt]; auto.
Qed.

Variable m_in: mut_in_ctx m gamma.

Section MatchSmallerLemma.

(*TODO: move*)
Lemma v_subst_aux_sort_eq (v: typevar -> vty) (t: vty):
  (forall x, In x (type_vars t) -> is_sort (v x)) ->
  is_sort (v_subst_aux v t).
Proof.
  intros. induction t; simpl; intros; auto.
  apply H. left; auto.
  apply is_sort_cons_iff.
  intros. rewrite in_map_iff in H1.
  destruct H1 as [y [Hy Hiny]]; subst.
  rewrite Forall_forall in H0. apply H0; auto.
  intros. apply H. simpl. simpl_set. exists y. split; auto.
Qed.

(*TODO: move*)
Lemma dom_cast_compose {domain_aux: sort -> Set} {s1 s2 s3: sort}
  (Heq1: s2 = s3) (Heq2: s1 = s2) x:
  dom_cast domain_aux Heq1 (dom_cast domain_aux Heq2 x) =
  dom_cast domain_aux (eq_trans Heq2 Heq1) x.
Proof.
  subst. reflexivity.
Qed.

Lemma map_ty_subst_var (vars: list typevar) (vs2: list vty):
  length vars = length vs2 ->
  NoDup vars ->
  map (ty_subst vars vs2) (map vty_var vars) = vs2.
Proof.
  intros.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite map_nth_inbound with (d2:=vty_int); [|rewrite map_length; auto].
  rewrite map_nth_inbound with (d2:=EmptyString); auto.
  unfold ty_subst. simpl. apply ty_subst_fun_nth; auto.
Qed.

Lemma hlist_hd_cast {d: sort -> Set} 
  {s1 s2: sort} {t1 t2: list sort}
  {a: arg_list d (s1 :: t1)}
  (Heq1: s1 :: t1 = s2 :: t2)
  (Heq2: s1 = s2):
  hlist_hd (cast_arg_list Heq1 a) =
  scast (f_equal d Heq2) (hlist_hd a).
Proof.
  subst. inversion Heq1; subst.
  assert (Heq1 = eq_refl).
    apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
  subst. reflexivity.
Qed. 

Lemma hide_ty_eq {s1 s2: sort} (d1: domain s1) (d2: domain s2) 
  (Hs: s1 = s2):
  d2 = dom_cast (dom_aux pd) Hs d1 ->
  hide_ty d1 = hide_ty d2.
Proof.
  intros. subst.
  reflexivity.
Qed.

(*THIS lemma is not provable if we use {x: vty & domain (val v x)}
  instead of sort because we cannot destruct (val v1 = val v2).
  We need the more general form*)
Lemma hide_ty_dom_cast {s1 s2 s3: sort} (d: domain s1) 
  (Hs1: s1 = s2) (Hs2: s1 = s3):
  hide_ty (dom_cast (dom_aux pd) Hs1 d) =
  hide_ty (dom_cast (dom_aux pd) Hs2 d).
Proof.
  subst. reflexivity.
Qed.

Lemma v_subst_twice {v} ty:
  v_subst v (v_subst v ty) = v_subst v ty.
Proof.
  symmetry. apply subst_sort_eq.
Qed.

(*This is a very tricky theorem to prove but it proves that our
  pattern matching actually works: all of the resulting valuations
  that correspond to syntactically smaller variables (those arising
  from nested constructor application)
  when we match a pattern actually give smaller ADT types.
  We prove a stronger claim, for both [pat_constr_vars]
  and [pat_constr_vars_inner] for induction *)
Theorem match_val_single_smaller (vt: val_typevar) (v: val_vars pd vt) (ty: vty)
  (p: pattern)
  (Hp: pattern_has_type sigma p ty)
  (Hty: vty_in_m m vs ty)
  (d: domain(v_subst vt ty))
  (l: list (vsymbol * {s: sort & domain s})):
  match_val_single gamma_valid pd all_unif vt ty p Hp d = Some l ->
    (*For [pat_constr_vars_inner], either same or smaller*)
    (forall x y, In (x, y) l ->
      In x (pat_constr_vars_inner m vs p) ->
      y = hide_ty d \/
      adt_smaller_trans y (hide_ty d)) /\
    (*For [pat_constr_vars], strictly smaller*)
    (forall x y, In (x, y) l ->
      In x (pat_constr_vars m vs p) ->
    adt_smaller_trans y (hide_ty d)).
Proof.
  clear -fs ps Hty m_in vs_len.
  (*We will do it manually; it is very complicated*)
  revert d l. generalize dependent ty.
  induction p; intros.
  - (*Var case is easy - it is the same*) simpl in H. simpl.
    split; [intros |intros x y Hin [] ].
    inversion Hp; subst.
    unfold vsym_in_m in H1. rewrite Hty in H1.
    destruct H1 as [Hxv | []]; subst.
    inversion H; subst. clear H.
    destruct H0 as [Hy | []]. inversion Hy; subst. clear Hy.
    left. unfold hide_ty. 
    reflexivity.
  - (*Constr case is the hard and interesting one.*)
    revert H0.
    rewrite pat_constr_vars_inner_eq.
    rewrite match_val_single_rewrite. cbn zeta.
    generalize dependent (@is_vty_adt_spec _ _ gamma_valid ty).
    generalize dependent (@adt_vty_length_eq _ _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ _ gamma_valid ty).
    destruct (is_vty_adt ty) eqn : Hisadt.
    2: intros; discriminate.
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m' adt] vs2].
    destruct (Hadtspec m' adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    clear Hadtspec.
    (*Now want to show equiv between m and m'*)
    assert (m = m'). {
      subst.
      apply (reflect_iff _ _ (vty_in_m_spec _ _ _)) in Hty. 
      destruct Hty as [a' [Ha' Hty']]; subst.
      inversion Hty'; subst.
      apply (mut_adts_inj gamma_valid m_in Hinctx Ha' Hinmut); auto.
    }
    subst m'.
    assert (vs2 = vs). {
      subst.
      apply (reflect_iff _ _ (vty_in_m_spec _ _ _)) in Hty. 
      destruct Hty as [a' [Ha' Hty']]; subst.
      inversion Hty'; subst; auto.
    }
    subst vs.
    (*A few more generalizations to make the goal nicer*)
    simpl.
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma_valid (Pconstr f vs0 ps0) ty Hp)).
    clear Hvslen2.
    intros Hvslen2.
    destruct (funsym_eq_dec
    (projT1
       (find_constr_rep gamma_valid m Hinctx (map (v_subst vt) vs2)
          (eq_trans (map_length (v_subst vt) vs2) Hvslen2) 
          (dom_aux pd) adt Hinmut
          (Semantics.adts pd m (map (v_subst vt) vs2)) 
          (all_unif m Hinctx)
          (scast (Semantics.adts pd m (map (v_subst vt) vs2) adt Hinmut)
             (dom_cast (dom_aux pd)
                (eq_trans (f_equal (v_subst vt) Htyeq)
                   (v_subst_cons (adt_name adt) vs2)) d)))) f);
    [| intros; discriminate].
    generalize dependent (find_constr_rep gamma_valid m Hinctx (map (v_subst vt) vs2)
    (eq_trans (map_length (v_subst vt) vs2) Hvslen2) 
    (dom_aux pd) adt Hinmut
    (Semantics.adts pd m (map (v_subst vt) vs2))
    (all_unif m Hinctx)
    (scast
       (Semantics.adts pd m (map (v_subst vt) vs2) adt Hinmut)
       (dom_cast (dom_aux pd)
          (eq_trans (f_equal (v_subst vt) Htyeq)
             (v_subst_cons (adt_name adt) vs2)) d))).
    intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
    simpl.
    (*generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).*)
    destruct Hf'. simpl.
    (*Here, let us prove that 
      everything in (snd x) is smaller than d - this is the key
      theorem - when we pattern match, we actually get a smaller
      ADT*)
    set (srts:=(map (v_subst vt) vs2)) in *.
    assert (Hparams: s_params f = m_params m). {
      eapply adt_constr_params. apply gamma_valid.
      auto. apply Hinmut. apply (fst x).
    }
    assert (Hlenvs2: length vs2 = length (s_params f)) by
    (rewrite Hparams; auto).
    (*We do NOT want val_sort_eq, instead prove directly*)
    assert (Hithcast: forall i, i < length (s_args f) ->
      nth i (sym_sigma_args f srts) s_int =
      v_subst vt (ty_subst (s_params f) vs2 
        (nth i (s_args f) vty_int))). {
      intros. subst srts. rewrite sym_sigma_args_map; auto.
      unfold ty_subst_list. rewrite map_map.
      rewrite map_nth_inbound with (d2:=vty_int); auto. 
    }

    assert (Hsmall: forall i (Hi: i < length (s_args f))
      (Hithcast: nth i (sym_sigma_args f srts) s_int =
      v_subst vt (ty_subst (s_params f) vs2 
        (nth i (s_args f) vty_int))),
      vty_in_m m (map vty_var (m_params m)) (nth i (s_args f) vty_int) ->
      adt_smaller 
      (hide_ty (dom_cast (dom_aux pd)  Hithcast
        (hnth i (snd x) s_int (dom_int pd)))) (hide_ty d)). {
      intros.
      apply (reflect_iff _ _ (vty_in_m_spec _ _ _)) in H0.
      destruct H0 as [adt2 [Hina2 Hntheq]].
      assert (Hvalntheq: v_subst vt 
        (nth i (sym_sigma_args f srts) s_int) =
      typesym_to_sort (adt_name adt2) srts). {
        (*TODO: maybe separate lemma or something - inverse of
          [adts_from_constrs] or whatever it is*)
        apply (reflect_iff _ _ (vty_in_m_spec m vs2 _)) in Hty.
        destruct Hty as [a' [Ha' Hty]].
        subst.
        unfold sym_sigma_args, ty_subst_list_s,
        typesym_to_sort.
        apply sort_inj. simpl.
        rewrite map_nth_inbound with(d2:=vty_int); auto.
        rewrite Hntheq.
        simpl.
        unfold ty_subst_s, ty_subst_fun_s. simpl.
        unfold sorts_to_tys. 
        rewrite !map_map.
        f_equal.
        assert (Hlensrts: length srts = length (m_params m)). {
          subst srts. rewrite map_length. auto.
        }
        apply list_eq_ext'; rewrite !map_length; auto. 
        intros n d' Hn.
        rewrite !map_nth_inbound with (d2:=EmptyString); auto.
        rewrite <- subst_is_sort_eq.
        2: {
          apply v_subst_aux_sort_eq. rewrite Hparams.
          intros. fold (sorts_to_tys srts).
          replace vty_int with (sort_to_ty s_int) by reflexivity. 
          apply ty_subst_fun_sort.
        }
        rewrite !map_nth_inbound with (d2:=s_int); [|lia].
        simpl.
        rewrite <- Hparams.
        rewrite ty_subst_fun_nth with(s:=s_int); auto.
        + simpl. rewrite map_nth_inbound with (d2:=s_int); auto. lia.
        + rewrite map_length, Hparams. auto.
        + rewrite Hparams; auto. 
        + apply s_params_Nodup.
      }
      eapply (ADT_small (hide_ty (dom_cast (dom_aux pd) Hithcast0
          (hnth i (snd x) s_int (dom_int pd)))) (hide_ty d)
          (v_subst vt 
            (ty_subst (s_params f) vs2 (nth i (s_args f) vty_int)))
          (v_subst vt 
            (vty_cons (adt_name adt) vs2))
           _ _ m adt2 adt srts f (snd x)
          eq_refl eq_refl eq_refl eq_refl
      ).
      exact e.
      exists i.
      eexists. split; auto.
      rewrite !dom_cast_compose. simpl.
      rewrite !dom_cast_compose. reflexivity.
      Unshelve.
      2: assumption.
      rewrite <- Hvalntheq.
      rewrite Hithcast; auto.
      rewrite v_subst_twice. reflexivity.
    }
    (*The second claim is stronger. We prove that first*)
    (*Now we can do induction for the first claim, and prove the second
      directly.*)
    clear e.
    intros Hl.
    match goal with
    | |- ?A /\ ?B => assert B
    end.
    { (*Need to generalize cast proof*)
      generalize dependent (Hvslen1 m adt vs2 f eq_refl
        (pat_has_type_valid gamma_valid (Pconstr f vs0 ps0)
          (vty_cons (adt_name adt) vs2) Hp) (fst x)).
      clear Hvslen1.
      intros.
      generalize dependent (sym_sigma_args_map vt f vs2 e).
      clear e.
      
      generalize dependent ((pat_constr_ind gamma_valid Hp Hinctx Hinmut eq_refl (fst x))).
      destruct x. simpl.
      generalize dependent a.
      apply pat_constr_disj in Hp.
      generalize dependent ps0.
      assert (length (sym_sigma_args f srts) = length (s_args f)). {
        unfold sym_sigma_args, ty_subst_list_s. rewrite map_length; reflexivity.
      }
      unfold sym_sigma_args in *.
      (*generalize dependent ((sym_sigma_args f srts)).*)
      generalize dependent (s_args f).
      intros l0.
      generalize dependent l.
      induction l0; simpl; intros; auto. 
      + destruct ps0. inversion Hl; subst. 
        inversion H0.
        inversion Hl.
      + revert Hl. destruct ps0. discriminate.
        simpl.
        repeat match goal with 
        |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
          let Hp := fresh "Hmatch" in 
          destruct p eqn: Hp end.
        all: try discriminate.
        intro C; inversion C; subst. clear C.
        apply in_app_or in H0. destruct H0.
        * clear Hmatch0.
          destruct (constr_in_m f m && list_eq_dec vty_eq_dec vs0 vs2 &&
          (Datatypes.length (p :: ps0) =? S (Datatypes.length l0))) eqn : Hconds;
          [|inversion H2].
          simpl in H2. 
          (*2 cases are the same: we do in a separate lemma*)
          assert (Hdupfv: forall x' y l,
            length ps0 = length l0 ->
            In x' (big_union vsymbol_eq_dec (pat_constr_vars_inner m vs2)
            (map fst
                (filter
                  (fun x : pattern * vty => vty_in_m m (map vty_var (m_params m)) (snd x))
                  (combine ps0 l0)))) ->
            In (x', y) l ->
            match_val_single gamma_valid pd all_unif vt (ty_subst (s_params f) vs2 a) p
              (Forall_inv f0) (hlist_hd (cast_arg_list e a0)) = 
              Some l ->
            False). {
              intros x' y' Hlens Hinx1 Hinx2 l' Hmatch1.
              assert (Hinxfv1: In x' (pat_fv p)). {
                apply (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch1).
                rewrite in_map_iff. exists (x', y'). auto.
              }
              (*now we need to find the pattern in ps0 that it is in*)
              simpl_set.
              destruct Hinx2 as [p' [Hinp' Hinx0]].
              rewrite in_map_iff in Hinp'.
              destruct Hinp' as [pt [Hp' Hinpt]]; subst.
              rewrite in_filter in Hinpt.
              destruct pt as [p' t']; simpl in Hinpt, Hinx0.
              destruct Hinpt as [Hvtyin Hinpt].
              assert (Hcomb:=Hinpt).
              rewrite in_combine_iff in Hinpt; auto.
              destruct Hinpt as [i' [Hi' Hpteq]].
              specialize (Hpteq Pwild vty_int).
              inversion Hpteq; subst.
              assert (Hinxfv2: In x' (pat_fv (nth i' ps0 Pwild))). {
                apply pat_constr_vars_inner_fv in Hinx0; auto.
              }
              (*Contradicts disjointness*)
              rewrite disj_cons_iff in Hp.
              destruct Hp as [Hp Hdisj].
              exfalso.
              apply (Hdisj i' Pwild x'); auto.
          }
          destruct (vty_in_m m (map vty_var (m_params m)) a) eqn : Hadtv.
          -- simpl in H2. rewrite union_elts in H2.
            destruct H2.
            ++ (*This is the hard case - need to show that
                contr var in p is actually smaller*) inversion H1; subst.
              clear H6.
              specialize (Hsmall 0 (Nat.lt_0_succ (length l0)) 
                (Hithcast 0 (Nat.lt_0_succ (length l0))) Hadtv). simpl in Hsmall.
              eapply R_refl_trans_trans.
              2: {
                apply Rtrans_once. apply Hsmall.
              }
              (*Now need to know that (ty_subst (s_params f) vs2 a)
                is an ADT. Here is where it is CRUCIAL that we recurse on
                a type, not a sort in [match_val_single], or else
                Hadtv will not be strong enough*)
              assert (Halg: vty_in_m m vs2 (ty_subst (s_params f) vs2 a)). {
                apply (reflect_iff _ _ (vty_in_m_spec _ _ _)) in Hadtv.
                destruct Hadtv as [a' [Hina' Ha']]; subst.
                apply (reflect_iff _ _ (vty_in_m_spec _ _ _)).
                exists a'. split; auto.
                rewrite ty_subst_cons. f_equal.
                rewrite <- Hparams.
                rewrite map_ty_subst_var; auto.
                apply s_params_Nodup.
              }
              specialize (H5 _ _ Halg _ _ Hmatch).
              destruct H5. clear H4.
              specialize (H3 _ _ H0 H2).
              (*Both need this result*)
              assert (Haleq: hide_ty (hlist_hd (cast_arg_list e a0)) =
              hide_ty
                (dom_cast (dom_aux pd) (Hithcast 0 (Nat.lt_0_succ (Datatypes.length l0)))
                  (hlist_hd a0))). {
                erewrite hlist_hd_cast.
                unfold dom_cast. reflexivity.
              }
              destruct H3; subst; auto.
              ** (*these are the same*)
                rewrite <- Haleq.
                apply Rrefl_refl.
              ** (*Otherwise, we have transitivity*)
                apply Rrefl_R.
                rewrite <- Haleq. apply H3.
            ++ (*Contradiction case*)
              exfalso. apply (Hdupfv x0 y l1); auto.
              bool_hyps. simpl in H4.
              apply Nat.eqb_eq in H4. auto.
          -- (*Identical contradiction case*)
            exfalso. apply (Hdupfv x0 y l1); auto.
            bool_hyps. simpl in H4.
            apply Nat.eqb_eq in H4; auto.
        * (*Once again, get 2 cases depending on whether
          x0 is in constr vars of p or not*)
          simpl in H2.
          destruct (constr_in_m f m && list_eq_dec vty_eq_dec vs0 vs2 &&
          (Datatypes.length ps0 =? Datatypes.length l0)) eqn : Hconds;
          [| inversion H2].
          (*This time, the IH case appears twice - we will do in separate lemma*)
          assert (
            In x0 (big_union vsymbol_eq_dec (pat_constr_vars_inner m vs2)
              (map fst (filter
              (fun x : pattern * vty =>
               vty_in_m m (map vty_var (m_params m)) (snd x)) 
              (combine ps0 l0)))) ->
            adt_smaller_trans y (hide_ty d)
          ). 
          {
            intros Hinx1.
            rewrite hlist_tl_cast in Hmatch0.
            apply IHl0 with(ps0:=ps0)(a:=hlist_tl a0)(f:=Forall_inv_tail f0)
            (e:=(cons_inj_tl e))(l:=l2); auto.
            -- intros.
              apply (Hithcast (S i0) ltac:(lia)).
            -- inversion H1; subst; auto.
            -- apply disj_cons_impl in Hp; auto.
            -- rewrite Hconds. auto.
            -- intros. apply (Hsmall (S i0) ltac:(lia) Hithcast0). auto.
          }
          rewrite hlist_tl_cast in Hmatch0.
          destruct (vty_in_m m (map vty_var (m_params m)) a) eqn : Hinm; auto.
          simpl in H2.
          rewrite union_elts in H2; destruct H2; auto.
          (*Now just contradiction case - much easier*)
          assert (Hinx1: In x0 (pat_fv p)). {
            apply pat_constr_vars_inner_fv in H2; auto.
          }
          (*Need iterated version of [match_val_single_perm/free_var]*)
          assert (Hinx2: In x0 (big_union vsymbol_eq_dec pat_fv ps0)).
          {
            apply iter_arg_list_free_var with(x:=x0) in Hmatch0.
            - apply Hmatch0. rewrite in_map_iff.
              exists (x0, y). split; auto.
            - apply disj_cons_impl in Hp; auto.
            - rewrite Forall_forall; intros.
              apply match_val_single_perm in H5; auto.
          }
          simpl_set. destruct Hinx2 as [p' [Hinp' Hinx2]].
          destruct (In_nth _ _ Pwild Hinp') as [j [Hj Hp']]; subst.
          exfalso. rewrite disj_cons_iff in Hp.
          destruct Hp as [_ Hp]. apply (Hp j Pwild x0 Hj); auto.
    }
    (*Now, we can prove these cases easily*)
    split; auto.
    intros. right. apply (H0 _ _ H1 H2).
  - (*Pwild is contradiction*)  
    inversion H; subst; split; intros; inversion H0.
  - (*Por just by IH*)
    split; intros; simpl in H, H1;
    rewrite intersect_elts in H1; destruct H1 as [Hfv1 Hfv2];
    destruct (match_val_single gamma_valid pd all_unif vt ty p1 (proj1' (pat_or_inv Hp)) d) eqn : Hmatch1.
    + inversion H; subst.
      apply (proj1 (IHp1 _ _ Hty _ _ Hmatch1) x y); auto.
    + apply (proj1 (IHp2 _ _ Hty _ _ H) x y); auto.
    + inversion H; subst.
      apply (proj2 (IHp1 _ _ Hty _ _ Hmatch1) x y); auto.
    + apply (proj2 (IHp2 _ _ Hty _ _ H) x y); auto.
  - (*Pbind is Var + IH, just a lot of cases*)
    simpl. simpl in H.
    inversion Hp; subst.
    split; intros.
    + unfold vsym_in_m in H1. rewrite Hty in H1.
      rewrite union_elts in H1.
      destruct (match_val_single gamma_valid pd all_unif vt (snd v) p (proj1' (pat_bind_inv Hp)) d) eqn: Hmatch1;
      [|discriminate].
      inversion H; subst.
      destruct H0 as [Hxy | Hinl0].
      * inversion Hxy; subst. left. reflexivity.
      * destruct H1 as [[Hxv | []] | Hinx]; subst.
        -- (*Contradicts uniqueness of free vars*)
          exfalso. apply H3.
          apply match_val_single_free_var with(x:=x) in Hmatch1.
          apply Hmatch1. rewrite in_map_iff. exists (x, y); auto.
        -- (*IH case*)
          apply (proj1 (IHp _ _ Hty _ _ Hmatch1) x y); auto.
    + destruct (match_val_single gamma_valid pd all_unif vt (snd v) p (proj1' (pat_bind_inv Hp)) d) eqn : Hmatch1;
      [|discriminate].
      inversion H; subst.
      destruct H0 as [Hxy | Hinx]; subst.
      * inversion Hxy; subst.
        (*Contradiction: x in pat_fv bc in constr_vars*)
        apply pat_constr_vars_fv in H1. contradiction.
      * (*IH case*)
        apply (proj2 (IHp _ _ Hty _ _ Hmatch1) x y); auto.
Qed.

End MatchSmallerLemma.

(*Now that we are done, we can fix vt*)

Section Def.

Context  {vt: val_typevar} {pf: pi_funpred gamma_valid pd}.
 
Notation val x :=  (v_subst vt x).

Definition vt_eq srts:= forall i, i < length params ->
  vt (nth i params EmptyString) = nth i srts s_int.

Section WellFounded2.

(*Lemma for casting*)
Lemma arg_nth_eq srts (s: fpsym) (i: nat) (Hi: i < length (s_args s)) :
  nth i (sym_sigma_args s srts) s_int =
  val (ty_subst (s_params s) (sorts_to_tys srts)
    (nth i (s_args s) vty_int)).
Proof.
  assert ((ty_subst (s_params s) (sorts_to_tys srts) (nth i (s_args s) vty_int)) =
  (ty_subst_s (s_params s) srts (nth i (s_args s) vty_int))). {
    unfold ty_subst_s, ty_subst, v_subst. simpl. reflexivity. }
  rewrite H. clear H.
  unfold sym_sigma_args, ty_subst_list_s.
  rewrite map_nth_inbound with(d2:=vty_int); auto.
  apply subst_sort_eq.
Qed.

Lemma sn_idx_bound (s: sn) : sn_idx s < length (s_args (sn_sym s)).
Proof.
  destruct s; simpl in *.
  apply Nat.eqb_eq in sn_args_len. rewrite <- sn_args_len.
  apply Nat.ltb_lt. apply sn_idx_in.
Qed.

Lemma sn_idx_bound' (s: sn): sn_idx s < length (sn_args s).
Proof.
  destruct s. simpl. apply Nat.ltb_lt in sn_idx_in. auto.
Qed.

Lemma sn_args_Nodup s: NoDup (sn_args s).
Proof.
  destruct s; simpl in *.
  rewrite (reflect_iff _ _ (nodup_NoDup vsymbol_eq_dec _)); auto.
Qed.

Definition cast_symargs (srts: list sort) {s1 s2: fpsym} (H: s1 = s2) :
  sym_sigma_args s1 srts = sym_sigma_args s2 srts :=
  f_equal (fun x => sym_sigma_args x srts) H.

(*Our packed_args works over generic symbols, since it will be used
  for both functions and predicates.*)

Definition packed_args : Set :=
  {x: {s: sn | In s sns} & {srts: list sort & arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)}}.

(*The relation is simple: the (fn_idx)th element of the 1st
  arg_list must be smaller than the second*)
Inductive arg_list_smaller: 
 packed_args -> packed_args ->
  Prop :=
  | AL_small: forall 
    (x1: packed_args) 
    (x2: packed_args)
    (f1 f2: sn) 
    srts
    (Hsrts1: projT1 (projT2 x1) = srts)
    (Hsrts2: projT1 (projT2 x2) = srts)
    (a1: arg_list domain (sym_sigma_args (sn_sym f1) srts)) 
    (a2: arg_list domain (sym_sigma_args (sn_sym f2) srts))
    (Hf1: f1 = proj1_sig (projT1 x1))
    (Hf2: f2 = proj1_sig (projT1 x2))
    (Ha1: a1 = cast_arg_list 
      (eq_trans (cast_symargs (projT1 (projT2 x1)) (eq_sym (f_equal sn_sym Hf1)))
        (f_equal (sym_sigma_args (sn_sym f1)) Hsrts1))
      (projT2 (projT2 x1)))
    (Ha2: a2 = 
    cast_arg_list 
      (eq_trans (cast_symargs (projT1 (projT2 x2)) (eq_sym (f_equal sn_sym Hf2)))
        (f_equal (sym_sigma_args (sn_sym f2)) Hsrts2))
      (projT2 (projT2 x2))),
    adt_smaller_trans 
      (hide_ty (dom_cast _ (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1)) 
        (hnth (sn_idx f1) a1 s_int (dom_int pd))))
      (hide_ty (dom_cast _ (arg_nth_eq srts (sn_sym f2) (sn_idx f2) (sn_idx_bound f2)) 
        (hnth (sn_idx f2) a2 s_int (dom_int pd)))) ->
    arg_list_smaller x1 x2.

(*Now we prove that this is well-founded using
  well-founded induction on [adt_smaller_trans].
  This proof is actually very easy*)
Lemma arg_list_smaller_wf: well_founded arg_list_smaller.
Proof.
  unfold well_founded. intros a.
  (*Now we get y to induct on*)
  set (a2 :=projT2 (projT2 a)). simpl in a2.
  set (srts:=projT1(projT2 a)) in *.
  set (f2:= proj1_sig (projT1 a)). 
  remember ((hide_ty (dom_cast _ (arg_nth_eq srts (sn_sym f2) (sn_idx f2) (sn_idx_bound f2)) 
  (hnth (sn_idx f2) a2 s_int (dom_int pd))))) as y.
  subst a2 f2 srts.
  generalize dependent a. revert y.
  (*Apply IH*)
  match goal with
  | |- forall y, ?P => apply (well_founded_ind (adt_smaller_trans_wf)
    (fun y => P)) end. 
  (*Rest is direct from IH and inversion on rel*)
  intros x IH a2 Hx.
  constructor.
  intros a1 Hsmall.
  inversion Hsmall; subst.
  destruct a1; destruct a2; simpl in *.
  destruct s; destruct s0; subst; simpl in *. subst. simpl in *.
  eapply IH. 
  apply H. reflexivity.
Defined.

(*TODO: don't think we need the transitive closure of this, but see*)

End WellFounded2.


(*TODO: move*)
(*We can make this opaque: we don't actually need
  to compute with this*)
Definition find_fn (f: funsym) (l: list fn) : 
Either
  {f': fn | In f' l /\ f = fn_sym f'}
  (~ In f (map fn_sym l)).
induction l; simpl.
- apply Right. auto.
- destruct IHl.
  + destruct s as [f' [Hinf' Hf]]; subst.
    apply Left. apply (exist _ f'). split; auto.
  + destruct (funsym_eq_dec (fn_sym a) f).
    * subst. apply Left. apply (exist _ a). split; auto.
    * apply Right. intros [Heq | Hin]; subst; auto.
Qed.

Definition find_pn (p: predsym) (l: list pn) : 
Either
  {p': pn | In p' l /\ p = pn_sym p'}
  (~ In p (map pn_sym l)).
induction l; simpl.
- apply Right. auto.
- destruct IHl.
  + destruct s as [f' [Hinf' Hf]]; subst.
    apply Left. apply (exist _ f'). split; auto.
  + destruct (predsym_eq_dec (pn_sym a) p).
    * subst. apply Left. apply (exist _ a). split; auto.
    * apply Right. intros [Heq | Hin]; subst; auto.
Qed.

(*Invert [decrease_fun] for funs - 2 cases*)

Lemma dec_inv_tfun_in {small: list vsymbol} {hd: option vsymbol} {f: funsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
  {fn_def: fn} 
  (Hin: In fn_def fs)
  (Hfeq: f = fn_sym fn_def):
  l = map vty_var (s_params f) /\
  Forall (fun t => forall f, In f fs -> negb (funsym_in_tm (fn_sym f) t)) ts /\
  Forall (fun t => forall p, In p ps -> negb (predsym_in_term (pn_sym p) t)) ts.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H _ Hin).
    simpl in H. destruct (funsym_eq_dec (fn_sym fn_def) (fn_sym fn_def));
    simpl in H; try inversion H. contradiction.
  - split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists fn_def. split; auto.
Qed.

Lemma dec_inv_tfun_arg {small: list vsymbol} {hd: option vsymbol} {f: funsym}
{l: list vty} {ts: list term}
(Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
{fn_def: fn} 
(Hin: In fn_def fs)
(Hfeq: f = fn_sym fn_def):
exists x, In x small /\  nth (sn_idx fn_def) ts tm_d = Tvar x.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H _ Hin).
    simpl in H. destruct (funsym_eq_dec (fn_sym fn_def) (fn_sym fn_def));
    simpl in H; try inversion H. contradiction.
  - assert (fn_def = f_decl). apply (NoDup_map_in fs_uniq Hin H2 H3).
    subst. exists x. split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists fn_def. split; auto.
Qed. 

Lemma dec_inv_tfun_notin {small: list vsymbol} {hd: option vsymbol} {f: funsym}
{l: list vty} {ts: list term}
(Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
(Hnotin: ~ In f (map fn_sym fs)) :
Forall (decrease_fun fs ps small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_t.
    + intros. specialize (H _ H2). simpl in H.
      bool_hyps. rewrite existsb_false in H3.
      rewrite Forall_forall in H3. specialize (H3 _ H1).
      rewrite H3; auto.
    + intros. specialize (H0 _ H2). simpl in H0.
      bool_hyps. rewrite existsb_false in H0.
      rewrite Forall_forall in H0. specialize (H0 _ H1).
      rewrite H0; auto.
  - exfalso. apply Hnotin. rewrite in_map_iff.
    exists f_decl. split; auto.
  - rewrite Forall_forall. auto.
Qed.

(*As a corollary, we get that [decrease_fun] holds recursively*)
Corollary dec_inv_tfun_rec {small: list vsymbol} {hd: option vsymbol} {f: funsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) :
  Forall (fun t => decrease_fun fs ps small hd m vs t) ts.
Proof.
  destruct (in_dec funsym_eq_dec f (map fn_sym fs)).
  - rewrite in_map_iff in i. destruct i as [fn_def [Hfeq Hin]].
    apply dec_inv_tfun_in with(fn_def:=fn_def) in Hde; auto.
    destruct_all.
    revert H0 H1. rewrite !Forall_forall; intros.
    apply Dec_notin_t; auto.
  - eapply dec_inv_tfun_notin. apply Hde. auto.
Qed.

(*And we prove these for Fpred as well*)

Lemma dec_inv_fpred_in {small: list vsymbol} {hd: option vsymbol} 
  {p: predsym} {l: list vty} {ts: list term}
  (Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
  {pn_def: pn} 
  (Hin: In pn_def ps)
  (Hpeq: p = pn_sym pn_def):
  l = map vty_var (s_params p) /\
  Forall (fun t => forall f, In f fs -> negb (funsym_in_tm (fn_sym f) t)) ts /\
  Forall (fun t => forall p, In p ps -> negb (predsym_in_term (pn_sym p) t)) ts.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H0 _ Hin).
    simpl in H0. destruct (predsym_eq_dec (pn_sym pn_def) (pn_sym pn_def));
    simpl in H0; try inversion H0. contradiction.
  - split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists pn_def. split; auto.
Qed.

Lemma dec_inv_fpred_arg {small: list vsymbol} {hd: option vsymbol} 
{p: predsym}
{l: list vty} {ts: list term}
(Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
{pn_def: pn} 
(Hin: In pn_def ps)
(Hpeq: p = pn_sym pn_def):
exists x, In x small /\  nth (sn_idx pn_def) ts tm_d = Tvar x.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H0 _ Hin).
    simpl in H0. destruct (predsym_eq_dec (pn_sym pn_def) (pn_sym pn_def));
    simpl in H0; try inversion H0. contradiction.
  - assert (pn_def = p_decl). apply (NoDup_map_in ps_uniq Hin H2 H3).
    subst. exists x. split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists pn_def. split; auto.
Qed. 

Lemma dec_inv_fpred_notin {small: list vsymbol} {hd: option vsymbol} 
{p: predsym}
{l: list vty} {ts: list term}
(Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
(Hnotin: ~ In p (map pn_sym ps)) :
Forall (decrease_fun fs ps small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_t.
    + intros. specialize (H _ H2). simpl in H.
      bool_hyps. rewrite existsb_false in H.
      rewrite Forall_forall in H. specialize (H _ H1).
      rewrite H; auto.
    + intros. specialize (H0 _ H2). simpl in H0.
      bool_hyps. rewrite existsb_false in H3.
      rewrite Forall_forall in H3. specialize (H3 _ H1).
      rewrite H3; auto.
  - exfalso. apply Hnotin. rewrite in_map_iff.
    exists p_decl. split; auto.
  - rewrite Forall_forall. auto.
Qed.

(*As a corollary, we get that [decrease_fun] holds recursively*)
Corollary dec_inv_fpred_rec {small: list vsymbol} {hd: option vsymbol} 
  {p: predsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) :
  Forall (fun t => decrease_fun fs ps small hd m vs t) ts.
Proof.
  destruct (in_dec predsym_eq_dec p (map pn_sym ps)).
  - rewrite in_map_iff in i. destruct i as [pn_def [Hpeq Hin]].
    apply dec_inv_fpred_in with(pn_def:=pn_def) in Hde; auto.
    destruct_all.
    revert H0 H1. rewrite !Forall_forall; intros.
    apply Dec_notin_t; auto.
  - eapply dec_inv_fpred_notin. apply Hde. auto.
Qed.

(*TODO: remove or use eq_ind*)
Definition term_has_type_cast {t1 t2: term} {ty: vty} (Heq: t1 = t2)
  (Hty: term_has_type sigma t1 ty) : term_has_type sigma t2 ty :=
  match Heq with
  | eq_refl => Hty
  end.

(*We need a very complicated and ugly version of
  [get_arg_list] for this case. Both the inner function
  is much more complicated (requiring many more conditions)
  and the output is a sigma type because we need additional
  information about the output, and proving it later gives
  Coq a LOT of trouble in the later termination check.
  We give this version here; the real function has this
  inlined as a nested fix (or else Coq cannot prove
  termination). But later TODO, we will prove a lemma
  that relates them so that we have a nicer form to use*)

(*First, a lemma for the hard case so that the proof term
  (which we need to build manually for inlining)
  is not that horrible*)

Lemma arg_list_case_1
(v: val_vars pd vt)
(d: {s : sort & domain s})
(s: fpsym)
(vs': list vty)
(hd: option vsymbol)
(small: list vsymbol)
(Hsmall: forall x : vsymbol, In x small ->
  vty_in_m m vs (snd x) /\
   adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
   vty_in_m m vs (snd h) /\
   hide_ty (v h) = d)
(rep: forall (t : term) (ty : vty) (small : list vsymbol)
        (hd: option vsymbol)
        (Hty : term_has_type sigma t ty),
      decrease_fun fs ps small hd m vs t ->
      (forall x : vsymbol, In x small ->
      vty_in_m m vs (snd x) /\
       adt_smaller_trans (hide_ty (v x)) d) ->
      (forall h, hd = Some h ->
       vty_in_m m vs (snd h) /\
       hide_ty (v h) = d) ->
      {d : domain (val ty)
      | forall (x : vsymbol) (Heqx : t = Tvar x),
        d =
        dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0)
             (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
          (var_to_dom pd vt v x)})
(Hparamslen: Datatypes.length vs' = Datatypes.length (s_params s))
(thd: term)
(ttl: list term)
(Hdecs: Forall (fun t : term => decrease_fun fs ps small hd m vs t) (thd :: ttl))
(ahd: vty)
(atl: list vty)
(Heq: Datatypes.length (thd :: ttl) = Datatypes.length (ahd :: atl))
(Htys: Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
         (combine (thd :: ttl) (map (ty_subst (s_params s) vs') (ahd :: atl))))
(vs_small: vsymbol)
(Hthd: nth 0 (thd :: ttl) tm_d = Tvar vs_small):
exists
(ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
(Heq0 : val ty' = ty_subst_s (s_params s) (map (fun x : vty => val x) vs') ahd),
dom_cast (dom_aux pd)
  (funsym_subst_eq (s_params s) vs' vt ahd (s_params_Nodup s)
     (eq_sym Hparamslen))
  (proj1_sig
     (rep thd (ty_subst (s_params s) vs' ahd) small hd (Forall_inv Htys)
        (Forall_inv Hdecs) Hsmall Hhd)) =
dom_cast (dom_aux pd) Heq0
  (dom_cast (dom_aux pd)
     (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
     (var_to_dom pd vt v vs_small)).
Proof.
  exists (ty_subst (s_params s) vs' ahd).
  exists (eq_ind (nth 0 (thd :: ttl) tm_d)
  (fun t : term => term_has_type sigma t (ty_subst (s_params s) vs' ahd))
  (Forall_inv Htys) (Tvar vs_small) Hthd).
  exists (funsym_subst_eq (s_params s) vs' vt ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) .
  (*simpl.*)
  destruct (rep thd (ty_subst (s_params s) vs' ahd) small hd
    (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd) as [rep1 rep2].
  simpl.
  rewrite (rep2 vs_small Hthd).
  reflexivity.
(*Needs to be transparent for termination*)
Defined.

(*The function we need (TODO: change name)*)
Fixpoint get_arg_list_ext_aux' {v : val_vars pd vt} {hd d} (f: funsym)
  {vs': list vty} {ts: list term} (*{ty: vty}*)
  {small}
  (Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d)
  (rep: forall (t: term) (ty: vty) (small: list vsymbol) hd
      (Hty: term_has_type sigma t ty)
      (Hdec: decrease_fun fs ps small hd m vs t)
      (Hsmall: forall x, In x small ->
      vty_in_m m vs (snd x) /\
          (*TODO: type restriction here?*)
          adt_smaller_trans (hide_ty (v x)) d)
      (Hhd: forall h, hd = Some h ->
      vty_in_m m vs (snd h) /\
      hide_ty (v h) = d),
      {d: domain (val ty) | forall x (Heqx: t = Tvar x),
          d = dom_cast _ (f_equal (fun x => val x) 
            (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
            (var_to_dom _ vt v x)})
  (Hparamslen: length vs' = length (s_params f))
  {struct ts}:
  forall args
  (Hargslen: length ts = length args)
  (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine ts (map (ty_subst (s_params f) vs') args)))
  (Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
  {a: arg_list domain (ty_subst_list_s (s_params f) 
    (map (fun x => val x) vs') args) |
    forall (j: nat) (Hj: j < length ts) vs_small,
    nth j ts tm_d = Tvar vs_small ->
    exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
        Heq,
    (*Avoids the need to relate hnth to term_rep_aux (nth) by
    directly giving the result we need*)
    hnth j a s_int (dom_int pd) =
    dom_cast (dom_aux pd) Heq
      (dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
        (var_to_dom pd vt v vs_small))} :=
match ts as ts'
  return forall args,
  length ts' = length args ->
  Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
    (combine ts' (map (ty_subst (s_params f) vs') args)) ->
  Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
  {a: arg_list domain (ty_subst_list_s (s_params f) 
    (map (fun x => val x) vs') args) |
    forall (j: nat) (Hj: j < length ts') vs_small,
    nth j ts' tm_d = Tvar vs_small ->
    exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
        Heq,
    hnth j a s_int (dom_int pd) =
    dom_cast (dom_aux pd) Heq
      (dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
        (var_to_dom pd vt v vs_small))} 
  with
  | nil => fun args Hlen _ _ => 
      match args as a' return length nil = length a' -> 
      {a: arg_list domain (ty_subst_list_s (s_params f) 
        (map (fun x => val x) vs') a') |
        forall (j: nat) (Hj: j < length nil) vs_small,
        nth j nil tm_d = Tvar vs_small ->
        exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
            Heq,
        hnth j a s_int (dom_int pd) =
        dom_cast (dom_aux pd) Heq
          (dom_cast (dom_aux pd)
            (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
            (var_to_dom pd vt v vs_small))} 
      with 
      (*Both get contradictions here*)
      | nil => fun Hlena => exist _ (@HL_nil _ _) 
        (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
      | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
      end Hlen
  | thd :: ttl => 
    fun args Hlen Htys Hdecs => 
    match args as a' return length (thd :: ttl) = length a' ->
      Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
        (combine (thd :: ttl) (map (ty_subst (s_params f) vs') a')) ->
      {a: arg_list domain (ty_subst_list_s (s_params f) 
        (map (fun x => val x) vs') a') |
        forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
        nth j (thd :: ttl) tm_d = Tvar vs_small ->
        exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
            Heq,
        hnth j a s_int (dom_int pd) =
        dom_cast (dom_aux pd) Heq
          (dom_cast (dom_aux pd)
            (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
            (var_to_dom pd vt v vs_small))} 
      with
      | nil => fun Hlen =>
        False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
      | ahd :: atl => fun Heq Htys =>
        exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
        (funsym_subst_eq (s_params f) vs' vt ahd
         (s_params_Nodup _) (eq_sym Hparamslen)) 
          (proj1_sig (rep _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
          (proj1_sig (get_arg_list_ext_aux'  f  Hsmall Hhd rep Hparamslen atl 
            (Nat.succ_inj (length ttl) (length atl) Heq)
            (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
        (*build the function for second part*)
        (fun j => 
          match j as j' return j' < length (thd :: ttl) ->
            forall (vs_small: vsymbol),
            nth j' (thd :: ttl) tm_d = Tvar vs_small ->
            exists
              (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
            (Heq0 : val ty' =
                    nth j'
                      (ty_subst_list_s (s_params f) (map (fun x : vty => val x) vs') (ahd :: atl))
                      s_int),
              hnth j'
                (HL_cons domain (ty_subst_s (s_params f) (map (v_subst vt) vs') ahd)
                  (ty_subst_list_s (s_params f) (map (fun x : vty => val x) vs') atl)
                  (dom_cast (dom_aux pd)
                      (funsym_subst_eq (s_params f) vs' vt ahd 
                        (s_params_Nodup f) (eq_sym Hparamslen))
                      (proj1_sig
                        (rep (fst (thd, ty_subst (s_params f) vs' ahd))
                            (snd (thd, ty_subst (s_params f) vs' ahd)) small hd
                            (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                  (proj1_sig (get_arg_list_ext_aux' f Hsmall Hhd
                     rep Hparamslen atl
                      (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                      (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
                (dom_int pd) =
              dom_cast (dom_aux pd) Heq0
                (dom_cast (dom_aux pd)
                  (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                  (var_to_dom pd vt v vs_small))
          with
          | 0 => 
            (*Case when j = 0*)
            fun _ vs_small Hthd => 
              arg_list_case_1 v d f vs' hd small Hsmall Hhd rep Hparamslen thd ttl 
                Hdecs ahd atl Heq Htys vs_small Hthd
          | S j' => 
            (fun Hj vs_small Hnth =>
            (proj2_sig (get_arg_list_ext_aux' f Hsmall Hhd rep Hparamslen atl 
            (Nat.succ_inj (length ttl) (length atl) Heq)
            (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
            (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
            ) )
          end)
      end Hlen Htys
  end.

  (*
  (*A computable version - why is standard version not computable?*)
Definition proj1' {A B: Prop} (H: A /\ B) : A :=
  match H with
  | conj x x0 => x
  end.

Definition proj2' {A B: Prop} (H: A /\ B) : B :=
  match H with
  | conj x x0 => x0
  end.*)

(*Is this the lemma we need?*)

Lemma map_vars_srts srts: 
  length srts = length params ->
  vt_eq srts ->
  map (fun x => val x) (map vty_var params) = srts.
Proof.
  intros srts_len vt_eq.
  rewrite map_map. apply list_eq_ext'; rewrite map_length; auto;
  intros n d Hn.
  rewrite map_nth_inbound with(d2:= EmptyString); auto.
  apply sort_inj. simpl.
  rewrite vt_eq; auto. erewrite nth_indep; auto. lia.
Qed.

Lemma map_vals_srts' srts s:
  length srts = length params ->
  vt_eq srts ->
  In s sns ->
  map (fun x => val x) (map vty_var (s_params (sn_sym s))) = srts.
Proof.
  intros.
  rewrite params_eq; auto. apply map_vars_srts; auto.
Qed.

(*TODO: move*)
Lemma eq_trans_refl {A: Set} {x1 x2: A} (H: x1 = x2):
eq_trans eq_refl H = H.
Proof.
  destruct H. reflexivity.
Qed.

(*rewrite our cast into a [cast_arg_list] so we can simplify*)
Lemma scast_funsym_args_eq {s: fpsym} {s1 s2: list sort}
  (Heq: s1 = s2) x:
  scast (f_equal (fun x => arg_list domain (sym_sigma_args s x)) Heq)
    x =
  cast_arg_list (f_equal (fun x => sym_sigma_args s x) Heq) x.
Proof.
  destruct Heq. reflexivity.
Qed.

Lemma scast_funsym_args_eq' {s1 s2: fpsym} {srts: list sort}
  (Heq: s1 = s2) x:
  scast (f_equal (fun x => arg_list domain (sym_sigma_args x srts)) Heq) 
    x =
  cast_arg_list (f_equal (fun x => sym_sigma_args x srts) Heq) x.
Proof.
  destruct Heq. reflexivity.
Qed.


Lemma ty_subst_fun_params_id: forall params d v,
  In v params ->
  ty_subst_fun params (map vty_var params) d v = vty_var v.
Proof.
  intros. induction params0. inversion H.
  simpl. simpl in H. destruct (typevar_eq_dec v a); subst; auto.
  simpl. destruct H; subst; auto. contradiction.
Qed.

Lemma map_id' {A : Type} (f: A -> A) l:
  Forall (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction l; simpl; intros; auto. inversion H; subst; auto.
  rewrite H2. f_equal; auto.
Qed.

Lemma ty_subst_params_id: forall params x,
  (forall v, In v (type_vars x) -> In v params) ->
  ty_subst params (map vty_var params) x = x.
Proof.
  intros. unfold ty_subst. induction x; simpl; auto.
  apply ty_subst_fun_params_id. apply H. simpl; auto.
  f_equal. apply map_id'.
  revert H0. rewrite !Forall_forall; intros.
  apply H0; auto. intros. apply H. simpl. simpl_set; auto.
  exists x. split; auto.
Qed.

(*The type doesn't actually matter for [adt_smaller]; only
  the value. Thus, we can cast and still have the relation hold*)
Lemma adt_smaller_hide_cast {s1 s2: sort} (x: domain s1) 
  (y: {s: sort & domain s}) (Heq: s1 = s2):
  adt_smaller (hide_ty x) y ->
  adt_smaller (hide_ty (dom_cast (dom_aux pd) Heq x)) y.
Proof.
  intros. unfold hide_ty in *. destruct y as [ty_y dy].
  rename x into dx. inversion H. subst x1 x2.
  simpl in *. subst s0. subst s3. simpl in *.
  unfold dom_cast in Hx1_2, Hx2_2. simpl in Hx1_2, Hx2_2. subst d1 d2.
  eapply (ADT_small _ _ s2 ty_y (dom_cast (dom_aux pd) Heq dx) 
    dy m0 a1 a2 srts c args _ _ _ _ (eq_trans (eq_sym Heq) Hty1) 
    Hty2 a_in1 a_in2 m_in0 c_in lengths_eq).
  Unshelve. all: try reflexivity.
  - apply Hadt2.
  - destruct H0 as [i [Heq' [Hi Had1]]].
    exists i. exists Heq'. split; auto.
    subst adt1. rewrite <- Had1.
    (*Need to cancel out eq_sym*)
    unfold dom_cast; rewrite !scast_scast.
    rewrite eq_trans_assoc, <- eq_trans_map_distr.
    rewrite eq_trans_assoc, eq_trans_sym_inv_r.
    rewrite eq_trans_refl.
    reflexivity.
Qed.

(*And for transitive version:*)

Lemma adt_smaller_trans_hide_cast {s1 s2: sort} (x: domain s1)
  (y: {s: sort & domain s}) (Heq: s1 = s2):
  adt_smaller_trans (hide_ty x) y ->
  adt_smaller_trans (hide_ty (dom_cast (dom_aux pd) Heq x)) y.
Proof.
  intros.
  remember (hide_ty x) as x'.
  generalize dependent x.
  induction H; intros; subst.
  - constructor. apply adt_smaller_hide_cast; auto.
  - eapply Rtrans_multi.
    apply IHR_trans. reflexivity. auto.
Qed.


(*Create the valuation given a list of sorts and variables*)
(*TODO: move to Semantics/Interp*)
Fixpoint val_with_args (vv: val_vars pd vt) (vars: list vsymbol) 
  {srts: list sort}
  (a: arg_list domain srts) :
  val_vars pd vt :=
  fun (x: vsymbol) =>
  match vars, a with
  | hd :: tl, HL_cons shd stl d t =>
     (*Need to know that types are equal so we can cast the domain*)
     match (vty_eq_dec (val (snd x))) shd with
     | left Heq => if vsymbol_eq_dec hd x then 
        dom_cast _ (sort_inj (eq_sym Heq)) d
         else val_with_args vv tl t x
     | _ => val_with_args vv tl t x
     end
  | _, _ => vv x
  end.

  (*Basically UIP for x = y instead of x = x*)
Lemma dec_uip_diff {A: Set} {x1 x2: A} 
  (eq_dec: forall (x y: A), {x= y} + {x <> y}) 
  (H1 H2: x1 = x2):
  H1 = H2.
Proof.
  subst. apply UIP_dec. auto.
Qed.

Lemma val_with_args_in vv (vars: list vsymbol) (srts: list sort)
  (a: arg_list domain srts)
  (Hnodup: NoDup vars)
  (Hlen: length vars = length srts):
  forall i (Hi: i < length vars)
  (Heq: nth i srts s_int = val (snd (nth i vars vs_d))),
  val_with_args vv vars a (nth i vars vs_d) =
  dom_cast _ Heq (hnth i a s_int (dom_int pd)).
Proof.
  intros. generalize dependent srts. generalize dependent i.
  induction vars; simpl; intros.
  - inversion Hi.
  - destruct a0.
    + inversion Hlen.
    + simpl. destruct i.
      * (*i=0*) 
        destruct (vsymbol_eq_dec a a); try contradiction.
        destruct (vty_eq_dec (v_subst_aux (fun x0 : typevar => vt x0) (snd a)) x); subst.
        -- unfold dom_cast.
          f_equal. f_equal. apply dec_uip_diff. apply sort_eq_dec.
        -- exfalso. apply n.
          simpl in Heq. subst. reflexivity.
      * (*i <> 0*) inversion Hnodup; subst.
        destruct (vty_eq_dec
        (v_subst_aux (fun x0 : typevar => vt x0) (snd (nth i vars vs_d))) x).
        -- destruct (vsymbol_eq_dec a (nth i vars vs_d)).
          ++ exfalso; subst. apply H1. apply nth_In; auto. simpl in Hi. lia.
          ++ erewrite IHvars; auto. lia. 
        -- erewrite IHvars; auto. lia.
Qed.

(*The other case is much easier*)
Lemma val_with_args_notin vv (vars: list vsymbol) (srts: list sort)
  (a: arg_list domain srts) (x : vsymbol)
  (Hnotinx: ~ In x vars):
  val_with_args vv vars a x = vv x.
Proof.
  generalize dependent srts. induction vars; simpl; intros; auto.
  destruct a0; auto.
  simpl in Hnotinx. not_or Hx.
  destruct (vty_eq_dec (v_subst_aux (fun x1 : typevar => vt x1) (snd x)) x0).
  - destruct (vsymbol_eq_dec a x); subst; auto; contradiction.
  - apply IHvars; auto.
Qed.

Lemma fn_ret_cast_eq (f: fn) (Hinf: In f fs)
  (srts: list sort)
  (args: arg_list domain (sym_sigma_args (fn_sym f) srts))
  (Hlen: length srts = length params) (*TODO: see*)
  (Hvt_eq: vt_eq srts):
  val (f_ret (fn_sym f)) = funsym_sigma_ret (fn_sym f) srts.
Proof.
  unfold funsym_sigma_ret. rewrite funs_params_eq; auto.
  apply v_ty_subst_eq; auto.
  - rewrite <- (funs_params_eq _ Hinf); auto. apply s_params_Nodup.
  - eapply f_typevars. apply Hinf. left; auto.
Qed.

(*TODO: move*)
Variable fs_dec: Forall (fun (f: fn) => decrease_fun fs ps nil 
  (Some (nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) fs.
Variable ps_dec: Forall (fun (p: pn) => decrease_pred fs ps nil 
  (Some (nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p)) ps.

Lemma Forall_In {A: Type} {P: A -> Prop} {l: list A} {x: A}:
  Forall P l ->
  In x l ->
  P x.
Proof.
  induction l; simpl; intros; destruct H0; subst; inversion H; auto.
Qed.

(*Lift relation to dependent pairs*)
Definition R_projT1 {A : Type} (B: A -> Type) (R: A -> A -> Prop) :
  {x: A & B x} -> {x : A & B x} -> Prop :=
  fun x y => R (projT1 x) (projT1 y).

Lemma wf_projT1 {A : Type} {B: A -> Type} {R: A -> A -> Prop}
  (wf: well_founded R):
  well_founded (R_projT1 B R).
Proof.
  unfold R_projT1.
  assert (forall (z: {x : A & B x}),
    Acc R (projT1 z) ->
    Acc (fun (x : {x : A & B x}) (y : {x0 : A & B x0}) => 
      R (projT1 x) (projT1 y)) z).
  {
    intros. destruct z as [a b]. simpl in *.
    generalize dependent b.
    induction H.
    intros. constructor. intros.
    simpl in H1.
    destruct y as [y1 y2]. simpl in *.
    apply H0. auto.
  }
  unfold well_founded. intros.
  apply H. apply wf.
Qed. (*TODO: Defined?*)

(*In our function, we also must know that the sn we are dealing
  with belongs to some function or predicate symbol*)
Definition combined_args : Set :=
  {pa: packed_args & 
  Either {f: fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
         {p: pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}}.

Definition combine_args_fun (pa: packed_args) (f: fn)
  (Hin: In f fs)
  (Hf: fn_sn f = proj1_sig (projT1 pa)) :
  combined_args :=
  existT _ pa (Left _ _ (exist _ f (conj Hin Hf))).

Definition combine_args_pred (pa: packed_args) (p: pn)
  (Hin: In p ps)
  (Hp: pn_sn p = proj1_sig (projT1 pa)) :
  combined_args :=
  existT _ pa (Right _ _ (exist _ p (conj Hin Hp))).

Lemma in_fs_sns {f: fn}:
  In f fs ->
  In (fn_sn f) sns.
Proof.
  intros. unfold sns. rewrite in_app_iff. left. rewrite in_map_iff.
  exists f. split; auto.
Qed.

Lemma in_ps_sns {p: pn}:
  In p ps ->
  In (pn_sn p) sns.
Proof.
  intros. unfold sns. rewrite in_app_iff. right. rewrite in_map_iff.
  exists p. split; auto.
Qed.

(*Finally, we pack it all together with the valuation and
  some conditions on the srts list*)

(*TODO: name*)
Definition packed_args2 := {fa: combined_args &
(val_vars pd vt *
  (length (projT1 (projT2 (projT1 fa))) = length params /\
  vt_eq (projT1 (projT2 (projT1 fa)))))%type}.

Definition pack_args (fa: combined_args) (v: val_vars pd vt)
  (Hsrts: length (projT1 (projT2 (projT1 fa))) = length params /\
  vt_eq (projT1 (projT2 (projT1 fa)))) :
  packed_args2 :=
  existT _ fa (v, Hsrts). 

(*TODO: better way*)
(*Handle contradictions in term_rep_aux, only
  var case matters*)
Lemma const_not_var {c x}:
  Tconst c <> Tvar x.
Proof.
  intros. discriminate.
Qed.

Lemma fun_not_var {f l ts x}:
  Tfun f l ts <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tlet_not_var {t1 v t2 x}:
  Tlet t1 v t2 <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tif_not_var {f1 t2 t3 x}:
  Tif f1 t2 t3 <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tmatch_not_var {t1 v1 ps' x}:
  Tmatch t1 v1 ps' <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma teps_not_var {f1 v x}:
  Teps f1 v <> Tvar x.
Proof.
  discriminate.
Qed.

(*Only interesting case*)
Lemma var_case ty x v Hty' Heq: (fun d : domain (val ty) =>
forall (x0 : vsymbol) (Heqx : Tvar x = Tvar x0),
d =
dom_cast (dom_aux pd)
  (f_equal (fun x : vty => val x)
     (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty')))) 
  (var_to_dom pd vt v x0))
 (dom_cast (dom_aux pd) (f_equal (fun x : vty => val x) (eq_sym Heq))
    (var_to_dom pd vt v x)).
Proof.
  simpl. intros. injection Heqx. intros; subst.
  simpl. f_equal. apply dec_uip_diff. apply sort_eq_dec.
Qed.

(*TODO: move*)
Lemma rewrite_dom_cast: forall (v1 v2: sort) (Heq: v1 = v2)
  x,
  scast (f_equal domain Heq) x = dom_cast (dom_aux pd) Heq x.
Proof.
  intros. reflexivity.
Qed.

(*Inversion lemmas for decreasing*)

Ltac solve_dec_inv :=
  intros;
  match goal with
  | Heq: decrease_pred ?fs ?ps ?small ?hd ?m ?vs ?f |- _ =>
    inversion Heq; subst; auto
  | Heq: decrease_fun ?fs ?ps ?small ?hd ?m ?vs ?t |- _ =>
    inversion Heq; subst; auto
  end;
  repeat lazymatch goal with
  | |- ?P /\ ?Q => split
  | H1: forall (f: fn), In f ?fs -> 
      is_true (negb (funsym_in_fmla (fn_sym f) ?x)),
    H2: forall (p: pn), In p ?ps -> 
      is_true (negb (predsym_in (pn_sym p) ?x)) |- _ =>
      lazymatch goal with
      | |- decrease_pred ?fs ?ps ?small ?hd ?m ?vs ?y =>
          apply Dec_notin_f
      | |- decrease_fun ?fs ?ps ?small ?hd ?m ?vs ?y =>
        apply Dec_notin_t
      end;
    let z := fresh "z" in
    let Hin := fresh "Hin" in
    intros z Hin;
    simpl in H1; simpl in H2;
    try (specialize (H1 _ Hin));
    try (specialize (H2 _ Hin));
    bool_hyps
  | H1: ?b = false |-
    is_true (negb ?b) => rewrite H1; auto
  | H1: forall (f: fn), In f ?fs -> 
      is_true (negb (funsym_in_tm (fn_sym f) ?x)),
    H2: forall (p: pn), In p ?ps -> 
      is_true (negb (predsym_in_term (pn_sym p) ?x)) |- _ =>
      lazymatch goal with
      | |- decrease_pred ?fs ?ps ?small ?hd ?m ?vs ?y =>
          apply Dec_notin_f
      | |- decrease_fun ?fs ?ps ?small ?hd ?m ?vs ?y =>
        apply Dec_notin_t
      end;
    let z := fresh "z" in
    let Hin := fresh "Hin" in
    intros z Hin;
    simpl in H1; simpl in H2;
    try (specialize (H1 _ Hin));
    try (specialize (H2 _ Hin));
    bool_hyps
  end.

Lemma dec_inv_tlet {fs' ps' tm1 x tm2 small y}:
  decrease_fun fs' ps' small y m vs (Tlet tm1 x tm2) ->
  decrease_fun fs' ps' small y m vs tm1 /\
  decrease_fun fs' ps' (remove vsymbol_eq_dec x small) (upd_option y x) m vs tm2.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_tif {fs' ps' f1 t1 t2 small hd}:
  decrease_fun fs' ps' small hd m vs (Tif f1 t1 t2) ->
  decrease_pred fs' ps' small hd m vs f1 /\
  decrease_fun fs' ps' small hd m vs t1 /\
  decrease_fun fs' ps' small hd m vs t2.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_teps {fs' ps' f v small hd}:
  decrease_fun fs' ps' small hd m vs (Teps f v) ->
  decrease_pred fs' ps' (remove vsymbol_eq_dec v small) 
    (upd_option hd v) m vs f.
Proof.
  solve_dec_inv.
Qed.

(*Case analysis for [tmatch]*)
Definition tmatch_case (tm: term) (hd: option vsymbol) (small: list vsymbol) :
  Either {mvar: vsymbol | tm = Tvar mvar /\
    (hd = Some mvar \/ In mvar small)}
    (~ exists var, tm = Tvar var /\ (hd = Some var \/ In var small)).
Proof.
  destruct tm; try solve[apply Right; intros [var [Ht]]; inversion Ht].
  destruct hd as [h |].
  - destruct (vsymbol_eq_dec v h).
    + subst. apply Left. apply (exist _ h).  split; auto.
    + destruct (in_dec vsymbol_eq_dec v small).
      * apply Left. apply (exist _ v). split; auto.
      * apply Right. intros [var [Ht [Hvar | Hinvar]]]; try inversion Hvar; subst; 
        inversion Ht; subst; contradiction.
  - destruct (in_dec vsymbol_eq_dec v small).
    + apply Left. apply (exist _ v). split; auto.
    + apply Right. intros [var [Ht [Hvar | Hinvar]]]; try inversion Hvar; subst; 
      inversion Ht; subst; contradiction.
Qed.

(*Inversion lemmas for [tmatch] and [fmatch]*)
Lemma dec_inv_tmatch_fst {fs' ps' tm small hd v pats}:
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  decrease_fun fs' ps' small hd m vs tm.
Proof.
  solve_dec_inv.
  apply Dec_notin_t; simpl; auto.
Qed.

Lemma dec_inv_fmatch_fst {fs' ps' tm small hd v pats}:
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  decrease_fun fs' ps' small hd m vs tm.
Proof.
  solve_dec_inv.
  apply Dec_notin_t; simpl; auto.
Qed.

Lemma dec_inv_tmatch_var {fs' ps' tm small hd mvar v pats}
  (Htm: tm = Tvar mvar /\ (hd = Some mvar \/ In mvar small)):
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall
  (fun x : pattern * term =>
   decrease_fun fs' ps'
     (union vsymbol_eq_dec
        (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - (*No funsym or predsym occurrence*)
    rewrite Forall_forall. intros.
    apply Dec_notin_t; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - destruct Htm as [Ht _]. inversion Ht; subst.
    rewrite Forall_forall. auto.
  - exfalso. apply H7. exists mvar. auto.
Qed.

(*Proof identical*)
Lemma dec_inv_fmatch_var {fs' ps' tm small hd mvar v pats}
  (Htm: tm = Tvar mvar /\ (hd = Some mvar \/ In mvar small)):
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  Forall
  (fun x : pattern * formula =>
   decrease_pred fs' ps'
     (union vsymbol_eq_dec
        (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - (*No funsym or predsym occurrence*)
    rewrite Forall_forall. intros.
    apply Dec_notin_f; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - destruct Htm as [Ht _]. inversion Ht; subst.
    rewrite Forall_forall. auto.
  - exfalso. apply H7. exists mvar. auto.
Qed.

Lemma dec_inv_tmatch_notvar {fs' ps' tm small hd v pats}
  (Htm: ~ exists var, tm = Tvar var /\ (hd = Some var \/ In var small)):
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall (fun x => decrease_fun fs' ps' 
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
    ((upd_option_iter hd (pat_fv (fst x)))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_t; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - exfalso. apply Htm. exists mvar. auto.
  - rewrite Forall_forall. auto.
Qed.

(*Proof also identical*)
Lemma dec_inv_fmatch_notvar {fs' ps' tm small hd v pats}
  (Htm: ~ exists var, tm = Tvar var /\ (hd = Some var \/ In var small)):
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  Forall (fun x => decrease_pred fs' ps' 
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
    ((upd_option_iter hd (pat_fv (fst x)))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_f; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - exfalso. apply Htm. exists mvar. auto.
  - rewrite Forall_forall. auto.
Qed.

Lemma in_remove {A: Type} {P: A -> Prop} {l: list A} {x: A}
  {eq_dec: forall (x y: A), {x=y} +{x <> y}}:
  (forall x, In x l -> P x) ->
  (forall y, In y (remove eq_dec x l) -> P y).
Proof.
  intros. simpl_set. destruct H0. apply H; auto.
Qed.

(*We need to get d, the value we must be smaller than to
  recurse. This is the nth element of a, the arg_list we
  have as input. But using the naive way means that we cannot
  prove that the nth argument (in fn_args) actually corresponds 
  to d. So we need another lemma*)
Lemma arg_list_args_eq {srts: list sort} {s: sn} 
  (Hin: In s sns)
  (Hsrtslen: length srts = length params)
  (Hvteq: vt_eq srts)
  (i: nat):
  i < length (sn_args s) ->
  nth i (sym_sigma_args (sn_sym s) srts) s_int =
  val (snd (nth i (sn_args s) vs_d)).
Proof.
  intros Hi.
  pose proof (Hargs:=args_agree s Hin).
  assert (Hleneq: length (sn_args s) = length (s_args (sn_sym s))). {
    pose proof (f_equal (fun x => length x) Hargs) as Hlen.
    rewrite map_length in Hlen. unfold vsymbol. rewrite Hlen. auto.
  }
  assert (Hitheq: (snd (nth i (sn_args s) vs_d) =
  (nth i (s_args (sn_sym s)) vty_int))). {
    pose proof (f_equal (fun x => nth i x vty_int) Hargs) as Hntheq.
    rewrite <- Hntheq.
    rewrite map_nth_inbound with (d2:=vs_d); auto.
  }
  rewrite arg_nth_eq; [|lia]. 
  apply sort_inj; simpl.
  rewrite <- subst_is_sort_eq; auto.
  - symmetry. rewrite Hitheq. apply v_ty_subst_eq_aux; auto.
    + apply s_params_Nodup.
    + rewrite Hsrtslen. 
      rewrite (params_eq _ Hin). auto.
    + rewrite (params_eq _ Hin).
      apply Hvteq.
    + intros x. rewrite (params_eq _ Hin).
      eapply s_typevars. apply Hin.
      apply nth_In. lia.
  - unfold ty_subst. apply v_subst_aux_sort_eq.
    intros.
    (*Basically, know that these are all in params*)
    (*TODO: separate lemma?*)
    assert (In x params). {
      revert H. eapply s_typevars. apply Hin. 
      apply nth_In; lia.
    }
    rewrite (params_eq _ Hin).
    destruct (In_nth _ _ EmptyString H0) as [j [Hj Hx]]; subst.
    rewrite ty_subst_fun_nth with(s:=s_int); auto.
    + unfold sorts_to_tys. rewrite map_nth_inbound with(d2:=s_int); auto.
      * destruct (nth j srts s_int); auto.
      * rewrite Hsrtslen. auto.
    + unfold sorts_to_tys. rewrite map_length.
      auto.
    + rewrite <- (params_eq _ Hin).
      apply s_params_Nodup.
Qed.

(*Now we prove one of the key results: we call the
  function on smaller inputs, according to our well-founded
  relation. We do this in 2 parts*)

(*First, show it holds for any [arg_list] satisfying a property
  of its hnth elements which are variables.
  This does NOT use term_rep_aux, and it is generic in
  the choice of funsym or predsym*)

Lemma smaller_case_gen (v:val_vars pd vt) (input: packed_args2)  :
let fa:= projT1 (projT1 input) in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (sn_idx f1) (sn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1))
   (hnth (sn_idx f1) a1 s_int (dom_int pd))) in
forall (small: list vsymbol) hd
  (s1: fpsym) (sn_def: sn) (s_eq: s1 = sn_sym sn_def)
  (sn_in: In sn_def sns) (l: list vty) (ts: list term)
  (Hsmall: forall x : vsymbol,
    In x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d)
    (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d)
(args: arg_list domain
  (ty_subst_list_s 
    (s_params s1)
    (map (fun x : vty => val x) l) (s_args s1)))
(Hnth': forall (i: nat) vs_small,
  nth i ts tm_d = Tvar vs_small ->
  i < length ts ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
  Heq,
  hnth i args s_int (dom_int pd) =
dom_cast (dom_aux pd) Heq
  (dom_cast (dom_aux pd)
     (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
     (var_to_dom pd vt v vs_small)))

(Hdec2: Forall (fun t => decrease_fun fs ps small hd m vs t) ts)
(Hall:  Forall (fun x => term_has_type sigma (fst x) (snd x)) 
(combine ts (map (ty_subst (s_params s1) l) (s_args s1))))
(Hargslen: length ts = length (s_args s1))
(Hparamslen: length l = length (s_params s1))
(l_eq: l = map vty_var (s_params s1))
(srts_eq:  map (fun x0 : vty => val x0) (map vty_var (s_params s1)) = srts)
(Harg: exists x, In x small /\  nth (sn_idx sn_def) ts tm_d = Tvar x),

let s2 := sn_sym sn_def in 
let l_eq2: srts = map (fun x0 : vty => val x0) l := eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
let args': arg_list domain (sym_sigma_args s1 srts)  := scast
           (f_equal
              (fun x : list sort => arg_list domain (sym_sigma_args s1 x))
              (eq_sym l_eq2)) args in
let args'': arg_list domain (sym_sigma_args (sn_sym sn_def) srts):= scast
(f_equal
   (fun x : fpsym => arg_list domain (sym_sigma_args x srts))
   s_eq) args' in
let ind_arg:= existT
               (fun x : {s : sn | In s sns} =>
                {srts : list sort &
                arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
               (exist (fun s : sn => In s sns) sn_def sn_in)
               (existT
                  (fun srts : list sort =>
                   arg_list domain
                     (sym_sigma_args
                        (sn_sym
                           (proj1_sig (exist (fun s : sn => In s sns) sn_def sn_in)))
                        srts)) srts args'') : packed_args in
forall o, 
let ind_comb : combined_args := existT _ ind_arg o in
let ind_arg':= pack_args ind_comb v (conj srts_len vt_eq_srts) in
R_projT1
     (fun fa : combined_args =>
      (val_vars pd vt *
       (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
        vt_eq (projT1 (projT2 (projT1 fa)))))%type)
     (R_projT1
        (fun pa : packed_args =>
         Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
           {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) ind_arg' input.
Proof.
  intros.
  unfold R_projT1.
  subst ind_arg' ind_arg args'' args' l_eq2 d srts fa.
  unfold pack_args.
  simpl in *.

  (*We avoid evars as much as possible to make the proof faster*)
  apply (AL_small 
    (*We need to give the 1st arg or else Coq has problems*)
    (existT
     (fun x : {s : sn | In s sns} =>
      {srts : list sort & arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
     (exist (fun s : sn => In s sns) sn_def sn_in)
     (existT
        (fun srts : list sort => arg_list domain (sym_sigma_args (sn_sym sn_def) srts))
        (projT1 (projT2 (projT1 (projT1 input))))
        (scast
           (f_equal
              (fun x : fpsym =>
               arg_list domain
                 (sym_sigma_args x (projT1 (projT2 (projT1 (projT1 input)))))) s_eq)
           (scast
              (f_equal (fun x : list sort => arg_list domain (sym_sigma_args s1 x))
                 (eq_sym
                    (eq_trans (eq_sym srts_eq)
                       (f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
                          (eq_sym l_eq))))) args))))
    _ _ _ (projT1 (projT2 (projT1 (projT1 input)))) 
    eq_refl eq_refl _ _ eq_refl eq_refl eq_refl eq_refl).
    simpl. 
    unfold cast_arg_list.
    rewrite scast_funsym_args_eq. simpl.
    rewrite scast_funsym_args_eq'. 
    rewrite !hnth_cast_arg_list. 
    unfold cast_nth_eq.
    rewrite eq_trans_sym_distr, eq_sym_map_distr,
    !eq_sym_involutive, !eq_trans_map_distr, !f_equal_compose.
    destruct input as [fa [v' [srts_len' vt_eq_srts']]].
    simpl in *.
    destruct fa; simpl in *; subst.
    simpl.
    (*Now we need to know about hnth of get_arg_list_ext, from
      our assumption*)
    assert (Hidx: sn_idx sn_def < Datatypes.length ts). {
      rewrite Hargslen.
      apply sn_idx_bound.
    }
    (*Now we know that (nth (sn_idx x) ts tm_d) is a var in small*)
    destruct Harg as [vs_small [Hinvs Hvar]].
    destruct (Hnth' (sn_idx sn_def) vs_small Hvar Hidx) as [ty2 [Hty2 [Heq Hnth'']]].
    unfold sym_sigma_args.
    rewrite Hnth''.
    unfold var_to_dom.
    rewrite eq_trans_refl_l.
    rewrite rewrite_dom_cast.
    rewrite !dom_cast_compose.
    (*Now, this is just a casted version of the smaller assumption we
      have. So we can use [adt_smaller_trans_hide_cast]*)
    apply adt_smaller_trans_hide_cast.
    assert (term_has_type sigma (Tvar vs_small) (snd (nth (sn_idx sn_def) (sn_args sn_def) vs_d))). {
      rewrite Forall_forall in Hall.
      specialize (Hall (nth (sn_idx sn_def) ts tm_d, nth (sn_idx sn_def) (s_args (sn_sym sn_def)) vty_int)).
      simpl in Hall. rewrite <- Hvar.
      replace (snd (nth (sn_idx sn_def) (sn_args sn_def) vs_d)) with
      (nth (sn_idx sn_def) (s_args (sn_sym sn_def)) vty_int).
      - apply Hall.
        rewrite in_combine_iff; [|rewrite map_length; assumption].
        exists (sn_idx sn_def).
        split. apply Hidx.
        intros. f_equal. apply nth_indep; auto.
        rewrite map_nth_inbound with(d2:=vty_int); [|rewrite <- Hargslen; assumption]. 
        rewrite ty_subst_params_id; auto. intros.
        rewrite params_eq; auto.
        apply s_typevars with(s:=sn_def)
          (ty:=(nth (sn_idx sn_def) (s_args (sn_sym sn_def)) vty_int)); auto.
        apply nth_In. rewrite <- Hargslen; assumption.
      - rewrite <- args_agree; auto.
        rewrite map_nth_inbound with (d2:=vs_d); auto.
        rewrite <- args_agree in Hargslen; auto.
        rewrite map_length in Hargslen. unfold vsymbol. 
        rewrite <- Hargslen; assumption.
    }
    pose proof (Typechecker.term_has_type_unique _ _ _ _ Hty2 H) as Heqty.
    subst.
    pose proof (ty_var_inv H) as Hsndty.
    (*Finally, we apply Hsmall because we know that our argument
      is in the small list*)
    exact (proj2 (Hsmall _ Hinvs)).
Defined.

(*And the full result for funsyms, a corollary of the above. The 
  statement is very long (so that [term_rep_aux] can just
    call this directly), but the proof is very simple*)
Lemma func_smaller_case (v:val_vars pd vt) (input: packed_args2)  :
let fa:= projT1 (projT1 input) in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (sn_idx f1) (sn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1))
   (hnth (sn_idx f1) a1 s_int (dom_int pd))) in
forall (small: list vsymbol) hd
  (ty: vty) (f: funsym) (l: list vty) (ts: list term)
  (Hty': term_has_type sigma (Tfun f l ts) ty)
  (Hdec': decrease_fun fs ps small hd m vs (Tfun f l ts))
  (x: {f' : fn | In f' fs /\ f = fn_sym f'})
  (Hsmall: forall x : vsymbol,
    In x small ->
    vty_in_m m vs (snd x) /\
     adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
     vty_in_m m vs (snd h) /\
     hide_ty (v h) = d)
  (term_rep_aux: forall v (t : term) 
      (ty : vty) (small : list vsymbol) hd
      (Hty : term_has_type sigma t ty),
    decrease_fun fs ps small hd m vs t ->
    (forall x : vsymbol,
    In x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
    (forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d) ->
    {d : domain (val ty)
    | forall (x : vsymbol) (Heqx : t = Tvar x),
      d =
      dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0)
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
        (var_to_dom pd vt v x)}),
let get_arg_list_ext_aux':= fix get_arg_list_ext_aux' (s: fpsym)
{vs': list vty} {ts: list term} (*{ty: vty}*)
(Hparamslen: length vs' = length (s_params s))
{struct ts}:
forall args
(Hargslen: length ts = length args)
(Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs') args)))
(Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts) vs_small,
  nth j ts tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  (*Avoids the need to relate hnth to term_rep_aux (nth) by
  directly giving the result we need*)
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} :=
match ts as ts'
return forall args,
length ts' = length args ->
Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
  (combine ts' (map (ty_subst (s_params s) vs') args)) ->
Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts') vs_small,
  nth j ts' tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} 
with
| nil => fun args Hlen _ _ => 
    match args as a' return length nil = length a' -> 
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length nil) vs_small,
      nth j nil tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with 
    (*Both get contradictions here*)
    | nil => fun Hlena => exist _ (@HL_nil _ _) 
      (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
    | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
    end Hlen
| thd :: ttl => 
  fun args Hlen Htys Hdecs => 
  match args as a' return length (thd :: ttl) = length a' ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
      nth j (thd :: ttl) tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun Hlen =>
      False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
    | ahd :: atl => fun Heq Htys =>
      exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
      (funsym_subst_eq (s_params s) vs' vt ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) 
        (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
        (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
      (*build the function for second part*)
      (fun j => 
        match j as j' return j' < length (thd :: ttl) ->
          forall (vs_small: vsymbol),
          nth j' (thd :: ttl) tm_d = Tvar vs_small ->
          exists
            (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
          (Heq0 : val ty' =
                  nth j'
                    (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') (ahd :: atl))
                    s_int),
            hnth j'
              (HL_cons domain (ty_subst_s (s_params s) (map (v_subst vt) vs') ahd)
                (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') atl)
                (dom_cast (dom_aux pd)
                    (funsym_subst_eq (s_params s) vs' vt ahd 
                      (s_params_Nodup s) (eq_sym Hparamslen))
                    (proj1_sig
                      (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                          (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                          (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
                    (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                    (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
              (dom_int pd) =
            dom_cast (dom_aux pd) Heq0
              (dom_cast (dom_aux pd)
                (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                (var_to_dom pd vt v vs_small))
        with
        | 0 => 
          (*Case when j = 0*)
          fun _ vs_small Hthd => 
            arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
              Hdecs ahd atl Heq Htys vs_small Hthd
        | S j' => 
          (fun Hj vs_small Hnth =>
          (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
          (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
          ) )
        end)
    end Hlen Htys
end in
let Hinv:= fun_ty_inv Hty' in


let Hdec2:= dec_inv_tfun_rec Hdec' in
let Hall:= proj1' (proj2' (proj2' Hinv)) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let args := proj1_sig (get_arg_list_ext_aux' f Hparamslen (s_args f) Hargslen
Hall Hdec2) in

let fn_def:= proj1_sig x in
let f_fn:= proj2' (proj2_sig x) in
let fn_in:= proj1' (proj2_sig x)  in
let l_eq:= proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in
let sn_def := fn_sn fn_def in
let sn_in := in_fs_sns fn_in in
let s2 := sn_sym sn_def in
let s_eq := eq_trans (f_equal f_sym f_fn) (fn_wf fn_def) in
let srts_eq:= eq_trans
(f_equal
   (fun x : fpsym =>
    map (fun x0 : vty => val x0) (map vty_var (s_params x)))
   s_eq) (map_vals_srts' srts fn_def srts_len vt_eq_srts sn_in) in

let l_eq2:= eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
   let args':= scast
   (f_equal
      (fun x : list sort => arg_list domain (sym_sigma_args f x))
      (eq_sym l_eq2)) args in
let args'':= scast
(f_equal
(fun x : fpsym => arg_list domain (sym_sigma_args x srts))
s_eq) args' in
let ind_arg:= existT
       (fun x : {s : sn | In s sns} =>
        {srts : list sort &
        arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
       (exist (fun s : sn => In s sns) sn_def sn_in)
       (existT
          (fun srts : list sort =>
           arg_list domain
             (sym_sigma_args
                (sn_sym
                   (proj1_sig (exist (fun s : sn => In s sns) sn_def sn_in)))
                srts)) srts args'') : packed_args in
let ind_comb := combine_args_fun ind_arg fn_def fn_in eq_refl in
let ind_arg':= pack_args ind_comb v (conj srts_len vt_eq_srts) in
R_projT1
     (fun fa : combined_args =>
      (val_vars pd vt *
       (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
        vt_eq (projT1 (projT2 (projT1 fa)))))%type)
     (R_projT1
        (fun pa : packed_args =>
         Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
           {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) ind_arg' input.
Proof.
  intros.
  apply smaller_case_gen with(small:=small)(hd:=hd)(ts:=ts).
  - exact Hsmall.
  - exact Hhd.
  - intros. apply (proj2_sig ((get_arg_list_ext_aux'0 f l ts Hparamslen (s_args f) Hargslen Hall Hdec2))).
    exact H0. exact H.
  - exact Hdec2.
  - exact Hall.
  - exact Hargslen.
  - exact Hparamslen.
  - exact (dec_inv_tfun_arg Hdec' (proj1' (proj2_sig x)) f_fn).
Defined.

(*And the predicate case*)
Lemma pred_smaller_case (v:val_vars pd vt) (input: packed_args2)  :
let fa:= projT1 (projT1 input) in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (sn_idx f1) (sn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1))
   (hnth (sn_idx f1) a1 s_int (dom_int pd))) in
forall (small: list vsymbol) hd
  (p: predsym) (l: list vty) (ts: list term)
  (Hty': valid_formula sigma (Fpred p l ts))
  (Hdec': decrease_pred fs ps small hd m vs (Fpred p l ts))
  (x: {p' : pn | In p' ps /\ p = pn_sym p'})
  (Hsmall: forall x : vsymbol,
    In x small ->
    vty_in_m m vs (snd x) /\
     adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
     vty_in_m m vs (snd h) /\
     hide_ty (v h) = d)
  (term_rep_aux: forall v (t : term) 
      (ty : vty) (small : list vsymbol) hd
      (Hty : term_has_type sigma t ty),
    decrease_fun fs ps small hd m vs t ->
    (forall x : vsymbol,
    In x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
    (forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d) ->
    {d : domain (val ty)
    | forall (x : vsymbol) (Heqx : t = Tvar x),
      d =
      dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0)
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
        (var_to_dom pd vt v x)}),
let get_arg_list_ext_aux':= fix get_arg_list_ext_aux' (s: fpsym)
{vs': list vty} {ts: list term} (*{ty: vty}*)
(Hparamslen: length vs' = length (s_params s))
{struct ts}:
forall args
(Hargslen: length ts = length args)
(Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs') args)))
(Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts) vs_small,
  nth j ts tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  (*Avoids the need to relate hnth to term_rep_aux (nth) by
  directly giving the result we need*)
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} :=
match ts as ts'
return forall args,
length ts' = length args ->
Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
  (combine ts' (map (ty_subst (s_params s) vs') args)) ->
Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts') vs_small,
  nth j ts' tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} 
with
| nil => fun args Hlen _ _ => 
    match args as a' return length nil = length a' -> 
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length nil) vs_small,
      nth j nil tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with 
    (*Both get contradictions here*)
    | nil => fun Hlena => exist _ (@HL_nil _ _) 
      (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
    | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
    end Hlen
| thd :: ttl => 
  fun args Hlen Htys Hdecs => 
  match args as a' return length (thd :: ttl) = length a' ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
      nth j (thd :: ttl) tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun Hlen =>
      False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
    | ahd :: atl => fun Heq Htys =>
      exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
      (funsym_subst_eq (s_params s) vs' vt ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) 
        (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
        (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
      (*build the function for second part*)
      (fun j => 
        match j as j' return j' < length (thd :: ttl) ->
          forall (vs_small: vsymbol),
          nth j' (thd :: ttl) tm_d = Tvar vs_small ->
          exists
            (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
          (Heq0 : val ty' =
                  nth j'
                    (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') (ahd :: atl))
                    s_int),
            hnth j'
              (HL_cons domain (ty_subst_s (s_params s) (map (v_subst vt) vs') ahd)
                (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') atl)
                (dom_cast (dom_aux pd)
                    (funsym_subst_eq (s_params s) vs' vt ahd 
                      (s_params_Nodup s) (eq_sym Hparamslen))
                    (proj1_sig
                      (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                          (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                          (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
                    (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                    (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
              (dom_int pd) =
            dom_cast (dom_aux pd) Heq0
              (dom_cast (dom_aux pd)
                (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                (var_to_dom pd vt v vs_small))
        with
        | 0 => 
          (*Case when j = 0*)
          fun _ vs_small Hthd => 
            arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
              Hdecs ahd atl Heq Htys vs_small Hthd
        | S j' => 
          (fun Hj vs_small Hnth =>
          (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
          (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
          ) )
        end)
    end Hlen Htys
end in
let Hinv:= pred_val_inv Hty' in


let Hdec2:= dec_inv_fpred_rec Hdec' in
let Hall:= proj2' (proj2' Hinv) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let args := proj1_sig (get_arg_list_ext_aux' p Hparamslen (s_args p) Hargslen
Hall Hdec2) in

let pn_def:= proj1_sig x in
let p_pn:= proj2' (proj2_sig x) in
let pn_in:= proj1' (proj2_sig x)  in
let l_eq:= proj1' (dec_inv_fpred_in Hdec' pn_in p_pn) in
let sn_def := pn_sn pn_def in
let sn_in := in_ps_sns pn_in in
let s2 := sn_sym sn_def in
let s_eq := eq_trans (f_equal p_sym p_pn) (pn_wf pn_def) in
let srts_eq:= eq_trans
(f_equal
   (fun x : fpsym =>
    map (fun x0 : vty => val x0) (map vty_var (s_params x)))
   s_eq) (map_vals_srts' srts pn_def srts_len vt_eq_srts sn_in) in

let l_eq2:= eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
   let args':= scast
   (f_equal
      (fun x : list sort => arg_list domain (sym_sigma_args p x))
      (eq_sym l_eq2)) args in
let args'':= scast
(f_equal
(fun x : fpsym => arg_list domain (sym_sigma_args x srts))
s_eq) args' in
let ind_arg:= existT
       (fun x : {s : sn | In s sns} =>
        {srts : list sort &
        arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
       (exist (fun s : sn => In s sns) sn_def sn_in)
       (existT
          (fun srts : list sort =>
           arg_list domain
             (sym_sigma_args
                (sn_sym
                   (proj1_sig (exist (fun s : sn => In s sns) sn_def sn_in)))
                srts)) srts args'') : packed_args in
let ind_comb := combine_args_pred ind_arg pn_def pn_in eq_refl in
let ind_arg':= pack_args ind_comb v (conj srts_len vt_eq_srts) in
R_projT1
     (fun fa : combined_args =>
      (val_vars pd vt *
       (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
        vt_eq (projT1 (projT2 (projT1 fa)))))%type)
     (R_projT1
        (fun pa : packed_args =>
         Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
           {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) ind_arg' input.
Proof.
  intros.
  apply smaller_case_gen with(small:=small)(hd:=hd)(ts:=ts).
  - exact Hsmall.
  - exact Hhd.
  - intros. apply (proj2_sig ((get_arg_list_ext_aux'0 p l ts Hparamslen (s_args p) Hargslen Hall Hdec2))).
    exact H0. exact H.
  - exact Hdec2.
  - exact Hall.
  - exact Hargslen.
  - exact Hparamslen.
  - exact (dec_inv_fpred_arg Hdec' (proj1' (proj2_sig x)) p_pn).
Defined.

Lemma small_remove_lemma (v: val_vars pd vt) (x: vsymbol)
  (t: domain (val (snd x))) {small d} 
  (Hsmall: forall x, In x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d):
  forall y, In y (remove vsymbol_eq_dec x small) ->
  vty_in_m m vs (snd y) /\
  adt_smaller_trans (hide_ty (substi pd vt v x t y)) d.
Proof.
  intros.
  unfold substi. simpl_set. destruct H.
  split; [apply Hsmall; auto|].
  destruct (vsymbol_eq_dec y x); subst; auto; try contradiction.
  apply Hsmall; auto.
Qed.

Lemma small_hd_lemma (v: val_vars pd vt) (x: vsymbol)
(t: domain (val (snd x))) {hd d}
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
  forall h : vsymbol,
  upd_option hd x = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty
    (substi pd vt v x t h) = d.
Proof.
  intros. unfold upd_option in H. destruct hd; try discriminate.
  destruct (vsymbol_eq_dec x p); try discriminate.
  inversion H; subst.
  unfold substi. destruct (vsymbol_eq_dec h x); subst; try contradiction.
  apply Hhd. reflexivity.
Qed.

(*This lemma proves that the Hsmall invariant is preserved
  whenever we add constr variables (after removing pat vars).
  In other words, the variables we add are actually smaller.
  This is where we use [match_val_single_smaller].
  *)
Lemma small_match_lemma { tm v ty1 p Hty dom_t small d l mvar hd}
  (Hmatch: match_val_single gamma_valid pd all_unif vt ty1 p Hty dom_t =Some l)
  (Hty1: term_has_type sigma tm ty1)
  (Htm: tm = Tvar mvar /\ (hd = Some mvar \/ In mvar small))
  (Hdomt: dom_t = dom_cast _ (f_equal (fun x => val x) 
      (eq_sym (ty_var_inv (term_has_type_cast (proj1 Htm) Hty1))))
      (var_to_dom _ vt v mvar))
  (Hsmall: forall x,
    In x small ->
    vty_in_m m vs (snd x) /\ adt_smaller_trans (hide_ty (v x)) d)
  (Hhd : forall h : vsymbol, hd = Some h -> 
    vty_in_m m vs (snd h) /\ hide_ty (v h) = d):
  forall x,
    In x (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs p))
      (remove_all vsymbol_eq_dec (pat_fv p) small)) ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d.
Proof.
  intros.
  simpl_set. destruct H.
  - unfold vsyms_in_m in H. rewrite in_filter in H.
    destruct H. split; auto.
    destruct Htm as [Htm Hmvar]. subst.
    assert (Hty1m: vty_in_m m vs ty1). {
      inversion Hty1; destruct Hmvar; subst; auto.
      apply Hhd; auto.
      apply Hsmall; auto.
    }
    (*Now we get the domain val in the list l mapped from x*)
    assert (Hinx: In x (map fst l)). {
      apply (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch).
      eapply pat_constr_vars_fv. apply H0.
    }
    rewrite in_map_iff in Hinx. destruct Hinx as [[x' y'] [Hfst Hinxy]]; subst.
    simpl in *.
    rewrite (extend_val_with_list_lookup _ _ _ _ _ y'); auto.
    2: {
      apply (match_val_single_nodup _ _ _ _ _ _ _ _ _ Hmatch).
    }
    assert (val (snd x') = projT1 y'). {
      symmetry.
      apply (match_val_single_typs _ _ _ _ _ _ _ _ _ Hmatch). auto.
    }
    destruct (sort_eq_dec (val (snd x')) (projT1 y')); try contradiction.
    apply (proj2 (match_val_single_smaller vt v _ _ Hty Hty1m _ _ Hmatch)) with(y:=y') in H0; auto.
    (*First, we do some things that will simplify the casting*)
    destruct x' as [x1' x2']; simpl in *; subst.
    destruct y' as [y1 y2]. simpl in *; subst.
    assert (e = eq_refl). { apply UIP_dec. apply sort_eq_dec. }
    subst. unfold dom_cast. simpl.
    (*replace (hide_ty y2) with (existT ) by (destruct y'; reflexivity).*)
    inversion Hty1; subst.
    revert H0.
    match goal with 
      | |- adt_smaller_trans ?y (hide_ty (dom_cast ?d ?E ?x)) -> ?P =>
        assert (E = eq_refl) by (apply UIP_dec; apply sort_eq_dec)
        end.
    rewrite H0; clear H0. unfold dom_cast; simpl.
    unfold var_to_dom. intros.
    (*Now the goals are much clearer, we consider each case*)
    (*Now consider each case*)
    destruct Hmvar.
    + subst. (*If mvar = h, have equality, then use match result to
      get smaller*)
      specialize (Hhd mvar eq_refl).
      rewrite (proj2 Hhd) in H0; auto.
    + (*In this case, mvar is in small, so follows from
        transitivity*)
      specialize (Hsmall _ i).
      apply (R_trans_trans H0). apply Hsmall.
  - (*Otherwise, not in l, so follows from assumption*)
    simpl_set. destruct H.
    (*TODO: this lemma has an extra assumption*)
    rewrite extend_val_with_list_notin'; auto.
    rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch).
    auto.
Qed.

(*First (recursive) case for small lemma when we add valuations
  from [match_val_single]*)
Lemma match_val_single_small1 { v ty1 dom_t p Hty l small d}:
  match_val_single gamma_valid pd all_unif vt ty1 p Hty dom_t = Some l ->
  (forall x, In x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
  (forall x, In x (remove_all vsymbol_eq_dec (pat_fv p) small) ->
  vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d).
Proof.
  intros. simpl_set. destruct_all.
  split; [apply H0; auto|].
  rewrite extend_val_with_list_notin'; auto; [apply H0; auto|].
  eapply match_val_single_free_var in H. rewrite <- H. auto.
Qed.

Lemma upd_option_some (hd: option vsymbol) (x: vsymbol):
  forall h,
    upd_option hd x = Some h <-> hd = Some h /\ h <> x.
Proof.
  intros. unfold upd_option. destruct hd; [|split; intros; destruct_all; discriminate].
  destruct (vsymbol_eq_dec x v); subst.
  - split; intros; try discriminate.
    destruct H. inversion H; subst; contradiction.
  - split; intros; destruct_all; inversion H; subst; auto.
Qed.

Lemma upd_option_iter_some (hd: option vsymbol) (l: list vsymbol):
  forall h,
    upd_option_iter hd l = Some h <-> hd = Some h /\ ~ In h l.
Proof.
  intros. induction l; simpl.
  - split; intros; auto. apply H.
  - rewrite upd_option_some, IHl, and_assoc.
    split; intros; destruct_all; subst; auto; split; auto.
    intro C. destruct C; subst; contradiction.
Qed. 

(*hd invariant with upd_option and upd_option_iter*)
Lemma match_val_single_upd_option
  { v ty1 dom_t p Hty l d} (hd: option vsymbol) 
  (Hmatch: match_val_single gamma_valid pd all_unif vt ty1 p Hty dom_t 
    = Some l)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
forall h : vsymbol,
  upd_option_iter hd (pat_fv p) = Some h ->
  vty_in_m m vs (snd h) /\ hide_ty (extend_val_with_list pd vt v l h) = d.
Proof.
  intros. rewrite upd_option_iter_some in H. destruct H; subst.
  split; [apply Hhd; auto|].
  rewrite extend_val_with_list_notin'; auto.
  apply Hhd; auto.
  rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch).
  auto.
Qed.

(*TODO: organize better*)


(*More inversion lemmas for decrease_fun and decrease_pred*)
Lemma dec_inv_fnot {fs' ps' f small hd}:
  decrease_pred fs' ps' small hd m vs (Fnot f) ->
  decrease_pred fs' ps' small hd m vs f.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_fbinop {fs' ps' b f1 f2 small hd}:
  decrease_pred fs' ps' small hd m vs (Fbinop b f1 f2) ->
  decrease_pred fs' ps' small hd m vs f1 /\
  decrease_pred fs' ps' small hd m vs f2.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_quant {fs' ps' q v f small hd}:
  decrease_pred fs' ps' small hd m vs (Fquant q v f) ->
  decrease_pred fs' ps' (remove vsymbol_eq_dec v small) 
    (upd_option hd v) m vs f.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_eq {fs' ps' ty t1 t2 small hd}:
  decrease_pred fs' ps' small hd m vs (Feq ty t1 t2) ->
  decrease_fun fs' ps' small hd m vs t1 /\
  decrease_fun fs' ps' small hd m vs t2.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_flet {fs' ps' t1 v f small hd}:
  decrease_pred fs' ps' small hd m vs (Flet t1 v f) ->
  decrease_fun fs' ps' small hd m vs t1 /\
  decrease_pred fs' ps' (remove vsymbol_eq_dec v small)
    (upd_option hd v) m vs f.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_fif {fs' ps' f1 f2 f3 small hd}:
  decrease_pred fs' ps' small hd m vs (Fif f1 f2 f3) ->
  decrease_pred fs' ps' small hd m vs f1 /\
  decrease_pred fs' ps' small hd m vs f2 /\
  decrease_pred fs' ps' small hd m vs f3.
Proof.
  solve_dec_inv.
Qed.

(*The return type - depends on whether this is a function
  or predicate definition*)
(*TODO: move*)
Definition funrep_ret (fa: combined_args) : Set :=
  match (projT2 fa) with
  | Left fdata => 
    domain (funsym_sigma_ret (fn_sym (proj1_sig fdata)) 
    (projT1 (projT2 (projT1 fa))))
  | Right _ => bool
  end.

(*Finally, start building the real function. We separate into
  pieces to avoid too many layers of nested recursion and to
  make things easier for Coq's termination checker*)

Section TermRepAux.

Variable (input: packed_args2)
(rec:(forall
  y : packed_args2,
  (R_projT1 _ (R_projT1 _ arg_list_smaller)) y input ->
  funrep_ret (projT1 y))).

Notation fa := (projT1 (projT1 input)).
Notation Hsrts := (snd (projT2 input)).
Notation f1 := (proj1_sig (projT1 fa)).
Notation a1 := (projT2 (projT2 fa)).
Notation srts := (projT1 (projT2 fa)).
Notation srts_len := (proj1' Hsrts).
Notation vt_eq_srts := (proj2' Hsrts).
(*d is the ADT instance we must be smaller than to recurse*)
Notation d := (hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1))
   (hnth (sn_idx f1) a1 s_int (dom_int pd)))).
(*y is the vsymbol we must be syntactically decreasing on*)
Notation y := (nth (sn_idx f1) (sn_args f1) vs_d).

(*The body of [term_rep_aux]*)
Definition term_rep_aux_body 
(term_rep_aux: forall (v: val_vars pd vt) 
  (t: term) (ty: vty) (small: list vsymbol) (hd: option vsymbol)
  (Hty: term_has_type sigma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  (Hsmall: forall x, In x small ->
    vty_in_m m vs (snd x) /\
    (*TODO: type restriction here?*)
    adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d),
  {d: domain (val ty) | forall x (Heqx: t = Tvar x),
    d = dom_cast _ (f_equal (fun x => val x) 
      (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
      (var_to_dom _ vt v x)})
(formula_rep_aux: forall (v: val_vars pd vt) 
(f: formula) (small: list vsymbol) (hd: option vsymbol)
(Hval: valid_formula sigma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  (*TODO: type restriction here?*)
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d),
bool)
(v: val_vars pd vt)
(t: term)
(ty: vty)
(small: list vsymbol)
(hd: option vsymbol)
(Hty: term_has_type sigma t ty)
(Hdec: decrease_fun fs ps small hd m vs t)
(Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  (*TODO: type restriction here?*)
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
{d: domain (val ty) | forall x (Heqx: t = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
    (var_to_dom _ vt v x)} :=
  match t as tm return forall (Hty': term_has_type sigma tm ty),
  decrease_fun fs ps small hd m vs tm -> 
  {d: domain (val ty) | forall x (Heqx: tm = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty'))))
    (var_to_dom _ vt v x)} with
(*Some cases are identical to [term_rep]*)
| Tconst (ConstInt z) => fun Hty' _ =>
  let Htyeq : vty_int = ty :=
    eq_sym (ty_constint_inv Hty') in

  exist _ (cast_dom_vty pd Htyeq z)
    (fun x Heqx => False_rect _ (const_not_var Heqx)) 
| Tconst (ConstReal r) => fun Hty' _ =>
  let Htyeq : vty_real = ty :=
    eq_sym (ty_constreal_inv Hty') in

  exist _ (cast_dom_vty pd Htyeq r)
    (fun x Heqx => False_rect _ (const_not_var Heqx)) 
| Tvar x => fun Hty' _ =>
  let Heq : ty = snd x := ty_var_inv Hty' in
  (exist _ 
    (dom_cast _ (f_equal (fun x => val x) (eq_sym Heq)) 
    (var_to_dom _ vt v x)) (var_case ty x v Hty' Heq))
(*The function case is one of the 2 interesting cases*)
| Tfun f l ts => fun Hty' Hdec' =>

  (*Some proof we need; we give types for clarity*)
  let Htyeq : ty_subst (s_params f) l (f_ret f) = ty :=
    eq_sym (ty_fun_ind_ret Hty') in
  (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
    sigma sends (s_params f)_i -> l_i and 
    sigma' sends (s_params f) _i -> v(l_i)*)
  let Heqret : v_subst vt (ty_subst (s_params f) l (f_ret f)) =
    ty_subst_s (s_params f) (map (v_subst vt) l) (f_ret f) :=
      funsym_subst_eq (s_params f) l vt (f_ret f) (s_params_Nodup f)
      (tfun_params_length Hty') in

  (*This is a horrible function, hopefully eventually
  I can take it out but I doubt it*)
  (*lets generalize*)
  let fix get_arg_list_ext_aux' (s: fpsym)
    {vs': list vty} {ts: list term}
    (Hparamslen: length vs' = length (s_params s))
    {struct ts}:
    forall args
    (Hargslen: length ts = length args)
    (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
      (combine ts (map (ty_subst (s_params s) vs') args)))
    (Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts) vs_small,
      nth j ts tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      (*Avoids the need to relate hnth to term_rep_aux (nth) by
      directly giving the result we need*)
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} :=
  match ts as ts'
    return forall args,
    length ts' = length args ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine ts' (map (ty_subst (s_params s) vs') args)) ->
    Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts') vs_small,
      nth j ts' tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun args Hlen _ _ => 
        match args as a' return length nil = length a' -> 
        {a: arg_list domain (ty_subst_list_s (s_params s) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length nil) vs_small,
          nth j nil tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with 
        (*Both get contradictions here*)
        | nil => fun Hlena => exist _ (@HL_nil _ _) 
          (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
        | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
        end Hlen
    | thd :: ttl => 
      fun args Hlen Htys Hdecs => 
      match args as a' return length (thd :: ttl) = length a' ->
        Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
          (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
        {a: arg_list domain (ty_subst_list_s (s_params s) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
          nth j (thd :: ttl) tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with
        | nil => fun Hlen =>
          False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
        | ahd :: atl => fun Heq Htys =>
          exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
          (funsym_subst_eq (s_params s) vs' vt ahd
          (s_params_Nodup _) (eq_sym Hparamslen)) 
            (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
            (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
          (*build the function for second part*)
          (fun j => 
            match j as j' return j' < length (thd :: ttl) ->
              forall (vs_small: vsymbol),
              nth j' (thd :: ttl) tm_d = Tvar vs_small ->
              exists
                (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
              (Heq0 : val ty' =
                      nth j'
                        (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') (ahd :: atl))
                        s_int),
                hnth j'
                  (HL_cons domain (ty_subst_s (s_params s) (map (v_subst vt) vs') ahd)
                    (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') atl)
                    (dom_cast (dom_aux pd)
                        (funsym_subst_eq (s_params s) vs' vt ahd 
                          (s_params_Nodup s) (eq_sym Hparamslen))
                        (proj1_sig
                          (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                              (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                              (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                    (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
                        (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                        (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
                  (dom_int pd) =
                dom_cast (dom_aux pd) Heq0
                  (dom_cast (dom_aux pd)
                    (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                    (var_to_dom pd vt v vs_small))
            with
            | 0 => 
              (*Case when j = 0*)
              fun _ vs_small Hthd => 
                arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
                  Hdecs ahd atl Heq Htys vs_small Hthd
            | S j' => 
              (fun Hj vs_small Hnth =>
              (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
              (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
              ) )
            end)
        end Hlen Htys
    end in

  let s1 : fpsym := f_sym f in

  let Hinv := fun_ty_inv Hty' in 
  let Hall:= proj1' (proj2' (proj2' Hinv)) in
  let Hargslen:= proj1' Hinv in
  let Hparamslen:= proj1' (proj2' Hinv) in
  let Hdec2 := dec_inv_tfun_rec Hdec' in

  (*Get argument to apply recursively*)
  let args : arg_list domain (sym_sigma_args s1
    (map (fun x => val x) l))  :=
    proj1_sig (get_arg_list_ext_aux' f Hparamslen (s_args f) Hargslen
    Hall Hdec2) in

  (*If f is in fs, then we need to make a recursive call*)
  match (find_fn f fs) with
  | Left x =>
    let fn_def : fn := proj1_sig x in
    let fn_in: In fn_def fs := proj1' (proj2_sig x) in
    let f_fn : f = fn_sym fn_def := proj2' (proj2_sig x) in

    let sn_def : sn := fn_sn fn_def in
    let sn_in : In sn_def sns :=
      in_fs_sns fn_in in

    
    let s2 : fpsym := sn_sym sn_def in

    let s_eq: s1 = s2 := eq_trans (f_equal f_sym f_fn)
      (fn_wf fn_def) in

    let l_eq : l = map vty_var (s_params f) :=
      proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in

    (*With l_eq, we can begin casting*)
    let srts_eq : map (fun x => val x) (map vty_var (s_params s1)) =
      srts :=
      eq_trans (f_equal (fun (x: fpsym) => map (fun x => val x) (map vty_var (s_params x)))
        s_eq)
        (map_vals_srts' srts fn_def srts_len vt_eq_srts sn_in) in

    let l_eq2: srts = map (fun x => val x) l :=
      eq_trans (eq_sym srts_eq) 
        (f_equal (fun x => map (fun x => val x) x) (eq_sym l_eq)) in

    let args': arg_list domain (sym_sigma_args s1 srts) 
      :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args f x)) 
        (eq_sym l_eq2)) args in
    let args'' : arg_list domain (sym_sigma_args (sn_sym sn_def) srts) :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args x srts))
        s_eq) args' in

    let ind_arg : packed_args
    
    := existT _ (exist _ (sn_def) sn_in) 
      (existT _ srts args'') in
    let ind_comb: combined_args :=
      combine_args_fun ind_arg fn_def fn_in eq_refl in
    let ind_arg' : packed_args2 :=
      pack_args ind_comb v (conj srts_len vt_eq_srts) in

    (*TODO: it is v, right? Because rec changes val*)
    (*Here is our recursive call. We have to cast the result*)
    let ret_val:  domain (funsym_sigma_ret (fn_sym fn_def) srts) :=
    (rec ind_arg' 
    (*Proof of smaller*)
    (func_smaller_case v input small hd ty f l ts Hty' Hdec' x Hsmall Hhd
    term_rep_aux))
    in

    (*Now we have to cast in the reverse direction*)
    (*First, get in terms of f*)
    let ret1 : domain (funsym_sigma_ret f srts) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym f_fn)) ret_val in

    let ret2 : 
      domain (ty_subst_s (s_params f) 
        (map (v_subst vt) l) (f_ret f)) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => ty_subst_s (s_params f) x (f_ret f))
        l_eq2) ret1 in

    exist _ (cast_dom_vty pd Htyeq 
      (dom_cast (dom_aux pd) (eq_sym Heqret) ret2)) (
        fun x Heqx => False_rect _ (fun_not_var Heqx))
    

  | Right Hnotin =>
    (*Otherwise, use funs*)

  (* The final result is to apply [funs] to the [arg_list] created recursively
    from the argument domain values. We need two casts to make the dependent
    types work out*)

  (exist _ (cast_dom_vty pd Htyeq (
    dom_cast (dom_aux pd)
      (eq_sym Heqret)
        ((funs gamma_valid pd pf f 
          (map (fun x => val x) l)) args))) 
          (fun x Heqx => False_rect _ (fun_not_var Heqx)))
  end

(*Tlet is pretty simple. We need a lemma to show that we mantain
  the Hsmall invariant (holds because substi replaces the variable
  that we substitute in)
  We also have an awkward exist (proj1_sig _) H, because the inductive
  proof is not quite right, though both are trivial*)
| Tlet tm1 v1 tm2 => fun Hty' Hdec' =>
    let Ht1 : term_has_type sigma tm1 (snd v1) :=
      proj1 (ty_let_inv Hty') in
    let Ht2 : term_has_type sigma tm2 ty :=
      proj2 (ty_let_inv Hty') in 
    let Hdec1 : decrease_fun fs ps small hd m vs tm1 := 
      proj1 (dec_inv_tlet Hdec') in
    let Hdec2 : decrease_fun fs ps (remove vsymbol_eq_dec v1 small) (upd_option hd v1) m vs tm2 := 
      proj2 (dec_inv_tlet Hdec') in

    (*This is [[tm2]]_(v->[[tm1]]), but we need [small_remove_lemma]
    and [small_hd_lemma] to prove that the invariants are preserved*)
    exist _ (proj1_sig (term_rep_aux (substi pd vt v v1 
      (proj1_sig (term_rep_aux v tm1 (snd v1) small hd Ht1 Hdec1 Hsmall Hhd))) 
    tm2 ty (remove vsymbol_eq_dec v1 small) (upd_option hd v1) Ht2 Hdec2 
    (small_remove_lemma v v1 _ Hsmall)
    (small_hd_lemma v v1 _ Hhd))) 
    (fun x Heqx => False_rect _ (tlet_not_var Heqx))

(*TIf is simple recursion*)
| Tif f1 t2 t3 => fun Hty' Hdec' =>
  let Ht1 : term_has_type sigma t2 ty :=
    (proj1 (ty_if_inv Hty')) in
  let Ht2 : term_has_type sigma t3 ty :=
    (proj1 (proj2 (ty_if_inv Hty'))) in
  let Hf: valid_formula sigma f1 :=
    (proj2 (proj2 (ty_if_inv Hty'))) in
  let Hdec1 := proj1 (dec_inv_tif Hdec') in
  let Hdec2 := proj1 (proj2 (dec_inv_tif Hdec')) in
  let Hdec3 := proj2 (proj2 (dec_inv_tif Hdec')) in

  (*Need to unfold the dependent type and add a new one*)
  if (formula_rep_aux v f1 small hd Hf Hdec1 Hsmall Hhd)
  then 
  exist _ (proj1_sig 
  (term_rep_aux v t2 ty small hd Ht1 Hdec2 Hsmall Hhd))
  (fun x Heqx => False_rect _ (tif_not_var Heqx))
  else 
  exist _ (proj1_sig 
  (term_rep_aux v t3 ty small hd Ht2 Hdec3 Hsmall Hhd))
  (fun x Heqx => False_rect _ (tif_not_var Heqx))

(*Tmatch is the other interesting case, though most of
  the work was done in the previous lemmas*)
| Tmatch t ty1 pats => fun Hty' Hdec' =>
    let Ht1 : term_has_type sigma t ty1 :=
      proj1 (ty_match_inv Hty') in
    let Hall : Forall (fun x => term_has_type sigma (snd x) ty) pats :=
      proj2 (proj2 (ty_match_inv Hty')) in
    let Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats :=
      proj1 (proj2 (ty_match_inv Hty')) in

    let Hdec1 : decrease_fun fs ps small hd m vs t := 
      dec_inv_tmatch_fst Hdec' in

    let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
    let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in

    (*We have 2 different cases; we need to have 2
    different inner recursive functions, 1 for each case*)
    match tmatch_case t hd small with
    | Left z =>
      let mvar : vsymbol := proj1_sig z in
      let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
      let mvar_small : hd = Some mvar \/ In mvar small :=
        proj2' (proj2_sig z) in

      let Hdec2 : Forall (fun x => decrease_fun fs ps
        (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_tmatch_var (proj2_sig z) Hdec' in
       

      (*Can't make [match_rep] a separate function or else Coq
      cannot tell structurally decreasing. So we inline it*)
      (*Unfortunately, we need a different version for each
        pattern match*)
      let fix match_rep (pats: list (pattern * term)) 
        (Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
        (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
        (Hdec: Forall (fun x => decrease_fun fs ps
        (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
        domain (val ty) :=
      match pats as l' return 
        Forall (fun x => term_has_type sigma (snd x) ty) l' ->
        Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
        Forall (fun x => decrease_fun fs ps
        (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
        domain (val ty) with
      | (p , dat) :: ptl => fun Hall Hpats Hdec =>
        (*We need info about [match_val_single] to know how the
          valuation changes*)
        match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
          return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
          domain (val ty) with
        | Some l => fun Hmatch => 
          proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
          _ _ (Forall_inv Hall) (Forall_inv Hdec) 
          (small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1 (proj2_sig z))) Hsmall Hhd)
          (match_val_single_upd_option hd Hmatch Hhd))
        | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
          (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
        end eq_refl
      | _ => (*TODO: show we cannot reach this*) fun _ _ _ =>
        match domain_ne pd (val ty) with
        | DE x => x
        end
      end Hall Hpats Hdec in

       (*For some reason, Coq needs the typing annotation here*)
       exist (fun d => forall x Heqx, d = 
       dom_cast (dom_aux pd)
       (f_equal (fun x0 : vty => val x0)
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty')))) 
       (var_to_dom pd vt v x)) (match_rep pats Hall Hpats Hdec2)
         (fun x Heqx => False_rect _ (tmatch_not_var Heqx))

    | Right Hnotvar =>
      (*Easier, recursive case*)
      let Hdec2 : 
        Forall (fun x => decrease_fun fs ps 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_tmatch_notvar Hnotvar Hdec' in


      (*Can't make [match_rep] a separate function or else Coq
      cannot tell structurally decreasing. So we inline it*)
      let fix match_rep (pats: list (pattern * term)) 
        (Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
        (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
        (Hdec: Forall (fun x => decrease_fun fs ps 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
        domain (val ty) :=
      match pats as l' return 
        Forall (fun x => term_has_type sigma (snd x) ty) l' ->
        Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
        Forall (fun x => decrease_fun fs ps 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
        domain (val ty) with
      | (p , dat) :: ptl => fun Hall Hpats Hdec =>
        (*We need info about [match_val_single] to know how the
          valuation changes*)
        match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
          return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
          domain (val ty) with
        | Some l => fun Hmatch => 
          proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
          _ _ (Forall_inv Hall) (Forall_inv Hdec) 
          (match_val_single_small1 Hmatch Hsmall)
          (match_val_single_upd_option hd Hmatch Hhd))
        | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
          (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
        end eq_refl
      | _ => (*TODO: show we cannot reach this*) fun _ _ _ =>
        match domain_ne pd (val ty) with
        | DE x => x
        end
      end Hall Hpats Hdec in
      (*For some reason, Coq needs the typing annotation here*)
      exist (fun d => forall x Heqx, d = 
      dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0)
         (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty')))) 
      (var_to_dom pd vt v x)) (match_rep pats Hall Hpats Hdec2)
        (fun x Heqx => False_rect _ (tmatch_not_var Heqx))
    end

| Teps f x => fun Hty' Hdec' =>
  let Hval : valid_formula sigma f := proj1 (ty_eps_inv Hty') in
  let Heq : ty = snd x := proj2 (ty_eps_inv Hty') in
  let Hdec1 := dec_inv_teps Hdec' in
  (*We need to show that domain (val v ty) is inhabited*)
  let def : domain (val ty) :=
  match (domain_ne pd (val ty)) with
  | DE x => x 
  end in

  exist _ 
  (ClassicalEpsilon.epsilon (inhabits def) (fun (y: domain (val ty)) =>
    is_true (formula_rep_aux 
      (substi pd vt v x (dom_cast _ (f_equal (fun x => val x) Heq) y)) 
      f (remove vsymbol_eq_dec x small) (upd_option hd x) Hval Hdec1
      (small_remove_lemma v x _ Hsmall)
      (small_hd_lemma v x _ Hhd))))
  (fun x Heqx => False_rect _ (teps_not_var Heqx))

end Hty Hdec.

Definition formula_rep_aux_body 
(term_rep_aux: forall (v: val_vars pd vt) 
  (t: term) (ty: vty) (small: list vsymbol) (hd: option vsymbol)
  (Hty: term_has_type sigma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  (Hsmall: forall x, In x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d),
  {d: domain (val ty) | forall x (Heqx: t = Tvar x),
    d = dom_cast _ (f_equal (fun x => val x) 
      (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
      (var_to_dom _ vt v x)})
(formula_rep_aux: forall (v: val_vars pd vt) 
(f: formula) (small: list vsymbol) (hd: option vsymbol)
(Hval: valid_formula sigma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d),
bool)
(v: val_vars pd vt)
(f: formula)
(small: list vsymbol)
(hd: option vsymbol)
(Hval: valid_formula sigma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
bool :=
  match f as fmla return forall (Hval': valid_formula sigma fmla),
  decrease_pred fs ps small hd m vs fmla -> 
  bool with
| Ftrue => fun _ _ => true
| Ffalse => fun _ _ => false
| Fnot f' => fun Hval' Hdec' =>
  let Hf' : valid_formula sigma f' :=
    valid_not_inj Hval' in

  negb (formula_rep_aux v f' small hd Hf' 
    (dec_inv_fnot Hdec') Hsmall Hhd)
| Fbinop b f1 f2 => fun Hval' Hdec' =>
  let Hf1 : valid_formula sigma f1 :=
    proj1 (valid_binop_inj Hval') in
  let Hf2 : valid_formula sigma f2 :=
    proj2 (valid_binop_inj Hval') in
  let Hdec1 := proj1 (dec_inv_fbinop Hdec') in
  let Hdec2 := proj2 (dec_inv_fbinop Hdec') in

  bool_of_binop b 
    (formula_rep_aux v f1 small hd Hf1 Hdec1 Hsmall Hhd) 
    (formula_rep_aux v f2 small hd Hf2 Hdec2 Hsmall Hhd)
| Flet t x f' => fun Hval' Hdec' =>
  let Ht: term_has_type sigma t (snd x) :=
    (proj1 (valid_let_inj Hval')) in
  let Hf': valid_formula sigma f' :=
    (proj2 (valid_let_inj Hval')) in
  let Hdec1 := proj1 (dec_inv_flet Hdec') in
  let Hdec2 := proj2 (dec_inv_flet Hdec') in

  (*This is [[f]]_(v->[[t]]), but we need [small_remove_lemma]
    and [small_hd_lemma] to prove that the invariants are preserved*)
  formula_rep_aux (substi pd vt v x 
    (proj1_sig (term_rep_aux v t (snd x) small hd Ht Hdec1 Hsmall Hhd)))
  f' (remove vsymbol_eq_dec x small) (upd_option hd x) Hf' Hdec2
  (small_remove_lemma v x _ Hsmall)
  (small_hd_lemma v x _ Hhd)
| Fquant Tforall x f' => fun Hval' Hdec' =>
  let Hf' : valid_formula sigma f' :=
    valid_quant_inj Hval' in
  let Hdec1 := dec_inv_quant Hdec' in
  (*NOTE: HERE is where we need the classical axiom assumptions*)
  all_dec (forall d, formula_rep_aux (substi pd vt v x d) f'
    (remove vsymbol_eq_dec x small) (upd_option hd x) Hf' Hdec1
    (small_remove_lemma v x _ Hsmall)
    (small_hd_lemma v x _ Hhd))

| Fquant Texists x f' => fun Hval' Hdec' =>
  let Hf' : valid_formula sigma f' :=
    valid_quant_inj Hval' in
  let Hdec1 := dec_inv_quant Hdec' in
  (*NOTE: HERE is where we need the classical axiom assumptions*)
  all_dec (exists d, formula_rep_aux (substi pd vt v x d) f' 
    (remove vsymbol_eq_dec x small) (upd_option hd x) Hf' Hdec1
    (small_remove_lemma v x _ Hsmall)
    (small_hd_lemma v x _ Hhd))

| Feq ty t1 t2 => fun Hval' Hdec' =>
  let Ht1 : term_has_type sigma t1 ty := 
    proj1 (valid_eq_inj Hval') in
  let Ht2 : term_has_type sigma t2 ty :=
    proj2 (valid_eq_inj Hval') in
  let Hdec1 := proj1 (dec_inv_eq Hdec') in
  let Hdec2 := proj2 (dec_inv_eq Hdec') in
  (*TODO: require decidable equality for all domains?*)
  all_dec (
    proj1_sig (term_rep_aux v t1 ty small hd Ht1 Hdec1 Hsmall Hhd) = 
    proj1_sig (term_rep_aux v t2 ty small hd Ht2 Hdec2 Hsmall Hhd))

(*Fmatch is similar to Tmatch*)
| Fmatch t ty1 pats => fun Hval' Hdec' =>
  let Ht1 : term_has_type sigma t ty1 :=
    proj1 (valid_match_inv Hval') in
  let Hall : Forall (fun x => valid_formula sigma (snd x)) pats :=
    proj2 (proj2 (valid_match_inv Hval')) in
  let Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats :=
    proj1 (proj2 (valid_match_inv Hval')) in

  let Hdec1 : decrease_fun fs ps small hd m vs t := 
    dec_inv_fmatch_fst Hdec' in

  (*let Hval : valid_type sigma ty1 :=
    has_type_valid gamma_valid _ _ Ht1 in*)

  let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
  let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in

  (*hmm, we have 2 different cases: we might need to have 2
  different inner recursive functions, 1 for each case*)
  match tmatch_case t hd small with
  | Left z =>
    let mvar : vsymbol := proj1_sig z in
    let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
    let mvar_small : hd = Some mvar \/ In mvar small :=
      proj2' (proj2_sig z) in

    let Hdec2 : Forall (fun x => decrease_pred fs ps
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
      dec_inv_fmatch_var (proj2_sig z) Hdec' in
      

    (*Can't make [match_rep] a separate function or else Coq
    cannot tell structurally decreasing. So we inline it*)
    (*Unfortunately, we need a different version for each
      pattern match*)
    let fix match_rep (pats: list (pattern * formula)) 
      (Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
      (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
      (Hdec: Forall (fun x => decrease_pred fs ps
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
      bool :=
    match pats as l' return 
      Forall (fun x => valid_formula sigma (snd x)) l' ->
      Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
      Forall (fun x => decrease_pred fs ps
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
      bool with
    | (p , dat) :: ptl => fun Hall Hpats Hdec =>
      (*We need info about [match_val_single] to know how the
        valuation changes*)
      match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
        return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
        bool with
      | Some l => fun Hmatch => 
        formula_rep_aux (extend_val_with_list pd vt v l) dat
        _ _ (Forall_inv Hall) (Forall_inv Hdec) 
        (small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1 (proj2_sig z))) Hsmall Hhd)
        (match_val_single_upd_option hd Hmatch Hhd)
      | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
        (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
      end eq_refl
    | _ => (*TODO: show we cannot reach this*) fun _ _ _ =>
      false
    end Hall Hpats Hdec in

    match_rep pats Hall Hpats Hdec2

  | Right Hnotvar =>
    (*Easier, recursive case*)
    let Hdec2 : 
      Forall (fun x => decrease_pred fs ps 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
      dec_inv_fmatch_notvar Hnotvar Hdec' in


    (*Can't make [match_rep] a separate function or else Coq
    cannot tell structurally decreasing. So we inline it*)
    let fix match_rep (pats: list (pattern * formula)) 
      (Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
      (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
      (Hdec: Forall (fun x => decrease_pred fs ps 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
      bool :=
    match pats as l' return 
      Forall (fun x => valid_formula sigma (snd x)) l' ->
      Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
      Forall (fun x => decrease_pred fs ps 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
      bool with
    | (p , dat) :: ptl => fun Hall Hpats Hdec =>
      (*We need info about [match_val_single] to know how the
        valuation changes*)
      match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
        return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
        bool with
      | Some l => fun Hmatch => 
        formula_rep_aux (extend_val_with_list pd vt v l) dat
        _ _ (Forall_inv Hall) (Forall_inv Hdec) 
        (match_val_single_small1 Hmatch Hsmall)
        (match_val_single_upd_option hd Hmatch Hhd)
      | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
        (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
      end eq_refl
    | _ => (*TODO: show we cannot reach this*) fun _ _ _ =>
      false
    end Hall Hpats Hdec in
    (*For some reason, Coq needs the typing annotation here*)
     (match_rep pats Hall Hpats Hdec2)
  end

(*Fpred - similar to Tfun*)
| Fpred p l ts => fun Hval' Hdec' =>

  (*Some proof we need; we give types for clarity*)
  (*let Htyeq : ty_subst (s_params f) l (f_ret f) = ty :=
    eq_sym (ty_fun_ind_ret Hty') in*)
  (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
    sigma sends (s_params f)_i -> l_i and 
    sigma' sends (s_params f) _i -> v(l_i)*)
  (*let Heqret : v_subst vt (ty_subst (s_params f) l (f_ret f)) =
    ty_subst_s (s_params f) (map (v_subst vt) l) (f_ret f) :=
      funsym_subst_eq (s_params f) l vt (f_ret f) (s_params_Nodup f)
      (tfun_params_length Hty') in*)

  (*TODO: generalize with sym*)

  (*This is a horrible function, hopefully eventually
  I can take it out but I doubt it*)
  let fix get_arg_list_ext_aux' (s: fpsym)
    {vs': list vty} {ts: list term}
    (Hparamslen: length vs' = length (s_params s))
    {struct ts}:
    forall args
    (Hargslen: length ts = length args)
    (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
      (combine ts (map (ty_subst (s_params s) vs') args)))
    (Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts) vs_small,
      nth j ts tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      (*Avoids the need to relate hnth to term_rep_aux (nth) by
      directly giving the result we need*)
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} :=
  match ts as ts'
    return forall args,
    length ts' = length args ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine ts' (map (ty_subst (s_params s) vs') args)) ->
    Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts') vs_small,
      nth j ts' tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun args Hlen _ _ => 
        match args as a' return length nil = length a' -> 
        {a: arg_list domain (ty_subst_list_s (s_params s) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length nil) vs_small,
          nth j nil tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with 
        (*Both get contradictions here*)
        | nil => fun Hlena => exist _ (@HL_nil _ _) 
          (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
        | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
        end Hlen
    | thd :: ttl => 
      fun args Hlen Htys Hdecs => 
      match args as a' return length (thd :: ttl) = length a' ->
        Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
          (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
        {a: arg_list domain (ty_subst_list_s (s_params s) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
          nth j (thd :: ttl) tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with
        | nil => fun Hlen =>
          False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
        | ahd :: atl => fun Heq Htys =>
          exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
          (funsym_subst_eq (s_params s) vs' vt ahd
          (s_params_Nodup _) (eq_sym Hparamslen)) 
            (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
            (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
          (*build the function for second part*)
          (fun j => 
            match j as j' return j' < length (thd :: ttl) ->
              forall (vs_small: vsymbol),
              nth j' (thd :: ttl) tm_d = Tvar vs_small ->
              exists
                (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
              (Heq0 : val ty' =
                      nth j'
                        (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') (ahd :: atl))
                        s_int),
                hnth j'
                  (HL_cons domain (ty_subst_s (s_params s) (map (v_subst vt) vs') ahd)
                    (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') atl)
                    (dom_cast (dom_aux pd)
                        (funsym_subst_eq (s_params s) vs' vt ahd 
                          (s_params_Nodup s) (eq_sym Hparamslen))
                        (proj1_sig
                          (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                              (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                              (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                    (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
                        (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                        (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
                  (dom_int pd) =
                dom_cast (dom_aux pd) Heq0
                  (dom_cast (dom_aux pd)
                    (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                    (var_to_dom pd vt v vs_small))
            with
            | 0 => 
              (*Case when j = 0*)
              fun _ vs_small Hthd => 
                arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
                  Hdecs ahd atl Heq Htys vs_small Hthd
            | S j' => 
              (fun Hj vs_small Hnth =>
              (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
              (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
              ) )
            end)
        end Hlen Htys
    end in

  let s1 : fpsym := p_sym p in

  let Hinv := pred_val_inv Hval' in 
  let Hall:= proj2' (proj2' Hinv) in
  let Hargslen:= proj1' Hinv in
  let Hparamslen:= proj1' (proj2' Hinv) in
  let Hdec2 := dec_inv_fpred_rec Hdec' in

  (*Get argument to apply recursively*)
  let args : arg_list domain (sym_sigma_args s1
    (map (fun x => val x) l))  :=
    proj1_sig (get_arg_list_ext_aux' p Hparamslen (s_args p) Hargslen
    Hall Hdec2) in

  (*If p is in ps, then we need to make a recursive call*)
  match (find_pn p ps) with
  | Left x =>
    let pn_def : pn := proj1_sig x in
    let pn_in: In pn_def ps := proj1' (proj2_sig x) in
    let p_fn : p = pn_sym pn_def := proj2' (proj2_sig x) in

    let sn_def : sn := pn_sn pn_def in
    let sn_in : In sn_def sns :=
      in_ps_sns pn_in in

    
    let s2 : fpsym := sn_sym sn_def in

    let s_eq: s1 = s2 := eq_trans (f_equal p_sym p_fn)
      (pn_wf pn_def) in

    let l_eq : l = map vty_var (s_params p) :=
      proj1' (dec_inv_fpred_in Hdec' pn_in p_fn) in

    (*With l_eq, we can begin casting*)
    let srts_eq : map (fun x => val x) (map vty_var (s_params s1)) =
      srts :=
      eq_trans (f_equal (fun (x: fpsym) => map (fun x => val x) (map vty_var (s_params x)))
        s_eq)
        (map_vals_srts' srts pn_def srts_len vt_eq_srts sn_in) in

    let l_eq2: srts = map (fun x => val x) l :=
      eq_trans (eq_sym srts_eq) 
        (f_equal (fun x => map (fun x => val x) x) (eq_sym l_eq)) in

    let args': arg_list domain (sym_sigma_args s1 srts) 
      :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args p x)) 
        (eq_sym l_eq2)) args in
    let args'' : arg_list domain (sym_sigma_args (sn_sym sn_def) srts) :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args x srts))
        s_eq) args' in

    let ind_arg : packed_args
    
    := existT _ (exist _ (sn_def) sn_in) 
      (existT _ srts args'') in
    let ind_comb: combined_args :=
      combine_args_pred ind_arg pn_def pn_in eq_refl in
    let ind_arg' : packed_args2 :=
      pack_args ind_comb v (conj srts_len vt_eq_srts) in

    (*TODO: it is v, right? Because rec changes val*)
    (*Here is our recursive call. We have to cast the result*)
    let ret_val:  bool 
    (*domain (funsym_sigma_ret (fn_sym fn_def) srts)*) :=
    (rec ind_arg' 
    (*Proof of smaller*)
    (pred_smaller_case v input small hd p l ts Hval' Hdec' x Hsmall Hhd
    term_rep_aux))
    in

    ret_val

    (*Now we have to cast in the reverse direction*)
    (*First, get in terms of f*)
    (*let ret1 : domain (funsym_sigma_ret f srts) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym f_fn)) ret_val in

    let ret2 : 
      domain (ty_subst_s (s_params f) 
        (map (v_subst vt) l) (f_ret f)) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => ty_subst_s (s_params f) x (f_ret f))
        l_eq2) ret1 in

    exist _ (cast_dom_vty pd Htyeq 
      (dom_cast (dom_aux pd) (eq_sym Heqret) ret2)) (
        fun x Heqx => False_rect _ (fun_not_var Heqx))*)
    

  | Right Hnotin =>
    (*Otherwise, use preds*)

  (* The final result is to apply [preds] to the [arg_list] created recursively
    from the argument domain values.
    Don't need casting, unlike function case. *)

        ((preds gamma_valid pd pf p 
          (map (fun x => val x) l)) args)
  end

| _ => fun _ _ => false
end Hval Hdec.

(*We give the Fixpoint. Coq does not accept this
  without the horrible inlined function and proofs above*)
Fixpoint term_rep_aux
(v: val_vars pd vt)
(t: term)
(ty: vty)
(small: list vsymbol)
(hd: option vsymbol)
(Hty: term_has_type sigma t ty)
(Hdec: decrease_fun fs ps small hd m vs t)
(Hsmall: forall x, In x small ->
vty_in_m m vs (snd x) /\
 (*TODO: type restriction here?*)
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
vty_in_m m vs (snd h) /\
hide_ty (v h) = d)
  {struct t}:
{d: domain (val ty) | forall x (Heqx: t = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
    (var_to_dom _ vt v x)}  :=
term_rep_aux_body term_rep_aux formula_rep_aux v t ty small hd Hty Hdec Hsmall Hhd 
with formula_rep_aux 
(v: val_vars pd vt)
(f: formula)
(small: list vsymbol)
(hd: option vsymbol)
(Hval: valid_formula sigma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, In x small ->
vty_in_m m vs (snd x) /\
 (*TODO: type restriction here?*)
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
vty_in_m m vs (snd h) /\
hide_ty (v h) = d)
  {struct f}:
  bool :=
formula_rep_aux_body term_rep_aux formula_rep_aux v f small hd Hval Hdec Hsmall Hhd.

End TermRepAux.


(*Need to show that Hhd is satisfied for y*)
Lemma y_eq_d (input: packed_args2):
let fa := projT1 (projT1 input) in
let v := fst (projT2 input) in
let Hsrts := snd (projT2 input) in
let f1 := proj1_sig (projT1 fa) in
let a1 := projT2 (projT2 fa) in
let srts := projT1 (projT2 fa) in
let srts_len := proj1' Hsrts in
let vt_eq_srts := proj2' Hsrts in
(*d is the ADT instance we must be smaller than to recurse*)
let d :=  (dom_cast _ 
(arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1)) 
(hnth (sn_idx f1) a1 s_int (dom_int pd))) in
(*y is the vsymbol we must be syntactically decreasing on*)
let y := nth (sn_idx f1) (sn_args f1) vs_d in
forall (h : vsymbol),
Some y = Some h ->
vty_in_m m vs (snd h) /\
hide_ty (val_with_args v (sn_args f1) a1 h)= 
hide_ty d.
Proof.
  intros.
  inversion H; subst.
  assert (Hin: In f1 sns). {
    destruct fa. simpl in *. destruct x. auto.
  }
  split.
  - apply recurse_on_adt. auto. 
  - subst y.
    rewrite val_with_args_in with 
    (Heq:=arg_list_args_eq Hin srts_len vt_eq_srts (sn_idx f1) (sn_idx_bound' f1)); auto.
    + subst d.
      apply hide_ty_dom_cast.
    + apply sn_args_Nodup. 
    + unfold sym_sigma_args, ty_subst_list_s. 
      rewrite map_length, <- (args_agree _ Hin), map_length; auto.
    + apply sn_idx_bound'.
Qed.
(*The body of the outer function - calls [term_rep_aux]
  with appropriate arguments*)

Lemma fn_sym_eq (f: fn):
  f_sym (fn_sym f) = sn_sym f.
Proof.
  destruct f; auto.
Qed.

(*We define the full function body manually. We use the 
  list of "let"s rather than a deeper pattern match because
  the resulting proof term is much smaller
  (this is the same reason we give a manual, not tactic, definition) *)
Definition funcs_rep_aux_body (input: packed_args2)
(rec:(forall
  y : packed_args2,
  (R_projT1 _ (R_projT1 _ arg_list_smaller)) y input ->
  funrep_ret (projT1 y))):
  funrep_ret (projT1 input) :=

  match input as i return
  (forall
  y : packed_args2,
  (R_projT1 _ (R_projT1 _ arg_list_smaller)) y i ->
  funrep_ret (projT1 y)) -> funrep_ret (projT1 i) with
  (*We do each case separately*)
  | existT (existT packed (Left fndata)) valsrts => fun rec => 

    let s1 := proj1_sig (projT1 packed) in
    let s_in := proj2_sig (projT1 packed) in
    let srts := projT1 (projT2 packed) in
    let a1 := projT2 (projT2 packed) in
    let f := proj1_sig fndata in
    let Hinf := proj1' (proj2_sig fndata) in
    let Heqf := proj2' (proj2_sig fndata) in
    let v := fst valsrts in
    let srts_len := proj1' (snd valsrts) in
    let vt_eq_srts := proj2' (snd valsrts) in

    let input : packed_args2 := 
      existT _ (existT _ packed (Left _ _ fndata)) valsrts in

    let y := nth (sn_idx s1) (sn_args s1) vs_d in

    let y_eq : y = nth (sn_idx f) (sn_args f) vs_d := 
      f_equal (fun x => nth (sn_idx x) (sn_args x) vs_d) (eq_sym Heqf) in

    (*tm is the result of calling term_rep_aux*)
    let tm :=
    (proj1_sig (term_rep_aux input rec
      (val_with_args v (sn_args s1) a1) (fn_body f) 
        (f_ret (fn_sym f))  nil
      (Some y)
      (*proofs we need for [term_rep_aux]*)
      (Forall_In fs_typed Hinf)
      (eq_ind _ (fun x => decrease_fun fs ps _ x m vs _)  
        (Forall_In fs_dec Hinf) _ (f_equal Some (eq_sym y_eq)))
      (fun x Hx => match Hx with end)
      (y_eq_d input) )) in

    (*Then we cast the result*)

    let Hsf : sn_sym s1 = fn_sym f := 
      eq_sym (eq_trans (fn_sym_eq f) (f_equal sn_sym Heqf)) in

    let a2 : arg_list domain (sym_sigma_args (fn_sym f) srts) :=
      cast_arg_list (f_equal (fun x => sym_sigma_args x srts) Hsf) a1 in

    dom_cast _ (fn_ret_cast_eq f Hinf srts a2 srts_len vt_eq_srts) tm

  (*Pred case - slightly better, no casting needed*)
  | existT (existT packed (Right pndata)) valsrts => fun rec => 

    let s1 := proj1_sig (projT1 packed) in
    let s_in := proj2_sig (projT1 packed) in
    let srts := projT1 (projT2 packed) in
    let a1 := projT2 (projT2 packed) in
    let p := proj1_sig pndata in
    let Hinp := proj1' (proj2_sig pndata) in
    let Heqp := proj2' (proj2_sig pndata) in
    let v := fst valsrts in
    let srts_len := proj1' (snd valsrts) in
    let vt_eq_srts := proj2' (snd valsrts) in

    let input : packed_args2 := 
      existT _ (existT _ packed (Right _ _ pndata)) valsrts in

    let y := nth (sn_idx s1) (sn_args s1) vs_d in

    let y_eq : y = nth (sn_idx p) (sn_args p) vs_d := 
    f_equal (fun x => nth (sn_idx x) (sn_args x) vs_d) (eq_sym Heqp) in

    (formula_rep_aux input rec
      (val_with_args v (sn_args s1) a1) (pn_body p) 
      nil
      (Some y)
      (*proofs we need for [term_rep_aux]*)
      (Forall_In ps_typed Hinp)
      (eq_ind _ (fun x => decrease_pred fs ps _ x m vs _)  
        (Forall_In ps_dec Hinp) _ (f_equal Some (eq_sym y_eq)))
      (fun x Hx => match Hx with end)
      (y_eq_d input) )

  end rec.

(*Define final function with Fix*)
Definition funcs_rep_aux (pa: packed_args2) :
  (*The return type depends on whether this is a function or
    predicate definition*)
  funrep_ret (projT1 pa) :=

  @Fix packed_args2 _ 
  (*well-founded proof*)
  (wf_projT1 (wf_projT1 arg_list_smaller_wf): 
  well_founded (fun (x y: packed_args2) =>
    R_projT1 _ (R_projT1 _ arg_list_smaller) x y))
  (*type of function*)
  (fun (p: packed_args2) => 
  funrep_ret (projT1 p))
  (*body*)
  funcs_rep_aux_body
  (*applied to*)
  pa.

  (*We have it!*)

(*Now, we give a rewrite lemma.*)
  Lemma funcs_rep_aux_eq (pa: packed_args2):
  funcs_rep_aux pa = funcs_rep_aux_body pa
    (fun (x: packed_args2) 
      (p: R_projT1 _ (R_projT1 _ arg_list_smaller) x pa) => 
      funcs_rep_aux x).
  Proof.
    unfold funcs_rep_aux. rewrite Init.Wf.Fix_eq; auto.
    intros.
    (*TODO: maybe can prove without but we use funext anyway*)
    (*TODO: can use proof irrelevance but let's see*)
    assert (f = g). repeat (apply functional_extensionality_dep; intros); auto.
    subst; auto.
  Qed.

(*Plan: first write the definition and theorem with assumptions about
  fp, vt, vv, then define one with context and types to show
  that these are satisfied. Then prove theorems
  
  Will need:
  1. term_rep_aux/formula_rep_aux rewrite lemmas
  2. If pf1 and pf2 are equal on all fun/pred syms appearing in
  t/f that are not in fs, ps, then term_rep_aux pf1 t = term_rep_aux pf2 t
  and likewise for formula_rep
  3. If pf satisfies funs/preds rep (circular dependency)
    and vt satifies vt_eq (can build from vt_with_args)
    and vv is vv_with_args vv'
    and IH holds for reps,
    then term_rep_aux = term_rep and likewise

    later on, prove that we can substitute any vt as long as we
    have vt_eq (OR - show in term_rep that we can always "change"
    vt by adjusting valuation - might be easier to show)
  
  *)

Section FunRewrite.

Variable vv: val_vars pd vt.



(*Now a version for funsyms and predsyms that we can
  use for [funs] and [preds]*)
(*Still _aux (even though it is final in this file)
  because we don't just have typing assumptions yet*)
Definition funs_rep_aux (f: fn) (f_in: In f fs)
  (srts: list sort)
  (srts_len: length srts = length params)
  (*TODO: we will build the typesym map later so that this holds*)
  (vt_eq_srts: vt_eq srts)
  (a: arg_list domain (sym_sigma_args (sn_sym (fn_sn f)) srts)) :
  domain (funsym_sigma_ret (fn_sym f) srts) :=
  (*Pack everything up*)
  let pa: packed_args :=
    existT _ (exist _ (fn_sn f) (in_fs_sns f_in))
    (existT _ srts a) in
  let ca : combined_args :=
    combine_args_fun pa f f_in eq_refl in
  let pa2: packed_args2 :=
    existT _ ca (vv, conj srts_len vt_eq_srts) in
  (*and call the function*)
  funcs_rep_aux pa2.

Definition preds_rep_aux (p: pn) (p_in: In p ps)
  (srts: list sort)
  (srts_len: length srts = length params)
  (*TODO: we will build the typesym map later so that this holds*)
  (vt_eq_srts: vt_eq srts)
  (a: arg_list domain (sym_sigma_args (sn_sym (pn_sn p)) srts)) :
  bool :=
  (*Pack everything up*)
  let pa: packed_args :=
    existT _ (exist _ (pn_sn p) (in_ps_sns p_in))
    (existT _ srts a) in
  let ca : combined_args :=
    combine_args_pred pa p p_in eq_refl in
  let pa2: packed_args2 :=
    existT _ ca (vv, conj srts_len vt_eq_srts) in
  (*and call the function*)
  funcs_rep_aux pa2.

(*Now we state our correctness theorem.*)

(*First, we assume that [funs] and [preds] map all 
  f in fs and p in ps to their reps. We will construct this later*)
(*TODO: go back to typing, put stuff in right place, see what we need
  especially with pf, val_typevar, etc
  I think - want vt, then use vt_with_srts for definition of func
  otherwise we have a bad dependency*)
Variable pf_funs: forall (f: fn) (f_in: In f fs)
  (srts: list sort)
  (srts_len: length srts = length params)
  (vt_eq_srts: vt_eq srts)
  (a: arg_list domain (sym_sigma_args (fn_sym f) srts)),
  (*Unfortunately, we need to cast a*)
  funs gamma_valid pd pf (fn_sym f) srts a =
  funs_rep_aux f f_in srts srts_len vt_eq_srts 
    (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) (fn_wf f)) a).

Variable pf_preds: forall (p: pn) (p_in: In p ps)
(srts: list sort)
(srts_len: length srts = length params)
(vt_eq_srts: vt_eq srts)
(a: arg_list domain (sym_sigma_args (pn_sym p) srts)),
(*Unfortunately, we need to cast a*)
preds gamma_valid pd pf (pn_sym p) srts a =
preds_rep_aux p p_in srts srts_len vt_eq_srts 
  (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) (pn_wf p)) a).

(*Our spec: If we have f(a)(x) = b, then 
  for any s t, [[f(s)]](t) = [[b]]_(v1, v2), 
  where v1 maps a to s (assumed) and v2 maps x to t*)

(*The unfolded definition of our function in terms of [term_rep]
  and [formula_rep]: this is ugly*)
Definition funcs_rep_aux_unfold (pa: packed_args2) :
  funrep_ret (projT1 pa) :=
  match pa as p' return funrep_ret (projT1 p') with
    | existT (existT pa' (Left finfo)) pa2 => 
      let f : fn := proj1_sig finfo in
      let f_in : In f fs := proj1' (proj2_sig finfo) in
      let vv := (fst pa2) in
      let srts : list sort := projT1 (projT2 pa') in
      let srts_len  := proj1' (snd  pa2) in
      let vt_eq_srts := proj2' (snd pa2) in
      let a : arg_list domain (sym_sigma_args (fn_sym f) srts) := 
      (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) 
        (eq_trans (eq_sym (f_equal sn_sym (proj2' (proj2_sig finfo)))) (eq_sym (fn_wf f)))
        )
      (projT2 (projT2 pa'))) in
      (*Need a cast here*)
      dom_cast _ (fn_ret_cast_eq f f_in srts a srts_len vt_eq_srts) 
      (
      term_rep gamma_valid pd all_unif vt pf
        (*OK to use triv_val_vars here, later we will show equiv*)
        (val_with_args vv (sn_args f) a)
        (fn_body f) _
        (Forall_In fs_typed (proj1' (proj2_sig finfo))))
    | existT (existT pa' (Right pinfo)) pa2 =>
      let p : pn := proj1_sig pinfo in
      let p_in : In p ps := proj1' (proj2_sig pinfo) in
      let vv := (fst pa2) in
      let srts : list sort := projT1 (projT2 pa') in
      let srts_len  := proj1' (snd  pa2) in
      let vt_eq_srts := proj2' (snd pa2) in
      let a : arg_list domain (sym_sigma_args (pn_sym p) srts) := 
      (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) 
      (eq_trans (eq_sym (f_equal sn_sym (proj2' (proj2_sig pinfo)))) (eq_sym (pn_wf p)))
      ) (projT2 (projT2 pa'))) in
    formula_rep gamma_valid pd all_unif vt pf
      (*OK to use triv_val_vars here, later we will show equiv*)
      (val_with_args vv (sn_args p) a)
      (pn_body p)
      (Forall_In ps_typed (proj1' (proj2_sig pinfo)))
    end.

(*First, the theorem relating [term_rep] and [term_rep_aux]
  and likewise for formula*)


(*TODO: cannot assume pf, need to have term_rep input
  as [interp_with_funcs pf]*)
Theorem term_fmla_rep_aux_eq (t: term) (f: formula) :
  (forall (input: packed_args2)
    (rec: (forall y : packed_args2,
    R_projT1 _(R_projT1 _  arg_list_smaller) y input -> 
    funrep_ret (projT1 y)))
    (IH:forall (y: packed_args2)
    (small: R_projT1 _ (R_projT1 _ arg_list_smaller) y input),
    rec y small = funcs_rep_aux_unfold y)
    (v: val_vars pd vt) (*TODO: I think we don't need a condition
      here bc we prove equality*)
    (*TODO: what conditions on the term?*)
    (ty: vty) (small: list vsymbol) (hd: option vsymbol)
    (Hty: term_has_type sigma t ty)
    (Hdec: decrease_fun fs ps small hd m vs t)
    (Hsmall: forall x : vsymbol,
        In x small ->
        vty_in_m m vs (snd x) /\
        adt_smaller_trans (hide_ty (v x))
          (hide_ty
             (dom_cast (dom_aux pd)
                (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
                   (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))))
                (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (projT2 (projT2 (projT1 (projT1 input)))) s_int
                   (dom_int pd)))))
    (Hhd: forall h : vsymbol,
        hd = Some h ->
        vty_in_m m vs (snd h) /\
        hide_ty (v h) =
        hide_ty
          (dom_cast (dom_aux pd)
             (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
                (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))))
             (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                (projT2 (projT2 (projT1 (projT1 input)))) s_int 
                (dom_int pd)))),

    proj1_sig (term_rep_aux input rec v t ty small hd Hty Hdec Hsmall Hhd) =
    term_rep gamma_valid pd all_unif vt pf v t ty Hty
  ) /\
  (forall (input: packed_args2)
    (rec: (forall y : packed_args2,
    R_projT1 _(R_projT1 _  arg_list_smaller) y input -> 
    funrep_ret (projT1 y)))
    (IH:forall (y: packed_args2)
    (small: R_projT1 _ (R_projT1 _ arg_list_smaller) y input),
    rec y small = funcs_rep_aux_unfold y)
    (v: val_vars pd vt) (*TODO: I think we don't need a condition
      here bc we prove equality*)
    (*TODO: what conditions on the term?*)
    (small: list vsymbol) (hd: option vsymbol)
    (Hval: valid_formula sigma f)
    (Hdec: decrease_pred fs ps small hd m vs f)
    (Hsmall: forall x : vsymbol,
        In x small ->
        vty_in_m m vs (snd x) /\
        adt_smaller_trans (hide_ty (v x))
          (hide_ty
             (dom_cast (dom_aux pd)
                (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
                   (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))))
                (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (projT2 (projT2 (projT1 (projT1 input)))) s_int
                   (dom_int pd)))))
    (Hhd: forall h : vsymbol,
        hd = Some h ->
        vty_in_m m vs (snd h) /\
        hide_ty (v h) =
        hide_ty
          (dom_cast (dom_aux pd)
             (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
                (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))))
             (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                (projT2 (projT2 (projT1 (projT1 input)))) s_int 
                (dom_int pd)))),

    formula_rep_aux input rec v f small hd Hval Hdec Hsmall Hhd =
    formula_rep gamma_valid pd all_unif vt pf v f Hval
  )
  .
Proof.
Admitted.
  (*This proof just uses [term_formula_ind], we do not need
    any well-founded induction*)
  (*TODO: why does this proof take so long - 
    think because term_rep_aux is giant because of termination proof ugh *)
(*  revert t f. apply term_formula_ind; intros.
  (*TODO: prove rewrite lemma*)
Admitted.*)
  (*simpl_rep_full; auto.
  - destruct c; simpl_rep_full; reflexivity.
  - (*the function case will be hard and interesting
    TODO: start*)

  
  
  intros. simpl.*)

(*We have to prove the version with packed_args to get an appropriate
  induction hypothesis*)

(*TODO: term_rep should be with *)

Print val_with_args.

(*TODO: move*)
Lemma val_with_args_cast_eq (vv': val_vars pd vt) (l1 l2: list vsymbol)
  (s1 s2: list sort) (Heq: s1 = s2) (a1: arg_list domain s1):
  l1 = l2 ->
  val_with_args vv' l1 a1 = val_with_args vv' l2 (cast_arg_list Heq a1).
Proof.
  intros. subst. reflexivity.
Qed.

Theorem funpred_rep_aux_eq:
  forall (pa: packed_args2),
    funcs_rep_aux pa =
    funcs_rep_aux_unfold pa.
Proof.
  (*TODO: generalize some stuff*)
  (*Now we do induction on the well-founded relation*)
  apply (well_founded_induction (wf_projT1 (wf_projT1 arg_list_smaller_wf): 
  well_founded (fun (x y: packed_args2) =>
    R_projT1 _ (R_projT1 _ arg_list_smaller) x y))).
  intros pa IH.
  unfold funcs_rep_aux_unfold. simpl in *.
  (*We have to consider each case separately*)
  destruct pa as [[pa o] pa2].
  destruct o as [finfo | pinfo].
  - rewrite funcs_rep_aux_eq. simpl.
    (*Now we unfold all the casting until we get to
      a goal only about the [term_rep] and [term_rep_aux]*)
    f_equal.
    + f_equal. f_equal. apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
    + rewrite (proj1 (term_fmla_rep_aux_eq _ Ftrue)); auto.
      f_equal.
      assert (proj1_sig (projT1 pa) = (proj1_sig finfo)). {
        destruct finfo; simpl. destruct a; subst; auto.
      }
      apply val_with_args_cast_eq. f_equal. apply H; auto.
  - rewrite funcs_rep_aux_eq. simpl.
    rewrite (proj2 (term_fmla_rep_aux_eq tm_d _)); auto.
    f_equal.
    assert (proj1_sig (projT1 pa) = (proj1_sig pinfo)). {
      destruct pinfo; simpl. destruct a; subst; auto.
    }
    apply val_with_args_cast_eq. f_equal. apply H; auto.
Qed.

End FunRewrite.

(*Now we instead work from typing and give all the proofs*)
End Def.

End FunDef.

(*Now we give the full definition*)
Section Full.

(*First, we define when a mutual function body is in a context*)

(*TODO: move*)

(*Similar to mutual types*)

Definition funsym_in_mutfun (f: funsym) (l: list funpred_def) : bool :=
  in_bool funsym_eq_dec f 
    (fold_right (fun x acc => match x with | fun_def f' _ _ => 
      f' :: acc | _ => acc end) nil l).

Definition get_mutfun_fun (f: funsym) (gamma': context) : option (list funpred_def) :=
  find (funsym_in_mutfun f) (mutfuns_of_context gamma').

Definition predsym_in_mutfun (p: predsym) (l: list funpred_def) : bool :=
  in_bool predsym_eq_dec p 
    (fold_right (fun x acc => match x with | pred_def p' _ _ => 
      p' :: acc | _ => acc end) nil l).

Definition get_mutfun_pred (p: predsym) (gamma': context) : option (list funpred_def) :=
  find (predsym_in_mutfun p) (mutfuns_of_context gamma').
Print pi_funpred.


Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
{pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m).

(*TODO: move to typing*)

(*Get fs and ps associated with a funpred_def*)
Definition get_funpred_def_info (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)) : (list fn, list pn)

Notation domain := (domain (dom_aux pd)).

(*Definition of funs_rep*)
Definition funs_rep (f: funsym) (l: list funpred_def)
  (f_in: funsym_in_mutfun f l)
  (l_in: In l (mutfuns_of_context gamma))
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list domain (sym_sigma_args f srts)):
  domain (funsym_sigma_ret f srts) :=

  funs_rep_aux gamma_valid all_unif.



Definition funs_rep_aux (f: fn) (f_in: In f fs)
  (srts: list sort)
  (srts_len: length srts = length params)
  (*TODO: we will build the typesym map later so that this holds*)
  (vt_eq_srts: vt_eq srts)
  (a: arg_list domain (sym_sigma_args (sn_sym (fn_sn f)) srts)) :
  domain (funsym_sigma_ret (fn_sym f) srts) :=


Definition pf_with_funrep (pf: pi_funpred gamma_valid pd) 
(l: list funpred_def) : pi_funpred gamma_valid pd.
Admitted.

(*What we want to prove
1. For all mutual function defs and all funsyms and predsyms
  in these, this interpretation maps f srts a to
  the term_rep and p to the formula_rep (we also prove that)
2. For all other functions and predicates, the result is the same*)
Lemma pf_with_funrep_funs: forall (l: list funpred_def)
  (Hinl: In l (mutfuns_of_context gamma))
  (srts: list sort),
  (forall (f: funsym) (Hf:funsym_in_mutfun f l)
    (srts_len: length srts = length (s_params f))
    (a: arg_list domain (sym_sigma_args (fn_sym f) srts)):
    funs gamma_valid pd (pf_with_funrep)


Variable pf_funs: forall (f: fn) (f_in: In f fs)
  (srts: list sort)
  (srts_len: length srts = length params)
  (vt_eq_srts: vt_eq srts)
  (a: arg_list domain (sym_sigma_args (fn_sym f) srts)),
  (*Unfortunately, we need to cast a*)
  funs gamma_valid pd pf (fn_sym f) srts a =
  funs_rep_aux f f_in srts srts_len vt_eq_srts 
    (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) (fn_wf f)) a).

Variable pf_preds: forall (p: pn) (p_in: In p ps)
(srts: list sort)
(srts_len: length srts = length params)
(vt_eq_srts: vt_eq srts)
(a: arg_list domain (sym_sigma_args (pn_sym p) srts)),
(*Unfortunately, we need to cast a*)
preds gamma_valid pd pf (pn_sym p) srts a =
preds_rep_aux p p_in srts srts_len vt_eq_srts 
  (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) (pn_wf p)) a).







(*TODO: cannot make bool bc we don't have decidable equality on terms
  unless we use all_dec - do we need it?*)
Definition mutfun_in_ctx (l: list funpred_def) (gamma': ctx) : Prop :=
  in_bool


Check pi_funpred.


V



Check gamma.
Check fs.
Check fs_uniq.
End A.

End A.



Theorem funpred_rep_aux_eq:
  (forall (f: fn) (f_in: In f fs) (srts: list sort)
    (srts_len: length srts = length params)
    (vt_eq_srts: vt_eq srts)
    (a: arg_list domain (sym_sigma_args (fn_sym f) srts)),
    funs gamma_valid pd pf (fn_sym f) srts a =
    (*Unfortunately, we need a cast here because
      val (f_ret f) is not definitionally equal to
      funsym_sigma_ret f srts*)
    dom_cast _ (fn_ret_cast_eq f f_in srts a srts_len vt_eq_srts) 
    (
    term_rep gamma_valid pd all_unif vt pf
      (*OK to use triv_val_vars here, later we will show equiv*)
      (val_with_args vv (sn_args f) a)
       (fn_body f) _
       (Forall_In fs_typed f_in))) /\
  (forall (p: pn) (p_in: In p ps) (srts: list sort)
    (srts_len: length srts = length params)
    (vt_eq_srts: vt_eq srts)
    (a: arg_list domain (sym_sigma_args (pn_sym p) srts)),
    preds gamma_valid pd pf (pn_sym p) srts a =
    formula_rep gamma_valid pd all_unif vt pf
      (*OK to use triv_val_vars here, later we will show equiv*)
      (val_with_args vv (sn_args p) a)
      (pn_body p)
      (Forall_In ps_typed p_in)).
Proof.
  (*First, see what happens for 1 side - need well-founded recursion*)


  .





End FunDef.

Check funcs_rep_aux.



(*TODO: move these to Interp*)

(*Here, we fix our valuation since we cannot take in any
  input in our final version. We can give a trivial valuation
  and define the mapping on the typesyms and vsyms that we care
  about. We will need to show it equals a [term_rep] and [formula_rep]
  for an arbirtary valuation, which will require a bit of annoying casting*)

(*First, a trivial val_typevar*)

Definition triv_val_typevar : val_typevar :=
  fun x => s_int.

(*Then, from a val_typevar, set variables alpha to srts*)

Fixpoint vt_with_args (vt: val_typevar) (args: list typevar)
  (srts: list sort) : val_typevar :=
  fun (x: typevar) =>
  match args with
  | nil => vt x
  | a :: atl =>
    match srts with
    | nil => vt x
    | s1 :: stl => if typevar_eq_dec x a then s1 
      else vt_with_args vt atl stl x
    end
  end.

Lemma vt_with_args_nth (vt: val_typevar) args srts:
  length args = length srts ->
  NoDup args ->
  forall i, i < length args ->
  vt_with_args vt args srts (nth i args EmptyString) = nth i srts s_int.
Proof.
  intros. generalize dependent srts. generalize dependent i. 
  induction args; simpl; intros.
  simpl in *; lia.
  destruct srts; inversion H; subst.
  destruct i.
  - destruct (typevar_eq_dec a a); try contradiction; auto.
  - destruct (typevar_eq_dec (nth i args EmptyString) a).
    + subst. inversion H0; subst.
      exfalso. apply H5. apply nth_In. simpl in H1. lia.
    + simpl. apply IHargs; auto. inversion H0; subst; auto. lia.
Qed.

(*Now we prove that this has the [vt_eq] property - args = params*)
Lemma vt_with_args_vt_eq (vt: val_typevar)
  (srts: list sort):
  NoDup params ->
  length srts = length params ->
  @vt_eq (vt_with_args vt params srts) srts.
Proof.
  intros. unfold vt_eq. intros.
  apply vt_with_args_nth; auto.
Qed.

Definition func_vt (srts: list sort) : val_typevar := 
  vt_with_args triv_val_typevar params srts.


(*Trivial valuation gives default elements*)
Definition triv_val_vars (vt: val_typevar) : val_vars pd vt :=
  fun x => 
  match domain_ne pd (v_subst vt (snd x)) with
  | DE y => y
  end.