(*Induction for ADTs*)
Require Export Interp. (*TODO: require this so that
  we can refer to Interp.adts - 
  could generalize for any proof and just use IndTypes.v*)

Section Induction.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
{pd: pi_dom}.



(*The last piece is to prove an induction principle for [adt_rep]s
  that we can specialize to specific types. This follows from
  W_ind, but it is very hard to prove. We do so here*)

(*
  We of course rely on the induction principle for W-types, but
  our encoding is very complicated, so it is very difficult
  to get this into a usable form. We need lots of typecasts
  and intermediate results
  *)

Definition cast_w {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
  {i1 i2: I} (Heq: i1 = i2) (w: W I A B i1) : W I A B i2 :=
  match Heq with
  | Logic.eq_refl => w
  end.

Definition cast_a {I: Set} {A: I -> Set} {i1 i2: I} (Heq: i1 = i2)
  (a: A i1) : A i2 := scast (f_equal A Heq) a.

Definition cast_b {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
  {i1 i2 j: I} (Heq: i1 = i2) {a: A i1} (b: B i1 j a) :
    B i2 j (cast_a Heq a).
  destruct Heq. exact b.
Defined.

Lemma cast_a_sym {I: Set} {A: I -> Set} {i1 i2: I} (Heq: i1 = i2)
(a: A i1): cast_a (Logic.eq_sym Heq) (cast_a Heq a) = a.
Proof.
  unfold cast_a. subst. reflexivity.
Defined. 

Lemma cast_w_mkw {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
{i1 i2: I} (Heq: i1 = i2) (a: A i1) (f: forall j: I, B i1 j a -> W I A B j):
  cast_w Heq (mkW I A B i1 a f) =
  mkW I A B i2 (cast_a Heq a) 
  (fun (j: I) (b: B i2 j (@cast_a I A _ _ Heq a)) =>
    let b' : B i1 j (cast_a (Logic.eq_sym Heq) (cast_a Heq a)) 
      := cast_b (Logic.eq_sym Heq) b in
    let b'': B i1 j a := scast (f_equal (B i1 j) (cast_a_sym Heq a)) b' in
    f j b'').
Proof.
  unfold cast_w. subst. simpl. unfold cast_a. simpl.
  unfold scast, cast_a_sym. f_equal.
Qed. 

Lemma cast_i (m: mut_adt) (m_in: mut_in_ctx m gamma) 
  (i: finite (length (typs m))):
  i = get_idx adt_dec (fin_nth (typs m) i) (typs m)
  (In_in_bool adt_dec (fin_nth (typs m) i) (typs m) (fin_nth_in (typs m) i)).
Proof.
  rewrite get_idx_fin; auto.
  apply (adts_nodups gamma_valid). apply m_in.
Qed.

Definition cast_adt_rep {d m srts t1 t2 tin1 tin2}
  (H: t1 = t2)
  (x: adt_rep m srts d t1 tin1):
  adt_rep m srts d t2 tin2.
  revert x. unfold adt_rep, mk_adts.
  apply cast_w. subst. f_equal. apply bool_irrelevance.
Defined.

(*Relies on decidability of domain*)
Lemma cast_w_twice {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
{i1 i2: I}
(eq_dec: forall x y: I, {x=y} + {x<>y})
(Heq: i1 = i2) (Heq2: i2 = i1) (w: W I A B i1):
  cast_w Heq2 (cast_w Heq w) = w.
Proof.
  subst. unfold cast_w. assert (Heq2=Logic.eq_refl). apply UIP_dec. auto.
  rewrite H. reflexivity.
Qed.

(*We can rewrite under a proposition for equivalent ADTs*)
(*These lemmas show why it is critical to have a bool for t_in*)
Lemma rewrite_P {d m srts}
(P: forall t t_in, adt_rep m srts d t t_in -> Prop):
forall t1 t2 t_in1 t_in2 (Ht: t1 = t2) x,
  P t1 t_in1 x <-> P t2 t_in2 (cast_adt_rep Ht x).
Proof.
  intros. unfold cast_adt_rep. unfold cast_w, eq_ind_r, eq_ind.
  subst. simpl. 
  destruct ((bool_irrelevance _ t_in1 t_in2)).
  simpl. reflexivity.
Qed.

Lemma map_map_eq {A B: Type} (f: A -> B) (l: list A):
  seq.map f l = map f l.
Proof. reflexivity. Qed.

(*TODO: maybe separate out into separate lemma*)
(*We show that if the interpretation of a type is
  the ADT applied to sorts, the type of the constructor
  must have been the ADT name applied to the args.
  This is not as trivial as it would seem; we need to
  show it cannot be some typesym which is given the ADT
  as an interpretation. We do this by showing such a
  list would be impossible to construct in the following
  few functions. This seems a bit hacky:*)

(*A list of the "smaller" types contained in a type*)
Definition subterm_ty (v: vty) : list vty :=
  match v with
  | vty_cons _ tys => tys
  | _ => nil
  end.

Fixpoint vty_size (v: vty) : nat :=
  match v with
  | vty_int => 1
  | vty_real => 1
  | vty_var _ => 1
  | vty_cons _ ts => 1 + sum (map vty_size ts)
  end.

Definition vtys_size (l: list vty) : nat :=
  sum (map vty_size l).

Lemma vty_size_eq (v: vty):
  vty_size v =
  match v with
  | vty_int => 1
  | vty_real => 1
  | vty_var _ => 1
  | vty_cons _ ts => 1 + vtys_size ts
  end.
Proof.
  destruct v; auto.
Qed.

(*The size of a single type is smaller than 
  the whole list*)
Lemma vtys_size_in (l: list vty) (t: vty):
  In t l ->
  vty_size t <= vtys_size l.
Proof.
  unfold vtys_size.
  induction l; simpl; intros; auto. destruct H.
  destruct H; subst; try lia.
  specialize (IHl H). lia.
Qed.
  
(*An obvious lemma but one that is tricky to prove.
  We prove this by giving the above size function
  and proving that if (vty_cons t l) is in l, then
  it has a smaller size than l, a contradiction *)
(*Note: I believe that the same proof holds for any
  coutable type*)
Lemma sub_not_whole : forall t l,
    ~ In (vty_cons t l) l.
Proof.
  intros. intro C.
  apply vtys_size_in in C.
  rewrite vty_size_eq in C. lia.
Qed.

(*As a corollary, we get the following*)
Lemma list_srts_not_whole (n: nat) (tys: list vty) (ts: typesym):
  List.nth n tys vty_int <> vty_cons ts tys.
Proof.
  assert (n < length tys \/ length tys <= n) by lia. destruct H.
  - intro C.
    apply (sub_not_whole ts tys). rewrite <- C.
    apply nth_In; auto.
  - rewrite nth_overflow; auto. intro C; inversion C.
Qed. 

Theorem adts_from_constrs {m: mut_adt} (m_in: mut_in_ctx m gamma)
  (a': alg_datatype) (Hini: adt_in_mut a' m)
  (c: funsym) 
  (c_in: constr_in_adt c a')
  (t': alg_datatype) (t_in': adt_in_mut t' m)
  (j: nat) (srts: list sort)
  (Hj: j < Datatypes.length (s_args c))
  (Hlen: Datatypes.length srts = Datatypes.length (m_params m))
  (Hnth: nth j (sym_sigma_args c srts) s_int =
    typesym_to_sort (adt_name t') srts):
  nth j (s_args c) vty_int =
    vty_cons (adt_name t') (map vty_var (ts_args (adt_name t'))).
Proof.
  assert (Hparams: (s_params c) = (m_params m)). {
    eapply adt_constr_params. apply gamma_valid.
    auto. apply Hini. apply c_in. 
  }
  revert Hnth.
  unfold sym_sigma_args, typesym_to_sort, ty_subst_list_s.
  rewrite map_nth_inbound with(d2:=vty_int); auto.
  unfold ty_subst_s, v_subst; intros Heq.
  inversion Heq. clear Heq.
  destruct (nth j (s_args c) vty_int) eqn : Hnth; simpl in H0;
  try solve[inversion H0].
  - destruct (in_dec typevar_eq_dec t (s_params c)).
    + destruct (In_nth _ _ EmptyString i) as [n [Hn Hnthn]].
      rewrite <- Hnthn in H0.
      rewrite ty_subst_fun_nth with(s:=vty_int) in H0; auto.
      * unfold sorts_to_tys in H0.
        exfalso.
        (*We get contradiction: can't have srts inside srts
          This proves that this case cannot happen*)
        apply (list_srts_not_whole n (sorts_to_tys srts) (adt_name t')); auto.
      * unfold sorts_to_tys. rewrite map_length, Hlen, Hparams.
        reflexivity.
      * apply s_params_Nodup.
    + rewrite ty_subst_fun_notin in H0; auto. inversion H0.
  - (*The case that can actually happen: cons*)
    inversion H0; subst. clear H0. 
    (*Use uniformity - just instantiate all hyps, takes a while
      should automate*)
    assert (Hunif: uniform m). {
      apply (gamma_all_unif gamma_valid). auto.
    }
    unfold uniform in Hunif. unfold is_true in Hunif. 
    rewrite forallb_forall in Hunif.
    specialize (Hunif a' (in_bool_In _ _ _ Hini)).
    rewrite forallb_forall in Hunif.
    specialize (Hunif c).
    assert (Hinc: In c (ne_list_to_list (adt_constrs a'))). {
      apply in_bool_ne_In with(eq_dec:=funsym_eq_dec).
      apply c_in.
    }
    specialize (Hunif Hinc).
    unfold uniform_list in Hunif.
    rewrite forallb_forall in Hunif.
    assert (Hincons: In (vty_cons (adt_name t') l) (s_args c)). {
      rewrite <- Hnth. apply nth_In; auto.
    }
    specialize (Hunif _ Hincons). simpl in Hunif.
    rewrite implb_true_iff in Hunif.
    assert (Htsin: ts_in_mut_list (adt_name t') (typs m)). {
      unfold adt_in_mut in t_in'. 
      unfold ts_in_mut_list. apply In_in_bool. rewrite in_map_iff.
      exists t'. split; auto. apply (in_bool_In _ _ _ t_in'). 
    }
    specialize (Hunif Htsin). simpl_sumbool.
    f_equal.
    erewrite adt_args with(m:=m); [| apply gamma_valid |].
    + reflexivity.
    + unfold adt_mut_in_ctx. split; auto.
Qed.

(*TODO: move this*)
(*Suppose we know that the ith element of a list satisfies a predicate.
  Then we can find a j such that nth j (filter p l) = nth i l;
  and moreover, we know exactly which j*)

Definition idx_filter {A: Type} (p: A -> bool) (l: list A)
  (n: nat) := length (filter p (firstn n l)).

Lemma idx_filter_length {A: Type} (p: A -> bool) (l: list A)
  (n: nat) (Hn: n < length l) (d: A):
  p (nth n l d) ->
  idx_filter p l n < length (filter p l).
Proof.
  generalize dependent n.
  unfold idx_filter. induction l; intros; simpl; auto. inversion Hn.
  simpl in Hn. destruct n; simpl.
  - simpl in H. rewrite H. simpl; lia.
  - simpl in H.
    specialize (IHl n (ltac:(lia)) H).
    destruct (p a); simpl; lia.
Qed.

Lemma idx_filter_le {A: Type} (p: A -> bool) (l: list A)
(n: nat):
idx_filter p l n <= length (filter p l).
Proof.
  unfold idx_filter.
  revert n. induction l; simpl; intros; destruct n; simpl; auto.
  - lia.
  - specialize (IHl n). destruct (p a); simpl; lia.
Qed.

Lemma firstn_skipn_nth {A: Type} (n: nat) (l: list A) (d: A):
  n < length l ->
  l = firstn n l ++ (nth n l d) :: skipn (S n) l.
Proof.
  revert n. induction l; simpl; intros.
  - inversion H.
  - destruct n; auto.
    simpl firstn. rewrite <- app_comm_cons.
    f_equal. apply IHl. lia.
Qed. 

Lemma idx_filter_correct {A: Type} (p: A -> bool) (l: list A)
  (n: nat) (Hn: n < length l) (d: A):
  p (nth n l d) ->
  nth (idx_filter p l n) (filter p l) d = nth n l d.
Proof.
  intros. unfold idx_filter.
  generalize dependent n. induction l; simpl; intros.
  - inversion Hn.
  - destruct n.
    + simpl. rewrite H. reflexivity.
    + simpl firstn. simpl filter.
      destruct (p a); simpl; apply IHl; auto; lia.
Qed.

(*We need this specific function and j value for the following
  lemma:*)
Lemma hnth_hlist_map_filter  {A B: Set} {f: A -> Set} {l: list B}
(f1: B -> A) (h: hlist f (map f1 l)) (g: B -> bool) j d1 d2 d3
(eq_dec: forall (x y: A), {x = y} + {x <> y})
(Hij: (nth j (map f1 l) d1) = (nth (idx_filter g l j) (map f1 (filter g l)) d1))
(Hg: g (nth j l d2)):
  hnth (idx_filter g l j) (hlist_map_filter f1 h g) d1 d3 =
  (scast (f_equal f Hij) (hnth j h d1 d3)).
Proof.
  revert Hij.
  generalize dependent j.
  induction l; intros; simpl in Hij |- *.
  - destruct j; simpl in *; subst;
    assert (Hij = eq_refl) by (apply UIP_dec; apply eq_dec);
    rewrite H; simpl; reflexivity.
  - destruct j; simpl in Hij |- *.
    + unfold idx_filter in *. simpl in *.
      destruct (g a) eqn : Ha; simpl in *.
      * assert (Hij = eq_refl). apply UIP_dec. apply eq_dec.
        rewrite H; reflexivity.
      * inversion Hg.
    + unfold idx_filter in *; simpl in *.
      destruct (g a) eqn : Ha; simpl in *;
      apply IHl; auto.
Qed.

(*Casting over dependent types/build_rec;
  this is where things get very tricky*)

Definition cast_dep {A: Set} (B: A -> Set) 
  {a1 a2: A} (Heq: a1 = a2) (x: B a1) : B a2 :=
  scast (f_equal B Heq) x.

(*Another level*)
Definition cast_dep' {A: Set} (B: A -> Set) (C: forall (a: A), B a -> Set)
  {a1 a2: A} (Heq: a1 = a2) (x: B a1) (y: C a1 x) :
  C a2 (cast_dep B Heq x).
  destruct Heq. unfold cast_dep. exact y.
Defined.

Lemma cast_fun' {T: Set} {A: Type} {B: A -> T -> Type} 
  {C: A -> Type} {t1 t2: T} 
  {f: forall (x: A)(y: B x t1), C x} (Heq: t1 = t2):
  forall x y,
  (cast (f_equal (fun (x: T) => forall (a: A)(b: B a x), C a) Heq) f) x y = 
  (fun (x: A) (y: B x t2) => 
    f x (cast (f_equal (B x) (Logic.eq_sym Heq)) y)) x y.
Proof.
  destruct Heq. simpl. intros. reflexivity.
Qed.

Lemma scast_get_constr_type {m: mut_adt}
  {i1 i2: finite (length (typs m))} (Heqi: i1 = i2)
  {vars typesyms c Hinc Hinc' x}:
  scast (f_equal 
    (fun n => build_base vars typesyms (typs m)
    (adt_constrs (fin_nth (typs m) n))) Heqi)
  (get_constr_type vars typesyms (typs m) (adt_name (fin_nth (typs m) i1))
    (adt_constrs (fin_nth (typs m) i1)) c Hinc x) =
  get_constr_type vars typesyms (typs m) (adt_name (fin_nth (typs m) i2))
    (adt_constrs (fin_nth (typs m) i2)) c Hinc' x.
Proof.
  unfold scast. destruct Heqi. simpl.
  assert (Hinc = Hinc') by (apply bool_irrelevance).
  rewrite H. reflexivity.
Qed.

(*Cast from one [build_rec] to another*)
Definition cast_build_rec_gen {m: mut_adt} {constrs1 constrs2}
  (Heq: constrs1 = constrs2) vars typesyms ts ts1 ts2 c Hinc1 Hinc2 b1 b2:
    build_rec vars typesyms (typs m) ts constrs1
      (get_constr_type vars typesyms (typs m) ts1 constrs1 c Hinc1 b1) ->
    build_rec vars typesyms (typs m) ts constrs2
      (get_constr_type vars typesyms (typs m) ts2 constrs2 c Hinc2 b2).
Proof.
  destruct Heq. assert (Hinc1 = Hinc2) by apply bool_irrelevance.
  intros A.
  apply finite_to_build_rec.
  eapply build_rec_to_finite. apply A.
Defined.

(*Annoying dependent reasons why we need extra typesym*)
Lemma build_rec_to_finite_cast {m: mut_adt} {constrs1 constrs2}
(Heq: constrs1 = constrs2) vars typesyms ts ts1 ts2 ts3 
  (Hts: ts2 = ts3) c Hinc1 Hinc2 b1 b2 x:
  @build_rec_to_finite vars typesyms (typs m) ts3 ts constrs2 c Hinc2 b2
    (cast_build_rec_gen Heq vars typesyms ts ts1 ts2 c Hinc1 Hinc2 b1 b2 x) =
  build_rec_to_finite vars typesyms (typs m) x.
Proof.
  destruct Hts.
  unfold cast_build_rec_gen. subst.
  rewrite build_rec_finite_inv2. reflexivity.
Qed.

Definition cast_build_rec {m: mut_adt} {i1 i2: finite (length (typs m))} 
(Heqi: i1 = i2)
vars typesyms ts c Hinc  x:
build_rec vars typesyms (typs m) ts (adt_constrs (fin_nth (typs m) i1))
  (get_constr_type vars typesyms (typs m) (adt_name (fin_nth (typs m) i1))
  (adt_constrs (fin_nth (typs m) i1)) c Hinc x) ->
build_rec vars typesyms (typs m) ts (adt_constrs (fin_nth (typs m) i2))
(scast (f_equal 
(fun n => build_base vars typesyms (typs m)
(adt_constrs (fin_nth (typs m) n))) Heqi)
(get_constr_type vars typesyms (typs m) (adt_name (fin_nth (typs m) i1))
(adt_constrs (fin_nth (typs m) i1)) c Hinc x)).
apply (cast_dep' 
  (fun i : finite (Datatypes.length (typs m)) =>
    build_base vars typesyms (typs m) (adt_constrs (fin_nth (typs m) i)))
  (fun (i : finite (Datatypes.length (typs m)))
    (t : build_base vars typesyms (typs m)
      (adt_constrs (fin_nth (typs m) i))) =>
    build_rec vars typesyms (typs m) ts (adt_constrs (fin_nth (typs m) i)) t)
  Heqi).
Defined.

(*Injectivity for [existT]*)

Lemma existT_inj_dec {U: Type} {P: U -> Type} (eq_dec: forall x y : U, {x = y} + {x <> y}) {x1 x2: U} {H1: P x1} (H2: P x2):
  existT P x1 H1 = existT P x2 H2 ->
  {Heq: x1 = x2 & H2 = cast (f_equal P Heq) H1}.
Proof.
  intros. assert (Hex:=H).
  apply EqdepFacts.eq_sigT_fst in H. subst.
  apply inj_pair2_eq_dec in Hex. 2: apply eq_dec. subst.
  apply (existT _ (Logic.eq_refl)). reflexivity.
Qed.

Lemma existT_inj {U: Type} {P: U -> Type} {x1 x2: U} {H1: P x1} (H2: P x2):
  existT P x1 H1 = existT P x2 H2 ->
  {Heq: x1 = x2 & H2 = cast (f_equal P Heq) H1}.
Proof.
  intros. assert (Hex:=H).
  apply EqdepFacts.eq_sigT_fst in H. subst.
  apply Eqdep.EqdepTheory.inj_pair2 in Hex. subst.
  apply (existT _ (Logic.eq_refl)). reflexivity.
Qed.

Notation domain := (domain (dom_aux pd)).

(*Finally, we define a generalized induction principle on ADTs: 
  - Suppose we have P, a proposition on all ADTs in mut adt m
  - Suppose we know that, for any instance x = c(args) of
    an ADT in m, if P holds for all elements of args which are
    recursive, then P holds of x
  - Then P holds for all instances of ADTs in m  
  *)
Theorem adt_rep_ind m m_in srts
  (Hlen: length srts = length (m_params m)) 
  (P: forall t t_in, adt_rep m srts (dom_aux pd) t t_in -> Prop):
  (forall t t_in (x: adt_rep m srts (dom_aux pd) t t_in) 
    (c: funsym) (Hc: constr_in_adt c t) (a: arg_list domain (sym_sigma_args c srts))
    (Hx: x = constr_rep gamma_valid m m_in srts Hlen (dom_aux pd) t t_in c
      Hc (Interp.adts pd m srts) a),
    (forall i t' t_in' Heq, i < length (s_args c) ->
      (*If nth i a has type adt_rep ..., then P holds of it*)
      P t' t_in' (scast (Interp.adts pd m srts t' t_in') 
        (dom_cast _ Heq (hnth i a s_int (dom_int pd)))) 
      ) ->
    P t t_in x
    ) ->
  forall t t_in (x: adt_rep m srts (dom_aux pd) t t_in),
  P t t_in x.
Proof.
  intros.
  unfold adt_rep in x, P. unfold mk_adts in x, P.
  (*We use [W_ind], the induction principle for
  indexed W types. There is a LOT of work needed to
  use it for this*)
  pose proof (W_ind (finite (length (typs m)))
  (fun n : finite (Datatypes.length (typs m)) =>
    build_base (var_map m srts (dom_aux pd))
    (typesym_map m srts (dom_aux pd)) (typs m)
    (adt_constrs (fin_nth (typs m) n)))
  (fun this i : finite (Datatypes.length (typs m)) =>
    build_rec (var_map m srts (dom_aux pd))
      (typesym_map m srts (dom_aux pd)) (typs m)
      (adt_name (fin_nth (typs m) i))
      (adt_constrs (fin_nth (typs m) this)))
  (*instantiate P*)
  (fun i w => P (fin_nth (typs m) i)
    (In_in_bool adt_dec _ _ (fin_nth_in (typs m) i)) 
    (cast_w (cast_i m m_in i) w))
  ) as wind.
  (*There are two goals: show that W_ind allows us to
    conclude P ..., then prove that the hypotheses
    are satisfied. The first part is much easier, so we
    do it first*)
  match goal with
  | H: ?P -> ?Q |- _ => let Hhyp := fresh "Hindh" in
    assert (Hhyp: P); [clear H|specialize (H Hhyp); clear Hhyp]
  end.
  2: {
    specialize (wind 
      (get_idx _ t (typs m) t_in) x).
      simpl in wind.
    clear -wind.
    revert wind.
    assert (Ht: (fin_nth (typs m) (get_idx adt_dec t (typs m) t_in)) = t). {
      apply get_idx_correct.
    }
    rewrite rewrite_P with(P:=P)(t2:=t)(t_in2:=t_in)(Ht:=Ht).
    assert ((cast_adt_rep Ht
    (cast_w (cast_i m m_in (get_idx adt_dec t (typs m) t_in)) x)) = x). {
      clear. unfold cast_adt_rep.
      apply cast_w_twice.
      apply finite_eq_dec.
    }
  rewrite <- H at 2. auto.
  }
  (*The hard part: prove that the IH's coincide*)
  intros i a f IH.
  rewrite cast_w_mkw. simpl.
  match goal with
  | |- P ?i ?h ?y => set (x':=y) in *
  end.
  (*Idea: x' is some instance of W type (ith in m)
    we can find the constructor c and args such that x' = c(args)
    Then we use (complicated, dependent) inversion to
    connect the components of x' with those of the constructor and args
    *)
  destruct (find_constr_rep gamma_valid m m_in srts Hlen (dom_aux pd)
    (fin_nth (typs m) i) (In_in_bool adt_dec _ _ (fin_nth_in (typs m) i))
    (Interp.adts pd m srts) (gamma_all_unif gamma_valid m m_in) x') as [c [[c_in args] Hx']].
  (*Here, we need info about a*)
  assert (Hnodupb: nodupb funsym_eq_dec
    (ne_list_to_list (adt_constrs (fin_nth (typs m) i)))). {
    eapply constrs_nodups with(m:=m). apply gamma_valid. auto.
    rewrite in_map_iff. exists (fin_nth (typs m) i). split; auto.
    apply fin_nth_in.
  }
  destruct (get_funsym_base (var_map m srts (dom_aux pd))
    (typesym_map m srts (dom_aux pd)) (typs m) 
    (adt_name (fin_nth (typs m) i))
    (adt_constrs (fin_nth (typs m) i)) Hnodupb a
    ) as [c' [Hinc' [b1 Ha]]].
  assert (c = c'). {
    (*Idea: we know from x' + inversion that [get_constr_types]
      agree, use injectivity*)
    unfold constr_rep in Hx'.
    unfold make_constr in Hx'.
    subst x'.
    inversion Hx'. clear Hx'.
    apply inj_pair2_eq_dec in H1. 2: apply finite_eq_dec.
    revert H1.
    unfold cast_a.
    (*want to prove, essentially, that a = get_constr_type c b,
      for appropriate b (from [get_funsym_base])*)
    rewrite Ha.
    rewrite scast_get_constr_type with(Hinc':=
    (constr_in_lemma m (fin_nth (typs m) i)
    (In_in_bool adt_dec (fin_nth (typs m) i) (typs m)
      (fin_nth_in (typs m) i)) c' Hinc')).
    intros Hconstrs.
    apply get_constr_type_inj1 in Hconstrs.
    subst; auto.
  }
  subst c'.
  (*Now we know about a. This is helpful*)
  specialize (H _ _ x' c c_in args Hx').
  apply H.
  (*Now we need to show that the [forall i] condition
    corresponds to that in the IH. This is the hardest part*)
  intros j t' t_in' Heq Hj.
  specialize (IH (get_idx adt_dec t' (typs m) t_in')).
  assert (Heq': nth j (s_args c) vty_int =
    vty_cons (adt_name t') (map vty_var (ts_args (adt_name t')))). {
    apply (@adts_from_constrs m) with(a':=fin_nth (typs m) i)(srts:=srts); auto.
    apply In_in_bool. apply fin_nth_in.
  }
  subst a.
  (*Now we use [finite_to_build_rec] to get our b, which is
    the value [idx_filter] corresponding to j cast to a finite type*)
  assert (Hp: rec_occ_fun (adt_name t') (nth j (s_args c) vty_int)). {
    unfold rec_occ_fun. rewrite Heq'.
    bool_to_prop. split; simpl_sumbool.
  }
  pose proof (idx_filter_length _ _ _ Hj vty_int Hp) as Hn.
  pose proof (idx_filter_correct _ _ _ Hj vty_int Hp) as Hni.
  set (n:= (idx_filter (rec_occ_fun (adt_name t')) (s_args c) j)) in *.
  (*Build finite value*)
  assert ( Hn': n < (count_rec_occ
    (adt_name (fin_nth (typs m) 
      (get_idx adt_dec t' (typs m) t_in'))) c)). {
    rewrite get_idx_correct.
    apply Hn.
  }
  set (fin:=nat_to_finite n Hn').
  set (br:=(@finite_to_build_rec 
  (var_map m srts (dom_aux pd))
  (typesym_map m srts (dom_aux pd))
  (typs m)
  (adt_name (fin_nth (typs m) i))
  (adt_name (fin_nth (typs m) (get_idx adt_dec t' (typs m) t_in')))
  (adt_constrs (fin_nth (typs m) i))
  c Hinc' b1 fin
  )).
  specialize (IH br).
  (*Now, we need to cast*)
  revert IH.
  assert (Ht: fin_nth (typs m) (get_idx adt_dec t' (typs m) t_in') = t'). {
    apply get_idx_correct.
  }
  rewrite rewrite_P with(P:=P)(t2:=t')(t_in2:=t_in')(Ht:=Ht).
  (*The "only" thing that remains is to show that these last
    two casted ADTs are equal. This is not easy*)
  assert ((cast_adt_rep Ht
    (cast_w (cast_i m m_in (get_idx adt_dec t' (typs m) t_in'))
      (f (get_idx adt_dec t' (typs m) t_in')
        br))) =
            (scast (Interp.adts pd m srts t' t_in')
            (dom_cast (dom_aux pd) Heq (hnth j args s_int (dom_int pd))))). {
    unfold cast_adt_rep. rewrite cast_w_twice. 2: apply finite_eq_dec.
    (*Now we need to know something about f, again by
      inversion on x'*)
    unfold constr_rep in Hx'.
    unfold make_constr in Hx'.
    subst x'.
    inversion Hx'. clear Hx'.
    clear H1.
    apply existT_inj_dec in H2. 2: apply finite_eq_dec.
    destruct H2 as [Heq1 Hexeq].
    assert (Heq1 = Logic.eq_refl). {
      apply UIP_dec. apply finite_eq_dec.
    }
    rewrite H0 in Hexeq. simpl in Hexeq. clear H0.
    (*Here (and in other places), we need UIP*)
    apply existT_inj in Hexeq. destruct Hexeq as [Heq2 Hexeq].
    apply fun_args_eq_dep with(x:=(get_idx adt_dec t' (typs m) t_in')) in Hexeq.
    (*Idea: specialize with correct type, will need to simplify casts,
      get equivalence for f*)
    unfold cast_a in Hexeq.
    (*We use a cast on the [build_rec] to specialize the function*)
    set (br_cast := (cast_build_rec (cast_i m m_in i)
    (var_map m srts (dom_aux pd))
    (typesym_map m srts (dom_aux pd)) 
    (adt_name (fin_nth (typs m) (get_idx adt_dec t' (typs m) t_in')))
    c Hinc' b1 br
    )).
    apply fun_args_eq_dep with (x:=br_cast) in Hexeq.
    (*Now we have an equivalence for f, we need to simplify everything*)
    (*TO deal with implicit args, use tactics*)
    match goal with 
    | H: f ?i ?br' = ?z |- f ?i ?br = ?y => assert (Hbr: br = br');
      [|rewrite <- Hbr in H; rewrite H; clear Hbr]
    end.
    {
      clear. (*Now, just casting*) subst br br_cast.
      generalize dependent (cast_i m m_in i). intros. destruct e. simpl.
      reflexivity.
    }
    (*simplify casts in function*)
    (*this is a bit awful because we need all the function types*)
    rewrite (@cast_fun' _ 
      (finite (Datatypes.length (typs m)))
      (fun j0 a => build_rec (var_map m srts (dom_aux pd))
        (typesym_map m srts (dom_aux pd)) (typs m)
        (adt_name (fin_nth (typs m) j0))
        (adt_constrs
          (fin_nth (typs m)
              (get_idx adt_dec (fin_nth (typs m) i) 
                (typs m)
                (In_in_bool adt_dec (fin_nth (typs m) i) 
                    (typs m) (fin_nth_in (typs m) i))))) a)
      (fun (j0 : finite (Datatypes.length (typs m))) => 
      W (finite (Datatypes.length (typs m)))
        (fun n0 : finite (Datatypes.length (typs m)) =>
        build_base (var_map m srts (dom_aux pd))
          (typesym_map m srts (dom_aux pd)) (typs m)
          (adt_constrs (fin_nth (typs m) n0)))
        (fun this i0 : finite (Datatypes.length (typs m)) =>
        build_rec (var_map m srts (dom_aux pd))
          (typesym_map m srts (dom_aux pd)) (typs m)
          (adt_name (fin_nth (typs m) i0))
          (adt_constrs (fin_nth (typs m) this))) j0)
      _ _ _ Heq2).
    (*Now we have 2 goals: show that the finite types are
      equivalent, then prove that the values are the same.
      Both involve some awful casts, particularly the first one*)
    subst br_cast.
    match goal with
    | |- tnthS ?x ?y = ?z => assert (Hfin: y = fin); [|rewrite Hfin; clear Hfin]
    end.
    { 
      clear. subst fin.
      unfold cast_a in Heq2. unfold scast in Heq2.
      unfold cast_build_rec.
      (*We need to collapse these casts into one. The dependent
        types are awful, we need to be more generic; we do that here.
        This assertion is as general as we can be with a cast and cast_dep'
        in there*)
      assert (forall vars typesyms i1 i2 (Heqi: i1 = i2) ts c Hinc Hinc2 b1 b2
        (br: build_rec vars typesyms (typs m) ts (adt_constrs (fin_nth (typs m) i1))
          (get_constr_type vars typesyms (typs m) 
          (adt_name (fin_nth (typs m) i1)) (adt_constrs (fin_nth (typs m) i1)) c
          Hinc b1))
        (Heqx: get_constr_type vars typesyms (typs m) 
          (adt_name (fin_nth (typs m) i2)) 
          (adt_constrs (fin_nth (typs m) i2))
          c Hinc2 b2 =(cast_dep
          (fun i : finite (Datatypes.length (typs m)) =>
          build_base vars typesyms (typs m) (adt_constrs (fin_nth (typs m) i)))
          Heqi
          (get_constr_type vars typesyms (typs m)
            (adt_name (fin_nth (typs m) i1))
            (adt_constrs (fin_nth (typs m) i1)) c Hinc b1)))
          ,
        cast (@f_equal _ Type (fun (a: build_base vars typesyms (typs m)
          (adt_constrs (fin_nth (typs m) i2))) =>
          (build_rec vars typesyms (typs m) ts
          (adt_constrs (fin_nth (typs m) i2))) a) _ _ (Logic.eq_sym Heqx))
        (cast_dep' (fun i => build_base vars typesyms (typs m)
          (adt_constrs (fin_nth (typs m) i)))
          (fun i t => build_rec vars typesyms (typs m) ts
            (adt_constrs (fin_nth (typs m) i)) t)
          Heqi
          (get_constr_type vars typesyms (typs m) (adt_name (fin_nth (typs m) i1))
            (adt_constrs (fin_nth (typs m) i1)) c Hinc b1) br) =
          (cast_build_rec_gen (f_equal (fun x => adt_constrs (fin_nth (typs m) x)) Heqi)
            vars typesyms ts _ (adt_name (fin_nth (typs m) i1)) c _ Hinc2 _ b2 br)). {
          clear.
          intros. destruct Heqi.
          simpl.
          unfold cast_dep in Heqx. simpl in Heqx.
          assert (Hinc = Hinc2) by apply bool_irrelevance.
          subst.
          assert (b2 = b1) by (apply get_constr_type_inj2 in Heqx; subst; auto).
          subst.
          assert (Heqx = Logic.eq_refl). {
            (*rely on UIP here*)
            apply UIP.
          }
          subst. simpl.
          rewrite build_rec_finite_inv1. reflexivity.
        }
        (*With that lemma, we can rewrite*)
        rewrite (H (var_map m srts (dom_aux pd))
        (typesym_map m srts (dom_aux pd)) _ _ (cast_i m m_in i) ).
        (*Now we have a [build_rec_to_finite] of a single cast*)
        rewrite build_rec_to_finite_cast.
        2: {
          rewrite (cast_i m m_in i) at 1. reflexivity. }
        (*Finally, no more casting! Just need to show that
          finite types equal*)
        subst br.
        rewrite build_rec_finite_inv2.
        reflexivity.
    }
    (*Now, we show that this really is the nth of [args_to_ind_base].
      This will involve pushing the [tnthS] through the layers,
      introducing many, many casts. Then we simplify at the end*)
    clear Hexeq Heq2 Heq1 Ht.
    unfold args_to_ind_base, args_to_ind_base_aux.
    subst fin.
    (*need a default adt*)
    set (d_adt:= scast (Interp.adts pd m srts t' t_in')
    (dom_cast (dom_aux pd) Heq (hnth j args s_int (dom_int pd)))).
    (*1. Push through [tup_of_list]*)
    rewrite tnthS_tup_of_list with(d:=d_adt).
    (*2. Push through [cast_list]*)
    rewrite cast_list_nth.
    (*3. Push through [hlist_to_list]*)
    assert (Hn2: n <
    Datatypes.length
      (map (IndTypes.sigma m srts)
        (filter
            (rec_occ_fun
              (adt_name (fin_nth (typs m) (get_idx adt_dec t' (typs m) t_in'))))
            (s_args c)))). {
    rewrite map_length. apply Hn'. }
    rewrite hlist_to_list_nth_dec_set' with(Hi:=Hn2)(d1:=s_int)(d2:=dom_int pd).
    2: apply sort_eq_dec.
    (*4. Push through [hlist_map_filter]. Here we need
      the fact that n is [idx_filter j], but annoying the function
      in the [hlist_map_filter] is a bit different (though equal)*)
    subst d_adt.
    assert (Hnalt: n = idx_filter (rec_occ_fun
    (adt_name
      (fin_nth (typs m) (get_idx adt_dec t' (typs m) t_in'))))
      (s_args c) j). {
      subst n. f_equal. rewrite get_idx_correct. reflexivity.
    }
    generalize dependent n; intros. subst n.
    assert (Hnth': nth j (map (IndTypes.sigma m srts) (s_args c)) s_int =
    nth
      (idx_filter
        (rec_occ_fun
            (adt_name (fin_nth (typs m) (get_idx adt_dec t' (typs m) t_in'))))
        (s_args c) j)
      (map (IndTypes.sigma m srts)
        (filter
            (rec_occ_fun
              (adt_name (fin_nth (typs m) (get_idx adt_dec t' (typs m) t_in'))))
            (s_args c))) s_int). {
      rewrite map_nth_inbound with(d2:=vty_int); auto.
      rewrite (map_nth_inbound) with(d2:=vty_int); auto.
      f_equal. rewrite <- Hni. f_equal. f_equal. rewrite get_idx_correct.
      reflexivity.
    }
    rewrite hnth_hlist_map_filter with(d2:=vty_int)(Hij:=Hnth').
    2: apply sort_eq_dec.
    2: {
      rewrite get_idx_correct. auto.
    }
    (*5. Push through [cast_arg_list]*)
    rewrite hnth_cast_arg_list.
    (*Final cast simplification*)
    clear.
    (*Need UIP*)
    assert (forall {A B C D E: Set} x
      (H1: B = A) (H2: C = B) (H3: D = C) (H4: E = D)
      (H5: E = A),
      scast H1 (scast H2 (scast H3 (scast H4 x))) =
      scast H5 x). {
        clear. intros. subst. simpl.
        assert (H5 = eq_refl). apply UIP. subst. reflexivity.
    }
    generalize dependent (hnth j args s_int (dom_int pd)); intros d.
    unfold dom_cast.
    erewrite H.
    rewrite scast_scast. reflexivity.
  }
  (*And we are finally done!*)
  rewrite <- H0. intros X; apply X.
Qed.

End Induction.