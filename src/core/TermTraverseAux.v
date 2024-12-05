Require Import TermDefs TermFuncs.
Set Bullet Behavior "Strict Subproofs".


(*Termination proofs for [t_traverse]*)

Lemma t_subst_unsafe_aux_rewrite m t:
  t_subst_unsafe_aux m t =
  match (t_node_of t) with
  | Tvar u => (t_attr_copy t (Mvs.find_def _ t u m))
  | Tlet e (v, b, t2) =>
    let e1 := (t_subst_unsafe_aux m e) in 
    let m' := Mvs.remove _ v m in
    let m1 := Mvs.set_inter _ _ m' b.(bv_vars) in
    let e2 := if Mvs.is_empty _ m1 then t2 else t_subst_unsafe_aux m1 t2 in
    let b1 := bnd_new (Mvs.remove _ v (t_vars e2)) in 
    t_attr_copy t (t_let1 e1 (v, b1, e2) (t_ty_of t))
  | Tcase e bl =>
    let e1 := (t_subst_unsafe_aux m e) in
    let bl2 := map
      (fun (x: pattern_c * bind_info * term_c) =>
        let m' := Mvs.set_diff _ _ m (pat_vars_of (fst (fst x))) in
        let m1 := Mvs.set_inter _ _ m' (snd (fst x)).(bv_vars) in
        let e2 := if Mvs.is_empty _ m1 then snd x else t_subst_unsafe_aux m1 (snd x) in
        let b1 := bnd_new (Mvs.set_diff _ _ (t_vars e2) (pat_vars_of (fst (fst x)))) in
        (fst (fst x), b1, e2)
        ) bl in
    t_attr_copy t (t_case1 e1 bl2 (t_ty_of t))
  | Teps (v, b, t1) =>
    let m' := Mvs.remove _ v m in
    let m1 := Mvs.set_inter _ _ m' b.(bv_vars) in
    let e2 := if Mvs.is_empty _ m1 then t1 else t_subst_unsafe_aux m1 t1 in
    let b1 := bnd_new (Mvs.remove _ v (t_vars e2)) in
    t_attr_copy t (t_eps1 (v, b1, e2) (t_ty_of t))
  | Tquant q (vs, b, tr, t1) =>
    let m' := Mvs.set_diff _ _ m (Svs.of_list vs) in
    let m1 := Mvs.set_inter _ _ m' b.(bv_vars) in
    let e2 := if Mvs.is_empty _ m1 then t1 else t_subst_unsafe_aux m1 t1 in
    let b1 := bnd_new (Mvs.set_diff _ _ (t_vars e2) (Svs.of_list vs)) in
    let tr2 := (tr_map (t_subst_unsafe_aux m) tr) in
    t_attr_copy t (t_quant1 q (vs, b1, tr2, e2))
  | _ => t_map_unsafe (t_subst_unsafe_aux m) t
  end.
Proof. destruct t; reflexivity. Qed.

(*The size function*)

Fixpoint term_size (t: term_c) : nat :=
  match t_node_of t with
  | Tvar _ => 1
  | Tconst _ => 1
  | Tapp _ tms => 1 + sum (map term_size tms)
  | Tif t1 t2 t3 => 1 + term_size t1 + term_size t2 + term_size t3
  | Tlet t1 (_, _, t2) => 1 + term_size t1 + term_size t2
  | Tcase t1 pats => 1 + term_size t1 + sum (map (fun x => term_size (snd x)) pats)
  | Teps (_, _, t) => 1 + term_size t
  | Tquant _ (_, _, tr, t) => 1 + term_size t + sum (map (fun l => sum (map term_size l)) tr) 
  | Tbinop _ t1 t2 => 1 + term_size t1 + term_size t2
  | Tnot t => 1 + term_size t
  | Ttrue => 1
  | Tfalse => 1
  end.

Definition term_node_size (t: term_node) : nat :=
  match t with
  | Tvar _ => 1
  | Tconst _ => 1
  | Tapp _ tms => 1 + sum (map term_size tms)
  | Tif t1 t2 t3 => 1 + term_size t1 + term_size t2 + term_size t3
  | Tlet t1 (_, _, t2) => 1 + term_size t1 + term_size t2
  | Tcase t1 pats => 1 + term_size t1 + sum (map (fun x => term_size (snd x)) pats)
  | Teps (_, _, t) => 1 + term_size t
  | Tquant _ (_, _, tr, t) => 1 + term_size t + sum (map (fun l => sum (map term_size l)) tr) 
  | Tbinop _ t1 t2 => 1 + term_size t1 + term_size t2
  | Tnot t => 1 + term_size t
  | Ttrue => 1
  | Tfalse => 1
  end.

Lemma term_size_eq tm: term_size tm = term_node_size (t_node_of tm).
Proof. destruct tm; reflexivity. Qed.

(*Part 1: Generic results about [term_size]*)

(*There are a few complications that make a traversal function difficult to write.
  1. The size function recurses on the term node, so we don't have a straightforward
    rewrite/inversion principle. Instead, we manually prove lemmas for each case
  2. [t_subst_unsafe] uses [t_attr_copy], which means that it isn't even really structurally
    recursive only on the term_nodes. To deal with this, we need an alternate induction principle
    (see TermDefs.v)
  3. [t_attr_copy] does more than just copy the attributes; it also checks for similarity, for example.
    Terms that are [t_similar] do have the same size, but this is NOT trivial to show.
    To do this, we define a more general predicate that terms have the same "shape", show that this
    implies that they have the same size, and show that [t_similar] (and [t_attr_copy]) terms have
    the same shape. *)

Lemma term_size_nodes t1 t2:
  t_node_of t1 = t_node_of t2 ->
  term_size t1 = term_size t2.
Proof.
  rewrite !term_size_eq.
  intros Heq; rewrite Heq; reflexivity.
Qed.

(*Notion of "same shape" for terms*)
Fixpoint t_shape (t1 t2: term_c) {struct t1} : bool :=
  match t_node_of t1, t_node_of t2 with
  | Tconst _, Tconst _ => true
  | Tvar _, Tvar _ => true
  | Tapp l1 tms1, Tapp l2 tms2 => ls_equal l1 l2 && (length tms1 =? length tms2) && all2 t_shape tms1 tms2
  | Tlet t1 (_, _, t2), Tlet t3 (_, _, t4) => t_shape t1 t3 && t_shape t2 t4
  | Tif t1 t2 t3, Tif t4 t5 t6 => t_shape t1 t4 && t_shape t2 t5 && t_shape t3 t6
  | Tcase t1 b1, Tcase t2 b2 => t_shape t1 t2 && (length b1 =? length b2) &&
   forallb (fun x => x) (CommonList.map2 (fun x y => t_shape (snd x) (snd y)) b1 b2)
  | Teps (_, _, t1), Teps (_, _, t2) => t_shape t1 t2
  | Tquant q1 (_, _, tr1, t1), Tquant q2 (_, _, tr2, t2) => quant_eqb q1 q2 && 
    t_shape t1 t2 && (length tr1 =? length tr2) &&
      all2 (fun x y => length x =? length y) tr1 tr2 && all2 (all2 t_shape) tr1 tr2
  | Tbinop b1 t1 t2, Tbinop b2 t3 t4 => binop_eqb b1 b2 && t_shape t1 t3 && t_shape t2 t4
  | Tnot t1, Tnot t2 => t_shape t1 t2
  | Ttrue, Ttrue => true
  | Tfalse, Tfalse => true
  | _, _ => false
  end.

(*The fact that these functions are not really structurally recursive is very annoying*)
Ltac prove_shape t1 t2:=
  intros Hshape Heq;
  destruct t1 as [n1 ? ? ?]; destruct t2 as [n2 ? ? ?]; destruct n1; try solve[inversion Heq];
  simpl in Hshape; destruct n2; try discriminate; eauto.

Lemma t_shape_var {t1 t2 v}:
  t_shape t1 t2 ->
  t_node_of t1 = Tvar v ->
  exists v1, t_node_of t2 = Tvar v1.
Proof.
  prove_shape t1 t2.
Qed.

Lemma t_shape_const {t1 t2 c}:
  t_shape t1 t2 ->
  t_node_of t1 = Tconst c ->
  exists c1, t_node_of t2 = Tconst c1.
Proof.
  prove_shape t1 t2.
Qed.

Lemma t_shape_app {t1 t2 l tms}:
  t_shape t1 t2 ->
  t_node_of t1 = Tapp l tms ->
  exists tms2, t_node_of t2 = Tapp l tms2 /\ length tms = length tms2 /\ all2 t_shape tms tms2.
Proof.
  prove_shape t1 t2.
  apply andb_true_iff in Hshape.
  destruct Hshape as [Hls Hall].
  apply andb_true_iff in Hls.
  destruct Hls as [Hls Hlen].
  simpl. unfold ls_equal in Hls. apply lsymbol_eqb_eq in Hls. subst.
  simpl in Heq. inversion Heq; subst.
  apply Nat.eqb_eq in Hlen. eauto.
Qed.

Lemma t_shape_if {t1 t2 tm1 tm2 tm3}:
  t_shape t1 t2 ->
  t_node_of t1 = Tif tm1 tm2 tm3 ->
  exists e1 e2 e3, t_node_of t2 = Tif e1 e2 e3 /\ t_shape tm1 e1 /\ t_shape tm2 e2 /\ t_shape tm3 e3.
Proof.
  prove_shape t1 t2.
  bool_hyps. simpl in Heq. inversion Heq; subst. simpl. 
  repeat eexists; eauto.
Qed.

Lemma t_shape_let {t1 t2 tm1 v1 b1 tm2}:
  t_shape t1 t2 ->
  t_node_of t1 = Tlet tm1 (v1, b1, tm2) ->
  exists e1 v2 b2 e2, t_node_of t2 = Tlet e1 (v2, b2, e2)  /\ t_shape tm1 e1 /\ t_shape tm2 e2.
Proof.
  intros Hshape Heq. 
  destruct t1 as [n1 ? ? ?]; destruct t2 as [n2 ? ? ?]; destruct n1; try solve[inversion Heq].
  simpl in Hshape. destruct p as [[v2 b2] e2]. destruct n2; try solve[inversion Hshape].
  destruct p as [[v3 b3] e3]. simpl in Heq. inversion Heq; subst; clear Heq.
  bool_hyps. simpl. repeat eexists; eauto.
Qed.

Lemma t_shape_case {t1 t2 tm1 tbs}:
  t_shape t1 t2 ->
  t_node_of t1 = Tcase tm1 tbs ->
  exists tm2 tbs2, t_node_of t2 = Tcase tm2 tbs2 /\ t_shape tm1 tm2 /\ length tbs = length tbs2 /\ 
    all2 t_shape (map snd tbs) (map snd tbs2).
Proof.
  prove_shape t1 t2.
  apply andb_true_iff in Hshape.
  destruct Hshape as [Hls Hall].
  apply andb_true_iff in Hls.
  destruct Hls as [Hshape Hlen].
  simpl. apply Nat.eqb_eq in Hlen. unfold all2. setoid_rewrite map2_map.
  simpl in Heq. inversion Heq; subst.
  repeat eexists; eauto.
Qed.

Lemma t_shape_eps {t1 t2 v1 b1 tm1}:
  t_shape t1 t2 ->
  t_node_of t1 = Teps (v1, b1, tm1) ->
  exists v2 b2 e2, t_node_of t2 = Teps (v2, b2, e2) /\ t_shape tm1 e2.
Proof.
  intros Hshape Heq. 
  destruct t1 as [n1 ? ? ?]; destruct t2 as [n2 ? ? ?]; destruct n1; try solve[inversion Heq].
  simpl in Hshape. destruct p as [[v2 b2] e2]. destruct n2; try solve[inversion Hshape].
  destruct p as [[v3 b3] e3]. simpl in Heq. inversion Heq; subst; clear Heq.
  bool_hyps. simpl. repeat eexists; eauto.
Qed.

Lemma t_shape_quant {t1 t2 q vs1 b1 tr1 tm1}:
  t_shape t1 t2 ->
  t_node_of t1 = Tquant q (vs1, b1, tr1, tm1) ->
  exists vs2 b2 tr2 tm2, t_node_of t2 = Tquant q (vs2, b2, tr2, tm2) /\ t_shape tm1 tm2 /\
  length tr1 = length tr2 /\ all2 (fun x y => length x =? length y) tr1 tr2 /\ 
  all2 (all2 t_shape) tr1 tr2.
Proof.
  intros Hshape Heq. 
  destruct t1 as [n1 ? ? ?]; destruct t2 as [n2 ? ? ?]; destruct n1; try solve[inversion Heq].
  simpl in Hshape. destruct p as [[[vs2 b2] tr2] e2]. destruct n2; try solve[inversion Hshape].
  destruct p as [[[vs3 b3] tr3] e3]. simpl in Heq. inversion Heq; subst; clear Heq.
  bool_hyps. apply quant_eqb_eq in H. subst. apply Nat.eqb_eq in H2. simpl. repeat eexists; eauto.
Qed.

Lemma t_shape_binop {t1 t2 b tm1 tm2}:
  t_shape t1 t2 ->
  t_node_of t1 = Tbinop b tm1 tm2 ->
  exists e1 e2, t_node_of t2 = Tbinop b e1 e2 /\ t_shape tm1 e1 /\ t_shape tm2 e2.
Proof.
  prove_shape t1 t2.
  bool_hyps. apply binop_eqb_eq in H. subst. simpl in Heq. inversion Heq; subst. simpl. 
  repeat eexists; eauto.
Qed.

Lemma t_shape_not {t1 t2 tm1}:
  t_shape t1 t2 ->
  t_node_of t1 = Tnot tm1 ->
  exists tm2, t_node_of t2 = Tnot tm2 /\ t_shape tm1 tm2.
Proof.
  prove_shape t1 t2. simpl in Heq. inversion Heq; subst. eauto.
Qed.

Lemma t_shape_true {t1 t2}:
  t_shape t1 t2 ->
  t_node_of t1 = Ttrue ->
  t_node_of t2 = Ttrue.
Proof.
  prove_shape t1 t2.
Qed.

Lemma t_shape_false {t1 t2}:
  t_shape t1 t2 ->
  t_node_of t1 = Tfalse ->
  t_node_of t2 = Tfalse.
Proof.
  prove_shape t1 t2.
Qed.

(*And therefore, terms with the same shape have the same size*)
Lemma t_shape_size (t1 t2: term_c):
  t_shape t1 t2 ->
  term_size t1 = term_size t2.
Proof.
  revert t2.
  apply (term_ind_alt (fun t1 => forall t2 (Hshape: t_shape t1 t2), term_size t1 = term_size t2)); clear;
  intros.
  - destruct (t_shape_var Hshape Heq) as [v1 Heq2]. 
    rewrite !term_size_eq, Heq, Heq2. reflexivity.
  - destruct (t_shape_const Hshape Heq) as [c1 Heq2].
    rewrite !term_size_eq, Heq, Heq2. reflexivity.
  - destruct (t_shape_app Hshape Heq) as [tms1 [Heq2 [Hlen Hall]]].
    rewrite !term_size_eq, Heq, Heq2. simpl.
    f_equal. f_equal.
    clear Heq Heq2 Hshape. generalize dependent tms1.
    induction ts as [| thd ttl IH]; intros [| h2 tl2]; try discriminate; auto.
    simpl. intros Hlen. rewrite all2_cons. intros Hshape.
    bool_hyps. inversion H; subst. f_equal; auto.
  - destruct (t_shape_if Hshape Heq) as [e1 [e2 [e3 [Heq2 [Hshape1 [Hshape2 Hshape3]]]]]].
    rewrite !term_size_eq, Heq, Heq2. simpl. f_equal. f_equal; [f_equal |]; eauto.
  - destruct (t_shape_let Hshape Heq) as [e1 [v1 [b1 [e2 [Heq2 [Hshape1 Hshape2]]]]]].
    rewrite !term_size_eq, Heq, Heq2; simpl. f_equal. f_equal; auto.
  - destruct (t_shape_case Hshape Heq) as [tm2 [tbs2 [Heq2 [Hshape1 [Hlen Hall]]]]].
    rewrite !term_size_eq, Heq, Heq2; simpl. f_equal.
    f_equal; eauto. f_equal.
    rewrite all2_map in Hall.
    clear Heq Heq2 Hshape1 H. generalize dependent tbs2. induction tbs as [| h1 tl1 IH];
    intros [| h2 tl2]; try discriminate; auto; simpl.
    intros Hlen. rewrite all2_cons. intros Hall. bool_hyps. inversion H0; subst; f_equal; eauto.
  - destruct (t_shape_eps Hshape Heq) as [v2 [b2 [e2 [Heq2 Hshape2]]]].
    rewrite !term_size_eq, Heq, Heq2; simpl. eauto.
  - destruct (t_shape_quant Hshape Heq) as [vs2 [b2 [tr2 [tm2 [Heq2 [Hshape2 [Hlen [Htrlen Htrs]]]]]]]].
    rewrite !term_size_eq, Heq, Heq2. simpl. f_equal. f_equal; auto.
    f_equal. clear -Hlen Htrs Htrlen H.
    generalize dependent tr2. induction tr as [| h1 t1 IH]; simpl; auto;
    intros [| h2 t2]; try discriminate; auto.
    simpl. intros Hlen. rewrite !all2_cons. intros Halllen Hall. 
    apply andb_true_iff in Halllen, Hall. destruct Hall as [Hshapeh Hshapet].
    destruct Halllen as [Hlenh Hlent].
    inversion H; subst.
    f_equal; auto.
    clear -H2 Hshapeh Hlenh.
    (*TODO: should have better way to do this*)
    generalize dependent h2.
    induction h1 as [| x1 t1 IH]; intros [| x2 t2]; simpl; auto; try discriminate.
    intros Hlen. rewrite all2_cons. intros Hall. apply andb_true_iff in Hall; destruct Hall
    as [Hshapex Hshapet]; inversion H2; subst; f_equal; auto.
  - destruct (t_shape_binop Hshape Heq) as [e1 [e2 [Heq2 [Hshape1 Hshape2]]]].
    rewrite !term_size_eq, Heq, Heq2; simpl; auto.
  - destruct (t_shape_not Hshape Heq) as [tm2 [Heq2 Hshape2]];
    rewrite !term_size_eq, Heq, Heq2; simpl; auto.
  - rewrite !term_size_eq, Ht, (t_shape_true Hshape Ht). reflexivity.
  - rewrite !term_size_eq, Ht, (t_shape_false Hshape Ht). reflexivity.
Qed. 

(*Need a few more results before similar -> shape*)

Lemma all2_len_eq {A: Type} (l: list (list A)):
  all2 (fun x y => length x =? length y) l l.
Proof.
  induction l as [| h t IH]; simpl; auto.
  rewrite all2_cons; apply andb_true_iff; split; auto.
  rewrite Nat.eqb_refl; auto.
Qed.

Lemma t_shape_refl t:
  t_shape t t.
Proof.
  apply (term_ind_alt (fun t1 => t_shape t1 t1)); clear; auto;
  intros; destruct t as [n1 ty1 a1 p1]; simpl in *; subst; auto;
  try solve[unfold is_true; rewrite !andb_true_iff; split_all; auto].
  - rewrite Nat.eqb_refl.
    solve_bool. apply andb_true_iff. split; [apply lsymbol_eqb_eq; auto |].
    induction ts as [| h1 t1 IH]; simpl; auto.
    rewrite all2_cons. inversion H; subst. apply andb_true_iff; auto.
  - rewrite Nat.eqb_refl. solve_bool. apply andb_true_iff; split; auto.
    induction tbs as [| h1 tl1 IH]; simpl; auto.
    inversion H0; subst; apply andb_true_iff; split; auto.
  - unfold is_true. rewrite !andb_true_iff; split_all; auto.
    + apply quant_eqb_eq; auto.
    + rewrite Nat.eqb_refl; auto.
    + apply all2_len_eq. 
    + clear -H. induction tr as [| h t IH]; auto. rewrite all2_cons. inversion H; subst.
      apply andb_true_iff; split; auto. clear -H2.
      induction h as [| h t IH]; simpl; auto. rewrite all2_cons. inversion H2; subst.
      apply andb_true_iff; split; auto.
  - unfold is_true; rewrite !andb_true_iff; split_all; auto.
    apply binop_eqb_eq; auto.
Qed. 
  
Lemma all2_shape_refl l:
  all2 t_shape l l.
Proof.
  induction l as [| h1 t1 IH]; auto.
  rewrite all2_cons, t_shape_refl; auto.
Qed.

Lemma all2_all2_shape_refl l:
  all2 (all2 t_shape) l l.
Proof.
  induction l as [| h1 t1 IH]; auto.
  rewrite all2_cons, all2_shape_refl. auto.
Qed.

Lemma t_shape_node t1 t2:
  t_node_of t1 = t_node_of t2 ->
  t_shape t1 t2.
Proof.
  revert t2. apply (term_ind_alt (fun t1 => forall t2 (Hnode: t_node_of t1 = t_node_of t2), t_shape t1 t2));
  clear; auto; intros; destruct t as [n1 ty1 a1 p1]; simpl in *; subst; try rewrite <- Hnode; auto;
  try rewrite !t_shape_refl; auto.
  - rewrite Nat.eqb_refl.
    solve_bool. apply andb_true_iff. split; [apply lsymbol_eqb_eq; auto |].
    apply all2_shape_refl.
  - simpl. rewrite Nat.eqb_refl. simpl. clear -H0. induction tbs as [| h2 tl2 IH]; simpl; auto.
    inversion H0; subst.
    rewrite t_shape_refl; auto.
  - rewrite Nat.eqb_refl, all2_len_eq, all2_all2_shape_refl, !andb_true_r.
    apply quant_eqb_eq; auto.
  - rewrite !andb_true_r. apply binop_eqb_eq; auto. 
Qed.

(*Similar nodes have the same shape*)
Lemma t_similar_shape t1 t2:
  t_similar t1 t2 ->
  t_shape t1 t2.
Proof.
  unfold t_similar.
  destruct (oty_equal (t_ty_of t1) (t_ty_of t2)) eqn : Hopt; simpl; [|discriminate].
  destruct t1 as [n1 ty1 a1 p1]; destruct t2 as [n2 ty2 a2 p2].
  simpl.
  destruct n1; destruct n2; auto; unfold is_true; try rewrite !andb_true_iff;
  try unfold term_eqb_fast; try unfold term_bound_eqb_fast.
  - intros [Heq Hlisteq]. apply lsymbol_eqb_eq in Heq. subst.
    apply list_eqb_eq in Hlisteq; [| apply term_eqb_eq].
    subst. rewrite Nat.eqb_refl. split_all; auto.
    apply lsymbol_eqb_eq; auto.
    apply all2_shape_refl.
  - intros [[Heq1 Heq2] Heq3].
    apply term_eqb_eq in Heq1, Heq2, Heq3. subst. split_all; apply t_shape_refl.
  - intros [Heq1 Heq2].
    apply term_eqb_eq in Heq1. apply term_bound_eqb_eq in Heq2. subst.
    destruct p0 as [[v2 b2] t2]; rewrite !t_shape_refl; auto.
  - intros [Heq1 Heq2]. apply term_eqb_eq in Heq1. apply list_eqb_eq in Heq2; [| apply term_branch_eqb_eq];
    subst. rewrite Nat.eqb_refl, t_shape_refl. split_all; auto.
    clear. induction l0 as [| h1 t1 IH]; simpl; auto. rewrite t_shape_refl; auto.
  - intros Heq. apply term_bound_eqb_eq in Heq; subst.
    destruct p0 as [[v2 b2] t2]; apply t_shape_refl.
  - intros [Heq1 Heq2]. apply term_quant_eqb_eq in Heq2. subst.
    destruct p0 as [[[vs1 b1] tr1] t1].
    rewrite t_shape_refl, Nat.eqb_refl, all2_len_eq, all2_all2_shape_refl, !andb_true_r; auto.
  - intros [[Heq1 Heq2] Heq3].
    apply term_eqb_eq in Heq2, Heq3. subst. rewrite !t_shape_refl. split_all; auto.
  - intros Heq. apply term_eqb_eq in Heq; subst; apply t_shape_refl.
Qed.

Lemma t_attr_copy_shape t1 t2:
  t_shape (t_attr_copy t1 t2) t2.
Proof.
  unfold t_attr_copy.
  destruct (t_similar t1 t2 && Sattr.is_empty (t_attrs_of t2) &&
    negb (isSome (t_loc_of t2))) eqn : Hcond.
  - bool_hyps. apply t_similar_shape; auto.
  - apply t_shape_node. reflexivity.
Qed.

(*Therefore, size is the same*)
Lemma term_size_attr_copy t1 t2: term_size (t_attr_copy t1 t2) = term_size t2.
Proof.
  apply t_shape_size, t_attr_copy_shape.
Qed.

(*Finally, we can prove that substitution preserves size, though we need 2 results 
for the map invariant preservation:*)

(*The map change we need for several cases*)
Lemma subst_vars_ok1 {A: Type} (P: A -> Prop) (m1: Mvs.t A) x y
  (Hm1: forall v t1, Mvs.find_opt v m1 = Some t1 -> P t1):
  forall v t1, Mvs.find_opt v (Mvs.set_inter A CoqBigInt.t (Mvs.remove A x m1) y) = Some t1 ->
  P t1.
Proof.
  intros v1 t1. rewrite Mvs.set_inter_spec, Mvs.remove_spec.
  destruct (Vsym.Tg.equal v1 x); [discriminate|].
  destruct (Mvs.find_opt v1 m1) as [v2|] eqn : Hget; [|discriminate].
  destruct (Mvs.find_opt v1 y); [|discriminate]. intros Hsome; inversion Hsome; subst.
  apply (Hm1 _ _ Hget).
Qed.

Lemma subst_vars_ok2 {A: Type} (P: A -> Prop) (m1: Mvs.t A) x y
  (Hm1: forall v t1, Mvs.find_opt v m1 = Some t1 -> P t1):
  forall v t1, Mvs.find_opt v (Mvs.set_inter A CoqBigInt.t (Mvs.set_diff A unit m1 x) y) = Some t1 ->
  P t1.
Proof.
  intros v1 t1. rewrite Mvs.set_inter_spec, Mvs.set_diff_spec.
  destruct (Mvs.find_opt v1 m1) as [v2|] eqn : Hget; [|discriminate].
  destruct (Mvs.find_opt v1 x); [discriminate |].
  destruct (Mvs.find_opt v1 y); [|discriminate].
  intros Hsome; inversion Hsome; subst. apply (Hm1 _ _ Hget).
Qed.

(*Why we needed all of the above:*)
Lemma t_subst_unsafe_size m1 t (Hm1: forall v t1, Mvs.find_opt v m1 = Some t1 -> term_size t1 = 1): 
  term_size (t_subst_unsafe m1 t) = term_size t.
Proof.
  unfold t_subst_unsafe.
  destruct (Mvs.is_empty term_c m1); auto. (*we don't care about result*)
  revert m1 Hm1.
  apply term_ind_alt with  (P:=fun t1 => forall m1 
    (Hm1: forall v t1, Mvs.find_opt v m1 = Some t1 -> term_size t1 = 1),
    term_size (t_subst_unsafe_aux m1 t1) = term_size t1); clear t.
  - (*var*) intros. rewrite t_subst_unsafe_aux_rewrite, Heq; simpl.
    rewrite term_size_attr_copy.
    rewrite Mvs.find_def_spec.
    destruct (Mvs.find_opt v m1) as [v1|] eqn : Hfind; auto.
    apply Hm1 in Hfind. rewrite Hfind. 
    rewrite term_size_eq, Heq. reflexivity.
  - (*const*) intros. rewrite t_subst_unsafe_aux_rewrite, Heq.
    unfold t_map_unsafe. rewrite term_size_attr_copy, Heq. reflexivity.
  - (*app*) intros ls tms t2 Heq Hall m1 Hm1.
    rewrite t_subst_unsafe_aux_rewrite, Heq.
    unfold t_map_unsafe. rewrite term_size_attr_copy, Heq. simpl.
    rewrite term_size_eq, Heq. simpl. f_equal. f_equal.
    clear -Hall Hm1. induction tms as [| h1 t1 IH]; simpl; auto.
    inversion Hall; subst; f_equal; auto.
  - (*if*) intros t1 t2 t3 tm2 Heq IH1 IH2 IH3 m1 Hm1.
    rewrite (term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    unfold t_map_unsafe; rewrite term_size_attr_copy, Heq. simpl.
    f_equal. f_equal; [f_equal| ]; auto.
  - (*let*) intros t1 v b t2 tm2 Heq IH1 IH2 m1 Hm1.
    rewrite (term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    simpl. rewrite term_size_attr_copy. simpl.
    f_equal. f_equal; auto.
    destruct (Mvs.is_empty term_c _) eqn : Hisemp; auto.
    apply IH2.
    (*Need to know that property still holds - really just that everything in set_inter and remove
      is in original*)
    apply subst_vars_ok1; auto.
  - (*case*) intros t1 tbs tm2 Heq IH1 IH2 m1 Hm1.
    rewrite (term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    simpl. rewrite term_size_attr_copy. simpl. f_equal. f_equal.
    + apply IH1; auto.
    + f_equal. (*Prove that all are equal*) clear -Hm1 IH2.
      induction tbs as [| tb1 tbtl IH]; simpl; auto.
      inversion IH2; subst; auto. f_equal; auto.
      destruct (Mvs.is_empty _); auto.
      apply H1.
      apply subst_vars_ok2; auto.
  - (*eps*)
    intros v b t1 tm2 Heq IH m1 Hm1.
    rewrite (term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    simpl. rewrite term_size_attr_copy. simpl. f_equal.
    destruct (Mvs.is_empty _); auto.
    apply IH.  apply subst_vars_ok1; auto.
  - (*quant*) intros q vs b tr t1 tm2 Heq IH1 IH2 m1 Hm1.
    rewrite (term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    simpl. rewrite term_size_attr_copy. simpl. f_equal.
    destruct (Mvs.is_empty _); auto.
    + f_equal; auto. f_equal.
      clear -IH1 Hm1. induction tr as [| l1 t1 IH]; simpl; auto.
      inversion IH1; subst. f_equal; auto.
      clear -H1 Hm1. induction l1 as [| h1 t1 IH]; simpl; auto.
      inversion H1; subst; auto.
    + f_equal.
      * apply IH2, subst_vars_ok2; auto.
      * f_equal. clear -IH1 Hm1. induction tr as [| l1 t1 IH]; simpl; auto.
        inversion IH1; subst. f_equal; auto.
        clear -H1 Hm1. induction l1 as [| h1 t1 IH]; simpl; auto.
        inversion H1; subst; auto.
  - (*binop*) intros b t1 t2 tm2 Heq IH1 IH2 m1 Hm1.
    rewrite (term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    unfold t_map_unsafe. rewrite term_size_attr_copy, Heq. simpl.
    f_equal; auto.
  - (*not*) intros t1 tm2 Heq IH m1 Hm1.
    rewrite (term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    unfold t_map_unsafe. rewrite term_size_attr_copy, Heq. simpl.
    f_equal; auto.
  - (*true*) intros tm2 Heq m1 Hm1. 
    rewrite !(term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    unfold t_map_unsafe. rewrite term_size_attr_copy, term_size_eq, !Heq.
    reflexivity.
  - (*false*) intros tm2 Heq m1 Hm1. 
    rewrite !(term_size_eq tm2), t_subst_unsafe_aux_rewrite, Heq.
    unfold t_map_unsafe. rewrite term_size_attr_copy, term_size_eq, !Heq.
    reflexivity.
Qed.

(*Now, we prove the lemmas for each case in [tm_traverse]:*)

(*if cases*)

Lemma tif_size1 {t1 t2 t3 tm}
  (Hsz : term_node_size (Tif t1 t2 t3) = term_size tm):
  term_size t1 < term_size tm.
Proof.
  simpl in Hsz. lia.
Qed.

Lemma tif_size3 {t1 t2 t3 tm}
  (Hsz : term_node_size (Tif t1 t2 t3) = term_size tm):
  term_size t3 < term_size tm.
Proof.
  simpl in Hsz. lia.
Qed.

Lemma tif_size2 {t1 t2 t3 tm}
  (Hsz : term_node_size (Tif t1 t2 t3) = term_size tm):
  term_size t2 < term_size tm.
Proof.
  simpl in Hsz. lia.
Qed.

(*The bound cases are the intersting ones:*)

Lemma t_open_bound_size (b: term_bound): forall s,
  term_size (snd (fst (runState (t_open_bound b) s))) = term_size (snd b).
Proof.
  intros s. destruct b as [[v b] t].
  Opaque vs_rename.
  simpl.
  destruct (runState (vs_rename Mvs.empty v) s) as [[m1 v1] s1] eqn : Hrun.
  simpl.
  (*Get m1 value*)
  Transparent vs_rename. Opaque fresh_vsymbol.
  simpl in Hrun.
  destruct (runState (fresh_vsymbol v) s) as [v3 s3] eqn : Hrun3.
  inversion Hrun; subst.
  (*We don't care that the variable is fresh, but we care that it is a variable*)
  apply t_subst_unsafe_size.
  intros v2 tm1. rewrite Mvs.add_spec, Mvs.empty_spec.
  destruct (Vsym.Tg.equal v2 v); [|discriminate].
  intros Hsome; inversion Hsome; subst. reflexivity.
Qed.

(*Interesting case - why we need dependent bind*)
Lemma dep_bnd_size_bound {St b y s}
(Heq : forall z : vsymbol * term_c,
  fst
  (run_errState
  (@errst_tup1 CoqBigInt.t St _ (errst_lift1 (t_open_bound b))) s) =
  inr z -> y = z):
term_size (snd y) = term_size (snd b).
Proof.
  unfold errst_tup1 in Heq. Opaque t_open_bound. simpl in Heq.
  unfold run_errState in Heq. simpl in Heq.
  destruct (runState (t_open_bound b) (fst s)) as [v1 s1] eqn : Hrun.
  simpl in Heq.
  specialize (Heq v1 eq_refl). subst.
  (*Now we just need to reason about [t_open_bound] and its size*)
  pose proof (t_open_bound_size b (fst s)) as Hszb.
  rewrite Hrun in Hszb. simpl in Hszb.
  auto.
Qed.

(*And the branch version*)

Lemma t_open_branch_size (b: term_branch): forall s,
  term_size (snd (fst (runState (t_open_branch b) s))) = term_size (snd b).
Proof.
  intros s. destruct b as [[v b] t].
  Opaque pat_rename.
  simpl.
  destruct (runState (pat_rename Mvs.empty v) s) as [[m1 v1] s1] eqn : Hrun.
  simpl.
  (*Get m1 value*)
  Transparent pat_rename. Opaque add_vars.
  simpl in Hrun.
  destruct (runState (add_vars (Svs.elements (pat_vars_of v))) s) as [v3 s3] eqn : Hrun3.
  inversion Hrun; subst.
  (*We don't care that the variable is fresh, but we care that it is a variable*)
  apply t_subst_unsafe_size.
  intros v2 tm1. rewrite Mvs.union_spec; auto.
  rewrite Mvs.empty_spec.
  destruct (Mvs.find_opt v2 (Mvs.map t_var v3)) as [l2|] eqn : Hfind; [|discriminate].
  intros Hsome; inversion Hsome; subst.
  apply Mvs.map_spec in Hfind.
  destruct Hfind as [k1 [v1 [Heqv [Hfind Htm1]]]]; subst.
  reflexivity.
Qed.

Lemma dep_bnd_size_branch {St b y s}
(Heq: forall z : pattern_c * term_c,
    fst
    (run_errState
    (@errst_tup1 CoqBigInt.t St _ (errst_lift1 (t_open_branch b))) s) =
    inr z -> y = z):
term_size (snd y) = term_size (snd b).
Proof.
  unfold errst_tup1 in Heq. Opaque t_open_branch. simpl in Heq.
  unfold run_errState in Heq. simpl in Heq.
  destruct (runState (t_open_branch b) (fst s)) as [v1 s1] eqn : Hrun.
  simpl in Heq.
  specialize (Heq v1 eq_refl). subst.
  pose proof (t_open_branch_size b (fst s)) as Hszb.
  rewrite Hrun in Hszb. simpl in Hszb. auto.
Qed.

(*let cases*)

Lemma tlet_size2 {St t1 b y s tm}
(Hsz: term_node_size (Tlet t1 b) = term_size tm)
(Heq : forall z : vsymbol * term_c,
  fst
  (run_errState
  (@errst_tup1 CoqBigInt.t St _ (errst_lift1 (t_open_bound b))) s) =
  inr z -> y = z):
  term_size (snd y) < term_size tm.
Proof.
  rewrite (dep_bnd_size_bound Heq).
  simpl in Hsz. destruct b as [[b1 b2] b3]; simpl. lia.
Qed.

Lemma tlet_size1 {t1 b tm1}
  (Hsz: term_node_size (Tlet t1 b) = term_size tm1): 
  term_size t1 < term_size tm1.
Proof.
  simpl in Hsz. destruct b as [[b1 b2] b3]. lia.
Qed.

(*app case*)

Lemma sum_in_lt l n:
  In n l ->
  n <= sum l.
Proof.
  induction l as [| h t IH]; simpl; auto; [contradiction|].
  intros [Hn | Hin]; subst; try lia.
  apply IH in Hin; lia.
Qed.

Lemma tapp_size {l ts tm1}
  (Hsz: term_node_size (Tapp l ts) = term_size tm1):
  Forall (fun t => term_size t < term_size tm1) ts.
Proof.
  simpl in Hsz. rewrite Forall_forall. intros x Hinx.
  pose proof (sum_in_lt (map term_size ts) (term_size x)) as Hlt.
  forward Hlt.
  { rewrite in_map_iff; eauto. }
  lia.
Qed.

(*match cases*)

Lemma tmatch_size2 {St tm1 s y b}
  (Hx: term_size (snd b) < term_size tm1)
  (*(Hsz: term_node_size (Tcase t1 tbs)) (*TODO: do we need?*)*)
  (Heq: forall z : pattern_c * term_c,
    fst
    (run_errState
    (@errst_tup1 CoqBigInt.t St _ (errst_lift1 (t_open_branch b))) s) =
    inr z -> y = z):
  term_size (snd y) < term_size tm1.
Proof.
  rewrite (dep_bnd_size_branch Heq). auto.
Qed.

Lemma tmatch_size3 {tm1 t1 tbs}
  (Hsz: term_node_size (Tcase t1 tbs) = term_size tm1):
  Forall (fun x => term_size (snd x) < term_size tm1) tbs.
Proof.
  simpl in Hsz. rewrite Forall_forall. intros x Hinx.
  pose proof (sum_in_lt (map (fun x => term_size (snd x)) tbs) (term_size (snd x))) as Hlt.
  forward Hlt.
  { rewrite in_map_iff; eauto. }
  lia.
Qed.

Lemma tmatch_size1 {t1 tbs tm1}
  (Hsz: term_node_size (Tcase t1 tbs) = term_size tm1):
  term_size t1 < term_size tm1.
Proof.
  simpl in Hsz. lia.
Qed.

(*eps*)


Lemma teps_size {St b y s tm}
(Hsz: term_node_size (Teps b) = term_size tm)
(Heq : forall z : vsymbol * term_c,
  fst
  (run_errState
  (@errst_tup1 CoqBigInt.t St _ (errst_lift1 (t_open_bound b))) s) =
  inr z -> y = z):
  term_size (snd y) < term_size tm.
Proof.
  rewrite (dep_bnd_size_bound Heq). simpl in Hsz. destruct b as [[b1 b2] b3]; simpl in Hsz. 
  simpl. lia.
Qed.

(*quant is most difficult because we also have triggers*)

(*Do this separately because we need induction*)
Lemma vl_rename_aux_map vs s (m: Mvs.t term_c) x 
  (Hm: forall k t, Mvs.find_opt k m = Some t -> term_size t = 1):
  forall k t, Mvs.find_opt k (fst (fst (runState (vl_rename_aux vs (st_ret (m , x))) s))) = Some t -> 
  term_size t = 1.
Proof.
  revert s m x Hm. induction vs as [| h1 t1 IH]; simpl; auto.
  intros s m x Hm k t.
  destruct (runState (fresh_vsymbol h1) s ) as [v1 s1] eqn : Hrun1; simpl.
  destruct (runState _ s1) as [v2 s2] eqn : Hrun2; simpl.
  replace v2 with (fst (runState
      (vl_rename_aux t1 (st_ret (Mvs.add h1 (t_var v1) m, v1 :: x))) s1)) by (rewrite Hrun2; auto).
  apply IH. intros k1 tm1. rewrite Mvs.add_spec.
  destruct (Vsym.Tg.equal k1 h1); auto; [| apply Hm].
  intros Hsome; inversion Hsome; subst; reflexivity.
Qed.

Lemma t_open_quant1_size (b: term_quant): forall s,
  term_size (snd (fst (runState (t_open_quant1 b) s))) = term_size (snd b) /\
  Forall2 (Forall2 (fun x y => term_size x = term_size y)) (snd (fst (fst (runState (t_open_quant1 b) s)))) (snd (fst b)).
Proof.
  intros s. destruct b as [[[vs b] tr] t].
  Opaque vl_rename.
  simpl.
  destruct (runState (vl_rename Mvs.empty vs) s) as [[m1 v1] s1] eqn : Hrun.
  simpl.
  (*Get m1 value*)
  Transparent vl_rename. Opaque vl_rename_aux. simpl in Hrun.
  destruct (runState (vl_rename_aux vs (st_ret (Mvs.empty, []))) s) as [v3 s3] eqn : Hrun3.
  simpl in Hrun3. inversion Hrun; subst.
  replace v3 with (fst (runState (vl_rename_aux vs (st_ret (Mvs.empty, []))) s)) by (rewrite Hrun3; auto).
  split.
  - apply t_subst_unsafe_size. apply vl_rename_aux_map. intros k1 v1. rewrite Mvs.empty_spec. discriminate.
  - induction tr as [|tr1 tr2 IH]; auto.
    constructor; auto.
    induction tr1 as [| tm1 tm2 IH1]; auto.
    constructor; auto.
    apply t_subst_unsafe_size, vl_rename_aux_map. intros k1 v1. rewrite Mvs.empty_spec. discriminate.
Qed.

Lemma dep_bnd_size_quant {St b y s}
(Heq : forall z : list vsymbol * trigger * term_c,
fst
(run_errState
(@errst_tup1 CoqBigInt.t St _ (errst_lift1 (t_open_quant1 b)))
s) = inr z -> y = z):
(*Here we need info both about term and triggers*)
term_size (snd y) = term_size (snd b) /\
Forall2 (Forall2 (fun x y => term_size x = term_size y)) (snd (fst y)) (snd (fst b)). 
Proof.
  unfold errst_tup1 in Heq. Opaque t_open_quant1. simpl in Heq.
  unfold run_errState in Heq. simpl in Heq.
  destruct (runState (t_open_quant1 b) (fst s)) as [v1 s1] eqn : Hrun.
  simpl in Heq.
  specialize (Heq v1 eq_refl). subst.
  (*Now we just need to reason about [t_open_quant1] and its size*)
  pose proof (t_open_quant1_size b (fst s)) as Hszb.
  rewrite Hrun in Hszb. simpl in Hszb. auto.
Qed.

Lemma tquant_size_tr {St q tq s y tm1}
  (Hsz: term_node_size (Tquant q tq) = term_size tm1)
  (Heq: forall z : list vsymbol * trigger * term_c,
    fst
    (run_errState
    (@errst_tup1 CoqBigInt.t St _ (errst_lift1 (t_open_quant1 tq)))
    s) = inr z -> y = z):
  Forall (Forall (fun x : term_c => term_size x < term_size tm1)) (snd (fst y)).
Proof.
  pose proof (dep_bnd_size_quant Heq) as [Hsz1 Hsz2].
  simpl in Hsz. clear Heq. destruct tq as [[[vs b] tr] t]; simpl in *.
  assert (Hsz': sum (map (fun l => sum (map term_size l)) tr) < term_size tm1) by lia.
  clear -Hsz' Hsz2.
  generalize dependent tr. induction (snd (fst y)) as [| h1 t1 IH]; simpl; 
  intros [| h2 t2]; simpl; auto; intros Hall; inversion Hall; subst.
  intros Hsz. constructor; auto. 2: eapply IH; eauto; lia.
  assert (Hh2: sum (map term_size h2) < term_size tm1) by lia.
  clear -Hh2 H2. generalize dependent h2.
  induction h1 as [| x1 t1 IH]; intros [| x2 t2]; simpl; auto; intros Hall;
  inversion Hall; subst; auto. intros Hsz. constructor; auto; try lia.
  eapply IH; eauto; lia.
Qed.

Lemma tquant_size1 {St q tq s y tm1}
  (Hsz: term_node_size (Tquant q tq) = term_size tm1)
  (Heq: forall z : list vsymbol * trigger * term_c,
    fst
    (run_errState
    (@errst_tup1 CoqBigInt.t St _ (errst_lift1 (t_open_quant1 tq)))
    s) = inr z -> y = z):
  term_size (snd y) < term_size tm1.
Proof.
  pose proof (dep_bnd_size_quant Heq) as [Hsz1 Hsz2]. rewrite Hsz1.
  simpl in Hsz. destruct tq as [[[vs b] tr] t]; simpl in *. lia.
Qed.

(*rest of cases*)


Lemma tbinop_size1 {b t1 t2 tm}
  (Hsz : term_node_size (Tbinop b t1 t2) = term_size tm):
  term_size t1 < term_size tm.
Proof.
  simpl in Hsz. lia.
Qed.

Lemma tbinop_size2 {b t1 t2 tm}
  (Hsz : term_node_size (Tbinop b t1 t2) = term_size tm):
  term_size t2 < term_size tm.
Proof.
  simpl in Hsz. lia.
Qed.

Lemma tnot_size1 {t1 tm}
  (Hsz : term_node_size (Tnot t1) = term_size tm):
  term_size t1 < term_size tm.
Proof.
  simpl in Hsz. lia.
Qed.