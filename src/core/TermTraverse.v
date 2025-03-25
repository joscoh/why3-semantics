Require Import Monads TermDefs TermFuncs TermTraverseAux.
Import MonadNotations.
Local Open Scope errst_scope.
Require Import FunctionalExtensionality.


(*A traversal function*)


(*This will be generic for any errState (CoqBigInt.t * St) for some state St.
  This is the most generic we will need for our purposes*)
(*This is similar to [t_map] in the OCaml version, with 1 big difference:
  t_map is not explicitly recursive. However, it can be used recursively by instantiating
  the function argument with a recursive function. This doesn't work for us because Coq would
  not be able to prove such a function terminating.
  So instead we give a generic recursive traversal function that opens all the bindings.
  Defining this is extremely complicated. The recursion is not structural (since we do substitution
  when opening bindings). So we give a size metric and prove that substitution of variables
  preserves size (which is not trivial). Then, since we need to make recursive calls inside state
  monad bind operations, we need a dependently typed bind operator to remember the hypotheses
  we need. For similar reasons, we also need a dependently typed [map] function on lists*)
Section Traverse.
(*NOT dependently typed for OCaml purposes*)
Variable (St: Type). (*The type of state*)
Variable (R: Type). (*Return type*)

(*NOTE: removing term from these cases, then dont have to carry around.
  Can carry around type if we want or else calculate for app case*)

Notation T := (errState (CoqBigInt.t * St) R).

Variable (var_case: forall (tm: term_c) (x: vsymbol), T).

Variable (const_case: forall (tm: term_c) (c: constant) , T).
(*For now, only do let*)
(*NOTE: recursive case 2 on [t_open_bound], v is the NEW variable, t2 is the new term*)
Variable (let_case: forall (tm: term_c) (t1: term_c) (r1: R) (v: vsymbol) (t2: term_c) (r2: R), T).
Variable (if_case: forall (tm: term_c) (t1 t2 t3: term_c) (r1 r2 r3: R), T).

Variable (app_case: forall (tm: term_c) (l: lsymbol) (tms: list term_c) (rs: list R), T).
(*Again, tbs is a list of (new pattern, new term, recursive call)*)
Variable (match_case: forall (tm: term_c) (t1: term_c) (r1: R) (tb: list (pattern_c * term_c * R)), T).
(*As above: new variable, new term, new result*)
Variable (eps_case: forall (tm: term_c) (v: vsymbol) (t: term_c) (r: R), T).
Variable (quant_case: forall (tm: term_c) (q: quant) (vs: list vsymbol) (tr: list (list (term_c))) (rr: list (list R))
  (t: term_c) (r: R), T).
Variable (binop_case: forall (tm: term_c) (b: binop) (t1 t2: term_c) (r1 r2: R), T).
Variable (not_case: forall (tm: term_c) (t: term_c) (r: R), T).
Variable (true_case: term_c ->T).
Variable (false_case : term_c ->T).

(*We can't use Equations because it doesn't support mutual well-founded
  definitions. So we will use Xavier trick again*)
Definition termp := 0.
Definition term_size_eq' t := eq_sym (term_size_eq t).
(*For induction, it is useful to generalize proof. This is annoying; we need it in every case although
  it is always the same proof*)
Fixpoint term_traverse (tm1: term_c) (ACC: Acc lt (term_size tm1))
  (Heq: term_node_size (t_node_of tm1) = term_size tm1) : T :=
  match (t_node_of tm1) as t1 return term_node_size t1 = term_size tm1 -> _ with
  | Tconst c => fun _ => const_case tm1 c
  | Tvar x => fun _ => var_case tm1 x
  | Tif t1 t2 t3 => fun Hsz =>
    v1 <- term_traverse t1 (Acc_inv ACC (tif_size1 Hsz)) (term_size_eq' t1) ;;
    v2 <- term_traverse t2 (Acc_inv ACC (tif_size2 Hsz)) (term_size_eq' t2) ;;
    v3 <- term_traverse t3 (Acc_inv ACC (tif_size3 Hsz)) (term_size_eq' t3) ;;
    if_case tm1 t1 t2 t3 v1 v2 v3
  | Tlet t1 b => fun Hsz =>
    v1 <- term_traverse t1 (Acc_inv ACC (tlet_size1 Hsz)) (term_size_eq' t1) ;;
    (*Need dependent types here to have enough information for the proof*)
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun s y Heq => 
        v2 <- (term_traverse (snd y) (Acc_inv ACC (tlet_size2 Hsz Heq)) (term_size_eq' (snd y))) ;;
        let_case tm1 t1 v1 (fst y) (snd y) v2)
  | Tapp l ts => fun Hsz =>
    (*Need dependent map for termination proof*)
    recs <- errst_list (@dep_map _ _ (fun t => term_size t < term_size tm1) 
      (fun t1 (Ht1: term_size t1 < term_size tm1) => 
        term_traverse t1 (Acc_inv ACC Ht1) (term_size_eq' t1)) ts (tapp_size Hsz)) ;;
    (app_case tm1 l ts recs)
  (*Case is the trickiest: we need both a dependent map and a dependent bind*)
  | Tcase t1 tbs => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tmatch_size1 Hsz)) (term_size_eq' t1) ;;
    tbs2 <- errst_list (@dep_map _ _ (fun x => term_size (snd x) < term_size tm1)
      (*Idea: For each element in list, use dependent bind and recursively traverse*)
      (fun b (Hx: term_size (snd b) < term_size tm1) =>
        errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_branch b)))
          (fun s y Heq =>
            t2 <- term_traverse (snd y) (Acc_inv ACC (tmatch_size2 Hx Heq)) (term_size_eq' (snd y)) ;;
            errst_ret (y, t2))
        ) tbs (tmatch_size3 Hsz)) ;;
    match_case tm1 t1 r1 tbs2
  | Teps b => fun Hsz =>
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun s y Heq => 
        v <- (term_traverse (snd y) (Acc_inv ACC (teps_size Hsz Heq)) (term_size_eq' (snd y))) ;;
        eps_case tm1 (fst y) (snd y) v)
  (*A slight complication from the triggers - need nested dependent match*)
  | Tquant q tq => fun Hsz =>
    (*NOTE: doing bind ... ret, need for proofs even though superflous*)
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_quant1 tq)))
      (fun s (y : list vsymbol * trigger * term_c) Heq => 
        v <- (term_traverse (snd y) (Acc_inv ACC (tquant_size1 Hsz Heq)) (term_size_eq' (snd y))) ;;
        let vs := fst (fst y) in
        let tr := snd (fst y) in
        let t := snd y in
        (*Then traverse over triggers*)
        v2 <- errst_list (dep_map (fun l1 (Hl1: Forall (fun x => term_size x < term_size tm1) l1) =>
          errst_list (dep_map (fun tr1 (Ht1: term_size tr1 < term_size tm1) => 
            term_traverse tr1 (Acc_inv ACC Ht1) (term_size_eq' tr1))
            l1 Hl1)) tr (tquant_size_tr Hsz Heq)) ;;
        quant_case tm1 q vs tr v2 t v)
  | Tbinop b t1 t2 => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tbinop_size1 Hsz)) (term_size_eq' t1) ;;
    r2 <- term_traverse t2 (Acc_inv ACC (tbinop_size2 Hsz)) (term_size_eq' t2) ;;
    binop_case tm1 b t1 t1 r1 r2
  | Tnot t1 => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tnot_size1 Hsz)) (term_size_eq' t1) ;;
    not_case tm1 t1 r1
  | Ttrue => fun _ => true_case tm1
  | Tfalse => fun _ => false_case tm1
  end Heq.


(*unfolding is bad*)
Lemma term_traverse_rewrite (tm1: term_c) (ACC: Acc lt (term_size tm1)) Heq:
  term_traverse tm1 ACC Heq =
  match (t_node_of tm1) as t1 return term_node_size t1 = term_size tm1 -> _ with
  | Tconst c => fun _ => const_case tm1 c
  | Tvar x => fun _ => var_case tm1 x
  | Tif t1 t2 t3 => fun Hsz =>
    v1 <- term_traverse t1 (Acc_inv ACC (tif_size1 Hsz)) (term_size_eq' t1) ;;
    v2 <- term_traverse t2 (Acc_inv ACC (tif_size2 Hsz)) (term_size_eq' t2) ;;
    v3 <- term_traverse t3 (Acc_inv ACC (tif_size3 Hsz)) (term_size_eq' t3) ;;
    if_case tm1 t1 t2 t3 v1 v2 v3
  | Tlet t1 b => fun Hsz =>
    v1 <- term_traverse t1 (Acc_inv ACC (tlet_size1 Hsz)) (term_size_eq' t1) ;;
    (*Need dependent types here to have enough information for the proof*)
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun s y Heq => 
        v2 <- (term_traverse (snd y) (Acc_inv ACC (tlet_size2 Hsz Heq)) (term_size_eq' (snd y))) ;;
        let_case tm1 t1 v1 (fst y) (snd y) v2)
  | Tapp l ts => fun Hsz =>
    (*Need dependent map for termination proof*)
    recs <- errst_list (@dep_map _ _ (fun t => term_size t < term_size tm1) 
      (fun t1 (Ht1: term_size t1 < term_size tm1) => 
        term_traverse t1 (Acc_inv ACC Ht1) (term_size_eq' t1)) ts (tapp_size Hsz)) ;;
    (app_case tm1 l ts recs)
  (*Case is the trickiest: we need both a dependent map and a dependent bind*)
  | Tcase t1 tbs => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tmatch_size1 Hsz)) (term_size_eq' t1) ;;
    tbs2 <- errst_list (@dep_map _ _ (fun x => term_size (snd x) < term_size tm1)
      (*Idea: For each element in list, use dependent bind and recursively traverse*)
      (fun b (Hx: term_size (snd b) < term_size tm1) =>
        errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_branch b)))
          (fun s y Heq =>
            t2 <- term_traverse (snd y) (Acc_inv ACC (tmatch_size2 Hx Heq)) (term_size_eq' (snd y)) ;;
            errst_ret (y, t2))
        ) tbs (tmatch_size3 Hsz)) ;;
    match_case tm1 t1 r1 tbs2
  | Teps b => fun Hsz =>
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun s y Heq => 
        v <- (term_traverse (snd y) (Acc_inv ACC (teps_size Hsz Heq)) (term_size_eq' (snd y))) ;;
        eps_case tm1 (fst y) (snd y) v)
  (*A slight complication from the triggers - need nested dependent match*)
  | Tquant q tq => fun Hsz =>
    (*NOTE: doing bind ... ret, need for proofs even though superflous*)
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_quant1 tq)))
      (fun s (y : list vsymbol * trigger * term_c) Heq => 
        v <- (term_traverse (snd y) (Acc_inv ACC (tquant_size1 Hsz Heq)) (term_size_eq' (snd y))) ;;
        let vs := fst (fst y) in
        let tr := snd (fst y) in
        let t := snd y in
        (*Then traverse over triggers*)
        v2 <- errst_list (dep_map (fun l1 (Hl1: Forall (fun x => term_size x < term_size tm1) l1) =>
          errst_list (dep_map (fun tr1 (Ht1: term_size tr1 < term_size tm1) => 
            term_traverse tr1 (Acc_inv ACC Ht1) (term_size_eq' tr1))
            l1 Hl1)) tr (tquant_size_tr Hsz Heq)) ;;
        quant_case tm1 q vs tr v2 t v)
  | Tbinop b t1 t2 => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tbinop_size1 Hsz)) (term_size_eq' t1) ;;
    r2 <- term_traverse t2 (Acc_inv ACC (tbinop_size2 Hsz)) (term_size_eq' t2) ;;
    binop_case tm1 b t1 t1 r1 r2
  | Tnot t1 => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tnot_size1 Hsz)) (term_size_eq' t1) ;;
    not_case tm1 t1 r1
  | Ttrue => fun _ => true_case tm1
  | Tfalse => fun _ => false_case tm1
  end Heq.
Proof. destruct tm1. destruct t; destruct ACC;reflexivity.
Qed.

Definition tm_traverse (tm1: term_c) : T :=
  term_traverse tm1 (Wf_nat.lt_wf _) (eq_sym (term_size_eq tm1)).

Set Bullet Behavior "Strict Subproofs".

Lemma tm_size_wf: well_founded (fun t1 t2 => term_size t1 < term_size t2).
Proof.
  eapply well_founded_lt_compat with (f:=term_size). auto.
Defined.

Ltac funext := apply functional_extensionality_dep.

Ltac gen_dep_map :=
  match goal with |- context [dep_map ?f ?l ?H] => generalize dependent H end.

(*We want to prove an unfolding lemma so that we can express [tm_traverse] in terms
  of itself with no accessibility proofs (like the Equations rewrite principle).
  To this this, we first need to prove (inductively) that this definition is irrelevant in
  the accessibility proof. This requires funext*)

(*Don't need to change Heq, get proof irrelevance by UIP_dec*)
Lemma term_traverse_irrel t Heq ACC1 ACC2:
  term_traverse t ACC1 Heq = term_traverse t ACC2 Heq.
Proof.
  (*need to generalize for induction*)
  revert ACC1 ACC2 Heq.
  induction t using (well_founded_induction tm_size_wf). rename H into IH.
  intros ACC1 ACC2 Heq.
  rewrite !(term_traverse_rewrite t).
  destruct t as [n tyo a loc].
  destruct n; destruct ACC1; destruct ACC2; auto.
  - (*Tapp*) simpl.
    f_equal. f_equal. simpl in *. gen_dep_map.
    simpl. generalize dependent (S (sum (map term_size l0))).
    induction l0; simpl; auto. intros n IH a1 a2 _ Hall; inversion Hall; subst; f_equal; auto.
  - (*Tif*) simpl. (*rewrite to avoid needing funext*)
    rewrite (IH t) with (ACC2:=(a1 (term_size t) (tif_size1 Heq))) by (simpl; lia).
    rewrite (IH t0) with (ACC2:=(a1 (term_size t0) (tif_size2 Heq))) by (simpl; lia).
    rewrite (IH t1) with (ACC2:=(a1 (term_size t1) (tif_size3 Heq))) by (simpl; lia).
    reflexivity.
  - (*Tlet*) simpl. destruct p as [[v b] t1]. Opaque t_open_bound. simpl.
    rewrite (IH t) with (ACC2:=(a1 (term_size t) (tlet_size1 Heq))) by (simpl; lia).
    (*NOTE: need funext here I think*)
    f_equal. funext. intros x.
    f_equal. funext. intros s. funext. intros tb. funext. intros Htb.
    rewrite (IH (snd tb)) with (ACC2:=(a1 (term_size (snd tb)) (tlet_size2 Heq Htb))); auto.
    simpl. 
    eapply @tlet_size2 with (tm:=(mk_term_c (Tlet t (v, b, t1)) tyo a loc))(t1:=t) in Htb; simpl in *; lia.
  - (*Tcase*) Opaque t_open_branch. simpl.
    rewrite (IH t) with (ACC2:=(a1 (term_size t) (tmatch_size1 Heq))) by (simpl; lia).
    (*Combo of let and app essentially*)
    f_equal. funext. intros x. f_equal. f_equal.
    (*Again, need to generalize sum*)
    gen_dep_map. simpl in *. generalize dependent (@tmatch_size2 St (mk_term_c (Tcase t l) tyo a loc)).
    simpl.
    generalize dependent (S (term_size t + sum (map (fun x0 : pattern_c * bind_info * term_c => term_size (snd x0)) l))).
    (*Now general enough for induction*)
    induction l as [| [[p1 b1] t1] ps IHps]; simpl; auto.
    intros n IHn a1 a2 _ size_bound Hall. inversion Hall; subst; f_equal; auto.
    (*Now deal with head bound*)
    clear IHps.
    f_equal. funext. intros s. funext. intros b2. funext. intros Heq.
    rewrite (IHn (snd b2)) with (ACC2:=(a2 (term_size (snd b2)) (size_bound s b2 (p1, b1, t1) (Forall_inv Hall) Heq))); auto.
    apply dep_bnd_size_branch' in Heq. simpl in *; lia.
  - (*Teps*)
    simpl. destruct p as [[v b] t1]. f_equal. funext. intros s. funext. intros tb. funext. intros Htb.
    rewrite (IH (snd tb)) with (ACC2:=(a1 (term_size (snd tb)) (teps_size Heq Htb))); auto.
    simpl. 
    eapply @teps_size with (tm:=(mk_term_c (Teps (v, b, t1)) tyo a loc)) in Htb; simpl in *; lia.
  - (*Tquant*) Opaque t_open_quant1. destruct p as [[[vs1 b1] tr1] t1]. simpl.
    f_equal. funext. intros s. funext. intros tq. funext. intros Heq1.
    assert (Htq:=Heq1).
    apply dep_bnd_size_quant' in Htq. simpl in Htq. destruct Htq as [Hszt1 Hsztr1].
    rewrite (IH (snd tq)) with (ACC2:=(a1 (term_size (snd tq)) (tquant_size1 Heq Heq1))) by (simpl; lia).
    f_equal.  funext. intros x. f_equal. f_equal.
    (*Now prove trigger maps equiv*)
    gen_dep_map. simpl in *.
    generalize dependent (S(term_size t1 + Datatypes.length tr1 +
      sum (map (fun l : list term_c => sum (map term_size l)) tr1))).
    clear. induction (snd (fst tq)) as [| l1 tr1 IHtr]; simpl; auto.
    intros n IHn a1 a2 _ Hall. inversion Hall as [| ? ? IH1 IH2]; subst; f_equal; auto.
    (*And do single list*)
    f_equal.
    gen_dep_map. clear - IHn. induction l1 as [| x1 t1 IH]; simpl; auto. 
    intros Hall; inversion Hall; subst; f_equal; auto.
  - (*Tbinop*) simpl. 
    rewrite (IH t) with (ACC2:=(a1 (term_size t) (tbinop_size1 Heq))) by (simpl; lia).
    rewrite (IH t0) with (ACC2:=(a1 (term_size t0) (tbinop_size2 Heq))) by (simpl; lia).
    reflexivity.
  - (*Tnot*) simpl.
    rewrite (IH t) with (ACC2:=(a1 (term_size t) (tnot_size1 Heq))) by (simpl; lia).
    reflexivity.
Qed.


(*Now we prove the rewrite lemma. This does not require induction on the term
  (though it does need induction for the nested lists) and just applies
  the previous lemma repeatedly*)
Lemma tm_traverse_rewrite (tm1: term_c) :
  tm_traverse tm1 =
  match (t_node_of tm1) as t1 return term_node_size t1 = term_size tm1 -> _ with
  | Tconst c => fun _ => const_case tm1 c
  | Tvar x => fun _ => var_case tm1 x
  | Tif t1 t2 t3 => fun Hsz =>
    v1 <- tm_traverse t1 ;;
    v2 <- tm_traverse t2 ;;
    v3 <- tm_traverse t3 ;;
    if_case tm1 t1 t2 t3 v1 v2 v3
  | Tlet t1 b => fun Hsz =>
    v1 <- tm_traverse t1 ;;
    (*Need dependent types here to have enough information for the proof*)
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun s y Heq => 
        v2 <- (tm_traverse (snd y)) ;;
        let_case tm1 t1 v1 (fst y) (snd y) v2)
  | Tapp l ts => fun Hsz =>
    (*Need dependent map for termination proof*)
    recs <- errst_list (map tm_traverse ts) ;;
    (app_case tm1 l ts recs)
  (*Case is the trickiest: we need both a dependent map and a dependent bind*)
  | Tcase t1 tbs => fun Hsz =>
    r1 <- tm_traverse t1 ;;
    tbs2 <- errst_list (map (fun b =>
      (*Idea: For each element in list, use dependent bind and recursively traverse*)
        errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_branch b)))
          (fun s y Heq =>
            t2 <- tm_traverse (snd y) ;;
            errst_ret (y, t2))
        ) tbs) ;;
    match_case tm1 t1 r1 tbs2
  | Teps b => fun Hsz =>
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun s y Heq => 
        v <- (tm_traverse (snd y)) ;;
        eps_case tm1 (fst y) (snd y) v)
  (*A slight complication from the triggers - need nested dependent match*)
  | Tquant q tq => fun Hsz =>
    (*NOTE: doing bind ... ret, need for proofs even though superflous*)
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_quant1 tq)))
      (fun s (y : list vsymbol * trigger * term_c) Heq => 
        v <- (tm_traverse (snd y)) ;;
        let vs := fst (fst y) in
        let tr := snd (fst y) in
        let t := snd y in
        (*Then traverse over triggers*)
        v2 <- errst_list (map (fun l1 =>
          errst_list (map tm_traverse l1)) tr) ;;
        quant_case tm1 q vs tr v2 t v)
  | Tbinop b t1 t2 => fun Hsz =>
    r1 <- tm_traverse t1 ;;
    r2 <- tm_traverse t2 ;;
    binop_case tm1 b t1 t1 r1 r2
  | Tnot t1 => fun Hsz =>
    r1 <- tm_traverse t1 ;;
    not_case tm1 t1 r1
  | Ttrue => fun _ => true_case tm1
  | Tfalse => fun _ => false_case tm1
  end (eq_sym (term_size_eq tm1)).
Proof.
  (*Basically, use some sort of proof irrelevance*)
  unfold tm_traverse at 1.
  generalize dependent (lt_wf (term_size tm1)).
  destruct tm1. destruct t; intros ACC; destruct ACC; auto.
  - (*app*) simpl.
    f_equal. f_equal.
    match goal with |- context [dep_map ?f ?l ?H] => generalize dependent H end.
    simpl in *. generalize dependent (S (sum (map term_size l0))).
    induction l0; simpl in *; auto. intros n ACC Hall.
    inversion Hall; subst. f_equal; auto.
    (*Now use irrelevance*) apply term_traverse_irrel.
  - (*if*) simpl. unfold tm_traverse.
    erewrite (term_traverse_irrel t).
    erewrite (term_traverse_irrel t1).
    erewrite (term_traverse_irrel t2).
    reflexivity.
  - (*let*) simpl.
    unfold tm_traverse. f_equal.
    2: { apply term_traverse_irrel. }
    funext. intros x. f_equal. funext. intros tb.
    funext. intros s. funext. intros Htb.
    f_equal. apply term_traverse_irrel.
  - (*case*) simpl.
    unfold tm_traverse.
    f_equal. 2: apply term_traverse_irrel.
    funext. intros x. f_equal. f_equal.
    (*inner induction*) gen_dep_map. (*TEMP; bad *) 
    generalize dependent (@tmatch_size2 St (mk_term_c (Tcase t l) o t0 o0)).
    Opaque term_traverse. simpl in *. Transparent term_traverse.
    generalize dependent (S (term_size t + sum (map (fun x1 : pattern_c * bind_info * term_c => term_size (snd x1)) l))).
    induction l as [|[[p1 b1] t1] ps IH]; auto;
    intros n a size_bound Hall; auto. inversion Hall; subst.
    Opaque term_traverse. simpl. Transparent term_traverse. f_equal; auto.
    f_equal. funext. intros x1. funext. intros s. funext. intros Heq.
    f_equal. apply term_traverse_irrel.
  - (*eps*) simpl. f_equal. funext. intros tb. funext. intros s.
    funext. intros Heq. f_equal. apply term_traverse_irrel.
  - (*quant*) simpl. destruct p as [[[vs1 b1] tr1] t1]. simpl. f_equal. funext. intros s.
    funext. intros tq. funext. intros Heq. f_equal. 2: apply term_traverse_irrel.
    funext. intros x. f_equal. f_equal.
    (*nested ind*) simpl in *.
    gen_dep_map. simpl. generalize dependent (S (term_size t1 + Datatypes.length tr1 +
      sum (map (fun l : list term_c => sum (map term_size l)) tr1))).
    clear. induction (snd (fst tq)) as [| l1 trs IH]; auto; intros n a Hall; inversion Hall; subst;
    simpl; f_equal; auto.
    f_equal. gen_dep_map. clear. induction l1 as [| x1 l1 IH]; auto; simpl; intros Hall; inversion Hall; 
    subst; f_equal; auto. apply term_traverse_irrel.
  - (*binop*) simpl. erewrite (term_traverse_irrel t). erewrite (term_traverse_irrel t1); reflexivity.
  - (*not*) simpl. erewrite (term_traverse_irrel t). reflexivity.
Qed.

(*With this, we can prove an induction principle*)

(*Have to prove by hand because Equations has bug with monadic binders + well-founded rec*)

Section Induction.

Variable (P: term_c -> T -> Prop).

Variable (Pconst: forall t c, t_node_of t = Tconst c -> P t (const_case t c)).
Variable (Pvar: forall t x, t_node_of t = Tvar x -> P t (var_case t x)).
Variable (Pif: forall t t1 t2 t3, t_node_of t = Tif t1 t2 t3 ->
    P t1 (tm_traverse t1) -> P t2 (tm_traverse t2) -> P t3 (tm_traverse t3) ->
    P t (r1 <- tm_traverse t1 ;; r2 <- tm_traverse t2 ;; r3 <- tm_traverse t3 ;; 
      (if_case t t1 t2 t3 r1 r2 r3))).
(*With dep bind*)
Variable (Plet: forall t (t1: term_c) (b: term_bound), t_node_of t = Tlet t1 b ->
  P t1 (tm_traverse t1) ->
  (forall (y: vsymbol * term_c) (s: CoqBigInt.t * St), 
     fst (run_errState (errst_tup1 (errst_lift1 (t_open_bound b))) s) = inr y -> P (snd y) (tm_traverse (snd y))) ->
  P t (r1 <- tm_traverse t1 ;;
    errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun s y Heq => 
        r2 <- tm_traverse (snd y) ;;
        let_case t t1 r1 (fst y) (snd y) r2))).
(*app case needs nested induction*)
Variable (Papp: forall t l (ts: list term_c), t_node_of t = Tapp l ts ->
  Forall (fun x => P x (tm_traverse x)) ts ->
  P t (recs <- errst_list (map tm_traverse ts) ;; app_case t l ts recs)).
(*match needs both dependent bind and nested result*)
Variable (Pcase: forall t t1 (tbs: list (pattern_c * bind_info * term_c)),
  t_node_of t = Tcase t1 tbs ->
  P t1 (tm_traverse t1) ->
  Forall (fun b =>
    (forall (y: pattern_c * term_c) (s: CoqBigInt.t * St), 
        fst (run_errState (errst_tup1 (errst_lift1 (t_open_branch b))) s) = inr y -> 
        P (snd y) (tm_traverse (snd y)))) tbs ->
  P t (r1 <- tm_traverse t1 ;;
    tbs2 <- errst_list (map (fun b =>
        errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_branch b)))
          (fun s y Heq =>
            t2 <- tm_traverse (snd y) ;;
            errst_ret (y, t2))
        ) tbs) ;;
    match_case t t1 r1 tbs2)).
(*Others are easier*)
Variable (Peps: forall t b, t_node_of t = Teps b ->
  (forall (y:  vsymbol * term_c) (s: CoqBigInt.t * St), 
    fst (run_errState (errst_tup1 (errst_lift1 (t_open_bound b))) s) = inr y -> P (snd y) (tm_traverse (snd y))) ->
  P t (errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun s y Heq => 
        r2 <- tm_traverse (snd y) ;;
        eps_case t (fst y) (snd y) r2))).
(*Quant a bit more complicated because of double needs double nested, but not dependent so OK*)
(*triggers depend on opening bound (y)*)
Variable (Pquant: forall t q tq, t_node_of t = Tquant q tq ->
  (forall (y : list vsymbol * trigger * term_c) (s: CoqBigInt.t * St), 
    fst (run_errState (errst_tup1 (errst_lift1 (t_open_quant1 tq))) s) = inr y -> 
     P (snd y) (tm_traverse (snd y)) /\
     Forall (fun l1 => Forall (fun tr1 => P tr1 (tm_traverse tr1)) l1) (snd (fst y))) ->
  P t (errst_bind_dep' (errst_tup1 (errst_lift1 (t_open_quant1 tq)))
      (fun s (y : list vsymbol * trigger * term_c) Heq => 
        v <- (tm_traverse (snd y)) ;;
        let vs := fst (fst y) in
        let tr := snd (fst y) in
        let t' := snd y in
        (*Then traverse over triggers*)
        v2 <- errst_list (map (fun l1 =>
          errst_list (map tm_traverse l1)) tr) ;;
        quant_case t q vs tr v2 t' v))).
(*Easier*)
Variable (Pbinop: forall t b t1 t2, t_node_of t = Tbinop b t1 t2 ->
  P t1 (tm_traverse t1) -> P t2 (tm_traverse t2) ->
  P t (r1 <- tm_traverse t1 ;; r2 <- tm_traverse t2 ;;
      (binop_case t b t1 t1 r1 r2))).
Variable (Pnot: forall t t1, t_node_of t = Tnot t1 ->
  P t1 (tm_traverse t1) ->
  P t ( r1 <- tm_traverse t1 ;; not_case t t1 r1)).
Variable (Ptrue: forall t, t_node_of t = Ttrue -> P t (true_case t)).
Variable (Pfalse: forall t, t_node_of t = Tfalse -> P t (false_case t)).

(*Prove by well-founded induction on the size of t, use rewrite lemma
  to avoid dealing with accessibility proofs. Most cases are quite straightforward;
  relies on the size theorems in TermTraverseAux.v.
  The quant case is a bit annoying because we need double nested induction *)
Theorem tm_traverse_ind (t: term_c) : P t (tm_traverse t).
Proof.
  induction t using (well_founded_induction tm_size_wf). rename H into IH.
  (*Now use rewrite lemma so we don't need to worry about ACC proofs*)
  rewrite tm_traverse_rewrite.
  generalize dependent (eq_sym (term_size_eq t)).
  destruct t as [n tyo a loc].
  destruct n; auto.
  - (*var*) simpl. intros _. apply Pvar. reflexivity.
  - (*const*) simpl. intros _. apply Pconst. reflexivity.
  - (*app*) simpl. intros _. apply Papp; auto.
    (*Use IH to prove the Forall*)
    simpl in IH. clear -IH. rewrite Forall_forall.
    intros x Hinx. apply IH. 
    pose proof (sum_in_lt (map term_size l0) (term_size x)) as Hle.
    forward Hle. { rewrite in_map_iff. exists x; auto. }
    lia.
  - (*if*) simpl. intros _; apply Pif; auto; apply IH; simpl; lia.
  - (*let*) simpl. destruct p as [[v b] t1]. intros _. apply Plet; auto.
    + apply IH; simpl; lia.
    + intros y s Hrun. apply dep_bnd_size_bound' in Hrun.
      simpl in Hrun. apply IH. simpl. lia.
  - (*case*) simpl. intros _. apply Pcase; auto.
    + apply IH; simpl; lia.
    + rewrite Forall_forall. intros x Hinx y s Hy. apply IH.
      simpl. apply dep_bnd_size_branch' in Hy. 
      pose proof (sum_in_lt (map (fun x0 : pattern_c * bind_info * term_c => term_size (snd x0)) l) (term_size (snd x))) as Hle.
      forward Hle. { rewrite in_map_iff; exists x; auto. } lia.
  - (*eps*)  destruct p as [[v b] t1].  simpl. intros _; apply Peps; auto.
    intros y s Hy. apply dep_bnd_size_bound' in Hy. simpl in Hy. apply IH; simpl; lia.
  - (*quant*) simpl. intros _. apply Pquant; auto.
    intros y s Hy.
    apply dep_bnd_size_quant' in Hy.
    destruct Hy as [Hz1 Hsz2]. destruct p as [[[vs1 b1] tr1] t1].
    split.
    + apply IH; simpl in *; lia.
    + simpl in Hsz2. 
      (*Forall2 means we need nested induction*)
      rewrite Forall_forall. intros ts Hints. rewrite Forall_forall.
      intros x Hinx. apply IH. simpl.
      assert (Hsz: term_size x <=  sum (map (fun l : list term_c => sum (map term_size l)) tr1)); [|lia].
      clear -Hsz2 Hints Hinx. generalize dependent tr1. induction (snd (fst y)) as [|l1 tl1 IHl1]; intros [| l2 tl2];
      simpl; auto; try contradiction; intros Hall; inversion Hall as [| ? ? ? ? IH1 IH2]; subst; clear Hall.
      simpl in Hints. destruct Hints as [Hts | Hts]; subst; auto.
      2: { apply IHl1 in IH2; auto. lia. }
      assert (Hsz: term_size x <= sum (map term_size l2)); [|lia].
      clear -Hinx IH1. generalize dependent l2. induction ts as [| x1 tl1 IH]; intros [| y2 tl2]; auto; 
      try contradiction; intros Hall; inversion Hall as [| ? ? ? ? IH1 IH2]; subst. simpl.
      simpl in Hinx. destruct Hinx; subst; auto; try lia. apply IH in IH2; auto; lia.
  - (*binop*) simpl. intros _. apply Pbinop; auto; apply IH; simpl; lia.
  - (*not*) simpl. intros _. apply Pnot; auto; apply IH; simpl; lia.
Qed.

End Induction.


End Traverse.


(*And a version to map over terms and formulas specifically - 2 differences:
  1. non-recursive cases just return the term
  2. functions take in term as well - for e.g. using type info*)
Section Map.
Variable (St: Type). (*The type of state*)

Notation T := (errState (CoqBigInt.t * St) term_c).

(* Variable (var_case: forall (x: vsymbol), T).

Variable (const_case: forall (c: constant) , T). *)
(*For now, only do let*)
(*NOTE: recursive case 2 on [t_open_bound], v is the NEW variable, t2 is the new term*)
Variable (let_case: forall (t: term_c) (t1: term_c) (r1: term_c) (v: vsymbol) (t2: term_c) (r2: term_c), T).
Variable (if_case: forall (t: term_c) (t1 t2 t3: term_c) (r1 r2 r3: term_c), T).

(*NOTE: o is the OLD type so [rs] should be type-safe*)
Variable (app_case: forall (t: term_c) (l: lsymbol) (tms: list term_c) (rs: list term_c), T).
(*Again, tbs is a list of (new pattern, new term, recursive call)*)
Variable (match_case: forall (t: term_c) (t1: term_c) (r1: term_c) (tb: list (pattern_c * term_c * term_c)), T).
(*As above: new variable, new term, new result*)
Variable (eps_case: forall (t: term_c) (v: vsymbol) (t: term_c) (r: term_c), T).
Variable (quant_case: forall (t: term_c) (q: quant) (vs: list vsymbol) (tr: list (list (term_c))) (rr: list (list term_c))
  (t: term_c) (r: term_c), T).
Variable (binop_case: forall (t: term_c) (b: binop) (t1 t2: term_c) (r1 r2: term_c), T).
Variable (not_case: forall (t: term_c) (t: term_c) (r: term_c), T).
(* Variable (true_case: T).
Variable (false_case : T). *)

Definition term_map (tm1: term_c) : T :=
  tm_traverse St _
  (fun tm1 x => errst_ret tm1)
  (fun tm1 c => errst_ret tm1)
  let_case if_case app_case match_case eps_case quant_case binop_case not_case
  (fun tm1 => errst_ret tm1)
  (fun tm1 => errst_ret tm1)
  tm1.

(* End Map.

(*Default cases for map - when we don't do anything interesting except recurse*)
Section Default.
Context {St: Type}.
Notation T := (errState (CoqBigInt.t * ((hashcons_ty ty_c) * St))%type term_c).
Check t_app1. *)
(*Default arguments for any recursive-but-not-interesting cases*)

Definition tmap_let_default (_: term_c) (t1: term_c) (r1: term_c) (v: vsymbol) (t2: term_c) (r2: term_c) : T :=
  errst_lift2 (t_let_close v r1 r2).
Definition tmap_if_default (_: term_c) (t1 t2 t3: term_c) (r1 r2 r3: term_c) : T :=
  errst_lift2 (t_if r1 r2 r3).
Definition tmap_app_default (tm1: term_c) (l: lsymbol) (tms: list term_c) (rs: list term_c) : T :=
  errst_ret (t_app1 l rs (t_ty_of tm1)). (*NOTE: assuming type safe*)
Definition tmap_match_default (_: term_c) (t1: term_c) (r1: term_c) (tb: list (pattern_c * term_c * term_c)) : T :=
  errst_lift2 (t_case_close r1 (map (fun x => (fst (fst x), snd x)) tb)).
Definition tmap_eps_default (_: term_c) (v: vsymbol) (t: term_c) (r: term_c) : T :=
  errst_lift2 (t_eps_close v r).
Definition tmap_quant_default (_: term_c) (q: quant) (vs: list vsymbol) (tr: list (list (term_c))) (rr: list (list term_c))
  (t: term_c) (r: term_c) : T :=
  errst_lift2 (t_quant_close q vs rr r).
Definition tmap_binop_default (_: term_c) (b: binop) (t1 t2: term_c) (r1 r2: term_c) : T :=
  errst_lift2 (t_binary b r1 r2).
Definition tmap_not_default (_: term_c) (t: term_c) (r: term_c) : T := errst_lift2 (t_not r).

End Map.

(*And finally, a version to just make the term well-formed (i.e. unique binders)*)
Definition t_make_wf (t: term_c) {St} : errState (CoqBigInt.t * St) term_c :=
  term_map St (tmap_let_default _) (tmap_if_default _) (tmap_app_default _) 
  (tmap_match_default _) (tmap_eps_default _) (tmap_quant_default _) (tmap_binop_default _) 
  (tmap_not_default _) t.

(*And lastly, substitution*)

(*TODO: could combine in 1 to require only 1 pass, not worried about efficiency right now*)

(*Do [t_subst], [t_open_bound_with], [t_subst_single]*)
Definition t_subst1 {St} (m: Mvs.t term_c) (t: term_c) : errState (CoqBigInt.t * St) term_c :=
  _ <- errst_lift2 (iter_err (fun x => vs_check (fst x) (snd x)) (Mvs.bindings m)) ;;
  t1 <- t_make_wf t ;;
  errst_ret (t_subst_unsafe m t1).

Definition t_subst_single1 {St} (v: vsymbol) (t1: term_c) (t: term_c) : errState (CoqBigInt.t * St) term_c :=
  t_subst1 (Mvs.singleton _ v t1) t.

(*TODO: if doesnt work, just give 2*)
(* Definition t_open_bound_with1 {St} (e: term_c) (tb: term_bound) : errState (CoqBigInt.t * St) term_c :=
  let '(v, b, t) := tb in
  _ <- errst_lift2 (vs_check v e) ;;
  let m := Mvs.singleton _ v e in
  _ <- errst_lift2 (iter_err (fun x => vs_check (fst x) (snd x)) (Mvs.bindings m)) ;;
  t1 <- t_make_wf t ;;
  errst_ret (t_subst_unsafe m t1). *)


(* 

(*And a version to map over terms specifically - basically only difference is that
  non-recursive cases just return the term*)
Section Map.
Variable (St: Type). (*The type of state*)

Notation T := (errState (CoqBigInt.t * St) term_c).

(* Variable (var_case: forall (x: vsymbol), T).

Variable (const_case: forall (c: constant) , T). *)
(*For now, only do let*)
(*NOTE: recursive case 2 on [t_open_bound], v is the NEW variable, t2 is the new term*)
Variable (let_case: forall (t1: term_c) (r1: term_c) (v: vsymbol) (t2: term_c) (r2: term_c), T).
Variable (if_case: forall (t1 t2 t3: term_c) (r1 r2 r3: term_c), T).

(*NOTE: o is the OLD type so [rs] should be type-safe*)
Variable (app_case: forall (l: lsymbol) (tms: list term_c) (o: option ty_c) (rs: list term_c), T).
(*Again, tbs is a list of (new pattern, new term, recursive call)*)
Variable (match_case: forall (t1: term_c) (r1: term_c) (tb: list (pattern_c * term_c * term_c)), T).
(*As above: new variable, new term, new result*)
Variable (eps_case: forall (v: vsymbol) (t: term_c) (r: term_c), T).
Variable (quant_case: forall (q: quant) (vs: list vsymbol) (tr: list (list (term_c))) (rr: list (list term_c))
  (t: term_c) (r: term_c), T).
Variable (binop_case: forall (b: binop) (t1 t2: term_c) (r1 r2: term_c), T).
Variable (not_case: forall (t: term_c) (r: term_c), T).
(* Variable (true_case: T).
Variable (false_case : T). *)

Fixpoint term_map_rec (tm1: term_c) (ACC: Acc lt (term_size tm1)) : T :=
  match (t_node_of tm1) as t1 return term_node_size t1 = term_size tm1 -> _ with
  | Tconst c => fun _ => errst_ret tm1
  | Tvar x => fun _ => errst_ret tm1
  | Tif t1 t2 t3 => fun Hsz =>
    v1 <- term_map_rec t1 (Acc_inv ACC (tif_size1 Hsz)) ;;
    v2 <- term_map_rec t2 (Acc_inv ACC (tif_size2 Hsz)) ;;
    v3 <- term_map_rec t3 (Acc_inv ACC (tif_size3 Hsz)) ;;
    if_case t1 t2 t3 v1 v2 v3
  | Tlet t1 b => fun Hsz =>
    v1 <- term_map_rec t1 (Acc_inv ACC (tlet_size1 Hsz)) ;;
    (*Need dependent types here to have enough information for the proof*)
    errst_bind_dep (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun y s Heq => 
        v2 <- (term_map_rec (snd y) (Acc_inv ACC (tlet_size2 Hsz Heq))) ;;
        let_case t1 v1 (fst y) (snd y) v2)
  | Tapp l ts => fun Hsz =>
    (*Need dependent map for termination proof*)
    recs <- errst_list (@dep_map _ _ (fun t => term_size t < term_size tm1) 
      (fun t1 (Ht1: term_size t1 < term_size tm1) => 
        term_map_rec t1 (Acc_inv ACC Ht1)) ts (tapp_size Hsz)) ;;
    (app_case l ts (t_ty_of tm1) recs)
  (*Case is the trickiest: we need both a dependent map and a dependent bind*)
  | Tcase t1 tbs => fun Hsz =>
    r1 <- term_map_rec t1 (Acc_inv ACC (tmatch_size1 Hsz)) ;;
    tbs2 <- errst_list (@dep_map _ _ (fun x => term_size (snd x) < term_size tm1)
      (*Idea: For each element in list, use dependent bind and recursively traverse*)
      (fun b (Hx: term_size (snd b) < term_size tm1) =>
        errst_bind_dep (errst_tup1 (errst_lift1 (t_open_branch b)))
          (fun y s Heq =>
            t2 <- term_map_rec (snd y) (Acc_inv ACC (tmatch_size2 Hx Heq)) ;;
            errst_ret (y, t2))
        ) tbs (tmatch_size3 Hsz)) ;;
    match_case t1 r1 tbs2
  | Teps b => fun Hsz =>
    errst_bind_dep (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun y s Heq => 
        v <- (term_map_rec (snd y) (Acc_inv ACC (teps_size Hsz Heq))) ;;
        eps_case (fst y) (snd y) v)
  (*A slight complication from the triggers - need nested dependent match*)
  | Tquant q tq => fun Hsz =>
    (*NOTE: doing bind ... ret, need for proofs even though superflous*)
    errst_bind_dep (errst_tup1 (errst_lift1 (t_open_quant1 tq)))
      (fun (y : list vsymbol * trigger * term_c) s Heq => 
        v <- (term_map_rec (snd y) (Acc_inv ACC (tquant_size1 Hsz Heq))) ;;
        let vs := fst (fst y) in
        let tr := snd (fst y) in
        let t := snd y in
        (*Then traverse over triggers*)
        v2 <- errst_list (dep_map (fun l1 (Hl1: Forall (fun x => term_size x < term_size tm1) l1) =>
          errst_list (dep_map (fun tr1 (Ht1: term_size tr1 < term_size tm1) => 
            term_map_rec tr1 (Acc_inv ACC Ht1))
            l1 Hl1)) tr (tquant_size_tr Hsz Heq)) ;;
        quant_case q vs tr v2 t v)
  | Tbinop b t1 t2 => fun Hsz =>
    r1 <- term_map_rec t1 (Acc_inv ACC (tbinop_size1 Hsz)) ;;
    r2 <- term_map_rec t2 (Acc_inv ACC (tbinop_size2 Hsz)) ;;
    binop_case b t1 t1 r1 r2
  | Tnot t1 => fun Hsz =>
    r1 <- term_map_rec t1 (Acc_inv ACC (tnot_size1 Hsz)) ;;
    not_case t1 r1
  | Ttrue => fun _ => errst_ret tm1
  | Tfalse => fun _ => errst_ret tm1
  end (eq_sym (term_size_eq tm1)).

Definition term_map (tm1: term_c) : T :=
  term_map_rec tm1 (Wf_nat.lt_wf _).

(* End Map.

(*Default cases for map - when we don't do anything interesting except recurse*)
Section Default.
Context {St: Type}.
Notation T := (errState (CoqBigInt.t * ((hashcons_ty ty_c) * St))%type term_c).
Check t_app1. *)
(*Default arguments for any recursive-but-not-interesting cases*)

Definition tmap_let_default (t1: term_c) (r1: term_c) (v: vsymbol) (t2: term_c) (r2: term_c) : T :=
  errst_lift2 (t_let_close v r1 r2).
Definition tmap_if_default (t1 t2 t3: term_c) (r1 r2 r3: term_c) : T :=
  errst_lift2 (t_if r1 r2 r3).
Definition tmap_app_default (l: lsymbol) (tms: list term_c) (o: option ty_c) (rs: list term_c) : T :=
  errst_ret (t_app1 l rs o). (*NOTE: assuming type safe*)
Definition tmap_match_default (t1: term_c) (r1: term_c) (tb: list (pattern_c * term_c * term_c)) : T :=
  errst_lift2 (t_case_close r1 (map (fun x => (fst (fst x), snd x)) tb)).
Definition tmap_eps_default (v: vsymbol) (t: term_c) (r: term_c) : T :=
  errst_lift2 (t_eps_close v r).
Definition tmap_quant_default (q: quant) (vs: list vsymbol) (tr: list (list (term_c))) (rr: list (list term_c))
  (t: term_c) (r: term_c) : T :=
  errst_lift2 (t_quant_close q vs rr r).
Definition tmap_binop_default (b: binop) (t1 t2: term_c) (r1 r2: term_c) : T :=
  errst_lift2 (t_binary b r1 r2).
Definition tmap_not_default (t: term_c) (r: term_c) : T := errst_lift2 (t_not r).

End Map. *)




(* 
Equations term_traverse (tm1: term_c) : T by wf (term_size tm1) lt :=
  term_traverse tm1 := term_node_traverse (t_node_of tm1) 
with term_node_traverse (tm1: term_node) : T :=
  term_node_traverse (Tconst c) := const_case c;
  term_node_traverse (Tvar x) := var_case x;
  term_node_traverse (Tif t1 t2 t3) :=
    v1 <- term_traverse t1 ;;
    v2 <- term_traverse t2 ;;
    v3 <- term_traverse t3 ;;
    if_case t1 t2 t3 v1 v2 v3;
  term_node_traverse (Tlet t1 b) :=
    v1 <- term_traverse t1 ;;
    (*Need dependent types here to have enough information for the proof*)
    st_bind_dep _ _ _ (t_open_bound b)
      (fun y s Heq => 
        v2 <- (term_traverse (snd y)) ;;
        let_case t1 ((fst y), (snd b)) v1 v2). *)


