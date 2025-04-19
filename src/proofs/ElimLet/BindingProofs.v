(*Proofs about [t_open_bound] and similar*)
Require Import TermFuncs StateHoareMonad StateInvarPres VsymCount TermTactics Relations TermVars SubstUnsafeProofs.
From Proofs Require Import Substitution SubMulti.
Require Import InversionLemmas TermTraverseAux.

Local Open Scope Z_scope.
Set Bullet Behavior "Strict Subproofs".

(*We will need to know exactly how the state changes under [t_open_bound] (increases by 1)*)
Lemma fresh_vsymbol_incr v1: st_spec (fun _ : Z => True) (fresh_vsymbol v1)
  (fun (s1 : Z) (_ : TermDefs.vsymbol) (s2 : Z) => s2 = 1 + s1).
Proof.
  unfold fresh_vsymbol, create_vsymbol.
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = 1 + x) (Q2:=fun x y => x = y); auto.
  3: { intros; lia. }
  2: { intros; apply prove_st_spec_ret; auto. }
  (*id_register*)
  unfold id_register.
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = x) (Q2:=fun x y => y = 1 + x); auto.
  3: { intros; lia. }
  1: { apply IdCtr.st_spec_get. auto. }
  intros x.
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = 1 + x) (Q2:=fun x y => x = y); auto.
  3: { intros; lia. }
  2: { intros; apply prove_st_spec_ret; auto. }
  apply IdCtr.st_spec_incr. (*TODO: bad*) Transparent CoqBigInt.succ. unfold CoqBigInt.succ. intros; lia. 
  Opaque CoqBigInt.succ.
Qed.

Lemma t_open_bound_incr tb:
errst_spec (fun _ : full_st => True)
  (errst_tup1 (errst_lift1 (t_open_bound tb)))
  (fun (s1 : full_st) _ (s2 : full_st) => fst s2 = 1 + fst s1).
Proof.
  apply errst_spec_weaken with (P1:=fun _ => True /\ True) (Q1:=fun s1 _ s2 => (fst s2 = 1 + fst s1) /\ True); auto;
  [intros; tauto|].
  apply errst_spec_tup1' with (P1:=fun _ => True) (Q1:=fun _ => True) (P2:=fun x _ y => y = 1 + x) (Q:= fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*state proof*)
  unfold t_open_bound.
  destruct tb as [[v1 b1] t1].
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = 1 + x) (Q2:=fun x y => x = y); auto.
  3: { intros; subst; lia. }
  2: { intros [m v]. apply prove_st_spec_ret. auto. }
  (*main part is rename*)
  unfold vs_rename. 
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = 1 + x) (Q2:=fun x y => x = y); auto.
  3: { intros; lia. }
  2: { intros; apply prove_st_spec_ret; auto. }
  (*fresh vsymbol*)
  apply fresh_vsymbol_incr.
Qed.

(*Part 1: Prove things about state modification and invariant preservation (not output)*)
Section InvarPres.

(*Useful in multiple places*)
Lemma fresh_vsymbol_lt v:
  st_spec (fun _ : Z => True) (fresh_vsymbol v) (fun (s1 : Z) (_ : TermDefs.vsymbol) (s2 : Z) => s1 < s2).
Proof.
  eapply st_spec_weaken_post; [| apply fresh_vsymbol_incr]; simpl; lia.
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

End InvarPres.

(*Part 2: Results about the variable output of [t_open_bound]*)
Section Var.

Definition ident_with (i: ident) (s: Z) :=
  Build_ident (id_string i) (id_attrs i) (id_loc i) s.

Definition vsym_with (v: TermDefs.vsymbol) (s: Z) := Build_vsymbol (ident_with (vs_name v) s) (vs_ty v).

Lemma rename_spec m v1:
  st_spec (fun _ : Z => True) (vs_rename m v1)
  (fun (s1 : Z) (v : Mvs.t term_c * TermDefs.vsymbol) (_ : Z) => snd v = vsym_with v1 s1).
Proof.
  unfold vs_rename.
  apply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 v _ => v = vsym_with v1 s1)
  (Q2:=fun x _ y _ => x = snd y); auto.
  3: { intros s1 _ _ x y Hid Hx; subst; auto. }
  2: { intros x. apply prove_st_spec_ret. simpl. auto. }
  (*separate lemma for [fresh_vsymbol]?*)
  unfold fresh_vsymbol, create_vsymbol.
  eapply prove_st_spec_bnd with (Q1:=fun s1 i s2 => i = ident_with (vs_name v1) s1)
    (P2:=fun _ _ => True) (Q2:=fun i _ y _ => y = {| vs_name := i; vs_ty := vs_ty v1 |}); auto.
  3: { intros s1 _ _ x y Hx Hy; subst. reflexivity. }
  2: { intros x. apply prove_st_spec_ret. auto. }
  (*id_register part*)
  unfold id_register.
  eapply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:= fun s1 i _ => i = s1)
  (Q2 := fun x _ y _ => y = ident_with (vs_name v1) x); simpl; auto.
  3: { intros; subst; auto. }
  1: { apply IdCtr.st_spec_get; auto. }
  intros s1. 
  eapply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ _ => True)
  (Q2 := fun _ _ y _ => y = ident_with (vs_name v1) s1); simpl; auto.
  1: { unfold st_spec; auto. }
  intros _. apply prove_st_spec_ret. intros. unfold ident_with. f_equal.
  apply Mattr.set_union_empty_l.
Qed.

(*NOTE: not good name*)
Lemma vs_rename_var m v1:
  st_spec (fun _ : CoqBigInt.t => True) (vs_rename m v1)
    (fun (_ : CoqBigInt.t) (r : Mvs.t term_c * TermDefs.vsymbol) (_ : CoqBigInt.t) =>
     vs_ty (snd r) = vs_ty v1).
Proof.
  eapply st_spec_weaken_post; [| apply rename_spec].
  simpl. intros i x _ Hx; rewrite Hx; reflexivity.
Qed.

(*The resulting variable is the original variable with the state as the ID*)
Lemma t_open_bound_var tb1:
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun (x : full_st) (y : TermDefs.vsymbol * term_c) (_ : full_st) => fst y = vsym_with (fst (fst tb1)) (fst x)).
Proof.
  destruct tb1 as [[v1 b1] t1].
  apply errst_spec_weaken_post with (Q1:=fun s1 tb2 _ => fst tb2 = vsym_with v1 (fst s1) /\ True);
  [ intros; tauto|].
  apply ErrStateHoare.errst_spec_tup1 with (P:=fun s1 tb2 _ => fst tb2 = vsym_with v1 s1) 
  (Q:=fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*main proof*)
  unfold t_open_bound.
  eapply prove_st_spec_bnd with (P1:=fun _ => True) (Q1:=fun s1 v _ => snd v = vsym_with v1 s1)
  (P2:=fun _ _ => True) (Q2:=fun x _ y _ => snd x = fst y); auto.
  3: { intros s1 _ _ x y Hid Hxy; rewrite <- Hxy; auto. }
  2: { intros [m v]; simpl. apply prove_st_spec_ret. simpl. auto. }
  apply rename_spec.
Qed.

(*A corollary*)
Corollary rename_tag_spec m v1:
st_spec (fun _ : CoqWeakhtbl.tag => True) (vs_rename m v1)
  (fun (s1 : CoqWeakhtbl.tag) (v : Mvs.t term_c * TermDefs.vsymbol) (_ : CoqWeakhtbl.tag) =>
   id_tag (vs_name (snd v)) = s1).
Proof.
  eapply st_spec_weaken_post; [| apply rename_spec]; simpl. intros i x _ Hx. rewrite Hx. reflexivity.
Qed.

End Var.

(*Part 4: map of [vs_rename]*)
Section Map.

Lemma vs_rename_map m v1:
  st_spec (fun _ => True) (vs_rename m v1)
    (fun _ r _ => fst r = Mvs.add v1 (t_var (snd r)) m).
Proof.
  unfold vs_rename.
  eapply prove_st_spec_bnd_nondep with (Q1:=fun _ _ => True) (Q2:= fun _ y _ => fst y = Mvs.add v1 (t_var (snd y)) m); auto.
  1: { unfold st_spec; auto. }
  intros x. apply prove_st_spec_ret. auto.
Qed.

Definition map_idents_wf (m: Mvs.t term_c) s : Prop :=
  forall x y, Mvs.find_opt x m = Some y -> idents_of_term_wf y s.

(*A corollary of results about maps, ints, and vars*)
Lemma vs_rename_map_idents_wf v1: st_spec (fun _ : CoqWeakhtbl.tag => True) (vs_rename Mvs.empty v1)
  (fun (_ : CoqWeakhtbl.tag) (r : Mvs.t term_c * TermDefs.vsymbol) (s2 : CoqWeakhtbl.tag) =>
   map_idents_wf (fst r) s2).
Proof.
  apply st_spec_weaken with (P1:=fun _ => True /\ True /\ True) (Q1:=fun s1 r s2 => id_tag (vs_name (snd r)) = s1 /\ s1 < s2 /\
    fst r = Mvs.add v1 (t_var (snd r)) Mvs.empty); auto.
  - (*Prove implication*)
    intros i x i2 [Hi [Hii2 Hx]]. unfold map_idents_wf.
    intros x1 y1. rewrite Hx. rewrite Mvs.add_spec, Mvs.empty_spec.
    destruct (Vsym.Tg.equal x1 v1) eqn : Heq; try discriminate.
    intros Hsome; inversion Hsome; subst.
    unfold idents_of_term_wf. simpl. intros i [Hi | []]. subst. auto.
  - (*spec*)
    apply st_spec_and; [apply rename_tag_spec |apply st_spec_and; [apply vs_rename_lt| apply vs_rename_map]].
Qed.

End Map.

(*Part 5: wf of result*)

Section Wf.

Lemma concat_map_sublist {A B: Type} (f: A -> list B) (l1 l2: list A) (Hsub: forall x, In x l1 -> In x l2):
  forall x, In x (concat (map f l1)) -> In x (concat (map f l2)).
Proof.
  intros x Hinx. rewrite in_concat in *. destruct Hinx as [y [Hiny Hinx]]. rewrite in_map_iff in Hiny.
  destruct Hiny as [z [Hy Hinz]]; subst. exists (f z). split; auto. apply in_map; auto.
Qed.

(*Then, prove output wf*)
(*Need that initial vsym is wf for hash pruporses*)
Lemma t_open_bound_res_wf tb1 (Hwf: types_wf  (snd tb1)) :
  errst_spec (fun s1 => vsym_st_wf (fst (fst tb1)) s1 /\ term_st_wf (snd tb1) s1)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) s2 => 
    vsym_st_wf (fst tb2) s2 /\ term_st_wf (snd tb2) s2).
Proof.
  apply errst_spec_weaken with 
    (P1:=fun s1 => (vsym_ident_wf (fst (fst tb1)) (fst s1) /\
      idents_of_term_wf (snd tb1) (fst s1)) /\
      (vsym_hash_wf (fst (fst tb1)) (snd s1) /\ term_hash_wf (snd tb1) (snd s1)))
    (Q1:=fun _ tb2 s => (vsym_ident_wf (fst tb2) (fst s) /\
      idents_of_term_wf (snd tb2) (fst s)) /\
      (vsym_hash_wf (fst tb2) (snd s) /\ term_hash_wf (snd tb2) (snd s))).
  { intros i. unfold vsym_st_wf, term_st_wf; tauto. }
  { intros _ x f. unfold vsym_st_wf, term_st_wf; tauto. }
  eapply errst_spec_tup1' with (P1:=fun s =>  (vsym_ident_wf (fst (fst tb1)) s /\ idents_of_term_wf (snd tb1) s))
  (Q1:=fun s => vsym_hash_wf (fst (fst tb1)) s /\ term_hash_wf (snd tb1) s)
  (P2:=fun _ tb2 s => vsym_ident_wf (fst tb2) s /\ idents_of_term_wf (snd tb2) s)
  (Q:=fun _ tb2 s => vsym_hash_wf (fst tb2) s /\ term_hash_wf (snd tb2) s).
  - (*Prove hash pres*) intros s x s1.
    intros [Hhash1 Hhash2].
    (*Idea: need that this is same vsymbol w diff name*)
    destruct tb1 as [[v1 b1] t1]. simpl.
    cbn. (*TODO: bad*) destruct v1 as [vn vty]; simpl in *.
    destruct (runState (IdCtr.get tt) x). destruct (runState (IdCtr.incr tt) t0). simpl.
    intros Hinr; inversion Hinr; subst; simpl in *; clear Hinr.
    split. 
    + unfold vsym_hash_wf, gen_hash_wf in *. simpl in *. auto.
    + unfold term_hash_wf, gen_hash_wf in *. simpl in *. destruct Hhash2 as [Hhash2 Hhash3].
      set (m:=(Mvs.add {| vs_name := vn; vs_ty := vty |}
                 (t_var
                    {|
                      vs_name :=
                        {|
                          id_string := id_string vn;
                          id_attrs := Sattr.union Sattr.empty (id_attrs vn);
                          id_loc := id_loc vn;
                          id_tag := CoqWeakhtbl.create_tag t
                        |};
                      vs_ty := vty
                    |}) Mvs.empty)) in *.
      assert (Hm: forall v t, Mvs.find_opt v m = Some t -> exists v' : TermDefs.vsymbol, t = t_var v' /\ vs_ty v = vs_ty v').
      {
        intros v tm1. subst m. rewrite Mvs.add_spec.
        destruct (Vsym.Tg.equal v {| vs_name := vn; vs_ty := vty |}) eqn : heq.
        - intros Hsome; inversion Hsome; subst; simpl; auto. apply vsymbol_eqb_eq in heq.
          subst. eexists. split; [reflexivity | reflexivity].
        - rewrite Mvs.empty_spec; discriminate.
      }
      split.
      * clear -Hhash2 Hwf Hm. unfold all_in_hashtable in *.
        intros x Hin. apply concat_map_sublist with (l2:=(tys_of_term t1)) in Hin; auto.
        apply t_subst_unsafe_tys; auto.
      * clear -Hhash3 Hwf Hm. unfold all_idents_smaller in *.
        intros x Hin. apply concat_map_sublist with (l2:=(tys_of_term t1)) in Hin; auto.
        apply t_subst_unsafe_tys; auto.
  - (*Now reason about idents*)
    apply errst_spec_st.
    unfold t_open_bound.
    destruct tb1 as [[v1 b1] t1]. simpl.
    eapply prove_st_spec_bnd_nondep with (Q1:=fun mv s2 => (vsym_ident_wf (snd mv) s2 /\ map_idents_wf (fst mv) s2) /\
      idents_of_term_wf t1 s2) (Q2:=fun _ vt s2 => vsym_ident_wf (fst vt) s2 /\ idents_of_term_wf (snd vt) s2); auto.
    + (*Prove rename part - split and use invariant preservation for 2nd*)
      apply st_spec_and.
      2: { eapply st_spec_weaken_post with (Q1:=fun s1 _ s2 => idents_of_term_wf t1 s1 /\ s1 < s2).
        - intros i1 _ i2. unfold idents_of_term_wf. intros [Hall Hi12] i Hi. apply Hall in Hi; lia.
        - apply st_spec_weaken_pre with (P1:=fun s => idents_of_term_wf t1 s /\ True).
          + intros; tauto.
          + apply st_spec_and.
            * apply st_spec_init.
            * apply vs_rename_lt.
      }
      (*And now prove that new vsym is wf because its value is larger (could prove same)*)
      apply st_spec_weaken with (P1:=fun _ => True /\ True /\ True) (Q1:=fun s1 v s2 => 
        id_tag (vs_name (snd v)) = s1 /\ map_idents_wf (fst v) s2 /\ s1 < s2); auto.
      2: { apply st_spec_and; [apply rename_tag_spec|apply st_spec_and; [apply vs_rename_map_idents_wf | apply vs_rename_lt]]. }
      intros i x f [Hi [Hwfm Hif]]; subst. split; auto. 
    + intros [m v]. simpl. apply prove_st_spec_ret. simpl. intros i [[Hv Hmwf] Ht]. split; auto.
      unfold idents_of_term_wf in *. intros i' Hini'.
      unfold t_subst_unsafe in Hini'.
      destruct (Mvs.is_empty _ _); auto. apply idents_of_subst in Hini'.
      destruct Hini' as [Hin | Hin]; auto.
      unfold ident_in_map in Hin. unfold map_idents_wf in Hmwf.
      destruct Hin as [x [y [Hxy Hin]]]. apply Hmwf in Hxy. auto.
Qed.

End Wf.

(*Now prove actual result - most of work done in SubstUnsafeProofs.v*)
Section OpenBound.

(*Term of result*)
Lemma t_open_bound_subst tb:
  errst_spec (fun (_: full_st) => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
    (fun _ tb2 _ => snd tb2 = t_subst_unsafe (Mvs.add (fst (fst tb)) (t_var (fst tb2)) Mvs.empty) (snd tb)).
Proof.
  apply errst_spec_weaken with (P1:=fun _ => True /\ True) 
    (Q1:=fun _ tb2 _ => snd tb2 = t_subst_unsafe (Mvs.add (fst (fst tb)) (t_var (fst tb2)) Mvs.empty) (snd tb) /\ True); try solve[tauto].
  apply errst_spec_tup1' with (P1:=fun _ => True)
    (P2:=fun _ tb2 _ => snd tb2 = t_subst_unsafe (Mvs.add (fst (fst tb)) (t_var (fst tb2)) Mvs.empty) (snd tb)) (Q1:=fun _ => True) (Q:=fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*state proof*)
  unfold t_open_bound. destruct tb as [[v1 b1] t1].
  apply prove_st_spec_bnd_nondep with (Q1:=fun r _ => fst r = Mvs.add v1 (t_var (snd r)) Mvs.empty)
  (Q2:= fun _ tb2 _ => snd tb2 = t_subst_unsafe (Mvs.add v1 (t_var (fst tb2)) Mvs.empty) t1); auto; [apply vs_rename_map|].
  intros [m v]. apply prove_st_spec_ret. simpl. intros _ Hm. subst; auto.
Qed.

(*The full spec: opening a binder is the same as substituting in the returned variable for the
  old bound variable*)
Theorem t_open_bound_res_tm tb1 e1 (Hwf: types_wf (snd tb1)):
  eval_term (snd tb1) = Some e1 ->
   errst_spec (fun (_: full_st) => True)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) _ => 
    eval_term (snd tb2) = Some (sub_var_t (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1)).
Proof.
  intros Heval.
  eapply errst_spec_weaken_post; [| apply errst_spec_split; [apply t_open_bound_subst| apply t_open_bound_var]].
  simpl. intros i [v2 t2] _ [Ht2 Hv2]. destruct tb1 as [[v1 b1] t1]; simpl in *.
  subst.
  rewrite t_subst_unsafe_eval_term with (e1:=e1); auto.
  - rewrite sub_ts_alt_equiv, sub_var_t_equiv, sub_t_equiv.
    rewrite eval_subs_map_singleton with (g1:=(Tvar (eval_vsymbol (vsym_with v1 (fst i))))); auto.
  - (*only 1 var so all valid*) unfold subs_map_valid. rewrite Forall_forall. intros x Hinx. 
    assert (Hget: Mvs.find_opt (fst x) (Mvs.add v1 (t_var (vsym_with v1 (fst i))) Mvs.empty) = Some (snd x)).
    { apply Mvs.bindings_spec. exists (fst x). rewrite Vsym.Tg.eq_refl; destruct x; auto. }
    clear Hinx. rewrite Mvs.add_spec, Mvs.empty_spec in Hget.
    destruct (Vsym.Tg.equal (fst x) v1) eqn : Heq; try discriminate. inversion Hget; subst.
    auto.
  - (*same for type*) intros v t. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal v v1) eqn : Heq;
    try discriminate. inv Hsome. simpl. apply vsymbol_eqb_eq in Heq. subst; reflexivity.
Qed.

(*Formula version*)
Theorem t_open_bound_res_fmla tb1 e1  (Hwf: types_wf (snd tb1)):
  eval_fmla (snd tb1) = Some e1 ->
   errst_spec (fun (_ : full_st) => True)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) s2 => 
    eval_fmla (snd tb2) = Some (sub_var_f (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1)).
Proof.
  intros Heval.
  eapply errst_spec_weaken_post; [| apply errst_spec_split; [apply t_open_bound_subst| apply t_open_bound_var]].
  simpl. intros i [v2 t2] _ [Ht2 Hv2]. destruct tb1 as [[v1 b1] t1]; simpl in *.
  subst.
  rewrite t_subst_unsafe_eval_fmla with (e1:=e1); auto.
  - rewrite sub_fs_alt_equiv, sub_var_f_equiv, sub_f_equiv.
    rewrite eval_subs_map_singleton with (g1:=(Tvar (eval_vsymbol (vsym_with v1 (fst i))))); auto.
  - (*only 1 var so all valid*) unfold subs_map_valid. rewrite Forall_forall. intros x Hinx. 
    assert (Hget: Mvs.find_opt (fst x) (Mvs.add v1 (t_var (vsym_with v1 (fst i))) Mvs.empty) = Some (snd x)).
    { apply Mvs.bindings_spec. exists (fst x). rewrite Vsym.Tg.eq_refl; destruct x; auto. }
    clear Hinx. rewrite Mvs.add_spec, Mvs.empty_spec in Hget.
    destruct (Vsym.Tg.equal (fst x) v1) eqn : Heq; try discriminate. inversion Hget; subst.
    auto.
  - (*same for type*) intros v t. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal v v1) eqn : Heq;
    try discriminate. inv Hsome. simpl. apply vsymbol_eqb_eq in Heq. subst; reflexivity.
Qed.

End OpenBound.

(*Also, -types_wf still holds*)

Lemma t_open_bound_types_wf tb (Hwf: types_wf (snd tb)):
  errst_spec (fun (_: full_st) => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
    (fun _ tb2 _ => types_wf (snd tb2)).
Proof.
  eapply errst_spec_weaken_post; [| apply errst_spec_split; [apply t_open_bound_subst| apply t_open_bound_var]].
  simpl. intros i [v2 t2] _ [Ht2 Hv2]. destruct tb as [[v1 b1] t1]; simpl in *. subst.
  apply types_wf_sub; auto.
  + intros x y. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal x v1) eqn : Heq; try discriminate.
    apply vsymbol_eqb_eq in Heq. subst. inv Hsome. rewrite types_wf_rewrite; simpl. reflexivity.
  + intros x y. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal x v1) eqn : Heq; try discriminate.
    apply vsymbol_eqb_eq in Heq. subst. inv Hsome. reflexivity.
Qed.


(*Easy corollary of existing results*)
Lemma t_open_bound_ty tb (Hwf: types_wf (snd tb)):
  errst_spec (fun (_: full_st) => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
    (fun _ y _ => t_ty_of (snd y) = t_ty_of (snd tb)).
Proof.
  eapply errst_spec_weaken_post; [|apply errst_spec_split; [apply t_open_bound_subst| apply t_open_bound_var]].
  simpl. intros i [v2 t2] _ [Hsnd Hfst]. simpl in *; subst.
  unfold t_subst_unsafe. destruct (Mvs.is_empty _ _); auto.
  apply ty_subst_unsafe_aux_ty; auto.
  (*TODO: should be in separate lemma*)
  intros v t. rewrite Mvs.add_spec, Mvs.empty_spec.
  destruct (Vsym.Tg.equal v (fst (fst tb))) eqn : Heq; try discriminate.
  inv Hsome. simpl. apply vsymbol_eqb_eq in Heq. subst.
  reflexivity.
Qed. 

