Require Import TermDefs Relations VsymCount InversionLemmas.
From Proofs Require Import Task.



(*TODO: copied from [eliminate_algebraic_typing]; MOVE!*)

Lemma fmla_fv_fforalls (vs: list vsymbol) (f: formula):
  fmla_fv (fforalls vs f) = aset_diff (list_to_aset vs) (fmla_fv f).
Proof.
  induction vs as [| v vs IH]; simpl; auto.
  - rewrite list_to_aset_nil, aset_diff_empty. reflexivity.
  - rewrite IH. rewrite list_to_aset_cons.
    apply aset_ext. intros x. simpl_set. 
    split; intros; destruct_all; subst; split; auto.
    intros [Hxv | Hinx]; subst; contradiction.
Qed.

Lemma fmla_fv_fexists (vs: list vsymbol) (f: formula):
  fmla_fv (fexists vs f) = aset_diff (list_to_aset vs) (fmla_fv f).
Proof.
  induction vs as [| v vs IH]; simpl; auto.
  - rewrite list_to_aset_nil, aset_diff_empty. reflexivity.
  - rewrite IH. rewrite list_to_aset_cons.
    apply aset_ext. intros x. simpl_set. 
    split; intros; destruct_all; subst; split; auto.
    intros [Hxv | Hinx]; subst; contradiction.
Qed.

Lemma fmla_fv_gen_quants b vs f:
  fmla_fv (gen_quants b vs f) = aset_diff (list_to_aset vs) (fmla_fv f).
Proof.
  destruct b; [apply fmla_fv_fforalls | apply fmla_fv_fexists].
Qed.

(*Various definitions and proofs about variables of (augmented) terms.
  We define evaluation of maps and show that these evaluate to the
  corresponding core functions*)

Section FreeVars.

(*Ignore ocurrence count*)

Fixpoint p_free_vars (p: pattern_c) : Svs.t :=
  match pat_node_of p with
  | TermDefs.Pvar v => Svs.singleton v
  | Papp l ps => fold_right Svs.union Svs.empty (map p_free_vars ps)
  | TermDefs.Por p1 p2 => Svs.union (p_free_vars p1) (p_free_vars p2)
  | Pas p v => Svs.union (p_free_vars p) (Svs.singleton v)
  | TermDefs.Pwild => Svs.empty
  end.

Fixpoint t_free_vars (t: term_c) : Svs.t :=
  match t_node_of t with
  | TermDefs.Tvar v => Svs.singleton v
  | TermDefs.Tlet t1 (v, _, t2) => Svs.union (t_free_vars t1) (Svs.remove v (t_free_vars t2))
  | TermDefs.Tif t1 t2 t3 => Svs.union (t_free_vars t1) (Svs.union (t_free_vars t2) (t_free_vars t3))
  | Tapp l tms => (fold_right Svs.union Svs.empty (map t_free_vars tms))
  | Tcase t1 ps => Svs.union (t_free_vars t1) (fold_right Svs.union Svs.empty
      (map (fun x => Svs.diff (t_free_vars (snd x)) (p_free_vars (fst (fst x)))) ps) )
  | TermDefs.Teps (v, _, t) => Svs.remove v (t_free_vars t)
  | Tquant _ (vs, _, _, t) => Svs.diff (t_free_vars t) (Svs.of_list vs)
  | Tbinop _ t1 t2 => Svs.union (t_free_vars t1) (t_free_vars t2)
  | Tnot t1 => t_free_vars t1
  | _ => Svs.empty
  end.

(*rewrite lemmas*)
Lemma p_free_vars_rewrite p:
  p_free_vars p =
  match pat_node_of p with
  | TermDefs.Pvar v => Svs.singleton v
  | Papp l ps => fold_right Svs.union Svs.empty (map p_free_vars ps)
  | TermDefs.Por p1 p2 => Svs.union (p_free_vars p1) (p_free_vars p2)
  | Pas p v => Svs.union (p_free_vars p) (Svs.singleton v)
  | TermDefs.Pwild => Svs.empty
  end.
Proof. destruct p; auto. Qed.

Lemma t_free_vars_rewrite t:
  t_free_vars t = match t_node_of t with
  | TermDefs.Tvar v => Svs.singleton v
  | TermDefs.Tlet t1 (v, _, t2) => Svs.union (t_free_vars t1) (Svs.remove v (t_free_vars t2))
  | TermDefs.Tif t1 t2 t3 => Svs.union (t_free_vars t1) (Svs.union (t_free_vars t2) (t_free_vars t3))
  | Tapp l tms => (fold_right Svs.union Svs.empty (map t_free_vars tms))
  | Tcase t1 ps => Svs.union (t_free_vars t1) (fold_right Svs.union Svs.empty
      (map (fun x => Svs.diff (t_free_vars (snd x)) (p_free_vars (fst (fst x)))) ps) )
  | TermDefs.Teps (v, _, t) => Svs.remove v (t_free_vars t)
  | Tquant _ (vs, _, _, t) => Svs.diff (t_free_vars t) (Svs.of_list vs)
  | Tbinop _ t1 t2 => Svs.union (t_free_vars t1) (t_free_vars t2)
  | Tnot t1 => t_free_vars t1
  | _ => Svs.empty
  end.
Proof. destruct t; auto. Qed.

End FreeVars.

Section Eq.

(*NOTE: not extensional anymore so can't use equality*)
Definition mvs_eq {A: Type} (m1 m2: Mvs.t A): Prop :=
  forall x, Mvs.find_opt x m1 = Mvs.find_opt x m2.
Definition svs_eq {A B: Type} (s1 : Mvs.t A) (s2: Mvs.t B) : Prop :=
  forall x, Mvs.mem x s1 = Mvs.mem x s2.

(*iff but dont prove*)
Lemma mvs_svs_eq (s1 s2: Svs.t):
  svs_eq s1 s2 ->
  mvs_eq s1 s2.
Proof.
  unfold svs_eq, mvs_eq. intros Heq x.
  unfold Svs.mem, Svs.M.mem in Heq.
  specialize (Heq x). destruct (Mvs.find_opt x s1) as [[]|] eqn : Hget1; simpl in *;
  destruct (Mvs.find_opt x s2) as [[]|] eqn : Hget2; simpl in *; try discriminate; auto.
Qed.

(*Could prove in general but whatever*)
Lemma mvs_mem_map {A B: Type} (m: Mvs.t A) (f: A -> B) x:
  Mvs.mem x (Mvs.map f m) = Mvs.mem x m.
Proof.
  rewrite !Mvs.mem_spec. destruct (Mvs.find_opt x m) as [y|] eqn : Hget1; simpl;
  destruct (Mvs.find_opt x (Mvs.map f m)) as [y1|] eqn : Hget2; auto.
  - assert (Hmem: Mvs.find_opt x (Mvs.map f m) = Some (f y)). {
      apply Mvs.map_spec. exists x. exists y. split_all; auto. apply Vsym.Tg.eq_refl.
    }
    rewrite Hmem in Hget2; discriminate.
  - rewrite Mvs.map_spec in Hget2. destruct Hget2 as [k1 [v1 [Heq [Hfind Hf]]]]; subst.
    apply vsymbol_eqb_eq in Heq. subst. rewrite Hfind in Hget1. discriminate.
Qed.

(*TODO: should use svs_eq in var condition*)
Lemma mvs_eq_map_equiv {A: Type} (m: Mvs.t A) (s: Svs.t):
  mvs_eq (Mvs.map (fun _ => tt) m) s <-> svs_eq m s.
Proof.
  unfold mvs_eq, svs_eq. split; intros Heq x.
  - unfold Mvs.mem. rewrite <- Heq. rewrite <- !Mvs.mem_spec, mvs_mem_map; auto.
  - specialize (Heq x). unfold Mvs.mem in *. destruct (Mvs.find_opt x s); auto; simpl in *.
    + apply Svs.M.map_spec. destruct (Mvs.find_opt x m) as [y|] eqn : Hget; try discriminate.
      exists x. exists y. destruct u; split_all; auto. apply vsymbol_eqb_eq. auto.
    + destruct (Mvs.find_opt x (Mvs.map (fun _ => tt) m)) as [y|] eqn : Hget; auto.
      apply Mvs.map_spec in Hget. destruct Hget as [k1 [v1 [Heqk [Hfind Hy]]]]. subst.
      apply vsymbol_eqb_eq in Heqk. subst. rewrite Hfind in Heq. discriminate.
Qed.

(*not iff*)
Lemma mvs_svs_eq' {A: Type} (m1 m2: Mvs.t A):
  mvs_eq m1 m2 -> svs_eq m1 m2.
Proof.
  unfold mvs_eq, svs_eq. intros Hfind x. unfold Mvs.mem. rewrite Hfind; auto.
Qed.


End Eq.

(*Lemmas about [svs_eq]*)
Section SvsEq.

(*Equivalence relation*)
Lemma svs_eq_refl {A: Type} (m: Mvs.t A):
  svs_eq m m.
Proof.
  unfold svs_eq; auto.
Qed.

Lemma svs_eq_sym {A B: Type} (m1: Mvs.t A) (m2: Mvs.t B):
  svs_eq m1 m2 ->
  svs_eq m2 m1.
Proof.
  unfold svs_eq. auto.
Qed.

Lemma svs_eq_trans {A B C: Type} (m1: Mvs.t A) (m2: Mvs.t B) (m3: Mvs.t C):
  svs_eq m1 m2 ->
  svs_eq m2 m3 ->
  svs_eq m1 m3.
Proof.
  unfold svs_eq. intros Heq1 Heq2 x. rewrite Heq1. auto.
Qed.

(*Congruence lemmas*)

(*empty*)
Lemma svs_eq_empty {A: Type}:
  svs_eq (@Mvs.empty A) Svs.empty.
Proof.
  unfold svs_eq, Mvs.mem, Svs.empty. intros x.
  rewrite !Mvs.empty_spec. reflexivity.
Qed.

(*singleton*)
Lemma svs_eq_singleton {A: Type} x (y: A):
  svs_eq (Mvs.singleton _ x y) (Svs.singleton x).
Proof.
  unfold svs_eq, Mvs.mem, Svs.singleton. intros z.
  rewrite !Mvs.singleton_spec; auto. 2: exact tt.
  destruct (Vsym.Tg.equal z x); auto.
Qed.

(*remove*)
Lemma svs_eq_remove {A B: Type} (m1: Mvs.t A) (m2: Mvs.t B) x:
  svs_eq m1 m2 ->
  svs_eq (Mvs.remove _ x m1) (Mvs.remove _ x m2).
Proof.
  unfold svs_eq. intros Heq y. unfold Mvs.mem in *.
  rewrite !Mvs.remove_spec. destruct (Vsym.Tg.equal y x); auto.
Qed.

(*diff*)
Lemma svs_eq_diff {A B C D: Type} (m1: Mvs.t A) (m2: Mvs.t B) (s1: Mvs.t C) (s2:Mvs.t D):
  svs_eq m1 m2 ->
  svs_eq s1 s2 ->
  svs_eq (Mvs.set_diff _ _ m1 s1) (Mvs.set_diff _ _ m2 s2).
Proof.
  unfold svs_eq. intros Heq1 Heq2 y. unfold Mvs.mem in *.
  rewrite !Mvs.set_diff_spec. specialize (Heq1 y); specialize (Heq2 y).
  destruct (Mvs.find_opt y m1); destruct (Mvs.find_opt y m2); destruct (Mvs.find_opt y s1);
  destruct (Mvs.find_opt y s2); simpl in *; auto.
Qed.

(*map*)
Lemma svs_eq_map {A B: Type} (f: A -> B) (m: Mvs.t A):
  svs_eq (Mvs.map f m) m.
Proof.
  unfold svs_eq. intros x. apply mvs_mem_map.
Qed.

(*set union*)
Lemma svs_eq_set_union {A B: Type} (m1 m2: Mvs.t A) (m3 m4: Mvs.t B):
  svs_eq m1 m3 ->
  svs_eq m2 m4 ->
  svs_eq (Mvs.set_union _ m1 m2) (Mvs.set_union _ m3 m4).
Proof.
  unfold svs_eq. intros Heq1 Heq2 x. unfold Mvs.mem in *.
  rewrite !Mvs.set_union_spec. specialize (Heq1 x); specialize (Heq2 x).
  destruct (Mvs.find_opt x m1); destruct (Mvs.find_opt x m2);
  destruct (Mvs.find_opt x m3); destruct (Mvs.find_opt x m4); auto.
Qed.

(*union/vars_union*)
Lemma svs_eq_vars_union m1 m2 s1 s2:
  svs_eq m1 s1 ->
  svs_eq m2 s2 ->
  svs_eq (TermFuncs.vars_union m1 m2) (Svs.union s1 s2).
Proof.
  unfold svs_eq; intros Heq1 Heq2 x.
  unfold TermFuncs.vars_union, Svs.union, Mvs.mem.
  rewrite Mvs.union_spec; auto.
  rewrite Mvs.set_union_spec.
  unfold Mvs.mem in *.
  specialize (Heq1 x); specialize (Heq2 x).
  destruct (Mvs.find_opt x m1); destruct (Mvs.find_opt x m2);
  destruct (Mvs.find_opt x s1); destruct (Mvs.find_opt x s2); simpl in *; auto.
Qed.

(*A few other results about union*)

(*reason about folding union*)
Lemma in_fold_union x (l: list Svs.t):
  Mvs.mem x (fold_right Svs.union Svs.empty l) <-> exists y, In y l /\ Mvs.mem x y.
Proof.
  induction l as [| h t IH]; simpl.
  - unfold Mvs.mem, Svs.empty. rewrite Mvs.empty_spec. simpl. split; try discriminate.
    intros; destruct_all; contradiction.
  - unfold Mvs.mem in *. unfold Svs.union. rewrite Mvs.set_union_spec.
    destruct (Mvs.find_opt x h) as [y|] eqn : Hget.
    + simpl. split; auto. intros _. exists h. rewrite Hget; auto.
    + rewrite IH. split.
      * intros [y [Hiny Hsome]]. exists y. auto.
      * intros [y [[Hhy | Hiny] Hsome]]; subst; eauto. rewrite Hget in Hsome; discriminate.
Qed.

(*and reversal (to relate foldl and foldr)*)
Lemma fold_right_union_rev (l: list Svs.t):
  svs_eq (fold_right Svs.union Svs.empty l) (fold_right Svs.union Svs.empty (rev l)).
Proof.
  unfold svs_eq. intros x.
  apply is_true_eq.
  rewrite !in_fold_union. setoid_rewrite <- in_rev. reflexivity.
Qed.

(*commutativity*)
Lemma svs_eq_union_comm {A: Type} (m1 m2: Mvs.t A):
  svs_eq (Mvs.set_union _ m1 m2) (Mvs.set_union _ m2 m1).
Proof.
  unfold svs_eq. intros x. unfold Mvs.mem. rewrite !Mvs.set_union_spec.
  destruct (Mvs.find_opt x m1); destruct (Mvs.find_opt x m2); auto.
Qed.

(*associativity*)
Lemma svs_eq_union_assoc {A: Type} (m1 m2 m3: Mvs.t A):
  svs_eq (Mvs.set_union _ m1 (Mvs.set_union _ m2 m3)) (Mvs.set_union _ (Mvs.set_union _ m1 m2) m3).
Proof.
  unfold svs_eq. intros x. unfold Mvs.mem. rewrite !Mvs.set_union_spec.
  destruct (Mvs.find_opt x m1); destruct (Mvs.find_opt x m2); destruct (Mvs.find_opt x m3); auto.
Qed.

End SvsEq.

(*It is very helpful for [eval_vsymbol] to be injective. Though it is not
  compositional, we want to reason about maps over core and augmented vsymbols, and it
  is very useful for the domains of these maps to be the same*)
Section EvalInj.

Lemma pos_to_string_inj p1 p2:
  pos_to_string p1 = pos_to_string p2 ->
  p1 = p2.
Proof.
  revert p2. induction p1 as [p1 IH | p1 IH |]; intros [p2 | p2 |]; simpl; try discriminate; auto.
  - intros Heq. apply str_app_inj_l in Heq. f_equal. auto.
  - destruct p1; discriminate.
  - intros Heq. apply str_app_inj_l in Heq. f_equal. auto.
  - destruct p2; discriminate.
Qed.

Lemma eval_vsymbol_inj x y:
  eval_vsymbol x = eval_vsymbol y ->
  x = y.
Proof.
  unfold eval_vsymbol.
  intros Heq. apply pair_equal_spec in Heq. destruct Heq as [Hpos Hty].
  apply pos_to_string_inj in Hpos.
  apply (@countable.encode_inj _ _ vsymbol_countable) in Hpos. auto.
Qed.

End EvalInj.


(*evaluate a variable set*)
Section EvalSet.

(*ints tell number of times, but we just care about existence - can we ignore this*)
Definition eval_varset {A : Type} (s: Mvs.t A) : aset vsymbol :=
  list_to_aset (map eval_vsymbol (Mvs.keys _ s)).

Lemma eval_varset_mem {A: Type} (s: Mvs.t A) x:
  aset_mem x (eval_varset s) <-> exists y, x = eval_vsymbol y /\ Mvs.mem y s.
Proof.
  unfold eval_varset. simpl_set. rewrite in_map_iff.
  setoid_rewrite Mvs.mem_spec. unfold Mvs.keys.
  setoid_rewrite in_map_iff.
  split.
  - intros [x1 [Hx [x2 [Hx1 Hin]]]]. subst.
    exists (fst x2). split; auto.
    assert (Hfind: Mvs.find_opt (fst x2) s = Some (snd x2)). {
      apply Mvs.bindings_spec. exists (fst x2); split; auto.
      - apply vsymbol_eqb_eq. auto.
      - destruct x2; auto.
    }
    rewrite Hfind; auto.
  - intros [y [Hx Hfind]]. subst. exists y. split; auto.
    destruct (Mvs.find_opt y s) as [z|] eqn : Hlook; [|discriminate].
    exists (y, z). split; auto. apply Mvs.bindings_spec in Hlook.
    destruct Hlook as [k1 [Heq Hin]]. apply vsymbol_eqb_eq in Heq. subst.
    auto.
Qed.

Lemma mvs_eq_eval_varset {A: Type} (m1 m2: Mvs.t A):
  mvs_eq m1 m2 ->
  eval_varset m1 = eval_varset m2.
Proof.
  unfold mvs_eq; intros Heq.
  apply aset_ext. intros x. rewrite !eval_varset_mem.
  setoid_rewrite Mvs.mem_spec. setoid_rewrite Heq. reflexivity.
Qed.

Lemma svs_eq_eval_varset (s1 s2: Svs.t):
  svs_eq s1 s2 ->
  eval_varset s1 = eval_varset s2.
Proof.
  intros Heq. apply mvs_eq_eval_varset, mvs_svs_eq; auto.
Qed.

(*Correspondences*)


Lemma eval_varset_singleton {A: Type} x y:
  @eval_varset A (Mvs.singleton _ x y) = aset_singleton (eval_vsymbol x).
Proof.
  apply aset_ext. intros z. simpl_set.
  rewrite eval_varset_mem. split.
  - intros [y1 [Hz Hiny]]; subst.
    rewrite Mvs.mem_spec, Mvs.singleton_spec in Hiny; auto.
    destruct (Vsym.Tg.equal y1 x) eqn : Heq; try discriminate.
    apply vsymbol_eqb_eq in Heq. subst; auto.
  - intros Hz; subst. exists x. split; auto.
    rewrite Mvs.mem_spec, Mvs.singleton_spec; auto.
    rewrite Vsym.Tg.eq_refl. auto.
Qed.

Lemma eval_varset_union (s1 s2: Svs.t):
  eval_varset (Svs.union s1 s2) = aset_union (eval_varset s1) (eval_varset s2).
Proof.
  apply aset_ext. intros x. simpl_set.
  rewrite !eval_varset_mem. setoid_rewrite Mvs.mem_spec. 
  unfold Svs.union. setoid_rewrite Mvs.set_union_spec.
  split.
  - intros [y [Hxy Hmemy]]; subst. destruct (Mvs.find_opt y s1) eqn : Hfind1.
    + left. exists y. rewrite Hfind1. auto.
    + destruct (Mvs.find_opt y s2) eqn : Hfind2; [|discriminate].
      right. exists y. rewrite Hfind2. auto.
  - intros [[y [Hxy Hsome]] | [y [Hxy Hsome]]]; subst; exists y; split; auto;
    destruct (Mvs.find_opt y s1); auto.
Qed.

Lemma eval_varset_big_union {A} (f: A -> Svs.t)(l: list A):
  eval_varset (fold_right Svs.union Svs.empty (map f l)) =
  aset_big_union (fun x => eval_varset (f x)) l.
Proof.
  induction l as [| h t IH]; simpl; auto.
  rewrite eval_varset_union, IH. reflexivity.
Qed. 

Lemma eval_varset_empty {A}:
  @eval_varset A Mvs.empty = aset_empty.
Proof.
  apply aset_ext. intros x.
  rewrite eval_varset_mem.
  split.
  - intros [y [Hx Hmemy]]. subst.
    rewrite Mvs.mem_spec, Mvs.empty_spec in Hmemy. discriminate.
  - intros Hmem. simpl_set.
Qed.

Lemma eval_varset_remove {A} (m: Mvs.t A) k:
  eval_varset (Mvs.remove _ k m) = aset_remove (eval_vsymbol k) (eval_varset m).
Proof.
  apply aset_ext. intros x. simpl_set. rewrite !eval_varset_mem. setoid_rewrite Mvs.mem_spec.
  setoid_rewrite Mvs.remove_spec. split.
  - intros [y [Hx Heq]]. subst. 
    destruct (Vsym.Tg.equal y k) eqn : Heq'; try discriminate.
    split; eauto. intros Hc. apply eval_vsymbol_inj in Hc. subst. rewrite Vsym.Tg.eq_refl in Heq'.
    discriminate.
  - intros [[y [Hx Hsome]] Hnotx]; subst.
    exists y. split; auto. destruct (Vsym.Tg.equal y k) eqn : Heq; auto.
    apply vsymbol_eqb_eq in Heq. subst. contradiction.
Qed.

Lemma eval_varset_diff {A B} (m1: Mvs.t A) (m2: Mvs.t B):
  eval_varset (Mvs.set_diff _ _ m1 m2) = aset_diff (eval_varset m2) (eval_varset m1).
Proof.
  apply aset_ext. intros x. simpl_set. rewrite !eval_varset_mem. setoid_rewrite Mvs.mem_spec.
  setoid_rewrite Mvs.set_diff_spec. split.
  - intros [y [Hx Heq]]. subst.
    destruct (Mvs.find_opt y m1) eqn : Hfind1; try discriminate.
    destruct (Mvs.find_opt y m2) eqn : Hfin2; try discriminate.
    split.
    + exists y. rewrite Hfind1. auto.
    + intros [y1 [Heqy Hsome]]. apply eval_vsymbol_inj in Heqy. subst.
      rewrite Hfin2 in Hsome. discriminate.
  - intros [[y [Hx Hsome]] Hnotex]. subst. exists y. split; auto. 
    destruct (Mvs.find_opt y m1) eqn : Hget1; try discriminate.
    destruct (Mvs.find_opt y m2) eqn : Hget2; auto.
    exfalso; apply Hnotex. exists y. rewrite Hget2. auto.
Qed.

Lemma eval_varset_add {A: Type} (m: Mvs.t A) x y:
  eval_varset (Mvs.add x y m) = aset_union (aset_singleton (eval_vsymbol x)) (eval_varset m).
Proof.
  apply aset_ext. intros z. simpl_set. rewrite !eval_varset_mem.
  setoid_rewrite Mvs.mem_spec. setoid_rewrite Mvs.add_spec.
  split.
  - intros [y1 [Hzy Hsome]]. subst. destruct ( Vsym.Tg.equal y1 x) eqn : Heq.
    + apply vsymbol_eqb_eq in Heq; subst. auto.
    + right. exists y1. auto.
  - intros [Hz | [y1 [Hz Hsome]]]; subst; eauto.
    + exists x. split; auto. rewrite Vsym.Tg.eq_refl. auto.
    + exists y1. split; auto. destruct (Vsym.Tg.equal y1 x) eqn : Heq; auto.
Qed.

Lemma eval_varset_of_list l:
  eval_varset (Svs.of_list l) = list_to_aset (map eval_vsymbol l).
Proof.
  induction l as [| h t IH ]; simpl; auto. unfold Svs.add.
  rewrite list_to_aset_cons, eval_varset_add, IH. reflexivity.
Qed.

(*[eval_varset] is invariant under mapping*)

Lemma eval_varset_map {A B: Type} (m: Mvs.t A) (f: A -> B):
  eval_varset (Mvs.map f m) = eval_varset m.
Proof.
  apply aset_ext. intros x. rewrite !eval_varset_mem. setoid_rewrite mvs_mem_map. reflexivity.
Qed.

End EvalSet.

(*Prove free vars eval*)
Section EvalFreevars.


Lemma p_free_vars_eval (p: pattern_c) (e: pattern) (Heval: eval_pat p = Some e):
  eval_varset (p_free_vars p) = pat_fv e.
Proof.
  generalize dependent e.
  induction p using pat_ind_alt; simpl; auto; intros e Heval; rewrite p_free_vars_rewrite, Heq.
  - rewrite (eval_pat_tm Heq Heval); simpl.
    apply eval_varset_singleton.
  - rewrite eval_varset_big_union.
    destruct (eval_pat_app Heq Heval) as [l1 [tys1 [ps2 [He [Hl [Htys1 Hps1]]]]]]; subst.
    simpl. clear -H Hps1. generalize dependent ps2. induction ps as [| p1 t1 IH]; simpl.
    + intros [| p2 t2]; try discriminate. auto.
    + inversion H as [| ? ? Heq1 Heq2]; subst; clear H.
      intros ps2 Hbind. apply option_bind_some in Hbind. destruct Hbind as [p2 [Heval1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [t2 [Hopt Hsome]]. inversion Hsome; subst.
      simpl. rewrite (Heq1 _ Heval1). f_equal. auto.
  - rewrite eval_varset_union. destruct (eval_pat_or Heq Heval) as [e1 [e2 [He [Heval1 Heval2]]]].
    subst. rewrite (IHp1 _ Heval1), (IHp2 _ Heval2); auto.
  - destruct (eval_pat_as Heq Heval) as [e1 [He Heval1]]. subst. simpl.
    rewrite eval_varset_union, (IHp1 _ Heval1). f_equal. apply eval_varset_singleton.
  - rewrite (eval_pat_wild Heq Heval). simpl. apply eval_varset_empty.
Qed.


(*And for terms*)
Lemma t_free_vars_eval (t: term_c):
  (forall e (Heval: eval_term t = Some e), eval_varset (t_free_vars t) = tm_fv e) /\
  (forall e (Heval: eval_fmla t = Some e), eval_varset (t_free_vars t) = fmla_fv e).
Proof.
  induction t using term_ind_alt; split; intros e Heval; rewrite t_free_vars_rewrite; try rewrite Heq; try rewrite Ht.
  - (*Tvar*) rewrite (eval_var_tm Heq Heval). simpl. apply eval_varset_singleton.
  - (*Fvar*) exfalso. apply (eval_var_fmla Heq Heval).
  - (*Tconst*) destruct (eval_const_tm Heq Heval) as [c1 [He Hc1]]; subst.
      simpl. apply eval_varset_empty.
  - (*Fconst*) exfalso. apply (eval_const_fmla Heq Heval).
  - (*Tfun*) destruct (eval_app_tm Heq Heval) as [l1 [tys' [tys1 [ts1 [He1 [Hevall [Htys [Htys1 Hts]]]]]]]]; subst.
    simpl. rewrite eval_varset_big_union. clear -Hts H. generalize dependent ts1.
    induction ts as [| t1 tl1 IH]; simpl; auto.
    + intros [| t2 tl2]; try discriminate. auto.
    + inversion H as [| ? ? [Heq1 _] Heq2]; subst; clear H.
      intros ts1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [t2 [Heval1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [tl2 [Hopt Hsome]]. inversion Hsome; subst.
      simpl. rewrite (Heq1 _ Heval1). f_equal. auto.
  - destruct (eval_app_fmla Heq Heval) as [[Hl [t1' [t2' [t3' [t4' [ty1 [Hts [He1 [Ht1' [Ht2' Hty]]]]]]]]]] | 
      [Hl [fs [tys [ty1 [tms [He1 [Hfs [Htys [Htys1 Htms]]]]]]]]]]; subst.
    + (*Feq*) simpl. rewrite !eval_varset_union.
      assert (Hemp: (eval_varset Svs.empty) = aset_empty) by (apply eval_varset_empty). rewrite Hemp, aset_union_empty_r.
      inversion H as [| ? ? [IH1 _] Hrest]; subst. inversion Hrest as [| ? ? [IH2 _] _]; subst; clear H Hrest.
      f_equal; auto.
    + (*Fpred*) simpl. rewrite eval_varset_big_union. clear -Htms H. generalize dependent tms.
      induction ts as [| t1 tl1 IH]; simpl; auto.
      * intros [| t2 tl2]; try discriminate. auto.
      * inversion H as [| ? ? [Heq1 _] Heq2]; subst; clear H.
        intros ts1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [t2 [Heval1 Hbind]].
        apply option_bind_some in Hbind. destruct Hbind as [tl2 [Hopt Hsome]]. inversion Hsome; subst.
        simpl. rewrite (Heq1 _ Heval1). f_equal. auto.
  - (*Tif*) rewrite !eval_varset_union. destruct (eval_if_tm Heq Heval) as [e1 [e2 [e3 [He [He1 [He2 He3]]]]]]; subst.
     simpl. destruct_all. f_equal; auto. f_equal; auto.
  - (*Fif*) rewrite !eval_varset_union. destruct (eval_if_fmla Heq Heval) as [e1 [e2 [e3 [He [He1 [He2 He3]]]]]]; subst.
    simpl. destruct_all. f_equal; auto. f_equal; auto.
  - (*Tlet*) destruct (eval_let_tm Heq Heval) as [e1 [e2 [He [He1 He2]]]]. subst. simpl in *.
    destruct IHt1 as [IH1 _]. destruct IHt2 as [IH2 _]. unfold Svs.remove.
    rewrite !eval_varset_union, (IH1 _ He1), eval_varset_remove, (IH2 _ He2). reflexivity.
  - (*Flet*) destruct (eval_let_fmla Heq Heval) as [e1 [e2 [He [He1 He2]]]]. subst. simpl in *.
    destruct IHt1 as [IH1 _]. destruct IHt2 as [_ IH2]. unfold Svs.remove.
    rewrite !eval_varset_union, (IH1 _ He1), eval_varset_remove, (IH2 _ He2). reflexivity.
  - (*Tmatch*) destruct (eval_match_tm Heq Heval) as [e1 [ty1 [ps1 [He [He1 [Hty1 Hps1]]]]]].
    subst. simpl. rewrite eval_varset_union. destruct IHt1 as [IH1 _]. rewrite (IH1 _ He1).
    f_equal. rewrite eval_varset_big_union. rewrite Forall_map in H. clear -Hps1 H.
    generalize dependent ps1. induction tbs as [| [[p1 b1] t1] tl1 IH]; simpl; auto.
    + intros [| ? ?]; try discriminate; auto.
    + intros ps1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [pt [Hbind1 Hbind2]].
      apply option_bind_some in Hbind1. destruct Hbind1 as [p2 [Hevalp Hbind1]].
      apply option_bind_some in Hbind1. destruct Hbind1 as [t2 [Hevalt Hsome]]. inversion Hsome; subst; clear Hsome.
      apply option_bind_some in Hbind2. destruct Hbind2 as [tl2 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
      simpl. inversion H as [| ? ? [IH1 _] IH2]; subst; clear H. simpl in *.
      unfold Svs.diff. rewrite eval_varset_diff, (p_free_vars_eval _ _ Hevalp), (IH1 _ Hevalt). f_equal. auto.
  - (*Fmatch*) destruct (eval_match_fmla Heq Heval) as [e1 [ty1 [ps1 [He [He1 [Hty1 Hps1]]]]]].
    subst. simpl. rewrite eval_varset_union. destruct IHt1 as [IH1 _]. rewrite (IH1 _ He1).
    f_equal. rewrite eval_varset_big_union. rewrite Forall_map in H. clear -Hps1 H.
    generalize dependent ps1. induction tbs as [| [[p1 b1] t1] tl1 IH]; simpl; auto.
    + intros [| ? ?]; try discriminate; auto.
    + intros ps1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [pt [Hbind1 Hbind2]].
      apply option_bind_some in Hbind1. destruct Hbind1 as [p2 [Hevalp Hbind1]].
      apply option_bind_some in Hbind1. destruct Hbind1 as [t2 [Hevalt Hsome]]. inversion Hsome; subst; clear Hsome.
      apply option_bind_some in Hbind2. destruct Hbind2 as [tl2 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
      simpl. inversion H as [| ? ? [_ IH1] IH2]; subst; clear H. simpl in *.
      unfold Svs.diff. rewrite eval_varset_diff, (p_free_vars_eval _ _ Hevalp), (IH1 _ Hevalt). f_equal. auto.
  - (*Teps*) destruct (eval_eps_tm Heq Heval) as [e1 [He He1]]. simpl in *; subst.
    simpl. unfold Svs.remove. rewrite eval_varset_remove. f_equal. destruct_all; auto.
  - (*Feps*) exfalso. apply (eval_eps_fmla Heq Heval).
  - (*Tquant*) exfalso. apply (eval_quant_tm Heq Heval).
  - (*Fquant*) destruct (eval_quant_fmla Heq Heval) as [e1 [He He1]]. simpl in *. subst. unfold Svs.diff.
    rewrite eval_varset_diff. destruct IHt1 as [_ IH1]. rewrite fmla_fv_gen_quants,  eval_varset_of_list, (IH1 _ He1);
    reflexivity.
  - (*Tbinop*) exfalso. apply (eval_binop_tm Heq Heval).
  - (*Fbinop*) destruct (eval_binop_fmla Heq Heval) as [e1 [e2 [He [He1 He2]]]]. subst.
    simpl. destruct IHt1 as [_ IH1]; destruct IHt2 as [_ IH2]. 
    rewrite eval_varset_union, (IH1 _ He1), (IH2 _ He2); reflexivity.
  - (*Tnot*) exfalso. apply (eval_not_tm Heq Heval).
  - (*Fnot*) destruct (eval_not_fmla Heq Heval) as [e1 [He He1]]. subst. simpl. destruct_all; auto.
  - (*Ttrue*) exfalso. apply (eval_true_tm Ht Heval).
  - (*Ftrue*) rewrite (eval_true_fmla Ht Heval). reflexivity.
  - (*Tfalse*) exfalso. apply (eval_false_tm Ht Heval).
  - (*Ffalse*) rewrite (eval_false_fmla Ht Heval). reflexivity.
Qed.

Corollary t_free_vars_eval_term t e (Heval: eval_term t = Some e):
  eval_varset (t_free_vars t) = tm_fv e.
Proof.
  apply t_free_vars_eval; auto.
Qed.

Corollary t_free_vars_eval_fmla t e (Heval: eval_fmla t = Some e): 
  eval_varset (t_free_vars t) = fmla_fv e.
Proof.
  apply t_free_vars_eval; auto.
Qed.

End EvalFreevars.

(*All vars*)
Section AllVars.



(*Variables*)

Fixpoint term_c_vars (t: term_c) : Svs.t :=
  match (t_node_of t) with
  | TermDefs.Tvar v => Svs.singleton v
  | TermDefs.Tapp _ ts => fold_right Svs.union Svs.empty (map term_c_vars ts)
  | TermDefs.Tif t1 t2 t3 => Svs.union (term_c_vars t1) (Svs.union (term_c_vars t2) (term_c_vars t3))
  | TermDefs.Tlet t1 (v1, _, t2) => Svs.add v1 (Svs.union (term_c_vars t1) (term_c_vars t2))
  | TermDefs.Teps (v1, _, t1) => Svs.add v1 (term_c_vars t1)
  | TermDefs.Tcase t1 tbs => Svs.union (term_c_vars t1)
      (fold_right Svs.union Svs.empty (map (fun x => Svs.union (p_free_vars (fst (fst x))) (term_c_vars (snd x))) tbs))
  | TermDefs.Tquant q (vs, _, _, f) => (Svs.union (Svs.of_list vs) (term_c_vars f)) (*ignore triggers*)
  | TermDefs.Tbinop _ t1 t2 => Svs.union (term_c_vars t1) (term_c_vars t2)
  | TermDefs.Tnot t1 => term_c_vars t1
  | _ => Svs.empty
  end.

Lemma term_c_vars_rewrite t:
  term_c_vars t =
  match (t_node_of t) with
  | TermDefs.Tvar v => Svs.singleton v
  | TermDefs.Tapp _ ts => fold_right Svs.union Svs.empty (map term_c_vars ts)
  | TermDefs.Tif t1 t2 t3 => Svs.union (term_c_vars t1) (Svs.union (term_c_vars t2) (term_c_vars t3))
  | TermDefs.Tlet t1 (v1, _, t2) => Svs.add v1 (Svs.union (term_c_vars t1) (term_c_vars t2))
  | TermDefs.Teps (v1, _, t1) => Svs.add v1 (term_c_vars t1)
  | TermDefs.Tcase t1 tbs => Svs.union (term_c_vars t1)
      (fold_right Svs.union Svs.empty (map (fun x => Svs.union (p_free_vars (fst (fst x))) (term_c_vars (snd x))) tbs))
  | TermDefs.Tquant q (vs, _, _, f) => (Svs.union (Svs.of_list vs) (term_c_vars f)) (*ignore triggers*)
  | TermDefs.Tbinop _ t1 t2 => Svs.union (term_c_vars t1) (term_c_vars t2)
  | TermDefs.Tnot t1 => term_c_vars t1
  | _ => Svs.empty
  end.
Proof. destruct t; auto. Qed.

Opaque aset_union.


Lemma fmla_vars_fforalls (vs: list vsymbol) (f: formula):
  fmla_vars (fforalls vs f) = aset_union (list_to_aset vs) (fmla_vars f).
Proof.
  induction vs as [| v vs IH]; simpl; auto.
  - rewrite list_to_aset_nil, aset_union_empty_l. reflexivity.
  - rewrite IH. rewrite list_to_aset_cons, aset_union_assoc. reflexivity.
Qed.

Lemma fmla_vars_fexists (vs: list vsymbol) (f: formula):
  fmla_vars (fexists vs f) = aset_union (list_to_aset vs) (fmla_vars f).
Proof.
  induction vs as [| v vs IH]; simpl; auto.
  - rewrite list_to_aset_nil, aset_union_empty_l. reflexivity.
  - rewrite IH. rewrite list_to_aset_cons, aset_union_assoc. reflexivity.
Qed.

Lemma fmla_vars_gen_quants b vs f:
  fmla_vars (gen_quants b vs f) = aset_union (list_to_aset vs) (fmla_vars f).
Proof.
  destruct b; [apply fmla_vars_fforalls| apply fmla_vars_fexists].
Qed.

Lemma term_c_vars_eval t1:
  (forall e1 (Heval: eval_term t1 = Some e1), eval_varset (term_c_vars t1) = tm_vars e1) /\
  (forall e1 (Heval: eval_fmla t1 = Some e1), eval_varset (term_c_vars t1) = fmla_vars e1).
Proof.
  induction t1 using term_ind_alt; split; intros e1 Heval;
  rewrite term_c_vars_rewrite; try rewrite Heq; try rewrite Ht.
  - (*var*) rewrite (eval_var_tm Heq Heval). simpl. apply eval_varset_singleton.
  - exfalso. apply (eval_var_fmla Heq Heval).
  - (*const*) destruct (eval_const_tm Heq Heval) as [c1 [He1 Hc1]]; subst. simpl.
    apply eval_varset_empty.
  - exfalso; apply (eval_const_fmla Heq Heval).
  - (*fun*) destruct (eval_app_tm Heq Heval) as [fs [tys [ty1 [tms [He1 [Hfs [_ [_ Htms]]]]]]]]; subst.
    simpl. rewrite eval_varset_big_union. clear -H Htms.
    generalize dependent tms. induction ts as [|  t1 IH]; simpl; auto; intros ps1 Hps1.
    + inversion Hps1; subst; auto.
    + apply option_bind_some in Hps1. destruct Hps1 as [e1 [He1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [es [Hfold Hsome]]. 
      inversion Hsome; subst; clear Hsome. simpl. inversion H as [| ? ? IH1 IH2]; subst; clear H. f_equal; auto.
      apply IH1; auto.
  - destruct (eval_app_fmla Heq Heval) as [[Hl [t1' [t2' [t3' [t4' [ty1 [Hts [He1 [Ht1' [Ht2' Hty]]]]]]]]]] | 
    [Hl [fs [tys [ty1 [tms [He1 [Hfs [_ [_ Htms]]]]]]]]]]; subst.
    + (*Feq*) simpl. inversion H as [| ? ? [IHt1 _] IHt2]; subst; clear H.
      inversion IHt2 as [| ? ? [IHt2' _] _]; clear IHt2; subst.
      rewrite eval_varset_union, (IHt1 _ Ht1'). f_equal.
      rewrite eval_varset_union, (IHt2' _ Ht2'). unfold Svs.empty. rewrite (@eval_varset_empty unit).
      apply aset_union_empty_r.
    + (*Fpred*) simpl. rewrite eval_varset_big_union. clear -H Htms.
      generalize dependent tms. induction ts as [|  t1 IH]; simpl; auto; intros ps1 Hps1.
      * inversion Hps1; subst; auto.
      * apply option_bind_some in Hps1. destruct Hps1 as [e1 [He1 Hbind]].
        apply option_bind_some in Hbind. destruct Hbind as [es [Hfold Hsome]]. 
        inversion Hsome; subst; clear Hsome. simpl. inversion H as [| ? ? IH1 IH2]; subst; clear H. f_equal; auto.
        apply IH1; auto.
  - (*Tif*) destruct (eval_if_tm Heq Heval) as [e1' [e2' [e3' [He1 [He1' [He2' He3']]]]]]; subst; simpl.
    destruct IHt1_1 as [_ IH1]. destruct IHt1_2 as [IH2 _]. destruct IHt1_3 as [IH3 _].
    rewrite !eval_varset_union. f_equal; [|f_equal]; auto.
  - (*Fif*) destruct (eval_if_fmla Heq Heval) as [e1' [e2' [e3' [He1 [He1' [He2' He3']]]]]]; subst; simpl.
    destruct IHt1_1 as [_ IH1]. destruct IHt1_2 as [_ IH2]. destruct IHt1_3 as [_ IH3].
    rewrite !eval_varset_union. f_equal; [|f_equal]; auto.
  - (*Tlet*) destruct (eval_let_tm Heq Heval) as [e1' [e2' [He1 [He1' He2']]]]; subst. simpl.
    unfold Svs.add. rewrite eval_varset_add. f_equal. rewrite eval_varset_union. 
    f_equal; [apply IHt1_1 | apply IHt1_2]; auto.
  - (*Flet*) destruct (eval_let_fmla Heq Heval) as [e1' [e2' [He1 [He1' He2']]]]; subst. simpl.
    unfold Svs.add. rewrite eval_varset_add. f_equal. rewrite eval_varset_union. 
    f_equal; [apply IHt1_1 | apply IHt1_2]; auto.
  - (*Tmatch*) destruct (eval_match_tm Heq Heval) as [e2 [ty1 [ps1 [He1 [He2 [Hty1 Hps1]]]]]]; subst.
    simpl. rewrite eval_varset_union. f_equal; [apply IHt1_1; auto|]. clear -H Hps1.
    rewrite eval_varset_big_union. rewrite Forall_map in H.
    generalize dependent ps1. induction tbs as [| t1 IH]; simpl; auto; intros ps1 Hps1.
    + inversion Hps1; subst; auto.
    + apply option_bind_some in Hps1. destruct Hps1 as [e1 [He1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [es [Hfold Hsome]].
      apply option_bind_some in He1. destruct He1 as [p1 [Hp1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [t2 [Ht2 Hsome1]]. 
      inversion Hsome; inversion Hsome1; subst; clear Hsome Hsome1. 
      simpl. inversion H as [| ? ? IH1 IH2]; subst; clear H. f_equal; auto.
      rewrite eval_varset_union. rewrite (p_free_vars_eval _ p1) ; auto.
      f_equal. apply IH1; auto.
  - (*Fmatch*) destruct (eval_match_fmla Heq Heval) as [e2 [ty1 [ps1 [He1 [He2 [Hty1 Hps1]]]]]]; subst.
    simpl. rewrite eval_varset_union. f_equal; [apply IHt1_1; auto|]. clear -H Hps1.
    rewrite eval_varset_big_union. rewrite Forall_map in H.
    generalize dependent ps1. induction tbs as [| t1 IH]; simpl; auto; intros ps1 Hps1.
    + inversion Hps1; subst; auto.
    + apply option_bind_some in Hps1. destruct Hps1 as [e1 [He1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [es [Hfold Hsome]].
      apply option_bind_some in He1. destruct He1 as [p1 [Hp1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [t2 [Ht2 Hsome1]]. 
      inversion Hsome; inversion Hsome1; subst; clear Hsome Hsome1. 
      simpl. inversion H as [| ? ? IH1 IH2]; subst; clear H. f_equal; auto.
      rewrite eval_varset_union. rewrite (p_free_vars_eval _ p1) ; auto.
      f_equal. apply IH1; auto.
  - (*Teps*) destruct (eval_eps_tm Heq Heval) as [e2 [He He2]]; subst; simpl.
    unfold Svs.add; rewrite eval_varset_add. f_equal; apply IHt1_1; auto.
  - exfalso; apply (eval_eps_fmla Heq Heval).
  - (*Fquant*) exfalso; apply (eval_quant_tm Heq Heval).
  - destruct (eval_quant_fmla Heq Heval) as [e2 [He1 He2]]; simpl in *; subst; simpl.
    rewrite fmla_vars_gen_quants, eval_varset_union, eval_varset_of_list. f_equal.
    apply IHt1_1; auto.
  - (*Fbinop*) exfalso; apply (eval_binop_tm Heq Heval).
  - destruct (eval_binop_fmla Heq Heval) as [e2 [e3 [He1 [He2 He3]]]]; subst; simpl.
    rewrite eval_varset_union. f_equal; [apply IHt1_1 | apply IHt1_2]; auto.
  - (*Fnot*) exfalso; apply (eval_not_tm Heq Heval).
  - destruct (eval_not_fmla Heq Heval) as [e2 [He1 He2]]; subst; simpl. apply IHt1_1; auto.
  - (*Ftrue*) exfalso; apply (eval_true_tm Ht Heval).
  - rewrite (eval_true_fmla Ht Heval); auto.
  - (*False*) exfalso; apply (eval_false_tm Ht Heval).
  - rewrite (eval_false_fmla Ht Heval); auto.
Qed.

Lemma term_c_vars_eval_tm t1 e1 (Heval: eval_term t1 = Some e1):
  eval_varset (term_c_vars t1) = tm_vars e1.
Proof.
  apply term_c_vars_eval; auto.
Qed.

Lemma term_c_vars_eval_fmla t1 e1 (Heval: eval_fmla t1 = Some e1):
  eval_varset (term_c_vars t1) = fmla_vars e1.
Proof.
  apply term_c_vars_eval; auto.
Qed.

End AllVars.


