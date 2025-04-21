(*The stdpp versions of sets and maps are nice for proofs (extensional) but bad
  for computation (the positives are VERY large) and slow the proof system down
  substantially.
  Here, we redefine some of the transformations using the old list-based versions.
  We prove equivalence with the gmap-based versions and then rewrite to these in
  the tactics in Tactics.v
  substitution and free variable computations are the main culprit for slowdowns.
  anything occurring in an "if" expression is fine: we can vm_compute to a bool anyway*)
From Proofs Require Import Task SubMulti Alpha.
From Proofs Require MatchSimpl Rewrite.
Set Bullet Behavior "Strict Subproofs".

Lemma amap_lookup_list {A B: Type} `{countable.Countable A} (l: list (A * B)) (x: A):
  amap_lookup (list_to_amap l) x =
  get_assoc_list EqDecision0 l x.
Proof.
  induction l as [| h t IH]; simpl.
  - apply amap_empty_get.
  - destruct (EqDecision0 x (fst h)); subst; simpl.
    + apply amap_set_lookup_same.
    + rewrite amap_set_lookup_diff; auto.
Qed.

(* list set ops *)

Section ListSet.

Context {A: Type}.
Variable eq_dec: forall (x y : A), {x = y} + {x <> y}.

(*Add all elements in l1 not in l2*)
Definition union (l1 l2: list A) :=
    fold_right (fun x acc => if in_dec eq_dec x acc then acc else x :: acc) l2 l1.

(*Iterated union*)
Definition big_union {B: Type} (f: B -> list A) (l: list B) :=
  fold_right (fun x acc => union (f x) acc) nil l.

Definition remove_all (l1 l2: list A) :=
  fold_right (remove eq_dec) l2 l1.

Lemma union_elts (l1 l2: list A) (x: A):
  In x (union l1 l2) <-> In x l1 \/ In x l2.
Proof.
  induction l1; simpl; auto.
  - split; intros; auto. destruct H as [[] |]; auto.
  - split; intros Hin; destruct (in_dec eq_dec a (union l1 l2)).
    + apply IHl1 in Hin. destruct Hin; solve_or.
    + destruct Hin; subst; try solve_or. apply IHl1 in H; destruct H; solve_or.
    + apply IHl1. destruct Hin as [Hin |?]; [destruct Hin; subst |]; try solve_or.
      apply IHl1; auto.
    + simpl. destruct Hin as [Hin|?]; [destruct Hin; subst|]; try solve_or.
      all: right; apply IHl1; solve_or.
Qed.

(*relate sets and lists - lift to aset so we have ext*)

Lemma union_list `{countable.Countable A} s1 s2:
  aset_union (list_to_aset s1) (list_to_aset s2) =
  list_to_aset (union s1 s2).
Proof.
  apply aset_ext. intros x. simpl_set. rewrite union_elts. reflexivity.
Qed.

Lemma singleton_list `{countable.Countable A} (x: A):
  aset_singleton x = list_to_aset [x].
Proof.
  apply aset_ext. intros y. simpl_set. simpl. 
  split; intros; destruct_all; auto. contradiction.
Qed.

End ListSet.


Section Maps.
(*Relate maps and assoc lists*)
Lemma amap_singleton_list {A B: Type} `{countable.Countable A} (x: A) (y: B):
  amap_singleton x y = list_to_amap [(x, y)].
Proof.
  reflexivity.
Qed.

Lemma amap_union_list {A B: Type} `{countable.Countable A} (l1 l2: list (A * B)):
  list_to_amap (l1 ++ l2) = aunion (list_to_amap l1) (list_to_amap l2).
Proof.
  apply amap_ext. intros x. rewrite aunion_lookup.
  rewrite !amap_lookup_list.
  induction l1 as [| [x1 y1] t1]; simpl; auto.
  destruct (EqDecision0 x x1); subst; auto.
Qed.


Lemma in_remove_iff {A} eq_dec
  (y : A) (l: list A) (x: A):
  In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof.
  split; intros.
  - apply (in_remove eq_dec _ _ _ H).
  - apply in_in_remove; apply H.
Qed.

Lemma remove_all_elts {A} eq_dec
(l1 l2: list A) x:
(In x l2 /\ ~In x l1) <-> In x (remove_all eq_dec l1 l2).
Proof.
  induction l1; simpl; split; intros; auto.
  destruct H; auto.
  - destruct H as [Hinx Hnot].
    destruct (eq_dec x a); subst; auto.
    + exfalso. apply Hnot; left; auto.
    + rewrite in_remove_iff, <- IHl1. split_all; auto.
  - rewrite in_remove_iff in H. destruct H.
    apply IHl1 in H. split_all; auto.
    intro C. destruct C; subst; contradiction.
Qed.

Lemma remove_list {A: Type} `{countable.Countable A} eq_dec (l: list A) x:
  aset_remove x (list_to_aset l) = list_to_aset (remove eq_dec x l).
Proof.
  apply aset_ext. intros y. simpl_set. split.
  - intros [Hin Hneq]. apply in_in_remove; auto.
  - apply in_remove.
Qed.

Lemma diff_list {A: Type} `{countable.Countable A} eq_dec (l1 l2: list A):
  aset_diff (list_to_aset l1) (list_to_aset l2) =
  list_to_aset (remove_all eq_dec l1 l2).
Proof.
  apply aset_ext. intros x. simpl_set. apply remove_all_elts.
Qed.
End Maps.

(*free vars*)
Section Fv.

Local Notation union' := (union vsymbol_eq_dec).
Local Notation big_union' := (big_union vsymbol_eq_dec).
Local Notation remove' := (remove vsymbol_eq_dec).
Local Notation remove_all' := (remove_all vsymbol_eq_dec).

(*Free variables of a pattern*)
Fixpoint pat_fv' (p: pattern) : list vsymbol :=
  match p with
  | Pvar x => [x]
  | Pwild => []
  | Pconstr _ _ ps => big_union' pat_fv' ps
  | Por p1 p2 => union' (pat_fv' p1) (pat_fv' p2)
  | Pbind p x => union' (pat_fv' p) [x]
  end.

(*Free variables of a term (all variables that appear free at least once)*)
Fixpoint tm_fv' (t: term) : list vsymbol :=
  match t with
  | Tconst _ => nil
  | Tvar x => [x]
  | Tfun f vtys tms => big_union' tm_fv' tms
  | Tlet t1 v t2 => union' (tm_fv' t1) (remove' v (tm_fv' t2))
  | Tif f t1 t2 => union' (fmla_fv' f) (union' (tm_fv' t1) (tm_fv' t2))
  | Tmatch t ty l => union' (tm_fv' t) (big_union' (fun x => remove_all' (pat_fv' (fst x)) (tm_fv' (snd x))) l)
  | Teps f x  => remove' x (fmla_fv' f)
  end

with fmla_fv' (f: formula) : list vsymbol :=
  match f with
  | Fpred p tys tms => big_union' tm_fv' tms
  | Fquant q v f => remove' v (fmla_fv' f)
  | Feq _ t1 t2 => union' (tm_fv' t1) (tm_fv' t2)
  | Fbinop b f1 f2 => union' (fmla_fv' f1) (fmla_fv' f2)
  | Fnot f => fmla_fv' f
  | Ftrue => nil
  | Ffalse => nil
  | Flet t v f => union' (tm_fv' t) (remove' v (fmla_fv' f))
  | Fif f1 f2 f3 => union' (fmla_fv' f1) (union' (fmla_fv' f2) (fmla_fv' f3))
  | Fmatch t ty l => union' (tm_fv' t) (big_union' (fun x => remove_all' (pat_fv' (fst x)) (fmla_fv' (snd x))) l)
  end.


Lemma pat_fv_list p:
  pat_fv p = list_to_aset (pat_fv' p).
Proof.
  induction p as [v | f tys tms IH | | p1 p2 IH1 IH2 | v p IH]; simpl.
  - apply singleton_list.
  - induction tms as [| h t IHtms]; simpl; auto.
    inversion IH as [| ? ? IH1 IH2]; subst.
    rewrite IH1. rewrite IHtms; auto.
    (*NOTE: could have lemma for big_union, see*)
    apply union_list.
  - reflexivity.
  - rewrite -> IH1, IH2. apply union_list.
  - rewrite -> IH, singleton_list. apply union_list.
Qed.


Lemma fv_list t f:
  (tm_fv t = list_to_aset (tm_fv' t)) /\ (fmla_fv f = list_to_aset (fmla_fv' f)).
Proof.
  revert t f;
  apply term_formula_ind; simpl; auto; try reflexivity.
  - intros v. rewrite singleton_list; auto.
  - intros _ _ tms IH.
    induction tms as [| h t IHtm]; simpl; auto.
    inversion IH as [| ? ? IH1 IH2]; subst. rewrite IH1, IHtm; auto.
    apply union_list.
  - intros tm1 v tm2 IH1 IH2. rewrite IH1, IH2. rewrite <- union_list. f_equal.
    apply remove_list.
  - intros f t1 t2 IH1 IH2 IH3. rewrite IH1, IH2, IH3.
    rewrite <- union_list; f_equal; apply union_list.
  - intros tm _ ps IH1 IH2. rewrite IH1. rewrite <- union_list; f_equal. clear IH1.
    rewrite Forall_map in IH2. induction ps as [| p1 ptl IH]; simpl; auto.
    inversion IH2 as [| ? ? IHp1 IHtl]; subst; clear IH2. rewrite IHp1, IH; auto.
    rewrite <- union_list, pat_fv_list. f_equal. apply diff_list.
  - intros f v IH. rewrite IH. apply remove_list.
  - intros _ _ tms IH.
    induction tms as [| h t IHtm]; simpl; auto.
    inversion IH as [| ? ? IH1 IH2]; subst. rewrite IH1, IHtm; auto.
    apply union_list.
  - intros _ v f IH.  rewrite IH. apply remove_list.
  - intros _ t1 t2 IH1 IH2. rewrite IH1, IH2; apply union_list.
  - intros _ t1 t2 IH1 IH2. rewrite IH1, IH2; apply union_list.
  - intros tm1 v tm2 IH1 IH2. rewrite IH1, IH2. rewrite <- union_list. f_equal.
    apply remove_list.
  - intros ? ? ? IH1 IH2 IH3. rewrite IH1, IH2, IH3.
    rewrite <- union_list; f_equal; apply union_list.
  - intros tm _ ps IH1 IH2. rewrite IH1. rewrite <- union_list; f_equal. clear IH1.
    rewrite Forall_map in IH2. induction ps as [| p1 ptl IH]; simpl; auto.
    inversion IH2 as [| ? ? IHp1 IHtl]; subst; clear IH2. rewrite IHp1, IH; auto.
    rewrite <- union_list, pat_fv_list. f_equal. apply diff_list.
Qed.

Definition tm_fv_list t := proj_tm fv_list t.
Definition fmla_fv_list f := proj_fmla fv_list f.


Lemma aset_mem_dec_list {A} `{countable.Countable A} eq_dec x (l: list A):
  proj_sumbool _ _ (aset_mem_dec x (list_to_aset l)) = in_bool eq_dec x l.
Proof.
  destruct (aset_mem_dec _ _); simpl_set; destruct (in_bool_spec eq_dec x l); simpl; auto; simpl_set;
  try contradiction. rewrite aset_mem_list_to_aset in n; contradiction.
Qed.

Lemma tm_fv_list_in v t:
  proj_sumbool _ _ (aset_mem_dec v (tm_fv t)) = in_bool vsymbol_eq_dec v (tm_fv' t).
Proof.
  rewrite (tm_fv_list t).
  apply aset_mem_dec_list.
Qed.

Lemma fmla_fv_list_in v t:
  proj_sumbool _ _ (aset_mem_dec v (fmla_fv t)) = in_bool vsymbol_eq_dec v (fmla_fv' t).
Proof.
  rewrite (fmla_fv_list t).
  apply aset_mem_dec_list.
Qed.

End Fv.

(*Substitution*)

Section Sub.

Definition remove_bindings (subs: list (vsymbol * term)) (vs: list vsymbol) :=
  filter (fun x => negb (in_dec vsymbol_eq_dec (fst x) vs)) subs.

Definition remove_binding subs v :=
  remove_bindings subs [v].


Fixpoint sub_ts' (subs : list (vsymbol * term)) (t : term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => match get_assoc_list vsymbol_eq_dec subs v with
              | Some t1 => t1
              | None => Tvar v
              end
  | Tfun fs tys tms => Tfun fs tys (List.map (sub_ts' subs) tms)
  | Tlet tm1 v tm2 => Tlet (sub_ts' subs tm1) v (sub_ts' (remove_binding subs v) tm2)
  | Tif f1 tm1 tm2 => Tif (sub_fs' subs f1) (sub_ts' subs tm1) (sub_ts' subs tm2)
  | Tmatch tm ty ps =>
      Tmatch (sub_ts' subs tm) ty
        (List.map (fun p : pattern * term => (fst p, sub_ts' (remove_bindings subs (pat_fv' (fst p))) (snd p))) ps)
  | Teps f1 v => Teps (sub_fs' (remove_binding subs v) f1) v
  end
with sub_fs' (subs : list (vsymbol * term)) (f : formula) {struct f} : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (List.map (sub_ts' subs) tms)
  | Fquant q v f' => Fquant q v (sub_fs' (remove_binding subs v) f')
  | Feq ty tm1 tm2 => Feq ty (sub_ts' subs tm1) (sub_ts' subs tm2)
  | Fbinop b f1 f2 => Fbinop b (sub_fs' subs f1) (sub_fs' subs f2)
  | Fnot f' => Fnot (sub_fs' subs f')
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f' => Flet (sub_ts' subs tm) v (sub_fs' (remove_binding subs v) f')
  | Fif f1 f2 f3 => Fif (sub_fs' subs f1) (sub_fs' subs f2) (sub_fs' subs f3)
  | Fmatch tm ty ps =>
      Fmatch (sub_ts' subs tm) ty
        (List.map (fun p : pattern * formula => ((fst p), sub_fs' (remove_bindings subs (pat_fv' (fst p))) (snd p)))
           ps)
  end.

Lemma get_assoc_list_irrel {A B} (eq1 eq2: forall (x y: A), {x = y} + {x <> y}) (l: list (A * B)) (x: A):
  get_assoc_list eq1 l x = get_assoc_list eq2 l x.
Proof.
  induction l as [| h t IH]; simpl; auto.
  destruct (eq1 x (fst h)); destruct (eq2 x (fst h)); subst; simpl; try contradiction; auto.
Qed.

Lemma remove_bindings_notin subs vs v:
  In v vs ->
  ~ In v (map fst (remove_bindings subs vs)).
Proof.
  intros. induction subs; simpl in *; auto.
  destruct (in_dec vsymbol_eq_dec (fst a) vs); simpl; auto.
  intro C. destruct C; subst; auto.
Qed.

(*This direction is OK bc we have extensionality*)
Lemma remove_bindings_list l s:
  SubMulti.remove_bindings (list_to_amap l) (list_to_aset s) =
  list_to_amap (remove_bindings l s).
Proof.
  apply amap_ext. intros x.
  rewrite remove_bindings_eq.
  destruct (aset_mem_dec x (list_to_aset s)) as [Hxs | Hxs]; simpl_set.
  - rewrite amap_diff_in; simpl_set; auto. symmetry; apply list_to_amap_none.
    apply remove_bindings_notin; auto.
  - rewrite amap_diff_notin; auto.
    (*avoid nodup hyp*)
    induction l as [| h t IH]; simpl; auto.
    rewrite aset_mem_list_to_aset in Hxs.
    destruct (in_dec vsymbol_eq_dec (fst h) s) as [Hsh | Hsh]; simpl; auto.
    + rewrite amap_set_lookup_diff; auto. intro C; subst; contradiction.
    + vsym_eq x (fst h); try contradiction.
      * rewrite !amap_set_lookup_same; auto.
      * rewrite !amap_set_lookup_diff; auto.
Qed.


Lemma remove_binding_list l v:
  SubMulti.remove_binding (list_to_amap l) v = list_to_amap (remove_binding l v).
Proof.
  apply amap_ext. intros x.
  rewrite remove_binding_eq.
  vsym_eq x v.
  - rewrite amap_remove_same. symmetry. apply list_to_amap_none.
    apply remove_bindings_notin. simpl; auto.
  - rewrite amap_remove_diff; auto.
    (*avoid nodup hyp*)
    induction l as [| h t IH]; simpl; auto.
    vsym_eq v (fst h); simpl; auto.
    + rewrite amap_set_lookup_diff; auto.
    + vsym_eq x (fst h); try contradiction.
      * rewrite !amap_set_lookup_same; auto.
      * rewrite !amap_set_lookup_diff; auto.
Qed.

(*Prove equal*)
Lemma sub_equiv t f:
  (forall l, sub_ts (list_to_amap l) t = sub_ts' l t) /\
  (forall l, sub_fs (list_to_amap l) f = sub_fs' l f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - intros v l. rewrite amap_lookup_list.
    erewrite get_assoc_list_irrel. reflexivity.
  - intros f tys tms IH l. f_equal.
    apply list_eq_ext'; simpl_len; auto. intros n d Hn.
    rewrite -> !map_nth_inbound with (d2:=tm_d); auto.
    rewrite Forall_nth in IH. apply IH; auto.
  - intros tm1 v tm2 IH1 IH2 l. rewrite -> IH1. f_equal.
    rewrite remove_binding_list. apply IH2.
  - intros f t1 t2 IH1 IH2 IH3 l. rewrite -> IH1, IH2, IH3; auto.
  - intros tm ty ps IH1 IH2 l. rewrite IH1. f_equal.
    rewrite Forall_map in IH2. apply list_eq_ext'; simpl_len; auto.
    intros n d Hn. rewrite -> !map_nth_inbound with (d2:=(Pwild, tm_d)); auto.
    f_equal. rewrite -> pat_fv_list, remove_bindings_list. 
    rewrite Forall_nth in IH2. apply IH2; auto.
  - intros f v IH l. rewrite remove_binding_list. f_equal; apply IH.
  - intros p tys tms IH l. f_equal.
    apply list_eq_ext'; simpl_len; auto. intros n d Hn.
    rewrite -> !map_nth_inbound with (d2:=tm_d); auto.
    rewrite Forall_nth in IH. apply IH; auto.
  - intros q v f IH l. f_equal. rewrite remove_binding_list. apply IH.
  - intros ty t1 t2 IH1 IH2 l. rewrite -> IH1, IH2; reflexivity.
  - intros b f1 f2 IH1 IH2 l. rewrite -> IH1, IH2; reflexivity.
  - intros f IH l. f_equal; apply IH.
  - intros tm v f IH1 IH2 l. rewrite -> IH1. f_equal.
    rewrite remove_binding_list. apply IH2.
  - intros f1 f2 f3 IH1 IH2 IH3 l. rewrite -> IH1, IH2, IH3; auto.
  - intros tm ty ps IH1 IH2 l. rewrite IH1. f_equal.
    rewrite Forall_map in IH2. apply list_eq_ext'; simpl_len; auto.
    intros n d Hn. rewrite -> !map_nth_inbound with (d2:=(Pwild, Ftrue)); auto.
    f_equal. rewrite -> pat_fv_list, remove_bindings_list. 
    rewrite Forall_nth in IH2. apply IH2; auto.
Qed.

Definition sub_ts_equiv l t:= proj_tm sub_equiv t l.
Definition sub_fs_equiv l f:=proj_fmla sub_equiv f l.


(*NOTE: lots of this breaks/does not compute well if I actually need alpha conversion*)
(*Can use [list_to_amap] in set because we will vm_compute to bool anyway*)
Definition safe_sub_ts' (subs: (list (vsymbol * term))) (t: term) : term :=
  (*TODO: bad, would be nice to have proper computable but tricky*)
  if check_disj (aset_big_union tm_fv (vals (list_to_amap subs))) (list_to_aset (tm_bnd t)) then
  sub_ts' subs t else
  sub_ts' subs (a_convert_t t (aset_big_union tm_fv (vals (list_to_amap subs)))).

Lemma safe_sub_ts_equiv subs t:
  safe_sub_ts' subs t =
  safe_sub_ts (list_to_amap subs) t.
Proof.
  unfold safe_sub_ts', safe_sub_ts.
  destruct (check_disj _ _);  symmetry; apply sub_ts_equiv.
Qed.

Definition safe_sub_fs' (subs: (list (vsymbol * term))) (f: formula) : formula :=
  if check_disj (aset_big_union tm_fv (vals (list_to_amap subs))) (list_to_aset (fmla_bnd f)) then
  sub_fs' subs f else
  sub_fs' subs (a_convert_f f (aset_big_union tm_fv (vals (list_to_amap subs)))).

Lemma safe_sub_fs_equiv subs f:
  safe_sub_fs' subs f =
  safe_sub_fs (list_to_amap subs) f.
Proof.
  unfold safe_sub_fs', safe_sub_fs.
  destruct (check_disj _ _);  symmetry; apply sub_fs_equiv.
Qed.

End Sub.


(*The main pieces: [simpl_match] and rewriting*)

(*Redo part of [simpl_match]*)
Section MatchSimpl'.

Import MatchSimpl.

Inductive match_result : Type :=
  | DontKnow : match_result
  | NoMatch : match_result
  | Matches : list (vsymbol * term) -> match_result.

Fixpoint matches gamma (p: pattern) (t: term) : match_result :=
  match p, t with
  | Pvar x, _ => Matches [(x, t)]
  | Pwild, _ => Matches nil
  | Por p1 p2, _ => 
    match (matches gamma p1 t) with
    | NoMatch => matches gamma p2 t
    | r => r
    end
  | Pbind p1 x, _ => match (matches gamma p1 t) with
                  | Matches l => Matches ((x, t) :: l)
                  | r => r
                  end
  | Pconstr f1 tys1 ps, Tfun f2 tys2 tms =>
    if funsym_eq_dec f1 f2 && list_eq_dec vty_eq_dec tys1 tys2 &&
      (Nat.eqb (length ps) (length tms)) then
    (fix nested_matches (p1: list pattern) (t1: list term) : match_result :=
      match p1, t1 with
      | p :: ps, t :: ts => 
        match matches gamma p t, nested_matches ps ts with
        | Matches l1, Matches l2 => Matches (l1 ++ l2)
        | DontKnow, _ => DontKnow
        | _, DontKnow => DontKnow
        | _, _ => NoMatch
        end
      | nil, nil => Matches nil
      | _, _ => (*Impossible*) DontKnow
      end) ps tms
    else
    if (is_funsym_constr gamma f2) then NoMatch
    else DontKnow
  | Pconstr _ _ _, Tconst _ => NoMatch
  | Pconstr _ _ _, _ => DontKnow
  end.

(*rewrite lemma*)
Fixpoint nested_matches gamma (ps: list pattern) (ts: list term) : match_result :=
  match ps, ts with
    | p :: ps, t :: ts => 
      match matches gamma p t, nested_matches gamma ps ts with
      | Matches l1, Matches l2 => Matches (l1 ++ l2)
      | DontKnow, _ => DontKnow
      | _, DontKnow => DontKnow
      | _, _ => NoMatch
      end
    | nil, nil => Matches nil
    | _, _ => (*Impossible*) DontKnow
  end.

Lemma matches_constr_rewrite gamma f1 tys1 ps1 t:
  matches gamma (Pconstr f1 tys1 ps1) t =
  match t with
  | Tfun f2 tys2 tms =>
     if funsym_eq_dec f1 f2 && list_eq_dec vty_eq_dec tys1 tys2 &&
      (length ps1 =? length tms) then
      nested_matches gamma ps1 tms
    else if (is_funsym_constr gamma f2) then NoMatch
    else DontKnow
  | Tconst c => NoMatch
  | _ => DontKnow
  end.
Proof.
  simpl. destruct t; auto.
  destruct (funsym_eq_dec f1 f); auto; simpl; subst.
  destruct (list_eq_dec vty_eq_dec tys1 l); auto; simpl; subst.
  destruct (Nat.eqb_spec (length ps1) (length l0)); auto.
  generalize dependent l0. induction ps1; simpl; intros; auto.
  destruct l0; auto.
  destruct (matches gamma a t) eqn : Hmatch; auto;
  rewrite IHps1; auto.
Qed.

Fixpoint check_match (gamma: context) {A: Type} (sub: list (vsymbol * term) -> A -> A)
(t: term) (ret: A) (l: list (pattern * A)) : A :=
match l with
| nil => ret
| pt :: tl => 
  match (matches gamma (fst pt) t) with
  | NoMatch => check_match gamma sub t ret tl
  | DontKnow => ret
  | Matches subs => sub subs (snd pt)
  end
end.

Definition match_result_eq (m: match_result) (m2: MatchSimpl.match_result) : Prop :=
  match m, m2 with
  | DontKnow, MatchSimpl.DontKnow => True
  | NoMatch, MatchSimpl.NoMatch => True
  | Matches l, MatchSimpl.Matches m => list_to_amap l = m
  | _, _ => False
  end.


Opaque amap_singleton list_to_amap.
Lemma matches_eq gamma p t:
  match_result_eq (matches gamma p t) (MatchSimpl.matches gamma p t).
Proof.
  revert t.
  induction p as [v | f tys ps IH | | q1 q2 IH1 IH2 | p v IH]; intros t.
  - simpl. symmetry; apply amap_singleton_list.
  - rewrite -> matches_constr_rewrite, MatchSimpl.matches_constr_rewrite.
    destruct t as [| | f1 tys1 tms | | | | ]; try solve[unfold match_result_eq; auto].
    destruct (funsym_eq_dec f f1); subst; simpl; auto.
    2: { destruct (is_funsym_constr gamma f1); reflexivity. }
    destruct (list_eq_dec vty_eq_dec tys tys1); subst; simpl; auto.
    2: { destruct (is_funsym_constr gamma f1); reflexivity. }
    destruct (Nat.eqb_spec (length ps) (length tms)) as [Hlen | Hlen]; simpl; auto.
    2: { destruct (is_funsym_constr gamma f1); reflexivity. }
    generalize dependent tms. induction ps as [| p1 ptl IHp];
    intros [| t1 ttl]; try discriminate; auto; simpl.
    + intros; reflexivity.
    + intros Hlen.
      inversion IH as [| ? ? IH1 IH2]; clear IH; subst.
      specialize (IH1 t1). specialize (IHp IH2 ttl ltac:(auto)). clear IH2.
      unfold match_result_eq in IH1.
      destruct (matches gamma p1 t1) eqn : Hmatch1;
      destruct (MatchSimpl.matches gamma p1 t1) eqn: Hmatch2; auto; try contradiction.
      * unfold match_result_eq in IHp.
        destruct (nested_matches gamma ptl ttl) eqn : Hmatch3; 
        destruct (MatchSimpl.nested_matches gamma ptl ttl) eqn : Hmatch4; auto.
      * unfold match_result_eq in IHp.
        destruct (nested_matches gamma ptl ttl) eqn : Hmatch3; 
        destruct (MatchSimpl.nested_matches gamma ptl ttl) eqn : Hmatch4; auto.
        unfold match_result_eq. subst. 
        apply amap_union_list.
  - simpl. reflexivity.
  - simpl. specialize (IH1 t). specialize (IH2 t). unfold match_result_eq in *.
    destruct (matches gamma q1 t); destruct (MatchSimpl.matches gamma q1 t); auto;
    contradiction.
  - simpl. specialize (IH t). unfold match_result_eq in *.
    destruct (matches gamma p t); destruct (MatchSimpl.matches gamma p); auto;
    try contradiction. subst. reflexivity.
Qed.

Lemma check_match_eq gamma {A: Type} (sub1: list (vsymbol * term) -> A -> A)
  (sub2: amap vsymbol term -> A -> A)
  t ret l (Hsub: forall l x, sub2 (list_to_amap l) x = sub1 l x):
  check_match gamma sub1 t ret l =
  MatchSimpl.check_match gamma sub2 t ret l.
Proof.
  induction l as [| h tl IH]; simpl; auto.
  pose proof (matches_eq gamma (fst h) t) as Hmatch.
  unfold match_result_eq in Hmatch.
  destruct (matches gamma (fst h) t); destruct ( MatchSimpl.matches gamma (fst h) t); auto; try contradiction.
  subst. auto.
Qed.

Lemma check_match_sub_eq gamma t ret l:
  MatchSimpl.check_match gamma safe_sub_ts t ret l =
  check_match gamma safe_sub_ts' t ret l.
Proof.
  symmetry; apply check_match_eq.
  intros; symmetry; apply safe_sub_ts_equiv.
Qed.

Lemma check_match_sub_eq' gamma t ret l:
  MatchSimpl.check_match gamma safe_sub_fs t ret l =
  check_match gamma safe_sub_fs' t ret l.
Proof.
  symmetry; apply check_match_eq.
  intros; symmetry; apply safe_sub_fs_equiv.
Qed.

Fixpoint simpl_match_t gamma (t: term) : term :=
  match t with
  | Tfun f tys tms => Tfun f tys (map (simpl_match_t gamma) tms)
  | Tlet t1 x t2 => Tlet (simpl_match_t gamma t1) x (simpl_match_t gamma t2)
  | Tif f1 t1 t2 => Tif (simpl_match_f gamma f1) (simpl_match_t gamma t1) (simpl_match_t gamma t2)
  | Tmatch t1 ty ps =>
    check_match gamma safe_sub_ts' t1 t ps
  | Teps f x => Teps (simpl_match_f gamma f) x
  | _ => t
  end
with simpl_match_f gamma (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (simpl_match_t gamma) tms)
  | Fquant q x f => Fquant q x (simpl_match_f gamma f)
  | Feq ty t1 t2 => Feq ty (simpl_match_t gamma t1) (simpl_match_t gamma t2)
  | Fbinop b f1 f2 => Fbinop b (simpl_match_f gamma f1) (simpl_match_f gamma f2)
  | Flet t x f => Flet (simpl_match_t gamma t) x (simpl_match_f gamma f)
  | Fif f1 f2 f3 => Fif (simpl_match_f gamma f1) (simpl_match_f gamma f2) (simpl_match_f gamma f3)
  | Fmatch t1 ty ps =>
    check_match gamma safe_sub_fs' t1 f ps
  | _ => f
  end.

Lemma simpl_match_eq gamma t f:
  (simpl_match_t gamma t = MatchSimpl.simpl_match_t gamma t) /\
  (simpl_match_f gamma f = MatchSimpl.simpl_match_f gamma f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - intros f tys tms IH. f_equal. 
    apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=tm_d); auto. rewrite Forall_nth in IH; auto.
  - intros ? ? ? IH1 IH2. rewrite IH1, IH2; reflexivity.
  - intros ? ? ? IH1 IH2 IH3. rewrite IH1, IH2, IH3; reflexivity.
  - intros. symmetry; apply check_match_sub_eq.
  - intros ? ? IH. rewrite IH; reflexivity.
  - intros ? ? ? IH. f_equal. 
    apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=tm_d); auto. rewrite Forall_nth in IH; auto.
  - intros ? ? ? IH; rewrite IH; reflexivity.
  - intros ? ? ? IH1 IH2; rewrite IH1, IH2; reflexivity.
  - intros ? ? ? IH1 IH2; rewrite IH1, IH2; reflexivity.
  - intros ? ? ? IH1 IH2. rewrite IH1, IH2; reflexivity.
  - intros ? ? ? IH1 IH2 IH3. rewrite IH1, IH2, IH3; reflexivity.
  - intros. symmetry; apply check_match_sub_eq'.
Qed.

Definition simpl_match_t_eq gamma t := proj_tm (simpl_match_eq gamma) t.
Definition simpl_match_f_eq gamma f := proj_fmla (simpl_match_eq gamma) f.

End MatchSimpl'.

(*And for rewrite/unfold*)
Section Replace.
Variable tm_o tm_n: term.

Fixpoint replace_tm_t (t: term) :=
  if term_eq_dec tm_o t then tm_n else
  (*Just a bunch of recursive cases*)
  match t with
  | Tfun f tys tms => Tfun f tys (map replace_tm_t tms)
  | Tlet t1 v t2 =>
    Tlet (replace_tm_t t1) v 
    (*Avoid capture -*)
    (if in_bool vsymbol_eq_dec v (tm_fv' tm_o) then t2
    else (replace_tm_t t2))
  | Tif f t1 t2 =>
    Tif (replace_tm_f f) (replace_tm_t t1) (replace_tm_t t2)
  | Tmatch tm ty ps =>
    Tmatch (replace_tm_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (tm_fv' tm_o))
       (pat_fv' (fst x))
         then
      snd x else (replace_tm_t (snd x)))) ps)
  | Teps f v =>
    Teps (if in_bool vsymbol_eq_dec v (tm_fv' tm_o) then f else
      replace_tm_f f) v
  | _ => t
  end
with replace_tm_f (f: formula) :=
  match f with
  | Fpred p tys tms =>
    Fpred p tys (map replace_tm_t tms)
  | Fquant q v f =>
    Fquant q v (if in_bool vsymbol_eq_dec v (tm_fv' tm_o) then f else
      replace_tm_f f)
  | Feq ty t1 t2 => Feq ty (replace_tm_t t1) (replace_tm_t t2)
  | Fbinop b f1 f2 => Fbinop b (replace_tm_f f1) (replace_tm_f f2)
  | Fnot f => Fnot (replace_tm_f f)
  | Flet t v f => Flet (replace_tm_t t) v
    (if in_bool vsymbol_eq_dec v (tm_fv' tm_o) then f 
      else (replace_tm_f f))
  | Fif f1 f2 f3 => Fif (replace_tm_f f1) (replace_tm_f f2)
    (replace_tm_f f3)
  | Fmatch tm ty ps =>
    Fmatch (replace_tm_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (tm_fv' tm_o))
      (pat_fv' (fst x))
        then
      snd x else (replace_tm_f (snd x)))) ps)
  | _ => f
  end.

(*For patmatch case*)
Lemma existsb_pat_fv_list p t:
   existsb (fun v : vsymbol => aset_mem_dec v (tm_fv t))
      (aset_to_list (pat_fv p)) =
    existsb (fun v : vsymbol => in_bool vsymbol_eq_dec v (tm_fv' t))
      (pat_fv' p).
Proof.
  apply is_true_eq. unfold is_true. rewrite !existsb_exists.
  setoid_rewrite pat_fv_list. split.
  - intros [v [Hinv Hfv]]. simpl_set. exists v; split; auto.
    erewrite tm_fv_list, aset_mem_dec_list in Hfv. apply Hfv.
  - intros [v [Hinv Hfv]]. exists v. simpl_set. split; auto.
    erewrite tm_fv_list, aset_mem_dec_list. apply Hfv.
Qed.

Lemma replace_tm_eq t f:
  (Rewrite.replace_tm_t tm_o tm_n t = replace_tm_t t) /\
  (Rewrite.replace_tm_f tm_o tm_n f = replace_tm_f f).
Proof.
  revert t f; apply term_formula_ind; simpl; try reflexivity.
  - intros f tys tms IH. destruct (term_eq_dec tm_o (Tfun f tys tms)); auto.
    f_equal. apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=tm_d); auto. rewrite Forall_nth in IH; auto.
  - intros tm1 v tm2 IH1 IH2. destruct (term_eq_dec _ _); auto.
    rewrite IH1. f_equal. rewrite <- tm_fv_list_in. destruct (aset_mem_dec _ _); auto.
  - intros f t1 t2 IH1 IH2 IH3. destruct (term_eq_dec _ _); auto.
    rewrite IH1, IH2, IH3; reflexivity.
  - intros tm ty ps IH IHps. destruct (term_eq_dec _ _); auto.
    rewrite IH; f_equal. clear IH n. rewrite Forall_map in IHps.
    apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=(Pwild, tm_d)); auto.
    f_equal. rewrite existsb_pat_fv_list. destruct (existsb _ _); auto.
    rewrite Forall_nth in IHps. auto.
  - intros f v IH. destruct (term_eq_dec _ _); auto.
    rewrite <- tm_fv_list_in. destruct (aset_mem_dec _ _); simpl; auto. f_equal; auto.
  - intros p tys tms IH.
    f_equal. apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=tm_d); auto. rewrite Forall_nth in IH; auto.
  - intros q f v IH. rewrite <- tm_fv_list_in. destruct (aset_mem_dec _ _); simpl; auto. f_equal; auto.
  - intros ty t1 t2 IH1 IH2. rewrite IH1, IH2; reflexivity.
  - intros b t1 t2 IH1 IH2. rewrite IH1, IH2; reflexivity.
  - intros f IH. rewrite IH; reflexivity.
  - intros tm1 v tm2 IH1 IH2.
    rewrite IH1. f_equal. rewrite <- tm_fv_list_in. destruct (aset_mem_dec _ _); auto.
  - intros f t1 t2 IH1 IH2 IH3. rewrite IH1, IH2, IH3; reflexivity.
  - intros tm ty ps IH IHps. 
    rewrite IH; f_equal. clear IH. rewrite Forall_map in IHps.
    apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=(Pwild, Ftrue)); auto.
    f_equal. rewrite existsb_pat_fv_list. destruct (existsb _ _); auto.
    rewrite Forall_nth in IHps. auto.
Qed.

Definition replace_tm_t_eq t := proj_tm replace_tm_eq t.
Definition replace_tm_f_eq f := proj_fmla replace_tm_eq f.

End Replace.

(*And replace fmla*)
Section ReplaceFmla.

Variable fmla_o fmla_n: formula.

Fixpoint replace_fmla_t (t: term) :=
  (*Just a bunch of recursive cases*)
  match t with
  | Tfun f tys tms => Tfun f tys (map replace_fmla_t tms)
  | Tlet t1 v t2 =>
    Tlet (replace_fmla_t t1) v 
    (*Avoid capture -*)
    (if in_bool vsymbol_eq_dec v (fmla_fv' fmla_o) then t2
    else (replace_fmla_t t2))
  | Tif f t1 t2 =>
    Tif (replace_fmla_f f) (replace_fmla_t t1) (replace_fmla_t t2)
  | Tmatch tm ty ps =>
    Tmatch (replace_fmla_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (fmla_fv' fmla_o))
       (pat_fv' (fst x))
         then
      snd x else (replace_fmla_t (snd x)))) ps)
  | Teps f v =>
    Teps (if in_bool vsymbol_eq_dec v (fmla_fv' fmla_o) then f else
    replace_fmla_f f) v
  | _ => t
  end
with replace_fmla_f (f: formula) :=
if formula_eq_dec fmla_o f then fmla_n else
  match f with
  | Fpred p tys tms =>
    Fpred p tys (map replace_fmla_t tms)
  | Fquant q v f =>
    Fquant q v (if in_bool vsymbol_eq_dec v (fmla_fv' fmla_o) then f else
    replace_fmla_f f)
  | Feq ty t1 t2 => Feq ty (replace_fmla_t t1) (replace_fmla_t t2)
  | Fbinop b f1 f2 => Fbinop b (replace_fmla_f f1) (replace_fmla_f f2)
  | Fnot f => Fnot (replace_fmla_f f)
  | Flet t v f => Flet (replace_fmla_t t) v
    (if in_bool vsymbol_eq_dec v (fmla_fv' fmla_o) then f 
      else (replace_fmla_f f))
  | Fif f1 f2 f3 => Fif (replace_fmla_f f1) (replace_fmla_f f2)
    (replace_fmla_f f3)
  | Fmatch tm ty ps =>
    Fmatch (replace_fmla_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (fmla_fv' fmla_o))
      (pat_fv' (fst x))
        then
      snd x else (replace_fmla_f (snd x)))) ps)
  | _ => f
  end.

Lemma existsb_pat_fv_list' p t:
   existsb (fun v : vsymbol => aset_mem_dec v (fmla_fv t))
      (aset_to_list (pat_fv p)) =
    existsb (fun v : vsymbol => in_bool vsymbol_eq_dec v (fmla_fv' t))
      (pat_fv' p).
Proof.
  apply is_true_eq. unfold is_true. rewrite !existsb_exists.
  setoid_rewrite pat_fv_list. split.
  - intros [v [Hinv Hfv]]. simpl_set. exists v; split; auto.
    erewrite fmla_fv_list, aset_mem_dec_list in Hfv. apply Hfv.
  - intros [v [Hinv Hfv]]. exists v. simpl_set. split; auto.
    erewrite fmla_fv_list, aset_mem_dec_list. apply Hfv.
Qed.


Lemma replace_fmla_eq t f:
  (Rewrite.replace_fmla_t fmla_o fmla_n t = replace_fmla_t t) /\
  (Rewrite.replace_fmla_f fmla_o fmla_n f = replace_fmla_f f).
Proof.
  revert t f; apply term_formula_ind; simpl; try reflexivity.
  - intros f tys tms IH. f_equal. apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=tm_d); auto. rewrite Forall_nth in IH; auto.
  - intros tm1 v tm2 IH1 IH2. 
    rewrite IH1. f_equal. rewrite <- fmla_fv_list_in. destruct (aset_mem_dec _ _); auto.
  - intros f t1 t2 IH1 IH2 IH3. rewrite IH1, IH2, IH3; reflexivity.
  - intros tm ty ps IH IHps. rewrite IH; f_equal. clear IH. rewrite Forall_map in IHps.
    apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=(Pwild, tm_d)); auto.
    f_equal. rewrite existsb_pat_fv_list'. destruct (existsb _ _); auto.
    rewrite Forall_nth in IHps. auto.
  - intros f v IH. rewrite <- fmla_fv_list_in. destruct (aset_mem_dec _ _); simpl; auto. f_equal; auto.
  - intros p tys tms IH. destruct (formula_eq_dec _ _); auto.
    f_equal. apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=tm_d); auto. rewrite Forall_nth in IH; auto.
  - intros q f v IH. destruct (formula_eq_dec _ _); auto. 
    rewrite <- fmla_fv_list_in. destruct (aset_mem_dec _ _); simpl; auto. f_equal; auto.
  - intros ty t1 t2 IH1 IH2. destruct (formula_eq_dec _ _); auto. rewrite IH1, IH2; reflexivity.
  - intros b t1 t2 IH1 IH2. destruct (formula_eq_dec _ _); auto. rewrite IH1, IH2; reflexivity.
  - intros f IH. destruct (formula_eq_dec _ _); auto. rewrite IH; reflexivity.
  - intros tm1 v tm2 IH1 IH2. destruct (formula_eq_dec _ _); auto.
    rewrite IH1. f_equal. rewrite <- fmla_fv_list_in. destruct (aset_mem_dec _ _); auto.
  - intros f t1 t2 IH1 IH2 IH3. destruct (formula_eq_dec _ _); auto. rewrite IH1, IH2, IH3; reflexivity.
  - intros tm ty ps IH IHps. destruct (formula_eq_dec _ _); auto. 
    rewrite IH; f_equal. clear IH. rewrite Forall_map in IHps.
    apply list_eq_ext'; simpl_len; auto. intros n' d Hn.
    rewrite !map_nth_inbound with (d2:=(Pwild, Ftrue)); auto.
    f_equal. rewrite existsb_pat_fv_list'. destruct (existsb _ _); auto.
    rewrite Forall_nth in IHps. auto.
Qed.

Definition replace_fmla_t_eq t := proj_tm replace_fmla_eq t.
Definition replace_fmla_f_eq f := proj_fmla replace_fmla_eq f.

End ReplaceFmla.
