(*Test for induction - we define natural numbers and prove that
  addition is commutative*)


(*TODO: move this to other file in proofsystem
  NO ssrreflect*)
From Proofs Require Import Task SubMulti Alpha.
From Proofs Require MatchSimpl.

(*Kind of cheating but whatever*)
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

Definition remove_bindings (subs: list (vsymbol * term)) (vs: list vsymbol) :=
  filter (fun x => negb (in_dec vsymbol_eq_dec (fst x) vs)) subs.

Definition remove_binding subs v :=
  remove_bindings subs [v].

(** Union on lists with decidable equality **)

Section Union.

Context {A: Type}.
Variable eq_dec: forall (x y : A), {x = y} + {x <> y}.

(*Add all elements in l1 not in l2*)
Definition union (l1 l2: list A) :=
    fold_right (fun x acc => if in_dec eq_dec x acc then acc else x :: acc) l2 l1.
(* 
Lemma union_nodup: forall (l1 l2: list A),
  NoDup l2 ->
  NoDup (union l1 l2).
Proof.
  intros l1 l2. induction l1; simpl; auto.
  intros Hnodup.
  destruct (in_dec eq_dec a (union l1 l2)); auto.
  apply NoDup_cons; auto.
Qed.


Lemma union_elts: forall (l1 l2: list A) (x: A),
  In x (union l1 l2) <-> In x l1 \/ In x l2.
Proof.
  intros l1 l2. induction l1; simpl; auto.
  - intros x; split; intros; auto. destruct H as [[] |]; auto.
  - intros x; split; intros Hin; destruct (in_dec eq_dec a (union l1 l2)).
    + apply IHl1 in Hin. destruct Hin; solve_or.
    + destruct Hin; subst; try solve_or. apply IHl1 in H; destruct H; solve_or.
    + apply IHl1. destruct Hin as [Hin |?]; [destruct Hin; subst |]; try solve_or.
      apply IHl1; auto.
    + simpl. destruct Hin as [Hin|?]; [destruct Hin; subst|]; try solve_or.
      all: right; apply IHl1; solve_or.
Qed.

Lemma union_remove: forall (l1 l2: list A) (x: A),
  union (remove eq_dec x l1) (remove eq_dec x l2) =
  remove eq_dec x (union l1 l2).
Proof.
  intros l1 l2. induction l1; simpl; auto.
  intros x. destruct (eq_dec x a); subst.
  - destruct (in_dec eq_dec a (union l1 l2)); simpl.
    + apply IHl1.
    + destruct (eq_dec a a); auto. contradiction.
  - simpl. destruct (in_dec eq_dec a (union l1 l2)).
    + destruct (in_dec eq_dec a (union (remove eq_dec x l1) (remove eq_dec x l2))); auto.
      exfalso. apply n0. rewrite IHl1. apply in_in_remove; auto.
    + simpl. destruct (eq_dec x a); subst; try contradiction.
      destruct (in_dec eq_dec a (union (remove eq_dec x l1) (remove eq_dec x l2))); auto;
      [| rewrite IHl1; auto].
      exfalso. apply n0. rewrite IHl1 in i. apply in_remove in i. destruct i; auto.
Qed.

Lemma union_nil: forall (l1 l2: list A),
  union l1 l2 = nil ->
  l1 = nil /\ l2 = nil.
Proof.
  intros. induction l1; simpl; auto.
  simpl in H. destruct (in_dec eq_dec a (union l1 l2)).
  - rewrite H in i. inversion i.
  - inversion H.
Qed.

Lemma union_nil_eq (l1 l2: list A):
  l1 = nil ->
  l2 = nil ->
  union l1 l2 = nil.
Proof.
  intros ->->. reflexivity.
Qed.

Lemma union_nil_r (l1: list A):
  NoDup l1 ->
  union l1 nil = l1.
Proof.
  induction l1; simpl; auto.
  intros. inversion H; subst.
  rewrite IHl1; auto.
  destruct (in_dec eq_dec a l1); auto; contradiction.
Qed.

Lemma filter_union (l1 l2: list A)
  (f: A -> bool):
  filter f (union l1 l2) =
  union (filter f l1) (filter f l2).
Proof.
  induction l1; simpl; auto.
  destruct (in_dec eq_dec a (union l1 l2)).
  - destruct (f a) eqn : Hf.
    + simpl. rewrite <- IHl1.
      destruct (in_dec eq_dec a (filter f (union l1 l2))); auto.
      exfalso. apply n. rewrite in_filter. split; auto.
    + apply IHl1.
  - simpl. destruct (f a) eqn : Hf; auto.
    simpl. rewrite <- IHl1.
    destruct (in_dec eq_dec a (filter f (union l1 l2))); auto.
    exfalso. rewrite in_filter in i. destruct_all; contradiction.
Qed. *)

(*Iterated union*)
Definition big_union {B: Type} (f: B -> list A) (l: list B) :=
  fold_right (fun x acc => union (f x) acc) nil l.

Definition remove_all (l1 l2: list A) :=
  fold_right (remove eq_dec) l2 l1.

End Union.


(*TODO: move this*)
Print sub_ts.

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

End Fv.



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

Lemma union_elts {A} eq_dec (l1 l2: list A) (x: A):
  In x (union eq_dec l1 l2) <-> In x l1 \/ In x l2.
Proof.
  induction l1; simpl; auto.
  - split; intros; auto. destruct H as [[] |]; auto.
  - split; intros Hin; destruct (in_dec eq_dec a (union eq_dec l1 l2)).
    + apply IHl1 in Hin. destruct Hin; solve_or.
    + destruct Hin; subst; try solve_or. apply IHl1 in H; destruct H; solve_or.
    + apply IHl1. destruct Hin as [Hin |?]; [destruct Hin; subst |]; try solve_or.
      apply IHl1; auto.
    + simpl. destruct Hin as [Hin|?]; [destruct Hin; subst|]; try solve_or.
      all: right; apply IHl1; solve_or.
Qed.

Lemma union_list {A: Type} `{countable.Countable A} (eq_dec: forall (x y: A), {x = y} + {x <> y}) s1 s2:
  aset_union (list_to_aset s1) (list_to_aset s2) =
  list_to_aset (union eq_dec s1 s2).
Proof.
  apply aset_ext. intros x. simpl_set. rewrite union_elts. reflexivity.
Qed.

Lemma singleton_list {A: Type} `{countable.Countable A} (x: A):
  aset_singleton x = list_to_aset [x].
Proof.
  apply aset_ext. intros y. simpl_set. simpl. 
  split; intros; destruct_all; auto. contradiction.
Qed.

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

Print safe_sub_ts.

(* Definition disjb' {A : Type} eq_dec (l1 l2: list A): bool :=
  forallb (fun x => negb (in_dec eq_dec x l2)) l1.
Locate existsb.
Lemma forallb_existsb {A: Type} (p: A -> bool) (l: list A):
  forallb p l = negb (existsb (fun x => negb (p x)) l).
Proof.
  induction l; simpl; auto.
  rewrite negb_orb, negb_involutive. f_equal; auto.
Qed.

Lemma disjP' {A: Type} eq_dec (l1 l2: list A):
  reflect (disj l1 l2) (disjb' eq_dec l1 l2).
Proof.
  unfold disjb', disj.
  destruct (forallb (fun x : A => negb (in_dec eq_dec x l2)) l1) eqn : Hall.
  - apply ReflectT. rewrite forallb_forall in Hall.
    intros. intros [Hinx1 Hinx2].
    specialize (Hall _ Hinx1).
    destruct (in_dec eq_dec x l2); auto.
  - apply ReflectF. intros C.
    rewrite forallb_existsb in Hall.
    apply negb_false_iff in Hall.
    rewrite existsb_exists in Hall.
    destruct Hall as [x [Hinx1 Hinx2]].
    rewrite negb_involutive in Hinx2.
    simpl_sumbool.
    apply (C x); auto.
Qed.
Print safe_sub_ts. *)
(*NOTE: lots of this breaks/does not compute well if I actually need alpha conversion*)
(*Can use [list_to_amap] in set because we will vm_compute to bool anyway*)
Definition safe_sub_ts' (subs: (list (vsymbol * term))) (t: term) : term :=
  (*TODO: bad, would be nice to have proper computable but tricky*)
  if check_disj (aset_big_union tm_fv (vals (list_to_amap subs))) (list_to_aset (tm_bnd t)) then
  sub_ts' subs t else
  sub_ts' subs (a_convert_t t (aset_big_union tm_fv (vals (list_to_amap subs)))).

Set Bullet Behavior "Strict Subproofs".

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

(*And for rewrite/unfold*)
Section Replace.
Variable tm_o tm_n: term.

Require Rewrite.

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

Check union_list.


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


From Proofs.proofsystem Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Module InductionTest.

Local Open Scope string_scope.

(*First, define nat type*)
Definition nat_ts : typesym := mk_ts "nat" nil.
Definition wnat : vty := vty_cons nat_ts nil.
Definition O_fs : funsym := constr_noty "O" nil wnat 2.
Definition S_fs: funsym := constr_noty "S" [wnat] wnat 2.
Definition wnat_adt : alg_datatype := alg_def nat_ts
  (list_to_ne_list [O_fs; S_fs] erefl).
Definition wnat_mut : mut_adt := mk_mut [wnat_adt] nil erefl.

Definition O : term := Tfun O_fs nil nil.
Definition S (t: term) : term := Tfun S_fs nil [t].

(*Function definition*)
Definition n : vsymbol := ("n", wnat).
Definition m: vsymbol := ("m", wnat).
Definition n': vsymbol := ("n'", wnat).
Definition add_fs : funsym := funsym_noconstr_noty "add" [wnat; wnat] wnat.
Definition add (t1 t2: term) := Tfun add_fs nil [t1; t2].
Definition add_def : funpred_def :=
  fun_def add_fs [n; m] 
  (Tmatch (Tvar n) wnat
    [(Pconstr O_fs nil nil, Tvar m); (*O -> m*)
     (Pconstr S_fs nil [Pvar n'], S (add (Tvar n') (Tvar m))) (*S n' -> S (add n' m)*)
    ]).

Definition induction_theory : theory :=
  rev [
    tdef (datatype_def wnat_mut);
    tdef (recursive_def [add_def]);
    (*We need two lemmas*)
    tprop Plemma "add_0_r" (fforalls [n]
      (Feq wnat (add (Tvar n) O) (Tvar n)));
    tprop Plemma "plus_n_Sm" (fforalls [n; m]
      (Feq wnat (S (add (Tvar n) (Tvar m)))
        (add (Tvar n) (S (Tvar m)))));
    tprop Pgoal "add_comm" (fforalls [n; m]
      (Feq wnat (add (Tvar n) (Tvar m))
        (add (Tvar m) (Tvar n))))
  ].

Lemma S_eq: forall t,
Tfun S_fs nil [t] = S t.
Proof.
  reflexivity.
Qed.

Lemma add_eq: forall t1 t2,
  Tfun add_fs nil [t1; t2] = add t1 t2.
Proof.
  reflexivity.
Qed.

Definition n_ : term := (t_constsym "n" wnat).
Definition m_ : term := (t_constsym "m" wnat).

Lemma n_eq_: Tfun (const_noconstr "n" wnat) nil nil = n_.
Proof.
  reflexivity.
Qed.

Lemma m_eq_ : Tfun (const_noconstr "m" wnat) nil nil = m_.
reflexivity. Qed.

Ltac extra_simpl ::= fold wnat; fold n_; fold m_; 
  try rewrite n_eq_; try rewrite m_eq_; 
  try fold O; try rewrite !S_eq; try rewrite !add_eq.

Lemma induction_theory_typed : typed_theory induction_theory.
Proof.
  check_theory.
Qed.
Require Import Induction.

Ltac simpl_aset_mem_dec :=
  try match goal with
   | |- context [ aset_mem_dec ?x ?y ] =>
         let z := fresh in
         set (z := aset_mem_dec x y) in *; vm_compute in z; subst z
   end.

Ltac simpl_aset_to_list :=
  try match goal with
   | |- context [ aset_to_list ?x ] =>
         let z := fresh in
         set (z := aset_to_list x) in *; vm_compute in z; subst z
   end.

(*NOTE: would really want to combine but Ltac does not allow arguments with wildcards*)
Ltac simpl_existsb :=
  try match goal with
   | |- context [ List.existsb ?x ?y ] =>
         let z := fresh in
         set (z := List.existsb x y) in *; vm_compute in z; subst z
   end.

Ltac simpl_amap_lookup :=
  try match goal with
   | |- context [ amap_lookup ?x ?y ] =>
         let z := fresh in
         set (z := amap_lookup x y) in *; vm_compute in z; subst z
   end.
Print sumbool.
Ltac simpl_if :=
  match goal with
      | |- context [match ?b with | true => ?c | false => ?d end] => let z := fresh in 
        set (z:= b) in *; vm_compute in z; subst z; cbv match
      | |- context [match ?b with | left _ => _ | right _ => _ end] => let z := fresh in 
        set (z:= b) in *; vm_compute in z; subst z; cbv match
      end.


Ltac winduction :=
  match goal with
  | |- derives (?g, ?d, Fquant Tforall ?x ?f) =>
    eapply D_induction;
    [reflexivity | reflexivity | reflexivity | prove_closed | ];
    simpl List.map; simpl iter_and; split_all; auto; unfold constr_case;

    simpl_gen_strs; simpl; unfold safe_sub_f; repeat simpl_if; simpl; extra_simpl
(* simpl_aset_mem_dec; cbv iota;
    repeat simpl_aset_to_list; simpl_existsb; simpl*)
    (*unfold constr_case; unfold safe_sub_f; simpl_gen_strs; (*Must do before simpl*) simpl;
    try extra_simpl*)
  | |- _ => fail "Induction requires generalization:
    goal must be in form (Forall (x: a(vs)), f
    where a is a non-mutual ADT"
  end.




    
(*
Print a_convert_t.



(*Alpha conv and safe sub*)
Module List.

Definition replace_var (l: list (string * string)) (x: vsymbol) : vsymbol :=
  match (get_assoc_list string_dec l (fst x)) with
  | Some y => (y, snd x)
  | None => x
  end.

Fixpoint map_pat (f: vsymbol -> vsymbol) (p: pattern) : pattern :=
  match p with
  | Pvar x => Pvar (f x)
  | Pwild => Pwild
  | Pconstr c tys ps =>
    Pconstr c tys (map (fun x => map_pat f x) ps)
  | Por p1 p2 =>
    Por (map_pat f p1) (map_pat f p2)
  | Pbind p1 x =>
    Pbind (map_pat f p1) (f x)
  end.

Definition a_convert_map_p (l: list (string * string)) (p: pattern) :
  pattern :=
  map_pat (replace_var l) p.

Fixpoint a_convert_map_t (l: list (string * string))
  (bnd: list vsymbol) (t: term) : term :=
  match t with
  | Tvar v =>
    Tvar (if in_bool vsymbol_eq_dec v bnd then 
    replace_var l v else v)
  | Tfun fs tys tms => Tfun fs tys (map (a_convert_map_t l bnd) tms)
  | Tlet t1 v t2 =>
    Tlet (a_convert_map_t l bnd t1) (replace_var l v) 
      (a_convert_map_t l (v :: bnd) t2)
  | Tif f1 t1 t2 =>
    Tif (a_convert_map_f l bnd f1) (a_convert_map_t l bnd t1) (a_convert_map_t l bnd t2)
  | Tmatch tm ty ps =>
    Tmatch (a_convert_map_t l bnd tm) ty
      (map (fun x => (a_convert_map_p l (fst x), 
        (a_convert_map_t l (pat_fv' (fst x) ++ bnd) (snd x)))) ps)
  | Teps f v => Teps (a_convert_map_f l (v :: bnd) f) (replace_var l v)
  | _ => t
  end
with a_convert_map_f (l: list (string * string)) 
  (bnd: list vsymbol) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (a_convert_map_t l bnd) tms)
  | Fquant q v f => Fquant q (replace_var l v) (a_convert_map_f l (v :: bnd) f)
  | Feq ty t1 t2 => Feq ty (a_convert_map_t l bnd t1) (a_convert_map_t l bnd t2)
  | Fbinop b f1 f2 => Fbinop b (a_convert_map_f l bnd f1) (a_convert_map_f l bnd f2)
  | Fnot f => Fnot (a_convert_map_f l bnd f)
  | Flet t v f => Flet (a_convert_map_t l bnd t) (replace_var l v)
    (a_convert_map_f l (v :: bnd) f)
  | Fif f1 f2 f3 => Fif (a_convert_map_f l bnd f1) (a_convert_map_f l  bnd f2)
    (a_convert_map_f l bnd f3)
  | Fmatch tm ty ps =>
    Fmatch (a_convert_map_t l bnd tm) ty
    (map (fun x => (a_convert_map_p l (fst x), 
      (a_convert_map_f l (pat_fv' (fst x) ++ bnd) (snd x)))) ps)
  | _ => f
  end.
(*NOTE: could be a problem because the alpha map is different - might need to prove
  maps are the same (somehow)*)

Definition a_convert_t (t: term) (l: list vsymbol) : term :=
  a_convert_map_t (combine (map fst l) 
    (GenElts.gen_strs (length l) (l ++ tm_bnd t ++ tm_fv t))) nil t.




safe_sub_ts =
fun (subs : amap vsymbol term) (t : term) =>
if Alpha.check_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (tm_bnd t))
then sub_ts subs t
else sub_ts subs (a_convert_t t (aset_big_union tm_fv (vals subs)))


(* 
Definition get_assoc_list {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (l: list (A * B)) (x: A) : option B :=
  fold_right (fun y acc => if eq_dec x (fst y) then Some (snd y) else acc) None l.
 *)
Lemma get_assoc_list_some {A B: Type} 
(eq_dec: forall (x y: A), {x = y} + { x <> y}) 
(l: list (A * B)) (x: A) (res: B):
  get_assoc_list eq_dec l x = Some res ->
  In (x, res) l.
Proof.
  induction l; simpl. intro C; inversion C.
  destruct (eq_dec x (fst a)); subst. intro C; inversion C; subst.
  left. destruct a; auto.
  intros. right. apply IHl. assumption.
Qed.

Lemma get_assoc_list_none {A B: Type} 
(eq_dec: forall (x y: A), {x = y} + { x <> y}) 
(l: list (A * B)) (x: A) :
  get_assoc_list eq_dec l x = None <->
  ~ In x (map fst l).
Proof.
  induction l; simpl; split; intros; auto.
  - intro C. destruct (eq_dec x (fst a)); subst.
    inversion H. destruct C. subst. contradiction.
    apply IHl; auto.
  - destruct (eq_dec x (fst a)); subst. exfalso. apply H. left; auto.
    apply IHl. intro C. apply H. right; assumption.
Qed.

Lemma get_assoc_list_nodup {A B: Type} 
  (eq_dec: forall (x y: A), {x=y} +{x<> y})
  (l: list (A * B)) (x: A) (y: B)
  (Hnodup: NoDup (map fst l))
  (Hin: In (x, y) l):
  get_assoc_list eq_dec l x = Some y.
Proof.
  unfold get_assoc_list. induction l; simpl; auto.
  inversion Hin.
  inversion Hnodup; subst.
  destruct Hin as [Heq | Hin]; subst; auto; simpl in *.
  destruct (eq_dec x x); try contradiction; auto.
  destruct a as [h1 h2]; subst; simpl in *.
  destruct (eq_dec x h1); subst; auto.
  exfalso. apply H1. rewrite in_map_iff. exists (h1, y); auto.
Qed.

*)

(*Substitution is the main one I think*)
Ltac wunfold x :=
  apply D_unfold with (f := add_fs); [ prove_closed |  ]; unfold unfold_f; simpl;unfold unfold_f_aux;
      simpl; unfold sub_body_t; rewrite <- !safe_sub_ts_equiv; unfold safe_sub_ts';
  repeat simpl_if; unfold TySubst.ty_subst_wf_tm, TySubst.make_tm_wf;
  repeat simpl_if; try rewrite replace_tm_t_eq; simpl; extra_simpl.
(*   apply D_unfold with (f := x); [ prove_closed |  ]; unfold unfold_f; simpl;unfold unfold_f_aux;
  simpl; unfold sub_body_t; rewrite <- safe_sub_ts_equiv; unfold safe_sub_ts';
  repeat simpl_if; unfold TySubst.ty_subst_wf_tm, TySubst.make_tm_wf;
  simpl_if; unfold TySubst.ty_subst_tm; simpl; extra_simpl. *)
(*   apply D_unfold with (f := x); [ prove_closed |  ]; unfold unfold_f; simpl; unfold unfold_f_aux; simpl;
  unfold sub_body_t, safe_sub_ts; repeat simpl_if;
  unfold TySubst.ty_subst_wf_tm, TySubst.make_tm_wf;
  simpl_if; unfold TySubst.ty_subst_tm; simpl List.map;
  rewrite sub_ts_equiv; simpl. *)

Ltac wintros_tac c :=
  match goal with
  | |- derives (?g, ?d, (Fquant Tforall ?x ?f)) =>
    apply (D_forallI g d x f c);
    [reflexivity | prove_fmlas_ty | prove_closed |];
    unfold safe_sub_f; repeat simpl_if; simpl; extra_simpl
  | |- derives (?g, ?d, (Fbinop Timplies ?f1 ?f2)) =>
    apply (D_implI g d c f1 f2);
    [prove_closed (*| apply /inP; reflexivity*) |];
    extra_simpl
  | |- _ => fail "wintros requires goal to be Forall or Implies"
  end.

Tactic Notation "wintros" constr(c1) :=
  wintros_tac c1.

Tactic Notation "wintros" constr(c1) constr(c2) :=
  wintros_tac c1;
  wintros_tac c2.

Tactic Notation "wintros" constr(c1) constr(c2) constr(c3) :=
  wintros_tac c1;
  wintros_tac c2;
  wintros_tac c3.




Ltac wsimpl_match :=
  apply D_simpl_match; [ prove_closed |  ];
      rewrite <- simpl_match_f_eq; simpl; unfold safe_sub_ts'; repeat simpl_if;
      simpl; extra_simpl. 
  (* apply D_simpl_match; [ prove_closed |  ]; unfold MatchSimpl.simpl_match_f; simpl List.map;
      rewrite check_match_sub_eq; simpl;
      unfold safe_sub_ts'; simpl_if; simpl; extra_simpl. *)
(* simpl; extra_simpl*)

Ltac wspecialize_tac name tm :=
  eapply (derives_specialize _ _ _ name tm);
  [reflexivity | prove_tm_ty | prove_closed_tm | prove_task_wf |];
  unfold replace_hyp; simpl;
  unfold safe_sub_f; repeat simpl_if; simpl;
  extra_simpl.

Ltac wspecialize_tac2 name tms :=
  match tms with
  | nil => idtac
  | ?tm :: ?tl => wspecialize_tac name tm; wspecialize_tac2 name tl
  end.


Ltac wrewrite' H :=
  match goal with
  | |- derives (?g, ?d, ?f) =>
    eapply (derives_rewrite g d f H);
    [reflexivity | prove_closed | prove_closed |];
    rewrite replace_tm_f_eq; simpl; extra_simpl
    (*unfold replace_tm_f; simpl; extra_simpl*)
  | _ => fail "Usage: rewrite H, where H : t1 = t2"
  end.

Ltac wrewrite_in H1 H2 :=
  eapply derives_rewrite_in with(name1:=H1)(name2:=H2);
  [reflexivity | reflexivity | prove_closed | prove_closed
    | prove_closed | prove_fmlas_ty |];
  rewrite replace_tm_f_eq; simpl;
  extra_simpl.

Tactic Notation "wrewrite" constr(H) :=
  wrewrite' H.
Tactic Notation "wrewrite" constr(H1) "in" constr(H2) :=
  wrewrite_in H1 H2.

Tactic Notation "wrewrite<-" constr(H) :=
  wsymmetry_in H; wrewrite H; wsymmetry_in H.

Tactic Notation "wrewrite<-" constr (H1) "in" constr(H2) :=
wsymmetry_in H1; wrewrite H1 in H2; wsymmetry_in H1.

Ltac wrewrite_with_tac H o b args :=
  (*First, generate new hypothesis*)
  match goal with
  | |- derives (?g, ?d, ?goal) =>
    let new := constr:(GenElts.gen_name EmptyString (list_to_aset (map fst d))) in
    wcopy H new;
    wspecialize_tac2 new args;
    match o with
    | Some ?H2 =>
      match b with
      | true => wrewrite<- new in H2
      | false => wrewrite new in H2
      end
    | None =>
      match b with
      | true => wrewrite<- new
      | false => wrewrite new
      end
    end;
    wclear new;
    extra_simpl
  end.

(*We will have versions for 1, 2, and 3 arguments. Unfortunately,
  this means we need 12 cases*)
Tactic Notation "wrewrite[" constr(H) constr(t1) "]" :=
  wrewrite_with_tac H (@None string) false [t1].
Tactic Notation "wrewrite[" constr(H) constr(t1) constr(t2) "]" :=
  wrewrite_with_tac H (@None string) false [t1; t2].
Tactic Notation "wrewrite[" constr(H) constr(t1) constr(t2) constr(t3) "]" :=
  wrewrite_with_tac H (@None string) false [t1; t2; t3].

Tactic Notation "wrewrite<-[" constr(H) constr(t1) "]" :=
  wrewrite_with_tac H (@None string) true [t1].
Tactic Notation "wrewrite<-[" constr(H) constr(t1) constr(t2) "]" :=
  wrewrite_with_tac H (@None string) true [t1; t2].
Tactic Notation "wrewrite<-[" constr(H) constr(t1) constr(t2) constr(t3) "]" :=
  wrewrite_with_tac H (@None string) true [t1; t2; t3].

Tactic Notation "wrewrite[" constr(H) constr(t1) "] in " constr(H2) :=
  wrewrite_with_tac H (Some H2) false [t1].
Tactic Notation "wrewrite[" constr(H) constr(t1) constr(t2) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) false [t1; t2].
Tactic Notation "wrewrite[" constr(H) constr(t1) constr(t2) constr(t3) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) false [t1; t2; t3].

Tactic Notation "wrewrite<-[" constr(H) constr(t1) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) true [t1].
Tactic Notation "wrewrite<-[" constr(H) constr(t1) constr(t2) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) true [t1; t2].
Tactic Notation "wrewrite<-[" constr(H) constr(t1) constr(t2) constr(t3) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) true [t1; t2; t3].


Ltac wunfold_at x n :=
  apply D_unfold_single with (f:=x)(i:=n); [prove_closed |];
  unfold unfold_f_single; unfold get_fun_body_args, get_rec_fun_body_args; simpl fold_right;
  cbv match; simpl_if; unfold unfold_f_single_aux, sub_fun_body_f;
  rewrite replace_tm_f_eq; simpl; unfold sub_body_t;
  rewrite <- safe_sub_ts_equiv; unfold safe_sub_ts'; repeat simpl_if;
  unfold TySubst.ty_subst_wf_tm, TySubst.make_tm_wf;
  repeat simpl_if; try rewrite replace_tm_t_eq; simpl; extra_simpl.

(*   apply D_unfold_single with (f:=x)(i:=n); [prove_closed |];
  unfold unfold_f_single; simpl; unfold unfold_f_single_aux; simpl;
  unfold sub_fun_body_f, replace_tm_f, sub_body_t;
  rewrite <- !safe_sub_ts_equiv; unfold safe_sub_ts'; repeat simpl_if; simpl;
  repeat (progress(extra_simpl)). *)


(* simpl; unfold unfold_f_aux; simpl;
   unfold unfold_f_single_aux; simpl; unfold sub_fun_body_f, replace_tm_f, sub_body_t, safe_sub_ts;
   simpl; extra_simpl.*)
Opaque amap_lookup.
Opaque safe_sub_ts.
Lemma induction_theory_valid : valid_theory induction_theory.
Proof.
  simpl. split_all; auto.
  - (*Prove "add_0_r"*)
    wstart.
    winduction.
    + wunfold add_fs.  wsimpl_match. wreflexivity.
    + wintros "n" "IH".
      wunfold add_fs.
      wsimpl_match.
      extra_simpl.
      wrewrite "IH".
      wreflexivity.
  - (*Prove "plus_n_Sm"*)
    wstart.
    winduction.
    + wintros "m".
      wunfold add_fs.
      wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold add_fs.
      wsimpl_match.
      wrewrite["IH" m_]. (*NOTE: still slow*)
      wreflexivity.
  - (*And the main theorem*)
    wstart.
    winduction.
    + wintros "m". wrewrite["add_0_r" m_]. 
      wunfold add_fs. wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold_at add_fs 0%N; wsimpl_match.
      wrewrite["IH" m_].
      wrewrite["plus_n_Sm" m_ n_].
      wreflexivity.
Qed.
   



  (*  winduction.
    + wunfold add_fs. wsimpl_match. wreflexivity.
    + wintros "n" "IH".
      wunfold add_fs.
      wsimpl_match.
      wrewrite "IH".
      wreflexivity.
  - (*Prove "plus_n_Sm"*)
    wstart.
    winduction.
    + wintros "m".
      wunfold add_fs.
      wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold add_fs.
      wsimpl_match.
      wrewrite["IH" m_].
      wreflexivity.
  - (*And the main theorem*)
    wstart.
    winduction.
    + wintros "m". wrewrite["add_0_r" m_]. 
      wunfold add_fs. wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold_at add_fs 0%N; wsimpl_match.
      wrewrite["IH" m_].
      wrewrite["plus_n_Sm" m_ n_].
      wreflexivity.
Qed. *)

End InductionTest.

(* 
(*Test for induction - we define natural numbers and prove that
  addition is commutative*)



From Proofs.proofsystem Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".


Module InductionTest.

Local Open Scope string_scope.

(*First, define nat type*)
Definition nat_ts : typesym := mk_ts "nat" nil.
Definition wnat : vty := vty_cons nat_ts nil.
Definition O_fs : funsym := mk_constr "0" nil nil wnat 2 erefl erefl erefl.
Definition S_fs: funsym := mk_constr "S" nil [wnat] wnat 2 erefl erefl erefl.
Definition wnat_adt : alg_datatype := alg_def nat_ts
  (list_to_ne_list [O_fs; S_fs] erefl).
Definition wnat_mut : mut_adt := mk_mut [wnat_adt] nil erefl.

Definition O : term := Tfun O_fs nil nil.
Definition S (t: term) : term := Tfun S_fs nil [t].

(*Function definition*)
Definition n : vsymbol := ("n", wnat).
Definition m: vsymbol := ("m", wnat).
Definition n': vsymbol := ("n'", wnat).
Definition add_fs : funsym := mk_noconstr "add" nil [wnat; wnat] wnat erefl erefl erefl.
Definition add (t1 t2: term) := Tfun add_fs nil [t1; t2].
Definition add_def : funpred_def :=
  fun_def add_fs [n; m] 
  (Tmatch (Tvar n) wnat
    [(Pconstr O_fs nil nil, Tvar m); (*O -> m*)
     (Pconstr S_fs nil [Pvar n'], S (add (Tvar n') (Tvar m))) (*S n' -> S (add n' m)*)
    ]).

Definition induction_theory : theory :=
  rev [
    tdef (datatype_def wnat_mut);
    tdef (recursive_def [add_def]);
    (*We need two lemmas*)
    tprop Plemma "add_0_r" (fforalls [n]
      (Feq wnat (add (Tvar n) O) (Tvar n)));
    tprop Plemma "plus_n_Sm" (fforalls [n; m]
      (Feq wnat (S (add (Tvar n) (Tvar m)))
        (add (Tvar n) (S (Tvar m)))));
    tprop Pgoal "add_comm" (fforalls [n; m]
      (Feq wnat (add (Tvar n) (Tvar m))
        (add (Tvar m) (Tvar n))))
  ].

Lemma S_eq: forall t,
Tfun S_fs nil [t] = S t.
Proof.
  reflexivity.
Qed.

Lemma add_eq: forall t1 t2,
  Tfun add_fs nil [t1; t2] = add t1 t2.
Proof.
  reflexivity.
Qed.

Definition n_ : term := (t_constsym "n" wnat).
Definition m_ : term := (t_constsym "m" wnat).

Lemma n_eq_: Tfun (const_noconstr "n" wnat) nil nil = n_.
Proof.
  reflexivity.
Qed.

Lemma m_eq_ : Tfun (const_noconstr "m" wnat) nil nil = m_.
reflexivity. Qed.



Ltac extra_simpl ::= fold wnat; fold n_; fold m_; 
  try rewrite n_eq_; try rewrite m_eq_; 
  try fold O; try rewrite !S_eq; try rewrite !add_eq; simpl_gen_strs. (*TODO: bad*)

From Equations Require Import Equations.

Lemma induction_theory_typed : typed_theory induction_theory.
Proof.
  apply /check_typed_theory_correct.
  reflexivity.
Qed.
(* 
Lemma fpsym_eq_dec' (f1 f2: fpsym) : {f1 = f2} + {f1 <> f2}.
Print fpsym.

destruct f1 as [s1 p1 a1 w1 n1]; destruct f2 as [s2 p2 a2 w2 n2].
destruct (string_dec s1 s2); [|right; intro C; injection C; contradiction].
destruct (list_eq_dec typevar_eq_dec p1 p2); [|right; intro C; injection C; contradiction].
destruct (list_eq_dec vty_eq_dec a1 a2);  [|right; intro C; injection C; contradiction].
left. apply fpsym_eq; auto.
Defined.

Lemma funsym_eq_dec' (f1 f2: funsym) : {f1 = f2} + {f1 <> f2}.
Print funsym.

destruct f1 as [s1 r1 c1 n1 w1]; destruct f2 as [s2 r2 c2 n2 w2].
destruct (fpsym_eq_dec' s1 s2); [| right; intro C; injection C; contradiction].
destruct (vty_eq_dec r1 r2); [| right; intro C; injection C; contradiction].
Search bool "dec".
destruct (Bool.bool_dec c1 c2); [| right; intro C; injection C; contradiction].
destruct (Nat.eq_dec n1 n2); [| right; intro C; injection C; contradiction].
left. apply funsym_eq; auto.
Defined.
Print add_fs.

Print funsym.
Print fpsym.
Definition add_fs' : funsym := Build_funsym (Build_fpsym "add" nil [wnat; wnat] Logic.eq_refl Logic.eq_refl) wnat false 0 Logic.eq_refl.
Eval cbn in (funsym_eq_dec add_fs' add_fs').

Lemma add_fs_eq: add_fs' = add_fs. Proof.
  apply funsym_eq; try reflexivity.
  apply fpsym_eq; reflexivity.
Qed.

Definition O_fs': funsym := Build_funsym (Build_fpsym "O" nil nil Logic.eq_refl Logic.eq_refl) wnat true 2 erefl. *)
 (*  -
 vm_compute.
  erewrite bool_irrelevance.

 simpl. f_equal. f_equal. f_equal. f_equal. reflexivity.

Eval cbn in (funsym_eqb add_fs add_fs).
Eval vm_compute in (funsym_eq_dec' add_fs add_fs).
Locate find_args.

Eval cbn in (type_vars vty_int).
Eval vm_compute in (type_vars (vty_cons ts_d [vty_var "a"%string])).
Print find_args.



Definition find_args (l: list vty) : list typevar :=
  aset_to_list (aset_big_union type_vars l). *)

(* Definition list_to_aset' {A: Type} `{countable.Countable A} (l: list A) : aset A :=
  fold_right (fun x acc => aset_union (aset_singleton x) acc) aset_empty l.

Definition aset_singleton' {A: Type} `{countable.Countable A} (x: A) : aset A.
  unfold aset. unfold gmap.gset. constructor.
  destruct (@aset_empty A _ _)  as [y].
  exact (gmap_partial_alter (fun _ => Some tt) x y).
Defined. *)
Require Import Induction.
Ltac winduction :=
  match goal with
  | |- derives (?g, ?d, Fquant Tforall ?x ?f) =>
    eapply D_induction;
    [reflexivity | reflexivity | reflexivity | prove_closed | ];
    simpl; split_all; auto;
    unfold constr_case; simpl_gen_strs; unfold safe_sub_f;  (*Must do before simpl*) simpl;
    try extra_simpl
  | |- _ => fail "Induction requires generalization:
    goal must be in form (Forall (x: a(vs)), f
    where a is a non-mutual ADT"
  end.

Ltac simpl_aset_mem_dec :=
  repeat match goal with
  | |- context [aset_mem_dec ?x ?s] =>
    let z := fresh in
    set (z := aset_mem_dec x s) in *;
    cbv in z;
    unfold z
  end.

Ltac simpl_aset_to_list :=
  repeat match goal with
  |- context [aset_to_list ?s] => let z := fresh in
      set (z := aset_to_list s) in *;
      cbv in z;
      subst z
    end.

(* Definition aset_empty'  {A: Type} `{countable.Countable A} : aset A.
unfold aset. constructor. constructor. apply gmap.GEmpty.
Defined.

Definition aset_union' {A: Type} `{countable.Countable A} (s1 s2: aset A) : aset A.
unfold aset in *.
unfold gmap.gset in *.
destruct s1 as [s1]. destruct s2 as [s2].
constructor. exact (gmap.gmap_merge _ _  _ (stdpp.base.union_with (fun x _ => Some x)) s1 s2).
Defined.

Definition aset_big_union' {A B: Type} `{countable.Countable A} (f: B -> aset A) (l: list B): aset A :=
  fold_right (fun x acc => aset_union' (f x) acc) aset_empty' l.

Lemma aset_big_union_eq {A B: Type} `{countable.Countable A} (f: B -> aset A) (l: list B):
  aset_big_union f l = aset_big_union' f l.
Proof. Admitted. *)


Lemma induction_theory_valid : valid_theory induction_theory.
Proof.
  simpl. split_all; auto.
  - (*Prove "add_0_r"*)
    wstart. eapply D_induction;
    [reflexivity | reflexivity | reflexivity | prove_closed | ];
    simpl; split_all; auto;
    unfold constr_case; simpl_gen_strs; unfold safe_sub_f; simpl_aset_mem_dec.
    + simpl List.filter. simpl combine. unfold List.map. simpl_aset_to_list. simpl.
      Print Ltac wunfold.
      (*TODO: come back and fix this later, not worth doing right now*)
      wunfold add_fs.
    2: {
    repeat match goal with
    | |- 
    simpl List.filter. cbv beta. unfold List.map.
    repeat match goal with
    | |- context [aset_to_list ?s] => let z := fresh in
      set (z := aset_to_list s) in *;
      cbv in z;
      subst z
    end.
    simpl.
    


 cbv beta. cbv iota. simpl List.map.
    match goal with
    | |- context [tm_fv ?s] => let z := fresh in
      set (z := tm_fv s) in *;
      simpl in z;
      subst z
    end.
    simpl a_convert_f.
    simpl.
    simpl in H1. exfalso.
    rewrite aset_big_union_eq in H1. simpl in H1. vm_compute in H1. simpl in H1.
    

 cbv in H1.
    unfold tm_fv in H1. cbn beta.
    set (l:= (List.map Tvar (combine [:: "x0"] (ty_subst_list' (s_params S_fs) [::] (s_args S_fs))))) in *.
    cbv in l. subst l. exfalso.
    rewrite aset_big_union_eq in H1. cbv in H1. simpl in H1.
    Print tm_fv.
    cbn in H1.
    cbv in H1.
    

 simpl.

 set (y:= (aset_to_list
                  (tm_fv
                     (Tfun S_fs [::]
                        (List.map Tvar
                           (combine [:: "x0"] (ty_subst_list' (s_params S_fs) [::] (s_args S_fs)))))))) in *.
    cbv in y. unfold y. 
    set (z:= 

simpl.
    +
 simpl. wunfold add_fs. wreflexivity.
    set (x:= aset_mem_dec n (fmla_fv (Feq wnat (add (Tvar n) O) (Tvar n)))).
    cbv in x. unfold x; simpl.
    match goal with
  |

    simpl aset_mem_dec.



 simpl.
    + unfold constr_case. simpl_gen_strs. simpl. try extra_simpl.
    Print Ltac winduction.
 
      match goal with
      |- context [GenElts.gen_strs ?x ?y] => set (z := GenElts.gen_strs x y) in *
      end.
      cbv in z. unfold z; simpl.
      


 simpl GenElts.gen_strs.
      match goal with
  
      
      set (x:= {|
                         mapset.mapset_car :=
                           base.union
                             (base.union (base.singletonM n tt)
                                (base.union
                                   (base.union (base.singletonM n tt) (base.union base.empty base.empty))
                                   (base.singletonM n tt))) base.empty
                       |}).
    vm_compute in x.
    set (y := aset_to_list x).
    vm_compute in y.
    set (z := map fst y).
    vm_compute in z.
    set (z1 := list_to_aset' z).
    unfold list_to_aset' in z1.
    set (z2 := aset_singleton "n").
    vm_compute in z2.
    set (z2 := aset_union (aset_singleton "n") aset_empty
    vm_compute in z1.
    set (y:= aset_map fst x).
    vm_compute in y.
    simpl in y.
Check strings.String.countable_obligation_1 .
  cbv in y.
    set (y:= (GenElts.gen_strs 0 x)).
    Print GenElts.gen_strs.
    Eval cbn in (aset_map fst x).


 cbn in y.


 unfold x. simpl GenElts.gen_strs at 1.
     vm_compute in x.
  

 simpl GenElts.gen_strs. simpl map. simpl combine.


 simpl safe_sub_f.


 simpl aset_size. simpl.  cbn. simpl. vm_compute aset_size. unfold safe_sub_f. cbn.
      vm_compute aset_mem_dec. simpl.
    set (x:=aset_mem_dec n
            {|
              mapset.mapset_car :=
                {|
                  gmap.gmap_car :=
                    gmap.gmap_dep_merge (base.union_with (fun x : unit => fun=> Some x))
                      (gmap.gmap_dep_ne_omap [eta Some]
                         (gmap.gmap_dep_ne_singleton (countable.encode ("n", wnat))
                            (gmap.gmap_key_encode ("n", wnat)) tt))
                      (gmap.GNodes
                         (gmap.gmap_dep_ne_singleton (countable.encode ("n", wnat))
                            (gmap.gmap_key_encode ("n", wnat)) tt))
                |}
            |}) in *.
    exfalso.
    vm_compute in x.


 unfold aset_mem_dec, gmap.gset_elem_of_dec. cbn.
      About mapset.mapset_elem_of_dec. Print mapset.mapset_elem_of_dec. About base.decide.

simpl mapset.mapset_elem_of_dec.
      unfold mapset.mapset_elem_of_dec. cbn. About base.decide. simpl.

 simpl.
    
    simpl; split_all; auto;
    unfold constr_case; unfold safe_sub_f; simpl;
    try extra_simpl.

 winduction.
    wintros "n". 
    + wunfold add_fs. wsimpl_match. wreflexivity.
    + wintros "n". wintros "IH".
      wunfold add_fs. wsimpl_match. wrewrite "IH". wreflexivity.
  (*Prove "plus_n_Sm"*)
  - wstart.
    winduction.
    + wintros "m".
      wunfold add_fs.
      wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold add_fs.
      (* wrewrite["IH" m_]. *) (*extremely slow*)
      wsimpl_match. wcopy "IH" "IH2". 
      wspecialize_tac2 "IH2" [m_].
      wrewrite "IH2".
      wreflexivity.
  - (*And the main theorem*)
    wstart.
    winduction.
    + wintros "m". wrewrite["add_0_r" m_]. 
      wunfold add_fs. wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold_at add_fs 0%N; wsimpl_match.
      (*Which part is so slow? see*)
      (* wrewrite["IH" m_]. *)
      wcopy "IH" "IH2". 
      wspecialize_tac2 "IH2" [m_].
      wrewrite "IH2".
      (* wrewrite["plus_n_Sm" m_ n_]. TODO: dont use gen_strs maybe?*)
      wcopy "plus_n_Sm" "plus_n_Sm_1".
      wspecialize_tac2 "plus_n_Sm_1" [m_; n_].
      wrewrite "plus_n_Sm_1".
      wreflexivity.
Qed.
(* 
      
 wsimpl_match. wreflexivity.
    + wintros "n" "IH".
      wunfold add_fs.
      wsimpl_match.
      wrewrite "IH".
      wreflexivity.
  - (*Prove "plus_n_Sm"*)
    wstart.
    winduction.
    + wintros "m".
      wunfold add_fs.
      wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold add_fs.
      wsimpl_match.
      wrewrite["IH" m_].
      wreflexivity.
  - (*And the main theorem*)
    wstart.
    winduction.
    + wintros "m". wrewrite["add_0_r" m_]. 
      wunfold add_fs. wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold_at add_fs 0%N; wsimpl_match.
      wrewrite["IH" m_].
      wrewrite["plus_n_Sm" m_ n_].
      wreflexivity.
Qed. *)

End InductionTest.
 *)
