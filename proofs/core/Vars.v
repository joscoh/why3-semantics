Require Export Syntax.
Set Bullet Behavior "Strict Subproofs".

(*Various functions on terms and formulas - free and bound
  variables, type variables, fun/pred symbols, etc*)

Section FreeVars.

Local Notation union' := (union vsymbol_eq_dec).
Local Notation big_union' := (big_union vsymbol_eq_dec).
Local Notation remove' := (remove vsymbol_eq_dec).
Local Notation remove_all' := (remove_all vsymbol_eq_dec).

(*Free variables of a pattern*)
Fixpoint pat_fv (p: pattern) : list vsymbol :=
  match p with
  | Pvar x => [x]
  | Pwild => []
  | Pconstr _ _ ps => big_union' pat_fv ps
  | Por p1 p2 => union' (pat_fv p1) (pat_fv p2)
  | Pbind p x => union' (pat_fv p) [x]
  end.

(*Free variables of a term (all variables that appear free at least once)*)
Fixpoint tm_fv (t: term) : list vsymbol :=
  match t with
  | Tconst _ => nil
  | Tvar x => [x]
  | Tfun f vtys tms => big_union' tm_fv tms
  | Tlet t1 v t2 => union' (tm_fv t1) (remove' v (tm_fv t2))
  | Tif f t1 t2 => union' (fmla_fv f) (union' (tm_fv t1) (tm_fv t2))
  | Tmatch t ty l => union' (tm_fv t) (big_union' (fun x => remove_all' (pat_fv (fst x)) (tm_fv (snd x))) l)
  | Teps f x  => remove' x (fmla_fv f)
  end

with fmla_fv (f: formula) : list vsymbol :=
  match f with
  | Fpred p tys tms => big_union' tm_fv tms
  | Fquant q v f => remove' v (fmla_fv f)
  | Feq _ t1 t2 => union' (tm_fv t1) (tm_fv t2)
  | Fbinop b f1 f2 => union' (fmla_fv f1) (fmla_fv f2)
  | Fnot f => fmla_fv f
  | Ftrue => nil
  | Ffalse => nil
  | Flet t v f => union' (tm_fv t) (remove' v (fmla_fv f))
  | Fif f1 f2 f3 => union' (fmla_fv f1) (union' (fmla_fv f2) (fmla_fv f3))
  | Fmatch t ty l => union' (tm_fv t) (big_union' (fun x => remove_all' (pat_fv (fst x)) (fmla_fv (snd x))) l)
  end.

Definition closed_term (t: term) : bool :=
  null (tm_fv t).
Definition closed_formula (f: formula) : bool :=
  null (fmla_fv f).

Lemma NoDup_pat_fv (p: pattern) : NoDup (pat_fv p).
Proof.
  induction p; simpl; try constructor; auto.
  - constructor.
  - apply big_union_nodup.
  - apply union_nodup; auto.
  - apply union_nodup; auto. constructor; auto. constructor.
Qed.

Lemma remove_nodup {A} (eq_dec: forall (x y: A), {x = y} + {x <> y}) x l:
  NoDup l ->
  NoDup (remove eq_dec x l).
Proof.
  intros. induction l; simpl; auto.
  inversion H; subst.
  destruct (eq_dec x a); auto. constructor; auto.
  simpl_set. intros [Hina Hax].
  contradiction.
Qed.

Lemma fv_nodup t f:
  NoDup (tm_fv t) /\ NoDup (fmla_fv f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros;
  try solve[repeat(constructor; auto)];
  repeat (apply big_union_nodup +
  apply union_nodup + apply remove_nodup); auto.
Qed.

Definition tm_fv_nodup t := proj_tm fv_nodup t.
Definition fmla_fv_nodup f := proj_fmla fv_nodup f.

End FreeVars.

Section BoundVars.

(*Define bound variables of formula and term *)
Fixpoint fmla_bnd (f: formula) : list vsymbol :=
  match f with
  | Fpred p tys tms => concat (map tm_bnd tms)
  | Fquant q v f' =>
    v :: fmla_bnd f'
  | Feq ty t1 t2 =>
    tm_bnd t1 ++ tm_bnd t2
  | Fbinop b f1 f2 =>
    fmla_bnd f1 ++ fmla_bnd f2
  | Fnot f' => fmla_bnd f'
  | Ftrue => nil
  | Ffalse => nil
  | Flet tm v f' =>
    v :: tm_bnd tm ++ fmla_bnd f' 
  | Fif f1 f2 f3 =>
    fmla_bnd f1 ++ fmla_bnd f2 ++ fmla_bnd f3
  | Fmatch tm ty ps =>
    tm_bnd tm ++ concat (map 
      (fun p => pat_fv (fst p) ++ fmla_bnd (snd p)) ps)
  end
with tm_bnd (t: term) : list vsymbol :=
  match t with
  | Tconst c => nil
  | Tvar v  => nil 
  | Tfun fs tys tms =>
    concat (map tm_bnd tms)
  | Tlet tm1 v tm2 =>
    v :: tm_bnd tm1 ++ tm_bnd tm2
  | Tif f1 t1 t2 =>
    fmla_bnd f1 ++ tm_bnd t1 ++ tm_bnd t2
  | Tmatch tm ty ps =>
    tm_bnd tm ++ concat (map
      (fun p => pat_fv (fst p) ++ tm_bnd (snd p)) ps)
  | Teps f1 v =>
    v :: fmla_bnd f1
  end.

End BoundVars.

Section FunPredSym.

Fixpoint predsym_in_fmla (p: predsym) (f: formula) {struct f}  : bool :=
  match f with
  | Fpred ps tys tms => predsym_eq_dec p ps || existsb (predsym_in_tm p) tms
  | Fquant q x f' => predsym_in_fmla p f'
  | Feq ty t1 t2 => predsym_in_tm p t1 || predsym_in_tm p t2
  | Fbinop b f1 f2 => predsym_in_fmla p f1 || predsym_in_fmla p f2
  | Fnot f' => predsym_in_fmla p f'
  | Ftrue => false
  | Ffalse => false
  | Flet t x f' => predsym_in_tm p t || predsym_in_fmla p f'
  | Fif f1 f2 f3 => predsym_in_fmla p f1 || predsym_in_fmla p f2 || predsym_in_fmla p f3
  | Fmatch t ty ps => predsym_in_tm p t || existsb (fun x => predsym_in_fmla p (snd x)) ps
  end
  
with predsym_in_tm (p: predsym) (t: term) {struct t}  : bool :=
  match t with
  | Tconst _ => false
  | Tvar _ => false
  | Tfun fs tys tms => existsb (predsym_in_tm p) tms
  | Tlet t1 x t2 => predsym_in_tm p t1 || predsym_in_tm p t2
  | Tif f t1 t2 => predsym_in_fmla p f || predsym_in_tm p t1 || predsym_in_tm p t2
  | Tmatch t ty ps => predsym_in_tm p t || existsb (fun x => predsym_in_tm p (snd x)) ps
  | Teps f x => predsym_in_fmla p f
  end.

Fixpoint funsym_in_tm (f: funsym) (t: term) : bool :=
  match t with
  | Tfun fs _ tms => funsym_eq_dec f fs || existsb (funsym_in_tm f) tms
  | Tlet t1 _ t2 => funsym_in_tm f t1 || funsym_in_tm f t2
  | Tif f1 t1 t2 => funsym_in_fmla f f1 || funsym_in_tm f t1 ||
    funsym_in_tm f t2
  | Tmatch t1 _ ps => funsym_in_tm f t1 ||
    existsb (fun x => funsym_in_tm f (snd x)) ps
  | Teps f1 _ => funsym_in_fmla f f1
  | _ => false
  end
  with funsym_in_fmla (f: funsym) (f1: formula) : bool :=
  match f1 with
  | Fpred _ _ tms => existsb (funsym_in_tm f) tms
  | Feq _ t1 t2 => funsym_in_tm f t1 || funsym_in_tm f t2
  | Fbinop _ fm1 fm2 => funsym_in_fmla f fm1 || funsym_in_fmla f fm2
  | Fquant _ _ f' | Fnot f' => funsym_in_fmla f f'
  | Flet t _ f' => funsym_in_tm f t || funsym_in_fmla f f'
  | Fif fm1 fm2 fm3 => funsym_in_fmla f fm1 || funsym_in_fmla f fm2 ||
    funsym_in_fmla f fm3
  | Fmatch t _ ps => funsym_in_tm f t ||
    existsb (fun x => funsym_in_fmla f (snd x)) ps
  | _ => false
  end.

End FunPredSym.

(*Get all type vars present in a term or formula.
  This is an overapproximation; some are duplicates in well-typed
  terms and formulas, but it makes some proofs easier*)
Section Typevars.

Notation union := (union typevar_eq_dec).
Notation big_union := (big_union typevar_eq_dec).

Fixpoint pat_type_vars (p: pattern) : list typevar :=
  match p with
  | Pvar v => type_vars (snd v)
  | Pconstr f tys ps => 
    union (big_union type_vars tys)
        (big_union pat_type_vars ps)
  | Por p1 p2 => union (pat_type_vars p1) (pat_type_vars p2)
  | Pwild => nil
  | Pbind p x => union (pat_type_vars p) (type_vars (snd x))
  end.

(* Definition pat_type_vars (p: pattern) : list typevar :=
  big_union type_vars (map snd (pat_fv p)). *)

Fixpoint tm_type_vars (t: term) {struct t} : list typevar :=
  match t with
  | Tvar x => type_vars (snd x)
  | Tfun f tys ts => 
    union
    (big_union type_vars tys)
    (big_union tm_type_vars ts)
  | Tlet t1 x t2 => (*Same reason we don't need to add *) 
    union (union (tm_type_vars t1) (tm_type_vars t2)) 
    (type_vars (snd x))
  | Tif f t1 t2 => union (fmla_type_vars f) 
    (union (tm_type_vars t1) (tm_type_vars t2))
  | Tmatch t ty ps =>
    (*Need a nested fix so Coq can tell it terminates*)
    let fix ps_vars (ts: list (pattern * term)) {struct ts} : list typevar :=
      match ts with
      | nil => nil
      | ( _, x) :: tl => union (tm_type_vars x) (ps_vars tl)
      end in
    union (union (tm_type_vars t) 
    (big_union pat_type_vars (map fst ps))) 
    (union (ps_vars ps) (type_vars ty) (*easier to include, though we shouldn't technically need it*))
  | Teps f x => union (fmla_type_vars f) (type_vars (snd x))
  | Tconst c => nil
  end
with fmla_type_vars (f: formula) : list typevar :=
  match f with
  | Fpred p tys ts => union
    (big_union type_vars tys)
    (big_union tm_type_vars ts)
  | Fquant q x f =>
    union (type_vars (snd x)) (fmla_type_vars f)
  | Feq ty t1 t2 =>
    union (type_vars ty)
    (union (tm_type_vars t1) (tm_type_vars t2))
  | Fbinop b f1 f2 =>
    union (fmla_type_vars f1) (fmla_type_vars f2)
  | Fnot f =>
    fmla_type_vars f
  | Flet t1 x f2 => union (union (tm_type_vars t1) (fmla_type_vars f2))
    (type_vars (snd x))
  | Fif f1 f2 f3 =>
    union (fmla_type_vars f1) 
    (union (fmla_type_vars f2) (fmla_type_vars f3))
  | Fmatch t ty ps =>
    (*Need a nested fix so Coq can tell it terminates*)
    let fix ps_vars (ts: list (pattern * formula)) {struct ts} : list typevar :=
      match ts with
      | nil => nil
      | ( _, x) :: tl => union (fmla_type_vars x) (ps_vars tl)
      end in
    union (union (tm_type_vars t) 
    (big_union pat_type_vars (map fst ps))) 
    (union (ps_vars ps) (type_vars ty))
  | Ftrue => nil
  | Ffalse => nil
  end.

Lemma tm_type_vars_tmatch t ty ps:
  tm_type_vars (Tmatch t ty ps) =
  union 
    (union (tm_type_vars t)
      (big_union pat_type_vars (map fst ps)))
    (union (big_union (fun x => tm_type_vars (snd x)) ps)
      (type_vars ty)).
Proof.
  simpl.
  f_equal.
  f_equal. induction ps; simpl; auto.
  destruct a; simpl. f_equal. auto.
Qed.

Lemma tm_type_vars_fmatch t ty ps:
  fmla_type_vars (Fmatch t ty ps) =
  union 
    (union (tm_type_vars t)
      (big_union pat_type_vars (map fst ps)))
    (union (big_union (fun x => fmla_type_vars (snd x)) ps)
      (type_vars ty)).
Proof.
  simpl.
  f_equal.
  f_equal. induction ps; simpl; auto.
  destruct a; simpl. f_equal. auto.
Qed.

Definition mono (f: formula) : bool :=
  null (fmla_type_vars f).

Definition mono_t tm : bool :=
  null (tm_type_vars tm).

(*[pat_type_vars] is not useful for induction.
  We give an alternate version. We don't necessarily
  have equality unless elements are distinct.
  But we just prove equal elements*)
(* Lemma pat_type_vars_rewrite (p: pattern):
  forall x, In x (pat_type_vars p) <-> In x
  match p with
  | Pvar v => type_vars (snd v)
  | Pconstr f tys ps => big_union pat_type_vars ps
  | Por p1 p2 => union (pat_type_vars p1) (pat_type_vars p2)
  | Pwild => nil
  | Pbind p x => union (pat_type_vars p) (type_vars (snd x))
  end.
Proof.
  intros x.
  destruct p; try reflexivity.
  - unfold pat_type_vars; simpl.
    rewrite union_nil_r; try reflexivity.
    apply type_vars_unique.
  - unfold pat_type_vars; simpl.
    induction l0; simpl; try reflexivity.
    revert IHl0.
    simpl_set; intros; split; intros.
    + destruct H as [y [Hiny Hinx]].
      rewrite in_map_iff in Hiny.
      destruct Hiny as [v [Hy Hinv]]; subst.
      simpl_set.
      destruct Hinv; [left | right].
      * exists (snd v). split; auto.
        rewrite in_map_iff. exists v; auto.
      * simpl_set. destruct H as [p [Hinp Hinv]].
        exists p. split; auto. simpl_set. exists (snd v). 
        split; auto. rewrite in_map_iff; exists v; auto.
    + destruct H.
      * destruct H as [y [Hiny Hinx]]. 
        rewrite in_map_iff in Hiny.
        destruct Hiny as [v [Hy Hinv]]; subst.
        exists (snd v). split; auto.
        rewrite in_map_iff. exists v; split; auto.
        simpl_set. auto.
      * destruct H as [p [Hinp Hinx]].
        simpl_set. destruct Hinx as [y [Hiny Hinx]].
        rewrite in_map_iff in Hiny. 
        destruct Hiny as [v [Hy Hinv]]; subst.
        exists (snd v). split; auto.
        rewrite in_map_iff. exists v; split; auto.
        simpl_set. right.
        exists p; auto.
  - unfold pat_type_vars; simpl; split; intros.
    + simpl_set. destruct H as [y [Hiny Hinx]].
      rewrite in_map_iff in Hiny.
      destruct Hiny as [v [Hy Hinv]]; subst.
      simpl_set.
      destruct Hinv; [left | right]; exists (snd v);
      split; auto; rewrite in_map_iff; exists v; auto.
    + simpl_set. destruct H as [H | H];
      simpl_set; destruct H as [y [Hiny Hinx]];
      rewrite in_map_iff in Hiny; destruct Hiny as
      [v [Hy Hinv]]; subst; exists (snd v);
      split; auto; rewrite in_map_iff; exists v; simpl_set; auto.
  - unfold pat_type_vars; simpl; split; simpl_set; intros.
    + destruct H as [y [Hiny Hinx]].
      rewrite in_map_iff in Hiny. destruct Hiny as [v1 [Hy Hinv1]]; subst.
      simpl_set. simpl in Hinv1.
      destruct_all; try contradiction; subst; auto.
      left. exists (snd v1). split; auto. rewrite in_map_iff.
      exists v1; auto.
    + destruct H.
      * destruct H as [y [Hiny Hinx]].
        rewrite in_map_iff in Hiny.
        destruct Hiny as [v1 [Hy Hinv1 ]]; subst.
        exists (snd v1); split; auto.
        rewrite in_map_iff. exists v1; simpl_set; auto.
      * exists (snd v). split; auto. 
        rewrite in_map_iff. exists v; simpl_set; auto.
Qed. *)

(*One theorem we need: all typevars in free vars of a term
  or formula are in [tm/fmla_type_vars] t/f*)
Lemma fv_vars_type_vars x y (t: term) (f: formula):
  (In x (tm_fv t) -> In y (type_vars (snd x)) ->
    In y (tm_type_vars t)) /\
  (In x (fmla_fv f) -> In y (type_vars (snd x)) ->
    In y (fmla_type_vars f)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto;
  try solve[repeat(simpl_set; destruct_all); auto].
  (*Only 4 interesting cases: fun/pred and match. Even those cases
    are not particularly interesting, we just need a nested induction*)
  - simpl_set_small. right.
    induction l1; simpl in *; auto.
    inversion H; subst.
    simpl_set_small.
    destruct H0; [left | right]; auto.
  - simpl_set_small. destruct H1; auto.
    right.
    induction ps; auto.
    simpl in H1. inversion H0; subst.
    destruct a as [p t]; simpl in *.
    repeat(simpl_set_small; destruct_all);  auto.
    specialize (IHps H6 H1). destruct_all; auto.
  - simpl_set_small. right.
    induction tms; simpl in *; auto.
    inversion H; subst.
    simpl_set_small.
    destruct H0; [left | right]; auto.
  - simpl_set_small. destruct H1; auto.
    right.
    induction ps; auto.
    simpl in H1. inversion H0; subst.
    destruct a as [p t]; simpl in *. 
    repeat(simpl_set_small; destruct_all); auto.
    specialize (IHps H6 H1). destruct_all; auto.
Qed.

Lemma fv_pat_vars_type_vars (p: pattern) x y:
  In x (pat_fv p) -> In y (type_vars (snd x)) ->
  In y (pat_type_vars p).
Proof.
  intros.
  induction p; simpl in *; auto; simpl_set_small; auto.
  - subst; auto.
  - simpl_set. destruct H as [p [Hinp Hinx]].
    rewrite Forall_forall in H1.
    specialize (H1 _ Hinp Hinx).
    right. exists p; auto.
  - destruct H; auto.
  - simpl in H. destruct_all; subst; auto. contradiction.  
Qed. 

(*Also for bound vars - easier to prove separately*)
Lemma bnd_vars_type_vars x y (t: term) (f: formula):
  (In x (tm_bnd t) -> In y (type_vars (snd x)) ->
    In y (tm_type_vars t)) /\
  (In x (fmla_bnd f) -> In y (type_vars (snd x)) ->
    In y (fmla_type_vars f)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto;
  try solve[repeat(simpl_set; destruct_all; try rewrite in_app_iff in *); auto]; try contradiction.
  (*Only 4 interesting cases: fun/pred and match. These cases are 
    a tiny bit more interesting above, but not too bad*)
  - simpl_set_small. right.
    induction l1; simpl in *; try contradiction.
    rewrite in_app_iff in H0. 
    inversion H; subst.
    simpl_set_small.
    destruct H0; [left | right]; auto.
  - simpl_set_small. rewrite in_app_iff in H1. destruct H1; auto.
    induction ps; auto.
    simpl in H1. rewrite !in_app_iff in H1. inversion H0; subst.
    destruct a as [p t]; simpl in *. 
    repeat(simpl_set_small; destruct_all); auto.
    + left. right. left. eapply fv_pat_vars_type_vars. apply H1. auto.
    + specialize (IHps H6 H1). destruct_all; auto.
  - simpl_set_small. right.
    induction tms; simpl in *; try contradiction.
    rewrite in_app_iff in H0. 
    inversion H; subst.
    simpl_set_small.
    destruct H0; [left | right]; auto.
  - simpl_set_small. rewrite in_app_iff in H1. destruct H1; auto.
    induction ps; auto.
    simpl in H1. rewrite !in_app_iff in H1. inversion H0; subst.
    destruct a as [p t]; simpl in *. 
    repeat(simpl_set_small; destruct_all); auto.
    + left. right. left. eapply fv_pat_vars_type_vars. apply H1. auto.
    + specialize (IHps H6 H1). destruct_all; auto.
Qed.

Definition tm_fv_vars_type_vars t: forall x y,
In x (tm_fv t) -> In y (type_vars (snd x)) ->
In y (tm_type_vars t) := fun x y =>
proj1 (fv_vars_type_vars x y t Ftrue).

Definition fmla_fv_vars_type_vars f: forall x y,
In x (fmla_fv f) -> In y (type_vars (snd x)) ->
In y (fmla_type_vars f) := fun x y =>
proj2 (fv_vars_type_vars x y tm_d f).

Definition tm_bnd_vars_type_vars t: forall x y,
In x (tm_bnd t) -> In y (type_vars (snd x)) ->
In y (tm_type_vars t) := fun x y =>
proj1 (bnd_vars_type_vars x y t Ftrue).

Definition fmla_bnd_vars_type_vars f: forall x y,
In x (fmla_bnd f) -> In y (type_vars (snd x)) ->
In y (fmla_type_vars f) := fun x y =>
proj2 (bnd_vars_type_vars x y tm_d f).

End Typevars.

(*Some "gen" results:*)

Definition gen_fv {b: bool} (t: gen_term b) : list vsymbol :=
  match b return gen_term b -> list vsymbol with
  | true => tm_fv
  | false => fmla_fv
  end t.

Definition gen_getvars {b: bool} (x: gen_term b) : list vsymbol :=
  match b return gen_term b -> list vsymbol with
  | true => fun t => tm_bnd t ++ tm_fv t
  | false => fun f => fmla_bnd f ++ fmla_fv f
  end x.

Lemma gen_fv_getvars {b: bool} (t: gen_term b) : forall x, In x (gen_fv t) -> In x (gen_getvars t).
Proof.
  intros x. unfold gen_fv, gen_getvars. destruct b; rewrite in_app_iff; auto.
Qed.

Lemma gen_getvars_let {b: bool} (v1: vsymbol) (tm: term) (a: gen_term b) (x: vsymbol):
  In x (gen_getvars (gen_let v1 tm a)) <->
  v1 = x \/ In x (tm_bnd tm) \/ In x (tm_fv tm) \/ In x (gen_getvars a).
Proof.
  unfold gen_let, gen_getvars.
  destruct b; simpl; simpl_set_small; rewrite !in_app_iff; simpl_set_small;
  split; intros; destruct_all; auto; destruct (vsymbol_eq_dec v1 x); auto.
Qed.