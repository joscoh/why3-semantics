Require Export Coq.Strings.String.
Require Export Coq.ZArith.BinInt.
Require Export Coq.Arith.PeanoNat.
Require Export Lia.

Require Export Common.

(*Type variable (ex: a)*)
Definition typevar : Type := string. 

Definition typevar_eq_dec : forall (t1 t2: typevar),
  {t1 = t2} + {t1 <> t2} := string_dec.

(*Type symbol (ex: list a)*)
Record typesym : Type := mk_ts {
  ts_name : string;
  ts_arity: nat
  }.

Lemma typesym_eq_dec: forall (t1 t2: typesym),
  {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality. apply Nat.eq_dec. apply string_dec.
Defined.

(*Value types*)
Unset Elimination Schemes.
Inductive vty : Type :=
  | vty_int : vty
  | vty_real : vty
  | vty_var: typevar -> vty
  | vty_cons: typesym -> list vty -> vty.
Set Elimination Schemes.

(*Induction for this type*)
Section TyInd.
Variable P : vty -> Prop.
Variable Hint: P vty_int.
Variable Hreal: P vty_real.
Variable Hvar: forall v, P (vty_var v).
Variable Hcons: forall tsym vs,
  Forall P vs -> P (vty_cons tsym vs).

Fixpoint vty_ind (t: vty) : P t :=
  match t with
  | vty_int => Hint
  | vty_real => Hreal
  | vty_var t => Hvar t
  | vty_cons tsym vs => Hcons tsym vs
    ((fix vty_ind_list (l: list vty) : Forall P l :=
      match l with
      | nil => Forall_nil _
      | x :: t => Forall_cons _ (vty_ind x) (vty_ind_list t)
      end) vs)
  end.

End TyInd.

(*Decidable equality on types*)
Fixpoint vty_eqb (t1 t2: vty) : bool :=
  match t1, t2 with
  | vty_int, vty_int => true
  | vty_real, vty_real => true
  | vty_var t1, vty_var t2 => typevar_eq_dec t1 t2
  | vty_cons ts1 vs1, vty_cons ts2 vs2 =>
    typesym_eq_dec ts1 ts2 &&
    ((fix vty_eqb_list (l1 l2: list vty) : bool :=
      match l1, l2 with
      | nil, nil => true
      | x1 :: t1, x2 :: t2 => vty_eqb x1 x2 && vty_eqb_list t1 t2
      | _, _ => false
      end) vs1 vs2)
  | _, _ => false
  end.

Lemma vty_eqb_eq: forall t1 t2,
  vty_eqb t1 t2 -> t1 = t2.
Proof.
  intros t1. induction t1; simpl; auto; intros; destruct t2; auto; 
  try match goal with
  | H : is_true false |- _ => inversion H
  end; try simpl_sumbool.
  apply andb_prop in H0. destruct H0.
  simpl_sumbool. f_equal. generalize dependent l. induction vs; simpl;
  auto; intros; destruct l; auto; try solve[inversion H1].
  inversion H; subst.
  apply andb_prop in H1. destruct H1.
  apply H3 in H0; subst. f_equal.
  apply IHvs; auto.
Qed.

Lemma vty_eq_eqb: forall t1 t2,
  t1 = t2 ->
  vty_eqb t1 t2.
Proof.
  intros t1. induction t1; simpl; auto; intros; destruct t2; auto; try solve[inversion H];
  try solve[inversion H0].
  - inversion H; subst. simpl_sumbool.
  - inversion H0; subst. apply andb_true_intro; split; [simpl_sumbool |].
    clear H0. induction l; simpl; auto.
    inversion H; subst. apply andb_true_intro; split; auto.
    apply H2; auto.
Qed. 

Definition vty_eq_dec: forall (v1 v2: vty), {v1 = v2} + {v1 <> v2}.
Proof.
  intros v1 v2. destruct (vty_eqb v1 v2) eqn : Heq.
  - apply vty_eqb_eq in Heq. subst. left. auto.
  - right. intro; subst. 
    assert (vty_eqb v2 v2 = true) by (apply vty_eq_eqb; auto).
    rewrite H in Heq; inversion Heq.
Defined.

(*Type substitution (assign meaning to a type variables)*)
Fixpoint ty_subst_single (v: typevar) (t: vty) (expr: vty) : vty :=
  match expr with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var tv => if typevar_eq_dec v tv then t else vty_var tv
  | vty_cons ts typs =>
      vty_cons ts (map (ty_subst_single v t) typs)
  end.

(*Substitute a list of typevars*)
Definition ty_subst (vs: list typevar) (ts: list vty) (expr: vty) : vty :=
  fold_right (fun x acc => ty_subst_single (fst x) (snd x) acc) expr (combine vs ts).

Definition ty_subst_list (vs: list typevar) (ts: list vty) (exprs: list vty) : list vty :=
  map (ty_subst vs ts) exprs.

(* Sorts *)

(*Get the type variables in a type, with no duplicates*)
Fixpoint type_vars (t: vty) : list typevar :=
  match t with
  | vty_int => nil
  | vty_real => nil
  | vty_var v => [v]
  | vty_cons sym ts => big_union typevar_eq_dec type_vars ts
  end.

Lemma type_vars_unique: forall t,
  NoDup (type_vars t).
Proof.
  destruct t; simpl; try solve[constructor].
  - constructor; auto. constructor.
  - apply big_union_nodup.
Qed.  
  
Definition is_sort (t: vty) : bool :=
  match (type_vars t) with
  | nil => true
  | _ => false
  end.

Definition sort : Type := {t: vty | is_sort t}.

Coercion sort_to_ty (s: sort) : vty := @proj1_sig _ _ s.

Definition sorts_to_tys (l: list sort) : list vty :=
  map sort_to_ty l.

Lemma sort_inj: forall (s1 s2: sort),
  sort_to_ty s1 = sort_to_ty s2 ->
  s1 = s2.
Proof.
  intros s1 s2; destruct s1; destruct s2; simpl; intros Heq; subst.
  assert (i = i0) by apply bool_irrelevance.
  subst; reflexivity.
Qed.

Lemma int_is_sort: is_sort vty_int.
Proof.
  unfold is_sort; simpl. auto.
Qed.

Definition s_int : sort := exist _ vty_int int_is_sort.

Lemma real_is_sort: is_sort vty_real.
Proof.
  unfold is_sort; simpl. auto.
Qed.

Definition s_real : sort := exist _ vty_real real_is_sort.

Lemma sort_type_vars: forall (s: sort),
  type_vars s = nil.
Proof.
  intros s. destruct s; simpl. unfold is_sort in i.
  destruct (type_vars x); auto. inversion i.
Qed. 

(*We want to know that when we substitute in sorts for type variables,
  the result is a sort *)

Lemma ty_subst_single_sort: forall (v: typevar) (s: sort) (expr: vty),
  type_vars (ty_subst_single v s expr) =
  remove typevar_eq_dec v (type_vars expr).
Proof.
  intros v s expr. induction expr; simpl; auto.
  - destruct (typevar_eq_dec v v0); simpl; auto.
    apply sort_type_vars.
  - induction vs; simpl; auto.
    inversion H; subst. rewrite H2, IHvs; auto.
    apply union_remove.
Qed.

(*Now, we lift this result to a list*)

Lemma ty_subst_remove_all: forall (vs: list typevar) (ss: list sort) (expr: vty),
  length vs = length ss ->
  type_vars (ty_subst vs (sorts_to_tys ss) expr) =
  remove_all typevar_eq_dec vs (type_vars expr).
Proof.
  intros vs ss expr. revert ss. induction vs; simpl; intros.
  symmetry in H. apply length_zero_iff_nil in H; subst; reflexivity.
  destruct ss as [|s ss]; inversion H; subst.
  simpl. unfold ty_subst in *; simpl.
  rewrite ty_subst_single_sort. f_equal. apply IHvs. assumption.
Qed.

(*Finally, we get the results we want*)

Lemma ty_subst_sort: forall (vs: list typevar) (ts: list sort) (expr: vty),
  length vs = length ts ->
  (sublist (type_vars expr) vs) ->
  is_sort (ty_subst vs (sorts_to_tys ts) expr).
Proof.
  intros vs ts expr Hlens Hsub. unfold is_sort.
  assert (Hvars: type_vars (ty_subst vs (sorts_to_tys ts) expr) = nil); [|rewrite Hvars; auto].
  rewrite ty_subst_remove_all; auto.
  apply remove_all_sublist; auto.
Qed.

(*A version that gives a sort*)
Definition ty_subst_s (vs: list typevar) (ts: list sort) (Hlen: length vs = length ts)
  (expr: vty) (Hsub: sublist (type_vars expr) vs) : sort :=
  exist _ (ty_subst vs (sorts_to_tys ts) expr) (ty_subst_sort vs ts expr Hlen Hsub).

(*Lift the result to lists - can't use map because of proofs *)
Definition ty_subst_list_s (vs: list typevar) (ts: list sort) (Hlen: length vs = length ts)
  (exprs: list vty) (Hsubs: forall x, In x exprs -> sublist (type_vars x) vs) : list sort.
Proof.
  induction exprs as [| e tl].
  - apply nil.
  - apply cons.
    + assert (sublist (type_vars e) vs). apply Hsubs. left. reflexivity.
      apply (ty_subst_s vs ts Hlen e H).
    + apply IHtl. intros x Hinx. apply Hsubs. right. apply Hinx.
Defined.