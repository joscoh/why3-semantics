Require Export Coq.Strings.String.
Require Export Coq.ZArith.BinInt.
Require Export Coq.Arith.PeanoNat.
Require Export Lia.

Require Export Common.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*Type variable (ex: a)*)
Definition typevar : Set := string.
Canonical typevar_eqType := EqType typevar string_eqMixin. 

(*Type symbol (ex: list a)*)
Record typesym : Type := mk_ts {
  ts_name : string;
  ts_args : list typevar;
  ts_args_uniq : uniq ts_args
  }.

Lemma typesym_eq: forall (t1 t2: typesym),
  (ts_name t1) = (ts_name t2) ->
  (ts_args t1) = (ts_args t2) ->
  t1 = t2.
Proof.
  intros. destruct t1; destruct t2; simpl in *; subst. f_equal.
  apply bool_irrelevance.
Qed.

Definition typesym_eqb (t1 t2: typesym) :=
  ((ts_name t1) == (ts_name t2)) &&
  ((ts_args t1) == (ts_args t2)).

Lemma typesym_eqb_axiom: Equality.axiom typesym_eqb.
Proof.
  move=>t1 t2; rewrite /typesym_eqb.
  case: (ts_name t1 == ts_name t2) /eqP => /= Hn; last by
    apply ReflectF => Ht12; move : Hn; rewrite Ht12.
  case: (ts_args t1 == ts_args t2) /eqP => /= Ha; last by
    apply ReflectF => Ht12; move: Ha; rewrite Ht12.
  by apply ReflectT, typesym_eq.
Qed.

Definition typesym_eqMixin := EqMixin typesym_eqb_axiom.
Canonical typesym_eqType := EqType typesym typesym_eqMixin.

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
  | vty_var t1, vty_var t2 => t1 == t2
  | vty_cons ts1 vs1, vty_cons ts2 vs2 =>
    (ts1 == ts2) &&
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
  end.
  - by move: H => /eqP ->.
  - move: H0 => /andP[/eqP Ht IH]; subst.
    f_equal. generalize dependent l. induction vs; simpl;
    auto; intros; destruct l; auto; try solve[inversion IH].
    inversion H; subst.
    move: IH => /andP[Hav Hvsl].
    apply H2 in Hav; subst. f_equal.
    apply IHvs; auto.
Qed.

Lemma vty_eq_eqb: forall t1 t2,
  t1 = t2 ->
  vty_eqb t1 t2.
Proof.
  intros t1. induction t1; simpl; auto; intros; destruct t2; auto; try solve[inversion H];
  try solve[inversion H0].
  - inversion H; subst. by rewrite eq_refl.
  - inversion H0; subst. rewrite eq_refl /=.
    clear H0. induction l; simpl; auto.
    inversion H; subst. rewrite H2 //=. by apply IHl.
Qed. 

Lemma vty_eqb_axiom: Equality.axiom vty_eqb.
Proof.
  move=>t1 t2. case Heq: (vty_eqb t1 t2).
  - by apply ReflectT, vty_eqb_eq.
  - apply ReflectF => Ht12. apply vty_eq_eqb in Ht12.
    by rewrite Heq in Ht12.
Qed.

Definition vty_eqMixin := EqMixin vty_eqb_axiom.
Canonical vty_eqType := EqType vty vty_eqMixin.

(* Sorts *)

(*Get the type variables in a type, with no duplicates*)
Fixpoint type_vars (t: vty) : list typevar :=
  match t with
  | vty_int => nil
  | vty_real => nil
  | vty_var v => [v]
  | vty_cons sym ts => big_union type_vars ts
  end.
  
Definition is_sort (t: vty) : bool :=
  null (type_vars t).

(*Defining it this way gets us eqType for free*)
Inductive sort : predArgType := Sort (srt: vty) of (is_sort srt).
Coercion sort_to_ty (s: sort) : vty := let: Sort x _ :=s in x.

Canonical sort_subType := [subType for sort_to_ty].
Definition sort_eqMixin := Eval hnf in [eqMixin of sort by <:].
Canonical sort_eqType := Eval hnf in EqType sort sort_eqMixin.

Definition sorts_to_tys (l: list sort) : list vty :=
  map sort_to_ty l.

Lemma sort_inj: forall {s1 s2: sort},
  sort_to_ty s1 = sort_to_ty s2 ->
  s1 = s2.
Proof. apply val_inj. Qed.

Lemma int_is_sort: is_sort vty_int.
Proof.
  unfold is_sort; simpl. auto.
Qed.

Definition s_int : sort := Sort vty_int int_is_sort.

Lemma real_is_sort: is_sort vty_real.
Proof.
  unfold is_sort; simpl. auto.
Qed.

Definition s_real : sort := Sort vty_real real_is_sort. 

Lemma sort_type_vars: forall (s: sort),
  type_vars s = nil.
Proof.
  intros s. destruct s; simpl. unfold is_sort in i.
  destruct (type_vars srt); auto. inversion i.
Qed.

Definition typesym_to_sort_proof: forall (t: typesym) (s: list sort),
  null (type_vars (vty_cons t (map sort_to_ty s))).
Proof.
  intros. assert (type_vars (vty_cons t (map sort_to_ty s)) = nil).
  2: { rewrite H; auto. } simpl. apply big_union_nil_eq. intros x Hinx.
  rewrite in_map_iff in Hinx. destruct Hinx as [y [Hy Hiny]]; subst.
  destruct y; simpl in *. unfold is_sort in i. clear Hiny.
  destruct (type_vars srt); auto. inversion i.
Qed.

Definition typesym_to_sort (t: typesym) (s: list sort)  : sort :=
  Sort _ (typesym_to_sort_proof t s).


(* Type substitution *)

(*Substitute according to function*)
Fixpoint v_subst_aux (v: typevar -> vty) (t: vty) : vty :=
  match t with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var tv => v tv
  | vty_cons ts vs => vty_cons ts (map (v_subst_aux v) vs)
  end.

Lemma v_subst_aux_sort: forall (v: typevar -> sort) t,
  is_sort (v_subst_aux v t).
Proof.
  intros v t. unfold is_sort.
  assert (H: type_vars (v_subst_aux v t) = nil); [|rewrite H; auto].
  induction t; simpl; intros; auto.
  apply sort_type_vars.
  induction vs; simpl; intros; auto.
  inversion H; subst.
  rewrite H2. auto.
Qed. 

Definition v_subst (v: typevar -> sort) (t: vty) : sort :=
  Sort _ (v_subst_aux_sort v t).

Fixpoint ty_subst_fun (vs: list typevar) (s: list vty) (d: vty) : typevar -> vty :=
  fun v => match vs, s with
            | v1 :: tl1, ty :: tl2 => if String.eqb v v1 then ty else
              ty_subst_fun tl1 tl2 d v
            | _, _ => d
            end.

Lemma ty_subst_fun_sort: forall vs (s: list sort) (d: sort) (t: typevar),
  is_sort (ty_subst_fun vs (sorts_to_tys s) d t).
Proof.
  intros. revert s. induction vs; simpl; intros; auto. destruct d; auto.
  destruct s; simpl. destruct d; auto.
  case: (String.eqb_spec t a) => Heq; subst.
  destruct s; auto. apply IHvs.
Qed.

Definition ty_subst_fun_s (vs: list typevar) (s: list sort) (d: sort) : typevar -> sort :=
  fun t => Sort _ (ty_subst_fun_sort vs s d t).

Definition ty_subst (vs: list typevar) (ts: list vty) (expr: vty) : vty :=
  v_subst_aux (ty_subst_fun vs ts vty_int) expr.

Definition ty_subst_list (vs: list typevar) (ts: list vty) (exprs: list vty) : list vty :=
  map (ty_subst vs ts) exprs.

Definition ty_subst_s (vs: list typevar) (ts: list sort) (expr: vty) : sort :=
  v_subst (ty_subst_fun_s vs ts s_int) expr.

Definition ty_subst_list_s (vs: list typevar) (ts: list sort) (exprs: list vty) : list sort :=
  map (ty_subst_s vs ts) exprs.

Lemma type_vars_cons: forall ts (vs: list vty),
  type_vars (vty_cons ts vs) = nil ->
  (forall x, In x vs -> type_vars x = nil).
Proof.
  intros. apply big_union_nil with(x:=x) in H; auto.
Qed. 
