Require Export Coq.Strings.String.
Require Export Coq.ZArith.BinInt.
Require Export Coq.Arith.PeanoNat.
Require Export Lia.

Require Export Common.

(*Type variable (ex: a)*)
Definition typevar : Type := string. 

Definition typevar_eqb : typevar -> typevar -> bool :=
  String.eqb.

Definition typevar_eq_dec : forall (t1 t2: typevar),
  {t1 = t2} + {t1 <> t2} := string_dec.

(*Type symbol (ex: list a)*)
Record typesym : Type := mk_ts {
  ts_name : string;
  ts_args : list typevar;
  ts_args_uniq : nodupb typevar_eq_dec ts_args
  }.

Fixpoint list_eqb {A: Type} (eq: A -> A -> bool) (l1 l2: list A) : bool :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => eq x1 x2 && list_eqb eq t1 t2
  | nil, nil => true
  | _, _ => false
  end.

Lemma list_eqb_spec: forall {A: Type} (eq: A -> A -> bool)
  (Heq: forall (x y : A), reflect (x = y) (eq x y))
  (l1 l2: list A),
  reflect (l1 = l2) (list_eqb eq l1 l2).
Proof.
  intros. revert l2. induction l1; simpl; intros.
  - destruct l2; simpl. apply ReflectT. constructor.
    apply ReflectF. intro C; inversion C.
  - destruct l2; simpl. apply ReflectF. intro C; inversion C.
    specialize (Heq a a0). destruct Heq.
    2 : {
      apply ReflectF. intro C; inversion C; subst; contradiction.
    }
    subst; simpl. specialize (IHl1 l2). destruct IHl1; subst.
    apply ReflectT. auto. apply ReflectF. intro C; inversion C; subst; contradiction.
Qed.

Definition bool_eqb (b1 b2: bool) : bool :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

Lemma typesym_eq: forall (t1 t2: typesym),
  (ts_name t1) = (ts_name t2) ->
  (ts_args t1) = (ts_args t2) ->
  t1 = t2.
Proof.
  intros. destruct t1; destruct t2; simpl in *; subst. f_equal.
  apply bool_irrelevance.
Qed.

Definition typesym_eqb (t1 t2: typesym) :=
  String.eqb (ts_name t1) (ts_name t2) &&
  list_eqb typevar_eqb (ts_args t1) (ts_args t2).

Lemma typesym_eqb_spec: forall (t1 t2: typesym),
  reflect (t1 = t2) (typesym_eqb t1 t2).
Proof.
  intros t1 t2. unfold typesym_eqb.
  destruct (String.eqb_spec (ts_name t1) (ts_name t2)); simpl.
  - destruct (list_eqb_spec typevar_eqb String.eqb_spec (ts_args t1) (ts_args t2)); simpl.
    + apply ReflectT. apply typesym_eq; auto.
    + apply ReflectF. intros C. destruct t1; destruct t2; subst. inversion C; contradiction.
  - apply ReflectF. intro C; destruct t1; destruct t2; inversion C; subst; contradiction.
Qed.

Lemma reflect_true: forall {P} {b} (H: reflect P b),
  b = true ->
  P.
Proof.
  intros. destruct H; subst; auto. inversion H0.
Qed.

Lemma reflect_false: forall {P} {b} (H: reflect P b),
  b = false ->
  ~ P.
Proof.
  intros. destruct H; subst; auto. inversion H0.
Qed.

(*Now we can transform "reflect" into computable "dec" EVEN if "reflect" is opaque.
  This is what we are missing in the ssreflect library. We do NOT match on
  "reflect"; we match on the boolean predicate directly*)
Definition reflect_dec' {P} {b} (H: reflect P b): {P} + {~P} :=
  match b as b1 return b = b1 -> _ with
  | true => fun Heq => left (reflect_true H Heq)
  | false => fun Hneq => right (reflect_false H Hneq)
  end eq_refl.

Definition typesym_eq_dec (t1 t2: typesym) : {t1 = t2} + {t1 <> t2} :=
  reflect_dec' (typesym_eqb_spec t1 t2).

Definition ts_unit : typesym := mk_ts "unit" nil eq_refl.


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

Lemma vty_eq_spec: forall t1 t2,
  reflect (t1 = t2) (vty_eqb t1 t2).
Proof.
  intros. destruct (vty_eqb t1 t2) eqn : Heq.
  - apply ReflectT. apply vty_eqb_eq. auto.
  - apply ReflectF. intro C; apply vty_eq_eqb in C; rewrite Heq in C; inversion C.
Qed.

Definition vty_eq_dec (v1 v2: vty): {v1 = v2} + {v1 <> v2} :=
  reflect_dec' (vty_eq_spec v1 v2).

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
  null (type_vars t).

Definition sort : Type := {t: vty | is_sort t}.

Coercion sort_to_ty (s: sort) : vty := @proj1_sig _ _ s.

Definition sorts_to_tys (l: list sort) : list vty :=
  map sort_to_ty l.

Lemma sort_inj: forall {s1 s2: sort},
  sort_to_ty s1 = sort_to_ty s2 ->
  s1 = s2.
Proof.
  intros s1 s2; destruct s1; destruct s2; simpl; intros Heq; subst.
  assert (i = i0) by apply bool_irrelevance.
  subst; reflexivity.
Qed.

Lemma sort_eq_dec: forall (s1 s2: sort),
  {s1 = s2} + {s1 <> s2}.
Proof.
  intros. destruct (vty_eq_dec (sort_to_ty s1) (sort_to_ty s2)).
  - left. apply sort_inj. auto.
  - right. intro C; subst; contradiction.
Defined.

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

Definition typesym_to_sort_proof: forall (t: typesym) (s: list sort),
  null (type_vars (vty_cons t (map sort_to_ty s))).
Proof.
  intros. assert (type_vars (vty_cons t (map sort_to_ty s)) = nil).
  2: { rewrite H; auto. } simpl. apply big_union_nil_eq. intros x Hinx.
  rewrite in_map_iff in Hinx. destruct Hinx as [y [Hy Hiny]]; subst.
  destruct y; simpl in *. unfold is_sort in i. clear Hiny.
  destruct (type_vars x); auto. inversion i.
Qed.

Definition typesym_to_sort (t: typesym) (s: list sort)  : sort :=
  exist _ (vty_cons t (map sort_to_ty s)) (typesym_to_sort_proof t s).


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
  exist _ (v_subst_aux v t) (v_subst_aux_sort v t).

Fixpoint ty_subst_fun (vs: list typevar) (s: list vty) (d: vty) : typevar -> vty :=
  fun v => match vs, s with
            | v1 :: tl1, ty :: tl2 => if typevar_eq_dec v v1 then ty else
              ty_subst_fun tl1 tl2 d v
            | _, _ => d
            end.

Lemma ty_subst_fun_sort: forall vs (s: list sort) (d: sort) (t: typevar),
  is_sort (ty_subst_fun vs (sorts_to_tys s) d t).
Proof.
  intros. revert s. induction vs; simpl; intros; auto. destruct d; auto.
  destruct s; simpl. destruct d; auto.
  destruct (typevar_eq_dec t a); subst. destruct s; auto. apply IHvs.
Qed.

Definition ty_subst_fun_s (vs: list typevar) (s: list sort) (d: sort) : typevar -> sort :=
  fun t => exist _ (ty_subst_fun vs (sorts_to_tys s) d t) (ty_subst_fun_sort vs s d t).

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


(*Type variables of a list of types*)

(*Suppose that all type variables in a type are included in a list. Then,
  suppose we substitute vs for these variables. Then, the type variables of
  the resulting type are simply the type variables present in vs*)

(*Suppose that all *)