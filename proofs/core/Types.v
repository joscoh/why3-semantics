Require Export Coq.Strings.String.
Require Export Coq.ZArith.BinInt.
Require Export Coq.Arith.PeanoNat.
Require Export Lia.

Require Export Common.

From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*Now we can transform "reflect" into computable "dec" EVEN if "reflect" is opaque.
  This is what we are missing in the ssreflect library. We do NOT match on
  "reflect"; we match on the boolean predicate directly*)
Definition reflect_dec' {P} {b} (H: reflect P b): {P} + {~P} :=
  match b as b1 return b = b1 -> _ with
  | true => fun Heq => left (elimT H Heq)
  | false => fun Hneq => right (elimF H Hneq)
  end erefl.

(*Type variable (ex: a)*)
Definition typevar : Set := string. 

(*
Definition typevar_eqb : typevar -> typevar -> bool :=
  String.eqb.

Lemma typevar_eqb_spec (t1 t2: typevar) : reflect (t1 = t2) (typevar_eqb t1 t2).
Proof.
  apply String.eqb_spec.
Qed.*)

Definition string_eqMixin := EqMixin String.eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.
(*Definition typevar_eqMixin := EqMixin typevar_eqb_spec.*)
Canonical typevar_eqType := EqType typevar string_eqMixin.

Definition typevar_eq_dec (t1 t2: typevar):
  {t1 = t2} + {t1 <> t2} := reflect_dec' (String.eqb_spec t1 t2).

(*Type symbol (ex: list a)*)
Record typesym : Set := mk_ts {
  ts_name : string;
  ts_args : list typevar;
  (*ts_args_uniq : nodupb typevar_eq_dec ts_args*)
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
  (*apply bool_irrelevance.*)
Qed.

(*Definition is_true_eqb {b1 b2: bool} (p1: is_true b1) (p2: is_true b2) : bool :=
  Bool.eqb b1 b2.*)
(*
Definition typesym_eqb (t1 t2: typesym) :=
  String.eqb (ts_name t1) (ts_name t2) &&
  list_eqb typevar_eqb (ts_args t1) (ts_args t2) &&
  (*This is not needed (we show that below), but it is
    very useful for the "rewrite" lemmas in IndTypes*)
  is_true_eqb (ts_args_uniq t1) (ts_args_uniq t2).*)

Definition typesym_eqb (t1 t2: typesym) :=
  ((ts_name t1) == (ts_name t2)) &&
  ((ts_args t1) == (ts_args t2)).

Lemma typesym_eqb_spec: forall (t1 t2: typesym),
  reflect (t1 = t2) (typesym_eqb t1 t2).
Proof.
  move=>[n1 a1] [n2 a2]; rewrite /typesym_eqb/=.
  case: (n1 == n2) /eqP => Hn/=; last by
    apply ReflectF => [[C]].
  case: (a1 == a2) /eqP => Ha/=; last by
    apply ReflectF => [[C]].
  apply ReflectT. by rewrite Hn Ha.
Qed.

Definition typesym_eqMixin := EqMixin typesym_eqb_spec.
Canonical typesym_eqType := EqType typesym typesym_eqMixin.



(*
Definition typesym_eqb (t1 t2: typesym) :=
  String.eqb (ts_name t1) (ts_name t2) &&
  list_eqb typevar_eqb (ts_args t1) (ts_args t2).
(*
Lemma typesym_eqb_equiv: forall t1 t2,
  typesym_eqb t1 t2 = typesym_eqb' t1 t2.
Proof.
  intros. unfold typesym_eqb, typesym_eqb'.
  destruct (String.eqb_spec (ts_name t1) (ts_name t2)); simpl; auto.
  destruct (list_eqb_spec _ typevar_eqb_spec (ts_args t1) (ts_args t2)); simpl; auto.
  unfold is_true_eqb.
  rewrite e0. apply eqb_reflx.
Qed.*)

Lemma typesym_eqb_spec: forall (t1 t2: typesym),
  reflect (t1 = t2) (typesym_eqb t1 t2).
Proof.
  intros t1 t2. unfold typesym_eqb.
  destruct (String.eqb_spec (ts_name t1) (ts_name t2)); simpl.
  - destruct (list_eqb_spec typevar_eqb String.eqb_spec (ts_args t1) (ts_args t2)); simpl.
    + apply ReflectT. apply typesym_eq; auto.
    + apply ReflectF. intros C. destruct t1; destruct t2; subst. inversion C; contradiction.
  - apply ReflectF. intro C; destruct t1; destruct t2; inversion C; subst; contradiction.
Qed.*)

Definition typesym_eq_dec (t1 t2: typesym) : {t1 = t2} + {t1 <> t2} :=
  reflect_dec' (typesym_eqb_spec t1 t2).

Definition ts_unit : typesym := mk_ts "unit" nil (*eq_refl*).


(*Value types*)
Unset Elimination Schemes.
Inductive vty : Set :=
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

(*Need a version for Type too*)

Inductive ForallT {A: Type} (P: A -> Type) : list A -> Type :=
  | ForallT_nil: ForallT P nil
  | ForallT_cons: forall {x: A} {l: list A},
    P x -> ForallT P l -> ForallT P (x :: l).

Lemma ForallT_hd {A: Type} (P: A -> Type) (x: A) (l: list A):
  ForallT P (x :: l) ->
  P x.
Proof.
  intros. inversion X; subst. apply X0.
Qed.

Lemma ForallT_tl {A: Type} (P: A -> Type) (x: A) (l: list A):
  ForallT P (x :: l) ->
  ForallT P l.
Proof.
  intros. inversion X; auto.
Qed.

Section TyIndType.

Variable P : vty -> Type.
Variable Hint: P vty_int.
Variable Hreal: P vty_real.
Variable Hvar: forall v, P (vty_var v).
Variable Hcons: forall tsym vs,
  ForallT P vs -> P (vty_cons tsym vs).

Fixpoint vty_rect (t: vty) : P t :=
  match t with
  | vty_int => Hint
  | vty_real => Hreal
  | vty_var t => Hvar t
  | vty_cons tsym vs => Hcons tsym vs
    ((fix vty_ind_list (l: list vty) : ForallT P l :=
      match l with
      | nil => ForallT_nil _
      | x :: t => ForallT_cons _ (vty_rect x) (vty_ind_list t)
      end) vs)
  end.

  End TyIndType.


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
  move=> t1; elim: t1 =>/=[t2 | t2 | v t2 | ts vs Hall t2];
  case: t2 =>//.
  - by move=> v2 => /eqP ->.
  - move=> ts2 vs2 => /andP[/eqP Hts Hlist].
    subst. f_equal. rewrite {ts2}.
    move: vs2 Hall Hlist. elim: vs => 
      [// [// | h2 t2 //] | h t /= IH [// | h2 t2 /=] Hall /andP[Hh Ht]].
    have->//: h = h2 by apply (Forall_inv Hall).
    f_equal. apply IH=>//. by apply (Forall_inv_tail Hall).
Qed.

Lemma vty_eq_eqb: forall t1 t2,
  t1 = t2 ->
  vty_eqb t1 t2.
Proof.
  move=> t1; elim: t1 =>/=[t2 | t2 | v t2 | ts vs Hall t2];
  case: t2 => //.
  - by move=> v2 [] /eqP.
  - move=> ts1 vs1 [] Hts Hvs; subst. rewrite eq_refl/=.
    rewrite {ts1}. move: Hall. elim: vs1 => [// | h t /= IH Hall].
    apply /andP; split.
    + by apply (Forall_inv Hall).
    + by apply IH, (Forall_inv_tail Hall).
Qed.

Lemma vty_eq_spec: forall t1 t2,
  reflect (t1 = t2) (vty_eqb t1 t2).
Proof.
  move=>t1 t2. case Heq: (vty_eqb t1 t2); constructor.
  - by apply vty_eqb_eq.
  - move=> C. have: vty_eqb t1 t2 by apply (vty_eq_eqb _ _ C).
    by rewrite Heq.
Qed.

Definition vty_eqMixin := EqMixin vty_eq_spec.
Canonical vty_eqType := EqType vty vty_eqMixin.

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

Definition sort : Set := {t: vty | is_sort t}.

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

Definition sort_eqb_spec: forall (s1 s2: sort),
  reflect (s1 = s2) ((sort_to_ty s1) == (sort_to_ty s2)).
Proof.
  move=> s1 s2. case: ((sort_to_ty s1) == (sort_to_ty s2)) /eqP => Hsort;
  constructor.
  - by apply sort_inj.
  - by move=> C; subst.
Qed.

Definition sort_eqMixin := EqMixin sort_eqb_spec.
Canonical sort_eqType := EqType sort sort_eqMixin.

Definition sort_eq_dec (s1 s2: sort) :
  {s1 = s2} + {s1 <> s2} :=
  reflect_dec _ _ (sort_eqb_spec s1 s2).
(*
Proof.
  intros. destruct (vty_eq_dec (sort_to_ty s1) (sort_to_ty s2)).
  - left. apply sort_inj. auto.
  - right. intro C; subst; contradiction.
Defined.*)

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

(*Lemmas about substitution*)
Lemma ty_subst_s_cons: forall (vs: list typevar) (ts: list Types.sort)
  (t: typesym) (args: list vty),
  ty_subst_s vs ts (vty_cons t args) = typesym_to_sort t (ty_subst_list_s vs ts args).
Proof.
  intros. unfold ty_subst_list_s, ty_subst_s, v_subst. simpl. apply sort_inj; simpl.
  f_equal.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn. rewrite -> !(map_nth_inbound) with (d2:=d) by auto.
  rewrite -> (map_nth_inbound) with (d2:=s_int) by (rewrite map_length; auto).
  rewrite -> (map_nth_inbound) with (d2:=d) by auto.
  reflexivity.
Qed.

Lemma ty_subst_fun_nth: forall (vars: list typevar) (vs: list vty)
  (d: vty) (n: nat) (a: typevar) (s: vty),
  length vars = length vs ->
  (n < length vars)%coq_nat ->
  NoDup vars ->
  ty_subst_fun vars vs d (List.nth n vars a) = List.nth n vs s.
Proof.
intros vars vs d n a s'. revert n. revert vs. induction vars.
- simpl; intros; lia.
- intros; destruct vs.
  + inversion H.
  + destruct n.
    * simpl. destruct (typevar_eq_dec a0 a0); auto. contradiction.
    * simpl.
      inversion H1; subst. simpl in H0.
      destruct (typevar_eq_dec (List.nth n vars a) a0); subst; auto.
      -- exfalso. apply H4. apply nth_In. lia.
      -- apply IHvars; try lia. inversion H; auto. assumption.
Qed.

Lemma ty_subst_fun_in_sort (vars: list typevar) (srts: list sort)
  (d: vty) x:
  length srts = length vars ->
  In x vars ->
  is_sort (ty_subst_fun vars (sorts_to_tys srts) d x).
Proof.
  intros. generalize dependent srts. 
  induction vars; simpl; intros. inversion H0.
  simpl in H0. destruct srts; simpl in *.
  - inversion H.
  - destruct (typevar_eq_dec x a); subst; simpl.
    + destruct s; auto.
    + destruct H0; subst; try contradiction.
      apply IHvars; auto.
Qed. 

Lemma ty_subst_fun_notin: forall params args d (x: typevar),
  ~In x params ->
  ty_subst_fun params args d x = d.
Proof.
  intros. revert args. induction params; simpl; intros; auto.
  destruct args; auto. destruct (typevar_eq_dec x a); auto; subst.
  exfalso. apply H. left; auto. apply IHparams. intro C. apply H. right; auto.
Qed.

Lemma ty_subst_fun_in: forall params args d (x: typevar),
  NoDup params ->
  In x params ->
  length params = length args ->
  exists ty, In (x, ty) (combine params args) /\ ty_subst_fun params args d x = ty.
Proof.
  intros. generalize dependent args. induction params; simpl; intros; auto.
  inversion H0.
  inversion H; subst. destruct args. inversion H1.
  simpl in H0. destruct H0; subst.
  - exists v. split. left; auto. destruct (typevar_eq_dec x x); auto. contradiction.
  - inversion H1. specialize (IHparams H5 H0 args H3). destruct IHparams as [ty [Hin Hty]].
    exists ty. split. right; auto. destruct (typevar_eq_dec x a); auto.
    subst. contradiction.
Qed. 

Lemma subst_same: forall (vars: list typevar) (srts: list Types.sort),
  length vars = length srts ->
  NoDup vars ->
  map (fun x => ty_subst_s vars srts (vty_var x)) vars = srts.
Proof.
  intros. apply list_eq_ext'; rewrite map_length; auto. intros n d Hd.
  assert (a: typevar). apply "A"%string.
  rewrite -> (map_nth_inbound) with (d2:=a); auto.
  unfold ty_subst_s. apply sort_inj; simpl.
  rewrite -> ty_subst_fun_nth with(s:=vty_int); try lia; unfold sorts_to_tys.
  rewrite -> (map_nth_inbound) with (d2:=d). reflexivity. lia.
  rewrite map_length; lia.
  assumption.
Qed.

Lemma is_sort_cons_iff: forall (ts: typesym) (l: list vty),
  is_sort (vty_cons ts l) <->
  forall x, In x l -> is_sort x.
Proof.
  intros. split; intros.
  - unfold is_sort in *. simpl in H.
    rewrite -> null_nil in *.
    eapply big_union_nil in H. apply H. assumption.
  - unfold is_sort in *. simpl. rewrite -> null_nil in *.
    apply big_union_nil_eq. intros.
    rewrite <- null_nil. apply H. auto.
Qed.

Lemma is_sort_cons: forall (ts: typesym) (l: list vty),
  is_sort (vty_cons ts l) ->
  forall x, In x l -> is_sort x.
Proof.
  intros ts l. apply is_sort_cons_iff.
Qed.

(* If we have a sort, then substituting a valuation does nothing *)
Lemma subst_is_sort_eq (t: vty) (Ht: is_sort t) (v: typevar -> vty):
  t = v_subst_aux v t.
Proof.
  induction t; simpl in *; auto. inversion Ht.
  f_equal. apply list_eq_ext'; [rewrite map_length|]; auto; intros.
  rewrite -> map_nth_inbound with (d2:=d); auto.
  rewrite Forall_nth in H. apply H; auto.
  apply (is_sort_cons _ _ Ht). apply nth_In; auto.
Qed. 

Lemma subst_sort_eq: forall (s: sort) (v: typevar -> sort),
  s = v_subst v (sort_to_ty s).
Proof.
  intros. unfold v_subst. destruct s. apply sort_inj. simpl.
  apply subst_is_sort_eq; auto.
Qed.

Lemma v_subst_aux_ext (v1 v2: typevar -> vty) ty:
  (forall x, In x (type_vars ty) -> v1 x = v2 x ) ->
  v_subst_aux v1 ty = v_subst_aux v2 ty.
Proof.
  intros. induction ty; simpl; auto.
  rewrite H; simpl; auto.
  f_equal. simpl in H. induction vs; simpl in *; auto.
  inversion H0; subst.
  f_equal.
  - apply H3. intros; apply H. simpl_set; triv.
  - apply IHvs; auto. intros. apply H; simpl_set; auto.
Qed.


Lemma v_subst_ext (v1 v2: typevar -> sort) ty:
  (forall x, In x (type_vars ty) -> v1 x = v2 x) ->
  v_subst v1 ty = v_subst v2 ty.
Proof.
  intros. apply sort_inj, v_subst_aux_ext.
  intros. apply H in H0. apply (f_equal sort_to_ty) in H0.
  auto.
Qed.

Lemma v_ty_subst_eq_aux (params: list typevar) (srts: list sort)
  (v: typevar -> sort) ty
  (Hnodup: NoDup params)
  (Hlen: length srts = length params):
  (forall i, (i < length params)%coq_nat -> 
    v (List.nth i params EmptyString) = List.nth i srts s_int) ->
  (forall x, In x (type_vars ty) -> In x params) ->
  v_subst_aux v ty = ty_subst params (sorts_to_tys srts) ty.
Proof.
  intros.
  unfold ty_subst.
  apply v_subst_aux_ext.
  intros.
  apply H0 in H1.
  destruct (In_nth _ _ EmptyString H1) as [i [Hi Hx]]; subst.
  rewrite H; auto.
  rewrite (ty_subst_fun_nth _ _ _ _ _ s_int); auto.
  - unfold sorts_to_tys.
    rewrite -> map_nth_inbound with(d2:=s_int); auto.
    rewrite Hlen; auto.
  - unfold sorts_to_tys. rewrite map_length. auto.
Qed.

(*Suppose we have a list of params and a list of srts such that
  for all i, v(nth i params) = nth i srts. Suppose that all
  type variables in ty are in params.
  Then v_subst v ty = ty_subst_list params srts ty*)
Lemma v_ty_subst_eq (params: list typevar) (srts: list sort)
  (v: typevar -> sort) ty
  (Hnodup: NoDup params)
  (Hlen: length srts = length params):
  (forall i, (i < length params)%coq_nat -> 
    v (List.nth i params EmptyString) = List.nth i srts s_int) ->
  (forall x, In x (type_vars ty) -> In x params) ->
  v_subst v ty = ty_subst_s params srts ty.
Proof.
  intros.
  apply sort_inj; simpl.
  apply v_ty_subst_eq_aux; auto.
Qed.