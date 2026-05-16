Require Export Stdlib.Strings.String.
Require Export Stdlib.ZArith.BinInt.
Require Export Stdlib.Arith.PeanoNat.
From Stdlib Require Export Lia.


Require Export Common.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".
Require countable strings.

(*Type variable (ex: a)*)
Definition typevar : Set := string. 

(*TODO: figure this out from Zulip*)

(*Need this to remove "redundant-canonical-projections" warning
  that still cannot recognize (in Typechecker) *)
Definition typevar_eqb (x y: typevar) : bool := String.eqb x y.

Definition typevar_eqb_spec (x y: typevar) : reflect (x = y) (typevar_eqb x y) :=
  String.eqb_spec x y.

HB.instance Definition _ := hasDecEq.Build string String.eqb_spec.
HB.instance Definition _ := hasDecEq.Build typevar typevar_eqb_spec.

Definition typevar_eq_dec (t1 t2: typevar):
  {t1 = t2} + {t1 <> t2} := reflect_dec' (String.eqb_spec t1 t2).

(*Type symbol (ex: list a)*)
Record typesym : Set := mk_ts {
  ts_name : string;
  ts_args : list typevar;
  }.



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
Qed.

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

HB.instance Definition _ := hasDecEq.Build typesym typesym_eqb_spec.

Definition typesym_eq_dec (t1 t2: typesym) : {t1 = t2} + {t1 <> t2} :=
  reflect_dec' (typesym_eqb_spec t1 t2).

(*Countable*)

Definition typesym_to_tup (ts: typesym) : string * (list typevar) := (ts_name ts, ts_args ts).
Definition typesym_of_tup (x: string * list typevar) : typesym := mk_ts (fst x) (snd x).
Lemma typesym_to_tup_inj: forall x, typesym_of_tup (typesym_to_tup x) = x.
Proof.
  intros [x1 x2]; simpl. reflexivity.
Qed. 

Instance typesym_EqDecision : @base.RelDecision typesym typesym eq.
Proof. unfold base.RelDecision. apply typesym_eq_dec. Defined.

Instance typesym_countable : countable.Countable typesym :=
  countable.inj_countable' typesym_to_tup typesym_of_tup typesym_to_tup_inj.

Definition ts_unit : typesym := mk_ts "unit" nil.

(*A default typesym*)
Definition ts_d : typesym := ts_unit.


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
  | vty_cons tsym vs => Hcons tsym vs (mk_Forall vty_ind vs)
  end.

End TyInd.

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

HB.instance Definition _ := hasDecEq.Build vty vty_eq_spec.

Definition vty_eq_dec (v1 v2: vty): {v1 = v2} + {v1 <> v2} :=
  reflect_dec' (vty_eq_spec v1 v2).

(*Countable*)

Instance vty_EqDecision : @base.RelDecision vty vty eq.
Proof. unfold base.RelDecision. apply vty_eq_dec. Defined.

(*Idea: map to [gen_tree]*)

(*Silly to write it this way but easier for Countable*)
Definition vty_nonind := (((unit + unit)%type + typevar) + typesym)%type.

Fixpoint vty_to_gen_tree (v: vty) : countable.gen_tree vty_nonind :=
  match v with
  | vty_int => countable.GenLeaf (inl (inl (inl tt)))
  | vty_real => countable.GenLeaf (inl (inl (inr tt)))
  | vty_var v => countable.GenLeaf (inl (inr v))
  | vty_cons ts tys => countable.GenNode 0 (countable.GenLeaf (inr ts) :: (map vty_to_gen_tree tys))
  end.

Definition fold_list_option {A: Type} (l: list (option A)) : option (list A) :=
  fold_right (fun x acc => CommonOption.option_bind x (fun h => CommonOption.option_bind acc (fun t => Some (h :: t)))) (Some nil) l.

Fixpoint gen_tree_to_vty (g: countable.gen_tree vty_nonind) : option vty :=
  match g with
  | countable.GenLeaf (inl (inl (inl _))) => Some vty_int
  | countable.GenLeaf (inl (inl (inr _))) => Some vty_real
  | countable.GenLeaf (inl (inr v)) => Some (vty_var v)
  | countable.GenNode 0 (countable.GenLeaf (inr ts) :: xs) => 
    CommonOption.option_bind (fold_list_option (map gen_tree_to_vty xs)) (fun l => Some (vty_cons ts l))
  | _ => None
  end.

(*Prove the partial injection*)
Lemma vty_to_gen_tree_inj: forall x,
  gen_tree_to_vty (vty_to_gen_tree x) = Some x.
Proof.
  intros ty. induction ty; simpl; auto.
  assert (Hvs: (fold_list_option [seq gen_tree_to_vty i | i <- [seq vty_to_gen_tree i | i <- vs]]) = (Some vs)).
  { induction vs as [| h t IH]; simpl; auto. inversion H as [| ? ? Heq Ht]; subst; auto.
    rewrite Heq. simpl. rewrite IH; auto.
  }
  rewrite Hvs. simpl. reflexivity.
Qed.

(*And thus, a countable instance (the sum allows the [vty_nonind] instance to be inferred*)
Instance vty_countable : countable.Countable vty :=
  countable.inj_countable vty_to_gen_tree gen_tree_to_vty vty_to_gen_tree_inj.

Instance vty_inhab : base.Inhabited vty.
Proof.
  exact (base.populate vty_int).
Defined.

(* Sorts *)

Unset Elimination Schemes.
Inductive sort :=
  | s_int : sort
  | s_real : sort
  | s_cons: typesym -> list sort -> sort.
Set Elimination Schemes.

Fixpoint sort_ind (P: sort -> Prop) (P_int: P s_int) (P_real: P s_real) 
  (P_cons: forall (ts: typesym) (srts: list sort) (IH: Forall P srts), P (s_cons ts srts))
  (s: sort) : P s :=
  match s with
  | s_int => P_int
  | s_real => P_real
  | s_cons ts srts => P_cons ts srts (mk_Forall (sort_ind P P_int P_real P_cons) srts)
  end.

Fixpoint sort_rect (P: sort -> Type) (P_int: P s_int) (P_real: P s_real) 
  (P_cons: forall (ts: typesym) (srts: list sort) (IH: ForallT P srts), P (s_cons ts srts))
  (s: sort) : P s :=
  match s with
  | s_int => P_int
  | s_real => P_real
  | s_cons ts srts => P_cons ts srts (mk_ForallT (sort_rect P P_int P_real P_cons) srts)
  end.

(*Decidable equality*)
Fixpoint sort_eqb (s1 s2: sort) : bool :=
  match s1, s2 with
  | s_int, s_int => true
  | s_real, s_real => true
  | s_cons ts1 srts1, s_cons ts2 srts2 => typesym_eqb ts1 ts2 && list_eqb sort_eqb srts1 srts2
  | _, _ => false
  end.

Lemma sort_eqb_spec s1 s2: reflect (s1 = s2) (sort_eqb s1 s2).
Proof.
  revert s2. induction s1 as [| | ts1 srts1 IH] using sort_rect;
  intros [| | ts2 srts2]; simpl;
  try solve[apply ReflectT; reflexivity];
  try solve[apply ReflectF; intro C; discriminate].
  assert (Hiff: ts1 = ts2 /\ srts1 = srts2 <-> s_cons ts1 srts1 = s_cons ts2 srts2). {
    split.
    - intros [? ?]; subst; auto.
    - intros H; inversion H; subst; auto.
  }
  eapply equivP; [| apply Hiff].
  apply andPP; [apply typesym_eqb_spec|]. clear Hiff.
  revert srts2. induction srts1 as [| s1 t1 IHs]; intros [| s2 t2]; simpl;
  try solve[apply ReflectT; reflexivity];
  try solve[apply ReflectF; intro C; discriminate].
  inversion IH as [| ? ? Hs1 Ht1]; subst. specialize (Hs1 s2). 
  destruct Hs1; simpl; [subst | apply ReflectF; intro C; inversion C; contradiction].
  specialize (IHs Ht1 t2). 
  destruct IHs; [subst; apply ReflectT; reflexivity | apply ReflectF; intro C; inversion C; contradiction].
Qed.

Definition sort_eq_dec s1 s2 := reflect_dec' (sort_eqb_spec s1 s2).


(*Bijection between types with no typevars and sorts*)

Fixpoint sort_to_ty (s: sort) : vty :=
  match s with
  | s_int => vty_int
  | s_real => vty_real
  | s_cons ts srts => vty_cons ts (List.map sort_to_ty srts)
  end.

Coercion sort_to_ty : sort >-> vty.

(*Get the type variables in a type, with no duplicates*)
Fixpoint type_vars (t: vty) : aset typevar :=
  match t with
  | vty_int => aset_empty
  | vty_real => aset_empty
  | vty_var v => aset_singleton v
  | vty_cons sym ts => aset_big_union type_vars ts
  end.

Definition is_sort (t: vty) : bool :=
  aset_is_empty (type_vars t).

Lemma sort_inj: forall {s1 s2: sort},
  sort_to_ty s1 = sort_to_ty s2 ->
  s1 = s2.
Proof.
  induction s1 as [| | ts1 srts1 IHs1]; intros [| | ts2 srts2]; try discriminate; auto.
  intros Hs; inversion Hs; subst. f_equal.
  clear -IHs1 H1. generalize dependent srts2. 
  induction srts1 as [| h1 t1 IH]; intros [| h2 t2];
  simpl; try discriminate; auto.
  intros H; inversion H; subst. inversion IHs1; subst.
  f_equal; auto.
Qed.

Definition sorts_to_tys (l: list sort) : list vty := List.map sort_to_ty l.

(*Lemmas about sorts*)

Lemma var_not_sort v: ~ is_sort (vty_var v).
Proof.
  unfold is_sort. simpl. rewrite aset_singleton_not_empty. auto.
Qed.

Lemma is_sort_cons_iff: forall (ts: typesym) (l: list vty),
  is_sort (vty_cons ts l) <->
  forall x, In x l -> is_sort x.
Proof.
  intros ts l. unfold is_sort. simpl.
  rewrite aset_big_union_empty. unfold is_true; rewrite forallb_forall.
  reflexivity.
Qed.

Lemma is_sort_cons: forall (ts: typesym) (l: list vty),
  is_sort (vty_cons ts l) ->
  forall x, In x l -> is_sort x.
Proof.
  intros ts l. apply is_sort_cons_iff.
Qed.

Lemma is_sort_cons_Forall ts l: is_sort (vty_cons ts l) -> Forall is_sort l.
Proof.
  rewrite Forall_forall. apply is_sort_cons.
Qed.

(*The reverse map*)

Fixpoint ty_to_sort (t: vty) (Hs: is_sort t) : sort :=
  match t return is_sort t -> sort with
  | vty_int => fun _ => s_int
  | vty_real => fun _ => s_real
  | vty_var v => fun Hs => False_rect _ (var_not_sort _ Hs)
  | vty_cons ts tys => fun Hs => s_cons ts (dep_map ty_to_sort tys (is_sort_cons_Forall _ _ Hs))
  end Hs.

Lemma sort_to_ty_is_sort s: is_sort (sort_to_ty s).
Proof.
  induction s; simpl; auto.
  apply is_sort_cons_iff.
  rewrite <- Forall_forall, Forall_map.
  exact IH.
Qed.

Lemma sort_to_ty_to_sort s Hsort:
  ty_to_sort (sort_to_ty s) Hsort = s.
Proof.
  revert Hsort.
  induction s; simpl; try reflexivity. intros Hsort. f_equal.
  generalize dependent (is_sort_cons_Forall ts (List.map sort_to_ty srts) Hsort).
  induction srts as [| s stl IHs]; simpl; auto.
  intros f. inversion IH as [| ? ? Hs Hst]; subst. 
  f_equal; auto. apply IHs; auto.
  apply (sort_to_ty_is_sort (s_cons ts stl)).
Qed.

Lemma ty_to_sort_to_ty ty Hsort:
  sort_to_ty (ty_to_sort ty Hsort) = ty.
Proof.
  revert Hsort.
  induction ty as [| | v | ts tys IHtys]; simpl; auto.
  - intros Hsort. exfalso. apply (var_not_sort _ Hsort).
  - intros Hsort. f_equal. rewrite map_dep_map.
    generalize dependent (is_sort_cons_Forall ts tys Hsort).
    clear Hsort. induction tys as [| x tl IHtl]; simpl; auto.
    intros Hall. inversion IHtys as [| ? ? Hx Htl]; subst.
    inversion Hall as [| ? ? Hsx Hstl]; subst.
    f_equal; auto.
Qed.

(* Type substitution *)

Section TySubst.

(*Substitute according to function*)
Fixpoint v_subst_aux (v: typevar -> vty) (t: vty) : vty :=
  match t with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var tv => v tv
  | vty_cons ts vs => vty_cons ts (List.map (v_subst_aux v) vs)
  end.

Fixpoint v_subst (v: typevar -> sort) (t: vty) : sort :=
  match t with
  | vty_int => s_int
  | vty_real => s_real
  | vty_var tv => v tv
  | vty_cons ts vs => s_cons ts (List.map (v_subst v) vs)
  end.

Lemma v_subst_aux_eq v1 v2 t
  (Hv: forall x, v1 x = sort_to_ty (v2 x)) :
  v_subst_aux v1 t = sort_to_ty (v_subst v2 t).
Proof.
  induction t; simpl; auto.
  f_equal. induction vs; simpl; auto. inversion H; subst.
  f_equal; auto.
Qed.

Definition ty_subst_fun {A: Type} (vs: list typevar) (s: list A) (d: A) : typevar -> A :=
  fun v =>
    match get_assoc_list string_dec (List.combine vs s) v with
    | Some ty => ty
    | None => d
    end.

Lemma ty_subst_fun_sorts vs srts d x:
  sort_to_ty (ty_subst_fun vs srts d x) = ty_subst_fun vs (sorts_to_tys srts) (sort_to_ty d) x.
Proof.
  unfold ty_subst_fun.
  unfold sorts_to_tys.
  rewrite get_assoc_list_combine_map.
  destruct (get_assoc_list _ _ _); auto.
Qed.

Lemma ty_subst_fun_cons {A: Type} {x xs} {y: A} {ys d z}:
  ty_subst_fun (x :: xs) (y :: ys) d z = if string_dec z x then y else ty_subst_fun xs ys d z.
Proof.
  unfold ty_subst_fun. simpl. destruct (string_dec _ _); auto.
Qed.

Definition ty_subst (vs: list typevar) (ts: list vty) (expr: vty) : vty :=
  v_subst_aux (ty_subst_fun vs ts vty_int) expr.

Definition ty_subst_list (vs: list typevar) (ts: list vty) (exprs: list vty) : list vty :=
  map (ty_subst vs ts) exprs.

Definition ty_subst_s (vs: list typevar) (ts: list sort) (expr: vty) : sort :=
  v_subst (ty_subst_fun vs ts s_int) expr.

Definition ty_subst_list_s (vs: list typevar) (ts: list sort) (exprs: list vty) : list sort :=
  map (ty_subst_s vs ts) exprs.

End TySubst.

(*Lemmas about substitution*)
Section TySubstLemmas.

Lemma ty_subst_s_cons: forall (vs: list typevar) (ts: list Types.sort)
  (t: typesym) (args: list vty),
  ty_subst_s vs ts (vty_cons t args) = s_cons t (ty_subst_list_s vs ts args).
Proof. reflexivity. Qed.

Lemma ty_subst_fun_nth {A: Type}: forall (vars: list typevar) (vs: list A)
  (d: A) (n: nat) (a: typevar) (s: A),
  length vars = length vs ->
  (n < length vars)%coq_nat ->
  NoDup vars ->
  ty_subst_fun vars vs d (List.nth n vars a) = List.nth n vs s.
Proof.
  intros vars vs d n a s' Hlen Hn Hnodup.
  unfold ty_subst_fun.
  rewrite -> get_assoc_list_combine_nth with (b:=s'); auto. lia.
Qed.

(*A version removing the equal length hypothesis*)
Lemma ty_subst_fun_nth_gen {A: Type}: forall (vars: list typevar) (vs: list A)
  (d: A) (n: nat) (a: typevar) (s: A),
  (n < length vars)%coq_nat ->
  (n < length vs)%coq_nat ->
  NoDup vars ->
  ty_subst_fun vars vs d (List.nth n vars a) = List.nth n vs s.
Proof.
  intros vars vs d n a s' Hlen Hn Hnodup.
  unfold ty_subst_fun.
  rewrite -> get_assoc_list_combine_nth with (b:=s'); auto.
Qed.

Lemma ty_subst_fun_notin {A: Type}: forall params args (d: A) (x: typevar),
  ~In x params ->
  ty_subst_fun params args d x = d.
Proof.
  intros. unfold ty_subst_fun.
  assert (Hassoc: get_assoc_list string_dec (combine params args) x = None).
  { apply get_assoc_list_none. rewrite map_fst_combine_eq. intros Hin.
    apply In_firstn in Hin. contradiction. }
  rewrite Hassoc.
  reflexivity.
Qed.

(*Substitutions that do nothing:*)

Lemma map_ty_subst_var (vars: list typevar) (vs2: list vty):
  length vars = length vs2 ->
  NoDup vars ->
  map (ty_subst vars vs2) (map vty_var vars) = vs2.
Proof.
  intros.
  apply list_eq_ext'; rewrite !length_map; auto.
  intros n d Hn.
  rewrite -> map_nth_inbound with (d2:=vty_int); [|rewrite length_map; auto].
  rewrite -> map_nth_inbound with (d2:=EmptyString); auto.
  unfold ty_subst. simpl. apply ty_subst_fun_nth; auto.
Qed.

Lemma map_ty_subst_var_sort: forall (vars: list typevar) (srts: list Types.sort),
  length vars = length srts ->
  NoDup vars ->
  map (fun x => ty_subst_s vars srts (vty_var x)) vars = srts.
Proof.
  intros.
  apply list_eq_ext'; rewrite !length_map; auto.
  intros n d Hn. rewrite -> map_nth_inbound with (d2:=""%string); auto.
  unfold ty_subst_s. simpl.
  rewrite -> ty_subst_fun_nth with (s:=d); auto.
Qed.

Lemma subst_sort_eq: forall (s: sort) (v: typevar -> sort),
  s = v_subst v (sort_to_ty s).
Proof.
  intros s v.
  induction s as [| | ts srts IH]; simpl; auto.
  f_equal. induction srts as [| h t IHs]; simpl; auto.
  inversion IH; subst. f_equal; auto.
Qed.


(* If we have a sort, then substituting a valuation does nothing *)
Lemma subst_is_sort_eq (t: vty) (Ht: is_sort t) v:
  t = v_subst v t.
Proof.
  assert (Hteq: t = sort_to_ty (ty_to_sort t Ht)). { symmetry; apply ty_to_sort_to_ty. }
  rewrite -> Hteq. rewrite <- subst_sort_eq. reflexivity.
Qed.

Lemma subst_aux_sort_eq: forall (v: typevar -> vty) (t: vty) (Ht: is_sort t),
  t = v_subst_aux v t.
Proof.
  intros v t.
  induction t as [| | x | ts srts IH]; simpl; auto.
  - intros Hsort. exfalso. apply (var_not_sort _ Hsort).
  - intros Hsort. f_equal. apply is_sort_cons_Forall in Hsort.
    assert (Hall: Forall (fun t => t = v_subst_aux v t) srts). {
      eapply Forall_impl_strong; [| apply Hsort].
      rewrite Forall_forall in IH. auto.
    }
    clear -Hall. induction srts as [| h t IH]; simpl; auto.
    inversion Hall; subst; f_equal; auto.
Qed.
  

(*Extensionality*)

Lemma v_subst_aux_ext (v1 v2: typevar -> vty) ty:
  (forall x, aset_mem x (type_vars ty) -> v1 x = v2 x ) ->
  v_subst_aux v1 ty = v_subst_aux v2 ty.
Proof.
  intros. induction ty; simpl; auto.
  - rewrite H; simpl; auto.
    rewrite aset_mem_singleton. auto.
  - f_equal. simpl in H. induction vs; simpl in *; auto.
    inversion H0; subst.
    f_equal.
    + apply H3. intros; apply H. rewrite aset_mem_union. auto.
    + apply IHvs; auto. intros. apply H; rewrite aset_mem_union; auto.
Qed.

Lemma v_subst_ext (v1 v2: typevar -> sort) ty:
  (forall x, aset_mem x (type_vars ty) -> v1 x = v2 x) ->
  v_subst v1 ty = v_subst v2 ty.
Proof.
  intros Hv12. induction ty; simpl; auto.
  - apply Hv12. simpl; auto.
    rewrite aset_mem_singleton. auto.
  - f_equal. simpl in Hv12. induction vs; simpl in *; auto.
    inversion H; subst.
    f_equal.
    + apply H2. intros; apply Hv12. rewrite aset_mem_union. auto.
    + apply IHvs; auto. intros. apply Hv12; rewrite aset_mem_union; auto.
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
  (forall x, aset_mem x (type_vars ty) -> In x params) ->
  v_subst v ty = ty_subst_s params srts ty.
Proof.
  intros Hv Hin.
  unfold ty_subst_s. apply v_subst_ext. intros x Hinx.
  apply Hin in Hinx. 
  destruct (In_nth _ _ EmptyString Hinx) as [i [Hi Hx]]; subst.
  rewrite Hv; auto.
  rewrite (ty_subst_fun_nth _ _ _ _ _ s_int); auto.
Qed.


(*Other lemmas*)

Lemma ty_subst_cons (vars: list typevar) (params: list vty)
  (ts: typesym) (vs: list vty):
  ty_subst vars params (vty_cons ts vs) =
  vty_cons ts (map (ty_subst vars params) vs).
Proof.
  reflexivity.
Qed.

Lemma ty_subst_var (vars: list typevar) (params: list vty)
  (v: typevar):
  ty_subst vars params (vty_var v) = ty_subst_fun vars params vty_int v.
Proof.
  reflexivity.
Qed.

Lemma v_subst_cons {f} ts vs:
  v_subst f (vty_cons ts vs) =
  s_cons ts (map (v_subst f) vs).
Proof. reflexivity. Qed.

Lemma v_subst_twice f ty:
  v_subst f (v_subst f ty) = v_subst f ty.
Proof.
  induction ty as [| | | ts tys IH]; simpl; auto.
  - rewrite <- subst_sort_eq; reflexivity.
  - f_equal. rewrite <- !map_comp.
    apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn.
    rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
    rewrite Forall_forall in IH. apply IH.
    apply nth_In; auto.
Qed.

Lemma v_subst_aux_type_vars (v: typevar -> vty) (t: vty):
  forall x, aset_mem x (type_vars (v_subst_aux v t)) ->
    exists y, aset_mem y (type_vars t) /\ aset_mem x (type_vars (v y)).
Proof.
  intros x. induction t; simpl; try (intros Hex; apply aset_mem_empty in Hex; contradiction).
  - intros Hinx. exists v0. rewrite aset_mem_singleton. auto.
  - rewrite aset_mem_big_union. intros [t [Hint Hinx]].
    rewrite in_map_iff in Hint.
    destruct Hint as [t2 [Ht Hint2]]; subst.
    rewrite Forall_forall in H.
    specialize (H _ Hint2 Hinx).
    destruct H as [y [Hiny Hinx2]].
    exists y. split; auto. rewrite aset_mem_big_union. exists t2. auto.
Qed. 

Lemma ty_subst_type_vars params tys ty:
  asubset (type_vars (ty_subst params tys ty)) 
    (aset_big_union type_vars tys).
Proof.
  unfold ty_subst. rewrite asubset_def.
  intros x Hinx.
  apply v_subst_aux_type_vars in Hinx.
  destruct Hinx as [y [Hiny Hinx]].
  unfold ty_subst_fun in Hinx.
  destruct (get_assoc_list _ _ _) eqn : Hassoc.
  - apply get_assoc_list_some, in_combine_r in Hassoc.
    simpl_set. exists v. auto.
  - simpl in Hinx. apply aset_mem_empty in Hinx. contradiction.
Qed.

Lemma ty_subst_s_params_id: forall params srts,
  length params = length srts ->
  NoDup params ->
  map (fun x => ty_subst_s params srts (vty_var x)) params = srts.
Proof.
  intros params srts Hlen Hnodup.
  apply list_eq_ext'; rewrite !length_map; auto.
  intros n d Hn.
  rewrite -> map_nth_inbound with (d2:=""%string); auto. unfold ty_subst_s. simpl.
  rewrite -> ty_subst_fun_nth with (s:=d); auto.
Qed.

Lemma ty_subst_cons_notin v1 vs ty1 tys x:
  ~ aset_mem v1 (type_vars x) ->
  ty_subst (v1 :: vs) (ty1 :: tys) x =
  ty_subst vs tys x.
Proof.
  intros Hnotin. unfold ty_subst. apply v_subst_aux_ext.
  intros y Hiny. 
  unfold ty_subst_fun. simpl. destruct (string_dec _ _); subst; auto.
  contradiction.
Qed. 

End TySubstLemmas.

(*A version of [ty_subst] that only changes the mapped
  variables, leaving everything else as in.
  Needed for type substitutions that do not change
  all type variables*)
Section TySubstAlt.

Fixpoint ty_subst' params args (v: vty) : vty :=
  match v with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var x => if in_dec typevar_eq_dec x params then
    (ty_subst params args) (vty_var x) else vty_var x
  | vty_cons ts vs =>
    vty_cons ts (map (ty_subst' params args) vs)
  end.

Definition ty_subst_list' (vs: list typevar) (ts: list vty) (l: list vty) :=
  map (ty_subst' vs ts) l.


(*Needed in many places: substituting tys1 for params1, 
  then tys2 for params2 is the same as substituing
  params1 with the result of substituting tys2 for params2 in tys1*)
Lemma ty_subst_twice params1 tys1 params2 tys2 ty:
  NoDup params1 ->
  length params1 = length tys1 ->
  ty_subst' params2 tys2 (ty_subst params1 tys1 ty) =
  ty_subst params1 (ty_subst_list' params2 tys2 tys1) ty.
Proof.
  intros Hn1 Hlen1.
  unfold ty_subst_list', ty_subst.
  induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params1).
    + destruct (In_nth _ _ EmptyString i) as [j [Hj Hv]]; subst. 
      rewrite -> !ty_subst_fun_nth with (s:=vty_int); auto; [| rewrite length_map; auto].
      rewrite -> map_nth_inbound with(d2:=vty_int); [| rewrite <- Hlen1; auto].
      reflexivity.
    + rewrite !ty_subst_fun_notin; auto. 
  - f_equal.
    apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn'.
    rewrite -> !map_nth_inbound with (d2:=vty_int); auto;
    [| rewrite length_map; auto].
    rewrite Forall_forall in H. apply H. apply nth_In; auto.
Qed.

Lemma ty_subst_equiv params tys ty:
  (asubset (type_vars ty) (list_to_aset params)) ->
  ty_subst params tys ty = ty_subst' params tys ty.
Proof.
  rewrite asubset_def.
  intros. unfold ty_subst. induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params); simpl; auto.
    exfalso. simpl in H.
    apply n. rewrite <- aset_mem_list_to_aset. apply H.
    rewrite aset_mem_singleton. auto.
  - f_equal. apply map_ext_in.
    intros. rewrite Forall_forall in H0.
    apply H0; auto.
    simpl in H. intros x Hinx.
    apply H. rewrite aset_mem_big_union. exists a; auto.
Qed.

End TySubstAlt.