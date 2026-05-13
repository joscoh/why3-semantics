(*An interpretation of an ADT should satisfy the following properties:
  1. Constructor interps are injective
  2. Constructor interps are disjoint (across types)
  3. An inversion principle holds
  4. A generalized induction principle holds
  
Plan:
X 1. Define these properties generally
2. Refactor existing proofs to use these properties instead of fixing to W-types
  NOTE: I think this will require the isomorphism already to give us the changing-context theorems
  TODO: let's start with the isomorphism
3. Prove that W-types satisfy these properties (probably need construction)
  NOTE: might involve following
  a. define construction
  b. prove it satisfies fixed point property
  c. prove we can construct pre-interp
  d. modify full interp proofs
4. Prove that any two interps satisfying these conditions are isomorphic (need similar construction)
5. Prove that (via isomorphism) any two interps that differ only on ADTs preserve denotation
6. Prove that we can give a fixed interp to prove validity
7. Turn this into a Rocq-based proof system

Goal: sound reasoning about Why3 proof terms via shallowly embedded Rocq terms
  *)
Require Export Hlist Typing Domain. (*TODO: remove*)

Definition fun_interp (pd: sort -> Set) := forall (f:funsym) (srts: list sort)
    (a: arg_list (domain pd) (sym_sigma_args f srts)),
    (domain pd (funsym_sigma_ret f srts)).

Definition adt_rep pd a srts := ((domain pd) (typesym_to_sort (adt_name a) srts)).

Definition constr_rep {gamma: context} (gamma_valid: valid_context gamma) 
  (pd: sort -> Set) (pf: fun_interp pd)
  {m : mut_adt} {a: alg_datatype} {c: funsym} {srts: list sort}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (srts_len: length srts = length (m_params m))
  (args: arg_list (domain pd) (sym_sigma_args c srts))
  : adt_rep pd a srts :=
  dom_cast _ (Logic.eq_sym (adt_typesym_funsym gamma_valid m_in a_in c_in srts_len)) 
      (pf c srts args).

(*Useful for defaults*)
Definition dom_int (pd: sort -> Set) : domain pd s_int := 0%Z.
Record adt_interp_props {gamma: context} (gamma_valid: valid_context gamma) 
  (pd: sort -> Set) (pf: fun_interp pd) :=
  {
    constrs_inj: forall {m: mut_adt} {a: alg_datatype} {f: funsym} 
    (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (f_in: constr_in_adt f a) 
    {srts: list sort} (srts_len: length srts = length (m_params m))
    (a1 a2: arg_list (domain pd) (sym_sigma_args f srts)),
    constr_rep gamma_valid pd pf m_in a_in f_in srts_len a1 =
    constr_rep gamma_valid pd pf m_in a_in f_in srts_len a2 ->
    a1 = a2;
    (*Have eq hypothesis which is read as: even if the domains are equal for the two
      constructors, the two values cannot be. Of course if domains are different,
      inequality is assured*)
    (*Let's assume we only deal with one: it could be ok for 2 isomorphic types to have
      the same interp, I think(?)*)
    constrs_disj: forall {m: mut_adt} {a: alg_datatype} {f1 f2: funsym} 
    (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) 
    (f1_in: constr_in_adt f1 a) (f2_in: constr_in_adt f2 a) 
    {srts: list sort} (srts_len: length srts = length (m_params m))
    (a1: arg_list (domain pd) (sym_sigma_args f1 srts))
    (a2: arg_list (domain pd) (sym_sigma_args f2 srts)),
    f1 <> f2 ->
    constr_rep gamma_valid pd pf m_in a_in f1_in srts_len a1 <>
    constr_rep gamma_valid pd pf m_in a_in f2_in srts_len a2;
    (*Inversion*)
    find_constr_rep: forall {m: mut_adt} {a: alg_datatype}
    (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) {srts: list sort}
    (srts_len: length srts = length (m_params m))
    (x: adt_rep pd a srts),
    {f: funsym & {Hf: constr_in_adt f a * arg_list (domain pd) (sym_sigma_args f srts) |
    x = constr_rep gamma_valid pd pf m_in a_in (fst Hf) srts_len (snd Hf)}};
    (*Induction*)
    adt_ind: forall {m: mut_adt} (m_in: mut_in_ctx m gamma) {srts: list sort}
    (srts_len: length srts = length (m_params m))
    (P: forall t t_in, adt_rep pd t srts -> Prop)
    (IH: forall t t_in (x: adt_rep pd t srts) (c: funsym) (c_in: constr_in_adt c t)
      (a: arg_list (domain pd) (sym_sigma_args c srts))
      (Hx: x = constr_rep gamma_valid pd pf m_in t_in c_in srts_len a),
      (forall i t' t_in' 
        (Heq : nth i (sym_sigma_args c srts) s_int =
          typesym_to_sort (adt_name t') srts), 
        i < length (s_args c) ->
      (*If nth i a has type adt_rep ..., then P holds of it*)
      P t' t_in' (dom_cast _ Heq (hnth i a s_int (dom_int _)))
      ) ->
    P t t_in x
    ),
    forall t t_in (x: adt_rep pd t srts), P t t_in x;
  }.

Require Import IndTypes.

Check adt_rep.

Search context option mut_adt.

Search sort "ind".

Print sort.
Print vty.

(*TODO: move*)
Definition mk_Forall {A: Type} {P: A -> Prop} := 
  fun (f: forall x, P x) =>
    fix mk_Forall (l: list A) {struct l} : Forall P l :=
      match l with
      | nil => Forall_nil _
      | x :: xs => Forall_cons _ _ _ (f x) (mk_Forall xs)
      end.

Definition mk_ForallT {A: Type} {P: A -> Type} := 
  fun (f: forall x, P x) =>
    fix mk_ForallT (l: list A) {struct l} : ForallT P l :=
      match l with
      | nil => ForallT_nil _
      | x :: xs => ForallT_cons _ (f x) (mk_ForallT xs)
      end.

Unset Elimination Schemes.
Inductive srt :=
  | srt_int : srt
  | srt_real : srt
  | srt_cons: typesym -> list srt -> srt.
Set Elimination Schemes.

Fixpoint srt_ind (P: srt -> Prop) (P_int: P srt_int) (P_real: P srt_real) 
  (P_cons: forall (ts: typesym) (srts: list srt) (IH: Forall P srts), P (srt_cons ts srts))
  (s: srt) : P s :=
  match s with
  | srt_int => P_int
  | srt_real => P_real
  | srt_cons ts srts => P_cons ts srts (mk_Forall (srt_ind P P_int P_real P_cons) srts)
  end.

Fixpoint srt_rect (P: srt -> Type) (P_int: P srt_int) (P_real: P srt_real) 
  (P_cons: forall (ts: typesym) (srts: list srt) (IH: ForallT P srts), P (srt_cons ts srts))
  (s: srt) : P s :=
  match s with
  | srt_int => P_int
  | srt_real => P_real
  | srt_cons ts srts => P_cons ts srts (mk_ForallT (srt_rect P P_int P_real P_cons) srts)
  end.

Lemma var_not_sort v: ~ is_sort (vty_var v).
Proof.
  unfold is_sort. simpl. rewrite aset_singleton_not_empty. auto.
Qed.

Lemma is_sort_cons_Forall ts l: is_sort (vty_cons ts l) -> Forall is_sort l.
Proof.
  rewrite Forall_forall. apply is_sort_cons.
Qed.

(*The isomorphism*)

Fixpoint sort_to_srt_aux (t: vty) (Hs: is_sort t) : srt :=
  match t return is_sort t -> srt with
  | vty_int => fun _ => srt_int
  | vty_real => fun _ => srt_real
  | vty_var v => fun Hs => False_rect _ (var_not_sort _ Hs)
  | vty_cons ts tys => fun Hs => srt_cons ts (dep_map sort_to_srt_aux tys (is_sort_cons_Forall _ _ Hs))
  end Hs.

Definition sort_to_srt (s: sort) : srt := sort_to_srt_aux (proj1_sig s) (proj2_sig s).

Fixpoint srt_to_ty (s: srt) : vty :=
  match s with
  | srt_int => vty_int
  | srt_real => vty_real
  | srt_cons ts srts => vty_cons ts (map srt_to_ty srts)
  end.

Lemma srt_to_ty_sort s: is_sort (srt_to_ty s).
Proof.
  induction s; simpl; auto.
  apply is_sort_cons_iff.
  rewrite <- Forall_forall, Forall_map.
  exact IH.
Qed.

Definition srt_to_sort (s: srt) : sort := exist is_sort _ (srt_to_ty_sort s).

Set Bullet Behavior "Strict Subproofs".

Lemma srt_to_sort_to_srt s:
  sort_to_srt (srt_to_sort s) = s.
Proof.
  unfold sort_to_srt, srt_to_sort. simpl.
  generalize dependent (srt_to_ty_sort s).
  induction s; simpl; try reflexivity.
  intros Hsort. f_equal.
  generalize dependent (is_sort_cons_Forall ts (map srt_to_ty srts) Hsort).
  induction srts as [| s stl IHs]; simpl; auto.
  intros f. inversion IH as [| ? ? Hs Hst]; subst. 
  f_equal.
  - apply Hs.
  - apply IHs; auto. inversion f; subst. 
    rewrite is_sort_cons_iff, <- Forall_forall.
    assumption.
Qed.

Lemma sort_to_srt_to_sort s:
  srt_to_sort (sort_to_srt s) = s.
Proof.
  unfold srt_to_sort, sort_to_srt. apply sort_inj. simpl.
  destruct s as [ty Hsort]. simpl.
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

Lemma srt_to_sort_int: srt_to_sort srt_int = s_int.
Proof.
  apply sort_inj. reflexivity.
Qed.

Lemma srt_to_sort_real: srt_to_sort srt_real = s_real.
Proof.
  apply sort_inj. reflexivity.
Qed.

Lemma srt_to_sort_cons ts srts: srt_to_sort (srt_cons ts srts) = typesym_to_sort ts (map srt_to_sort srts).
Proof.
  apply sort_inj. simpl. f_equal.
  induction srts as [| x t IH]; simpl; auto.
  f_equal. auto.
Qed.

(*And now an induction principle on sorts*)
Lemma sort_ind (P: sort -> Prop) (P_int: P s_int) (P_real: P s_real)
  (P_cons: forall (ts: typesym) (srts: list sort) (IH: Forall P srts), P (typesym_to_sort ts srts))
  (s: sort) : P s.
Proof.
  set (s' := sort_to_srt s).
  set (P' := fun (s: srt) => P (srt_to_sort s)).
  assert (Hp: P' s'). {
    apply srt_ind.
    - unfold P'. rewrite srt_to_sort_int. exact P_int.
    - unfold P'. rewrite srt_to_sort_real. exact P_real.
    - intros ts srts. unfold P'. rewrite srt_to_sort_cons. intros Hall. 
      apply P_cons; rewrite Forall_map; auto.
  }
  unfold P', s' in Hp. rewrite sort_to_srt_to_sort in Hp.
  exact Hp.
Qed.

(*Note: opaque for now*)
Lemma ForallT_map1 {A B: Type} (f: A -> B) (P: B -> Type) (l: list A):
  ForallT P (map f l) -> ForallT (fun x => P (f x)) l.
Proof.
  induction l as [| h t IH].
  - constructor.
  - intros Hall. inversion Hall; subst. constructor; auto.
Qed. 

Lemma ForallT_map2 {A B: Type} (f: A -> B) (P: B -> Type) (l: list A):
  ForallT (fun x => P (f x)) l -> ForallT P (map f l).
Proof.
  induction l as [| h t IH].
  - constructor.
  - intros Hall. inversion Hall; subst. constructor; auto.
Qed. 

(*Opaque*)
Lemma sort_rect (P: sort -> Type) (P_int: P s_int) (P_real: P s_real)
  (P_cons: forall (ts: typesym) (srts: list sort) (IH: ForallT P srts), P (typesym_to_sort ts srts))
  (s: sort) : P s.
Proof.
  set (s' := sort_to_srt s).
  set (P' := fun (s: srt) => P (srt_to_sort s)).
  assert (Hp: P' s'). {
    apply srt_rect.
    - unfold P'. rewrite srt_to_sort_int. exact P_int.
    - unfold P'. rewrite srt_to_sort_real. exact P_real.
    - intros ts srts. unfold P'. rewrite srt_to_sort_cons. intros Hall. 
      apply P_cons. apply ForallT_map2. exact Hall.
  }
  unfold P', s' in Hp. rewrite sort_to_srt_to_sort in Hp.
  exact Hp.
Qed.

(*TODO: just use recursive sort*)
Lemma sort_rect_int P P_int P_real P_cons:
  sort_rect P P_int P_real P_cons s_int = P_int.
Proof. Admitted.

Lemma sort_rect_real P P_int P_real P_cons:
  sort_rect P P_int P_real P_cons s_real = P_real.
Proof. Admitted.

Lemma sort_rect_typesym_to_sort P P_int P_real P_cons ts srts:
  sort_rect P P_int P_real P_cons (typesym_to_sort ts srts) = 
  P_cons ts srts (mk_ForallT (sort_rect P P_int P_real P_cons) srts).
Admitted.

Definition ts_map_to_pd (f: typesym -> list sort -> Set) : sort -> Set :=
  sort_rect (fun _ => Set) Z R (fun ts srts IH => f ts srts).

(* Lemma ts_map_to_pd_domain f:
   *)

Print adt_rep.

Definition adt_rep' (m: mut_adt) (srts: list sort) (d1 d2: sort -> Set) (a: alg_datatype)
  (a_in: adt_in_mut a m) :=
  mk_adts (var_map m srts d1) (typesym_map m srts d2) (adts m) (get_idx adt_dec a (adts m) a_in).

Fixpoint mk_ts_map (gamma: context) (pd: sort -> Set) (n: nat) (ts: typesym) (srts: list sort) : Set :=
  match n with
  | O => pd (typesym_to_sort ts srts)
  | S n' =>
    let pd' := ts_map_to_pd (mk_ts_map gamma pd n')
(*     sort_rect (fun _ => Set) Z R (fun ts srts IH => mk_ts_map gamma n' pd ts srts) *)
     (*  let fix f (s: srt) : Set :=
      match s with
      | srt_int => Z
      | srt_real => R
      | srt_cons ts srts => mk_ts_map gamma n' f ts (map srt_to_sort srts)
      end in
      f (sort_to_srt s) *)
    in
    match find_ts_in_ctx gamma ts as b return find_ts_in_ctx gamma ts = b -> _ with
    | Some (m, a) => fun Hfind => adt_rep m srts pd' a (proj1 (proj2 (find_ts_in_ctx_some _ _ _ _ Hfind)))
    | None => fun _ => pd (typesym_to_sort ts srts)
    end eq_refl
    end.

Definition mk_pd_aux (gamma: context) (pd: sort -> Set) (n: nat) (s: sort) : Set :=
  ts_map_to_pd (mk_ts_map gamma pd n) s.

(*Idea: should be invariant as long as n larger than max depth of sort*)
Fixpoint srt_depth (s: srt) : nat :=
  match s with
  | srt_int => 1
  | srt_real => 1
  | srt_cons ts srts => 1 + list_max (map srt_depth srts)
  end.

Definition srts_depth (s: list srt) : nat := list_max (map srt_depth s).

Definition sort_depth s := srt_depth (sort_to_srt s).
Definition sorts_depth s := srts_depth (map sort_to_srt s).

Definition mk_ts_full gamma pd ts srts :=
  mk_ts_map gamma pd (sorts_depth srts) ts srts.

Definition mk_pd (gamma: context) (pd: sort -> Set) (s: sort) : Set :=
  ts_map_to_pd (mk_ts_full gamma pd) s.


(*pd with all typesym_to_sort set correctly to the corresponidng W-type*)
Definition pd_full (gamma: context) (pd: sort -> Set) := forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m),
    pd (typesym_to_sort (adt_name a) srts) =
    adt_rep m srts pd a Hin.

Definition pd_full_aux (gamma: context) (pd: sort -> Set) (n: nat) := forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m) ,
    1 + sorts_depth srts < n ->
    pd (typesym_to_sort (adt_name a) srts) =
    adt_rep m srts pd a Hin.

(*TODO: move this*)
Print mk_adts.

(*Get vars in mutual datatype (note: by well-typing, should be in m_params m)*)
Print alg_datatype.

Print funsym.
Print fpsym.
Print f_sym.

Definition funsym_vars (f: funsym) : aset typevar :=
  aset_big_union type_vars (s_args f).
Definition adt_vars (a: alg_datatype) : aset typevar :=
  aset_big_union funsym_vars (adt_constr_list a).
Definition mut_vars (l: list (alg_datatype)) : aset typevar :=
  aset_big_union adt_vars l.

Print mk_adts.
Print build_base.
Print build_constr_base.
Print build_vty_base.
Print vty_to_set.

Definition vty_ts_pair (t: vty) : option (typesym * list vty) :=
  match t with
  | vty_cons ts vs => Some (ts, vs)
  | _ => None
  end.


Definition funsym_ts_pairs m (f: funsym) : list (typesym * list vty) :=
  omap vty_ts_pair (get_nonind_vtys m (s_args f)).

Definition adt_ts_pairs m a : list (typesym * list vty) :=
  concat (map (funsym_ts_pairs m) (adt_constr_list a)).

Definition mut_ts_pairs m := concat (map (adt_ts_pairs m) m).

Print W.
Check w_eq.
(*Lemma W_ext (I: Set) (A1 A2: I -> Set) (B1 B2:  *)

(*Lemma big_sprod_inj l1 l2:
  big_sprod l1 = big_sprod l2 ->
  *)

(*TODO: move - this is the key lemma that lets us change interps!*)
Lemma mk_adts_ext v a1 a2 m
  (*(Hv: forall v, aset_mem v (mut_vars m) -> v1 v = v2 v)*)
  (Ht: forall ts tys, In (ts, tys) (mut_ts_pairs m) -> a1 ts tys = a2 ts tys):
  mk_adts v a1 m = mk_adts v a2 m.
Proof.
  unfold mk_adts.
  assert (Hcbase: forall c a, In a m -> constr_in_adt c a -> 
    build_constr_base v a1 m c = build_constr_base v a2 m c).
  {
    intros c a a_in c_in.
    unfold build_constr_base, build_vty_base.
    f_equal.
    apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn.
    rewrite !map_nth_inbound with (d2:=vty_int) by assumption.
    unfold vty_to_set.
    (*Here, we use the assumption*)
    destruct (nth n (get_nonind_vtys m (s_args c)) vty_int) as [| | | ts vs] eqn : Hty; auto.
    apply Ht. unfold mut_ts_pairs. rewrite in_concat. exists ((adt_ts_pairs m) a).
    split; [rewrite in_map_iff; eauto|].
    unfold adt_ts_pairs. rewrite in_concat. exists (funsym_ts_pairs m c).
    rewrite in_map_iff. split; [exists c; split; auto; apply constr_in_adt_eq; auto|].
    unfold funsym_ts_pairs. rewrite in_omap_iff. exists (vty_cons ts vs).
    split; auto. rewrite <- Hty. apply nth_In. auto.
  }
  assert (Hbase': 
    forall a l, In a m -> 
    (forall x : funsym, in_bool_ne funsym_eq_dec x l -> constr_in_adt x a) ->
    build_base v a1 m l = build_base v a2 m l).
  {
    intros a l a_in Hall.
    induction l as [x | x l IH]; simpl in *.
    - apply Hcbase with (a:=a); auto. apply Hall. destruct (funsym_eq_dec x x); auto.
    - f_equal.
      + apply Hcbase with (a:=a); auto. apply Hall. destruct (funsym_eq_dec x x); auto.
      + apply IH. intros y Hiny. apply Hall. rewrite Hiny, orb_true_r. auto.
  }
  assert (Hbase: forall a : alg_datatype, In a m -> 
    build_base v a1 m (adt_constrs a) = build_base v a2 m (adt_constrs a)).
  {
    intros a a_in.
    apply Hbase' with (a:=a); auto.
  }
  assert (Heq: (fun n : finite (Datatypes.length m) => build_base v a1 m (adt_constrs (fin_nth m n))) =
    (fun n : finite (Datatypes.length m) => build_base v a2 m (adt_constrs (fin_nth m n)))).
  {
    apply functional_extensionality. intros x.
    pose proof (fin_nth_in _ x) as Hin.
    apply Hbase; auto.
  }
  apply w_eq with (Heq:=Heq).
  (*Now prove second part equiv*)
  intros i j a.
  pose proof (fin_nth_in m i) as Hina.
  generalize dependent (eq_idx Heq i). clear Heq.
  generalize dependent (fin_nth m i).
  (*Again, need to generalize (adt_constrs a)*)
  intros a b a_in Heq.
  set (l := adt_constrs a) in *.
  assert (Hall: forall (x: funsym), in_bool_ne funsym_eq_dec x l -> constr_in_adt x a).
  { intros x. auto. }
  induction l as [x | x l IH]; simpl in *; auto.
  assert (Heq1: build_constr_base v a1 m x = build_constr_base v a2 m x).
  { apply Hcbase with (a:=a); auto. apply Hall. destruct (funsym_eq_dec x x); auto. }
  assert (Heq2: build_base v a1 m l = build_base v a2 m l).
  { apply Hbase' with (a:=a); auto. intros y Hiny. apply Hall. rewrite Hiny, orb_true_r; auto. }
  destruct b.
  - (*Can't rewrite directly so we destruct and derive contradiction*)
    destruct (scast Heq _) eqn : Hs; auto.
    exfalso. rewrite scast_left with (H1:=Heq1) in Hs; [discriminate|]; auto.
  - destruct (scast Heq _) eqn : Hs; auto.
    { exfalso. rewrite scast_right with (H2:=Heq2) in Hs; [discriminate|]; auto. }
    rewrite scast_right with (H2:=Heq2) in Hs; auto.
    inversion Hs; subst.
    apply IH.
    intros y Hiny. apply Hall. rewrite Hiny, orb_true_r; auto.
Qed.


Lemma mk_ts_map_invar gamma pd n1 n2 s:
  sort_depth s < n1 ->
  sort_depth s < n2 ->
  ts_map_to_pd (mk_ts_map gamma pd n1) s = ts_map_to_pd (mk_ts_map gamma pd n2) s.
Proof.
  generalize dependent n2. generalize dependent s. induction n1 as [| n1 IHn1].
  { intros; lia. }
  intros s [| n2]; [lia | intros Hn1 Hn2].
  unfold ts_map_to_pd.
  (*TODO: need recursive sorts*)
  assert (Hs: s = s_int \/ s = s_real \/ exists ts srts, s = typesym_to_sort ts srts). { admit. }
  destruct Hs as [Hs | [Hs | [ts [srts Hs]]]].
  - subst. rewrite !sort_rect_int. reflexivity.
  - subst. rewrite !sort_rect_real. reflexivity.
  - subst. rewrite !sort_rect_typesym_to_sort. simpl.
    simpl. generalize dependent (find_ts_in_ctx_some gamma ts).
    destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind; auto.
    intros H. generalize dependent (proj1 (proj2 (H m a eq_refl))). clear H.
    intros a_in. unfold adt_rep.
    assert (Hveq: (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n1))) = 
      (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n2)))). {
      apply functional_extensionality. intros x.
      unfold var_map. unfold domain. unfold sigma. simpl.
      destruct (in_dec string_dec x (m_params m)) as [Hin| Hin].
      + (*Case 1: if var in list, maps to corresponding sort, which has smaller size than n1 and n2,
          so use IH*)
        (*Note: we need a lemma that doesnt require length eq, as long as in both lists, otherwise prove default
          for now just admit*)
        destruct (In_nth _ _ EmptyString Hin) as [n [Hn Hx]].
        subst. rewrite ty_subst_fun_nth with (s:=vty_int); auto.
        2: { (*here*) admit. }
        2: { apply m_params_Nodup. }
        unfold sorts_to_tys. rewrite !(map_nth_inbound) with (d2:=s_int); auto. 2: admit.
        destruct (sort_to_ty (nth n srts s_int)) eqn : Hs; auto.
        { (*sort not var*) unfold sort_to_ty in Hs. destruct (nth n srts s_int); simpl in Hs. subst.
          exfalso. apply (var_not_sort t); auto. }
        unfold ty_subst_s. unfold v_subst. simpl. apply IHn1.
        * (*identical proofs*)
          unfold sort_depth. unfold sort_to_srt. simpl.
          match goal with |- context [ sort_to_srt_aux ?x ?y] => generalize dependent y end.
          simpl. rewrite !ty_subst_fun_nth with (s:=vty_int); auto.
          2: { admit. } 2: { apply m_params_Nodup. }
          unfold sorts_to_tys. rewrite !map_nth_inbound with (d2:=s_int) by admit.
          (*TODO: this is doable once we have recursive sorts*)
          admit.
        * (*similar*) admit.
      + rewrite !ty_subst_fun_notin; auto.
    }
    rewrite Hveq.
    (*Now prove typesym_map equality*)
    erewrite mk_adts_ext; [reflexivity|].
    (*OK, so we need to prove this*)
    intros ts' tys' Hin'. unfold typesym_map.
    (*So we know (if we change bounds) that sort depth is smaller*)
    unfold domain. 
    destruct (sort_to_ty (typesym_to_sort ts' (seq.map (sigma m srts) tys'))) eqn : Hty; auto.
    { (*contradiction*) exfalso. apply (var_not_sort t). rewrite <- Hty; auto.
      destruct (typesym_to_sort ts' (seq.map (sigma m srts) tys')); auto.
    }
    (*Idea is that we need to show (ultimately) that this sort is small enough*)
    apply IHn1.
    (*TODO: come back once I fix sorts *)
    admit.
    admit.
Admitted.



(*Lemma mk_ts_map_change_n (gamma: context) (pd: sort -> Set) (n1 n2: nat) (ts: typesym) (srts: list sort)
  (Hn1: sorts_depth srts < n1)
  (Hn2: sorts_depth srts < n2):
  mk_ts_map gamma pd n1 ts srts = mk_ts_map gamma pd n2 ts srts.
Proof.
  generalize dependent n2. generalize dependent srts. induction n1 as [| n1 IHn1].
  - intros; lia.
  - intros srts Hn1 [| n2]; [lia|]; intros Hn2.
    simpl. generalize dependent (find_ts_in_ctx_some gamma ts).
    destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind; auto.
    intros Hdefs. generalize dependent (proj1 (proj2 (Hdefs m a eq_refl))).
    intros a_in. clear Hdefs.
    (*Now we need to show we can change adt_rep pd*)



    (*TODO: separate lemma*)
    unfold adt_rep.
    Print mk_adts.
    Print typesym_map.

Lemma mk_adts_ext (
    unfold var_map.
   
    

 specialize (Hdefs m a eq_refl).
  

Lemma mk_pd_aux_change_n gamma pd n1 n2:*)

Check adt_rep.
Lemma adt_rep_eq m srts pd a a_in:
  adt_rep' m srts pd pd a a_in = adt_rep m srts pd a a_in.
Proof. reflexivity. Qed.

(*Now we will try to prove for the generalized version*)
Lemma mk_pd_aux_full gamma pd n: valid_context gamma -> pd_full_aux gamma (mk_pd_aux gamma pd n) n.
Proof.
  intros gamma_valid.
  unfold pd_full_aux, mk_pd_aux. unfold ts_map_to_pd at 1. intros m srts a m_in a_in Hn.
  rewrite sort_rect_typesym_to_sort.
  (*TODO: could I prove that this equals mk_ts ... (pred n) (bc if n large enough, doesn't change)
    *)
  assert (Htest: adt_rep m srts (fun s : sort => ts_map_to_pd (mk_ts_map gamma pd n) s) a a_in =
    adt_rep m srts (fun s : sort => ts_map_to_pd (mk_ts_map gamma pd (pred n)) s) a a_in).
  {
    unfold adt_rep. f_equal. apply functional_extensionality. intros x.
    (*TODO: prove var_map result as separate lemma after previous (which we needed for induction, we needed sort
      explicitly)*)
    admit.
    (*TODO: prove typesym_map also*)
  }
  rewrite <- adt_rep_eq.
  rewrite Htest. clear Htest.
  generalize dependent srts. induction n as [| n' IH].
  - intros; lia.
  - intros srts Hdepth. (*TODO: generalize pd in [adt_rep]?*) simpl.
    generalize dependent (find_ts_in_ctx_some gamma (adt_name a)).
    assert (Hfind: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
      apply find_ts_in_ctx_iff; auto.
    }
    rewrite Hfind.
    intros H.
    assert (Heq: (proj1 (proj2 (H m a eq_refl))) = a_in) by (apply bool_irrelevance).
    rewrite Heq.

    (*I think we need a result (not sure if provable): for d2, if agrees on all 
      typesyms that are NOT in the ADT in question, then same (tying knot lemma)
      then need to show agrees on all typesyms not in ADT for all n, then connect with n = 0
      this lemma should be true, hopefully it is provable
*)

 clear H Heq.
    reflexivity.

(*So plan is this:
  1. If n1 and n2 are larger than depth, show that we can change n
  2. show we can change in adt_rep *)

    unfold adt_rep. 
    

 specialize (H m a eq_refl).


find_ts_in_ctx_iff
    Search find_ts_in_ctx.
    destruct (find_ts_in_ctx gamma (adt_name a)) as [ eqn : Hfind.

 eqn : Hfind.
 unfold mk_ts_map at 1.
  


  unfold sort_rect. simpl. intros m srts a m_in a_in Hn.

    

(*Going to prove 2 things:
  1. If we assume adts and constrs conditions hold, then we get [adt_interp_props]
  2. We can construct pd and pf st adts and constrs hold by assigning ADT_rep*)

(* constrs_disj: forall {m1 m2: mut_adt} {a1 a2: alg_datatype} {f1 f2: funsym} 
    (m1_in: mut_in_ctx m1 gamma) (m2_in: mut_in_ctx m2 gamma) 
    (a1_in: adt_in_mut a1 m1) (a2_in: adt_in_mut a2 m2) 
    (f1_in: constr_in_adt f1 a1) (f2_in: constr_in_adt f2 a2) 
    {srts: list sort}
    (arg1: arg_list (domain (dom_aux pd)) (sym_sigma_args f1 srts))
    (arg2: arg_list (domain (dom_aux pd)) (sym_sigma_args f2 srts)),
    f1 <> f2 ->
    constr_rep gamma_valid pd pf 
    (Heq: domain (dom_aux pd) (funsym_sigma_ret f2 srts) = domain (dom_aux pd) (funsym_sigma_ret f1 srts)),
    f1 <> f2 ->
    pf pd f1 srts arg1 <> scast Heq (pf pd f2 srts arg2);*)


(*(*Suffices to state for single ADT since others do not even have same type
      TODO: maybe we need another condition that interps are separate*)
    constrs_disj: forall {m: mut_adt} {a: alg_datatype} {f1 f2: funsym} 
    (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) 
    (f1_in: constr_in_adt f1 a) (f2_in: constr_in_adt f2 a) 
    {srts: list sort}
    (a1: arg_list (domain (dom_aux pd)) (sym_sigma_args f1 srts))
    (a2: arg_list (domain (dom_aux pd)) (sym_sigma_args f2 srts)),
    f1 <> f2 ->
    pf pd f1 srts a1 <> pf pd f2 srts a2*)

