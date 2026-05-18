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

Definition adt_rep pd a srts := ((domain pd) (s_cons (adt_name a) srts)).

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
          s_cons (adt_name t') srts), 
        i < length (s_args c) ->
      (*If nth i a has type adt_rep ..., then P holds of it*)
      P t' t_in' (dom_cast _ Heq (hnth i a s_int (dom_int _)))
      ) ->
    P t t_in x
    ),
    forall t t_in (x: adt_rep pd t srts), P t t_in x;
  }.
(* 
Require Import IndTypes.


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
Admitted. *)

Require Import IndTypes. (*TODO: move get_nond_vtys?*)

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


Set Bullet Behavior "Strict Subproofs".

Lemma list_map_map_In_le {A: Type} (f: A -> nat) {l: list A} {x: A}:
  In x l ->
  f x <= list_max (map f l).
Proof.
  intros Hin.
  pose proof (list_max_le (map f l) (list_max (map f l))) as [Hmax _].
  specialize (Hmax (ltac:(lia))).
  rewrite Forall_map, Forall_forall in Hmax.
  auto.
Qed. 


(*First, the depth measure:*)

Section TestDepth.

(*To avoid case analysis*)
Definition is_def_mut (d: def) : option mut_adt :=
  match d with
  | datatype_def m => Some m
  | _ => None
  end.


(*Mutually recursive on typesyms and types*)
Fixpoint size_ts (gamma: context) (ts: typesym) :=
  match gamma with
  | nil => 0
(*   | abs_type t :: g' => if typesym_eq_dec ts t then 1 else size_ts g' ts *)
  | d :: g' =>
    match is_def_mut d with
    | Some m =>
      if in_dec typesym_eq_dec ts (typesyms_of_mut m) then
      let fix size_ty (t: vty) : nat :=
        match t with
        | vty_real => 0
        | vty_int => 0
        | vty_var _ => 0 (*TODO*)
        | vty_cons ts tys => 1 + size_ts g' ts + list_max (map size_ty tys) (*Crucial: only nonind types!*)
        end in 
      1 + sum (map (fun x => size_ts g' (fst x) + list_max (map size_ty (snd x))) (mut_ts_pairs (adts m)))
      else size_ts g' ts
    | None => size_ts g' ts
    end
  end.

Fixpoint size_ty (gamma: context) (t: vty) : nat :=
  match t with
  | vty_real => 0
  | vty_int => 0
  | vty_var _ => 0
  | vty_cons ts tys => 1 + size_ts gamma ts + list_max (map (size_ty gamma) tys) (*Crucial: only nonind types!*)
  end.

Lemma size_ty_cons gamma ts tys:
  size_ty gamma (vty_cons ts tys) = 1 + size_ts gamma ts + list_max (map (size_ty gamma) tys).
Proof. reflexivity. Qed.

Definition size_tys (gamma: context) (tys: list vty) : nat :=
  list_max (map (size_ty gamma) tys).

Lemma size_ts_rewrite gamma ts:
  size_ts gamma ts =
  match gamma with
  | nil => 0
  | d :: g' =>
    match is_def_mut d with
    | Some m =>
(*   | abs_type t :: g' => if typesym_eq_dec ts t then 1 else size_ts g' ts *)
      if in_dec typesym_eq_dec ts (typesyms_of_mut m) then
        1 + sum (map (fun x => size_ts g' (fst x) + list_max (map (size_ty g') (snd x))) (mut_ts_pairs (adts m)))
      else size_ts g' ts
    | None => size_ts g' ts
    end
  end.
Proof.
  destruct gamma; simpl; auto.
  destruct (is_def_mut d); auto.
  destruct (in_dec typesym_eq_dec ts (typesyms_of_mut m)); auto.
  f_equal. f_equal.
  apply map_ext. intros a. f_equal. f_equal.
  apply map_ext. intros b.
  induction b; simpl; auto. do 3 f_equal.
  apply map_ext_in. intros x Hinx.
  rewrite Forall_forall in H. auto.
Qed.

(*And the sort version*)
Fixpoint size_sort (gamma: context) (s: sort) : nat :=
  match s with
  | s_int => 0
  | s_real => 0
  | s_cons ts srts => 1 + size_ts gamma ts + list_max (map (size_sort gamma) srts)
  end.

Definition size_sorts gamma srts := list_max (map (size_sort gamma) srts).

(*We need a few results*)
Lemma size_sorts_cons_bound gamma ts srts:
  size_sorts gamma srts < size_sort gamma (s_cons ts srts).
Proof.
  simpl. unfold size_sorts. lia.
Qed.

Lemma sort_size_in gamma {s srts}:
  In s srts ->
  size_sort gamma s <= size_sorts gamma srts.
Proof.
  intros Hin. unfold size_sorts. apply list_map_map_In_le. auto.
Qed.

Lemma ty_size_in gamma {t tys}:
  In t tys ->
  size_ty gamma t <= size_tys gamma tys.
Proof.
  intros Hin. unfold size_tys. apply list_map_map_In_le. auto.
Qed.

(*We need a bound on substitution: since this calculates depth (i.e the max chain of 
  typesym size-sums), this is bounded by the sum of the original tys and the substituted sorts
  (since sorts are substituted at a leaf)*)
Lemma size_subst_single gamma params srts ty:
  size_sort gamma (ty_subst_s params srts ty) <= size_ty gamma ty + size_sorts gamma srts.
Proof.
  induction ty as [| | x | ts tys IH]; simpl; try lia.
  - unfold ty_subst_s. simpl.
    destruct (ty_subst_fun_cases params srts s_int x) as [Hin | Hint].
    + apply sort_size_in; auto.
    + rewrite Hint. simpl. lia.
  - assert (list_max (map (size_sort gamma) (map (v_subst (ty_subst_fun params srts s_int)) tys)) <=
      list_max (map (size_ty gamma) tys) + size_sorts gamma srts); [|lia].
    apply list_max_le. rewrite !Forall_map. rewrite Forall_forall in IH |- *. intros x Hinx.
    specialize (IH x Hinx). unfold ty_subst_s in IH.
    pose proof (ty_size_in gamma Hinx) as Hle. unfold size_tys in Hle. lia.
Qed.

Lemma size_subst gamma params srts tys:
  size_sorts gamma (map (ty_subst_s params srts) tys) <= size_tys gamma tys + size_sorts gamma srts.
Proof.
  unfold size_sorts at 1. apply list_max_le.
  rewrite !Forall_map, Forall_forall. intros x Hinx.
  pose proof (size_subst_single gamma params srts x) as Hd.
  pose proof (ty_size_in gamma Hinx). lia.
Qed.

(*TODO: prove something like: for (ts, tys) in (mut_ts_pairs), ts and all typesyms in tys appear
  earlier in gamma*)

(*Need an assumption about our types - no nested recursion (TODO: add to typing/valid_context)*)
(* Lemma size_ty_cons_not_mut g d (Hd: is_def_mut d = None):
  forall ty, size_ty (d :: g) ty = size_ty g ty.
Proof.
  intros ty. induction ty; simpl; auto. *)

Lemma size_ts_not_mut g d (Hd: is_def_mut d = None):
  forall ts, size_ts (d :: g) ts = size_ts g ts.
Proof.
  intros ts. rewrite size_ts_rewrite. rewrite Hd. auto.
Qed.

Lemma mut_ts_pairs_in {m ts tys}:
  In (ts, tys) (mut_ts_pairs (adts m)) ->
  exists a c, adt_in_mut a m /\ constr_in_adt c a /\ In (vty_cons ts tys) (get_nonind_vtys (adts m) (s_args c)).
Proof.
  unfold mut_ts_pairs. rewrite in_concat. intros [l [Hinl Hint]].
  rewrite in_map_iff in Hinl. destruct Hinl as [a [Hl Hina]].
  subst. unfold adt_ts_pairs in Hint. rewrite in_concat in Hint.
  destruct Hint as [l [Hinl Hint]]. rewrite in_map_iff in Hinl.
  destruct Hinl as [c [Hl Hinc]]. subst.
  unfold funsym_ts_pairs in Hint. rewrite in_omap_iff in Hint.
  destruct Hint as [ty [Hinty Hty]]. unfold vty_ts_pair in Hty.
  destruct ty; try discriminate. inversion Hty; subst. clear Hty.
  exists a. exists c. split_all; auto.
  - apply In_in_bool; auto.
  - apply constr_in_adt_eq; auto.
Qed.

(*If (ts, tys) is in the [mut_ts_pairs] list, ts cannot be an adt in m*)
Lemma mut_ts_pairs_notin_ts {m ts tys}:
  In (ts, tys) (mut_ts_pairs (adts m)) ->
  ~ In ts (typesyms_of_mut m).
Proof.
  intros Hin.
  destruct (mut_ts_pairs_in Hin) as [a [c [a_in [c_in Hinty]]]].
  unfold get_nonind_vtys in Hinty.
  rewrite in_filter in Hinty.
  destruct Hinty as [Hneq Hint].
  unfold typesyms_of_mut.
  unfold ts_in_mut_list in Hneq.
  intros Hin'. apply In_in_bool with (eq_dec := typesym_eq_dec) in Hin'.
  rewrite Hin' in Hneq. discriminate.
Qed.

(*If (ts, tys) is in the [mut_ts_pairs] list, no adt from m appears in tys
  Contradicts non-nesting (NOTE: this is where we need the hypothesis)*)
Lemma mut_ts_pairs_not_tys {gamma m ts tys ty}
  (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma):
  In (ts, tys) (mut_ts_pairs (adts m)) ->
  In ty tys ->
  forall ts, In ts (typesyms_of_mut m) -> ~ (typesym_in_ty ts ty).
Proof.
  (*Super tedious and not interesting*)
  intros Hin Hinty.
  destruct (mut_ts_pairs_in Hin) as [a [c [a_in [c_in Hintys]]]].
  intros ts' Hints' Hinty'.
  pose proof (gamma_all_nonnest gamma_valid _ m_in) as Hnonnest.
  unfold nonnest in Hnonnest.
  unfold is_true in Hnonnest; rewrite forallb_forall in Hnonnest.
  specialize (Hnonnest a). prove_hyp Hnonnest. { apply in_bool_In in a_in; auto. }
  rewrite forallb_forall in Hnonnest. specialize (Hnonnest c).
  prove_hyp Hnonnest. { apply constr_in_adt_eq; auto. }
  unfold nonnest_list in Hnonnest.
  rewrite forallb_forall in Hnonnest. specialize (Hnonnest (vty_cons ts tys)).
  prove_hyp Hnonnest. { unfold get_nonind_vtys in Hintys. rewrite in_filter in Hintys. apply Hintys. }
  rewrite forallb_forall in Hnonnest. specialize (Hnonnest ts' Hints'). unfold ts_nested in Hnonnest.
  rewrite negb_true_iff, existsb_false in Hnonnest.
  rewrite Forall_forall in Hnonnest. specialize (Hnonnest _ Hinty). rewrite Hnonnest in Hinty'; discriminate.
Qed.

Lemma mut_ts_pairs_in_ctx_valid_type {gamma m ts tys}
  (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma):
  In (ts, tys) (mut_ts_pairs (adts m)) ->
  valid_type gamma (vty_cons ts tys).
Proof.
  intros Hin. destruct (mut_ts_pairs_in Hin) as [a [c [a_in [c_in Hintys]]]].
  pose proof (wf_context_full _ (valid_context_wf _ gamma_valid)) as [Hwf _].
  Search funsyms_of_context.
  pose proof (constrs_in_funsyms m_in a_in c_in) as Hinc.
  rewrite Forall_forall in Hwf. specialize (Hwf _ Hinc).
  unfold wf_funsym in Hwf.
  rewrite Forall_forall in Hwf.
  unfold get_nonind_vtys in Hintys. rewrite in_filter in Hintys.
  destruct Hintys as [Hnotmut Hintys].
  specialize (Hwf (vty_cons ts tys) (ltac:(simpl; auto))). apply Hwf.
Qed.

Lemma mut_ts_pairs_ts_in_ctx {gamma m ts tys}
  (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma):
  In (ts, tys) (mut_ts_pairs (adts m)) ->
  In ts (sig_t gamma).
Proof.
  intros Hin. pose proof (mut_ts_pairs_in_ctx_valid_type gamma_valid m_in Hin) as Hval.
  inversion Hval. auto.
Qed.

(*TODO: move*)
Lemma valid_type_typesym_in_ty {gamma ts s}:
  valid_type gamma s ->
  typesym_in_ty ts s ->
  In ts (sig_t gamma).
Proof.
  induction s as [| | x | ts1 tys IH]; try discriminate.
  intros Hval. simpl. inversion Hval; subst. rewrite Forall_forall in IH.
  destruct (typesym_eq_dec ts1 ts); simpl; subst; auto.
  unfold is_true. rewrite existsb_exists. intros [t [Hint Hints]].
  apply (IH t); auto.
Qed.

Lemma mut_ts_pairs_in_tys_in_ctx {gamma m ts tys}
  (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma):
  In (ts, tys) (mut_ts_pairs (adts m)) ->
  forall ts1 s, In s tys -> typesym_in_ty ts1 s -> In ts1 (sig_t gamma).
Proof.
  intros Hin. pose proof (mut_ts_pairs_in_ctx_valid_type gamma_valid m_in Hin) as Hval.
  inversion Hval; subst. intros ts1 s Hins Hints1.
  assert (Hvals: valid_type gamma s) by auto.
  apply (valid_type_typesym_in_ty Hvals); auto.
Qed.

(*Here is where we need the well-founded result: we define only in terms of smaller contexts,
  but this is OK because we look only at nonrecursive references, which must be defined earlier*)
Lemma size_ts_eq gamma ts:
  valid_context gamma ->
  size_ts gamma ts =
  match (find_ts_in_ctx gamma ts) with
  | Some (m, a) => 1 + sum (map (fun x => size_ts gamma (fst x) + list_max (map (size_ty gamma) (snd x))) (mut_ts_pairs (adts m)))
  | None => 0
  end.
Proof.
  intros gamma_valid. revert ts. 
  induction gamma_valid as [| d g' Hval IH Hwf1 Hwf2 Hdisj Hnodup Hne Hconstrs Hdef]; auto.
  intros ts.
  rewrite size_ts_rewrite.
  assert (Hval': valid_context (d :: g')) by (constructor; auto).
  destruct (is_def_mut d) as [m|] eqn : Hmut.
  2: {
    (*Easier case: not a mutual type*)
    assert (Hfind: find_ts_in_ctx (d :: g') ts = find_ts_in_ctx g' ts). { destruct d; auto. discriminate. }
    rewrite Hfind, IH. clear Hfind.
    destruct (find_ts_in_ctx g' ts) as [[m' a']|] eqn : Hfind; auto.
    f_equal. f_equal.
    assert (Htys: forall ty, size_ty (d :: g') ty = size_ty g' ty).
    {
      induction ty as [| | x | ts' tys IHty]; auto.
      rewrite !size_ty_cons. f_equal.
      - f_equal. apply size_ts_not_mut; auto.
      - f_equal. apply map_ext_in. rewrite Forall_forall in IHty. auto.
    }
    apply map_ext. intros a. symmetry. f_equal; auto.
    - apply size_ts_not_mut; auto.
    - f_equal. apply map_ext. auto.
  }
  (*Some results helpful for recursive cases. 1. If ts' not in m,
    then adding d does not change the size of ts' (TODO: separate lemmas?)*)
  assert (Hnotints: forall ts' (Hnotin: ~ In ts' (typesyms_of_mut m)),
        size_ts g' ts' = size_ts (d :: g') ts').
  { intros ts1 Hnotin1. rewrite (size_ts_rewrite (d :: g')), Hmut.
    destruct (in_dec typesym_eq_dec ts1 (typesyms_of_mut m)); auto.
    contradiction.
  }
  (*2: If no ts in m appears in ty, then size_ty is unaffected by adding d*)
  assert (Hnotinty: forall ty
    (Hnotin: forall ts : typesym, In ts (typesyms_of_mut m) -> ~ is_true (typesym_in_ty ts ty)),
    size_ty g' ty = size_ty (d :: g') ty).
  {
    intros ty'; induction ty' as [| | x | ts1 tys1 IHty]; auto.
    intros Hnotin'. rewrite !size_ty_cons, <- !Nat.add_assoc. f_equal.
    f_equal.
    - apply Hnotints. intros C. apply (Hnotin' ts1 C). simpl. destruct (typesym_eq_dec ts1 ts1); auto.
    - f_equal. apply map_ext_in. intros x Hinx.
      rewrite Forall_forall in IHty. apply IHty; auto. intros ts2 Hints2 C.
      apply (Hnotin' ts2 Hints2). simpl. apply orb_true_iff. right.
      rewrite existsb_exists. exists x. auto.
  }
  destruct (in_dec typesym_eq_dec ts (typesyms_of_mut m)) as [Hints | Hnotin].
  - (*Case 1: typesym is in mutual type*)
    assert (m_in: mut_in_ctx m (d :: g')). { apply mut_in_ctx_eq.
      simpl. destruct d; try discriminate. inversion Hmut; subst. simpl; auto. }
    unfold typesyms_of_mut in Hints. rewrite in_map_iff in Hints.
    destruct Hints as [a [Hts Hina]]. subst ts.
    assert (a_in: adt_in_mut a m). { apply In_in_bool; auto. } clear Hina.
    assert (Hfind: find_ts_in_ctx (d :: g') (adt_name a) = Some (m, a)). {
      apply find_ts_in_ctx_iff; auto.
    }
    rewrite Hfind.
    f_equal. f_equal.
    (*Now we prove that size_ty and size_ts are the same BECAUSE no types in (mut_ts_pairs) can be in d*)
    apply map_ext_in. intros [ts' tys'] Hin. simpl fst. simpl snd. f_equal.
    + (*Idea: we know that no typesym in d appears in the typesym*)
      apply Hnotints. apply (mut_ts_pairs_notin_ts Hin); auto. (*contradicts only nonind tys*)
    + (*And similar for the tys*)
      f_equal. apply map_ext_in. intros ty Hinty.
      apply Hnotinty.  intros ts Hints.
      apply (mut_ts_pairs_not_tys Hval' m_in Hin Hinty); auto.
  - (*Case 2: typesym not in mutual type*)
    assert (Hfind: find_ts_in_ctx (d :: g') ts = find_ts_in_ctx g' ts). {
      unfold find_ts_in_ctx. simpl. destruct d; try discriminate. inversion Hmut; subst.
      simpl. destruct (find_ts_in_mut ts m) eqn : Hfind; auto.
      exfalso. apply find_ts_in_mut_some in Hfind.
      destruct Hfind; subst. apply Hnotin. unfold typesyms_of_mut.
      apply in_map. apply in_bool_In in H; auto.
    }
    rewrite Hfind, IH.
    clear Hfind.
    destruct (find_ts_in_ctx g' ts) as [[m1 a1]|] eqn : Hfind; auto.
    f_equal. f_equal.
    (*Now we have a similar proof, but now we know that because they are defined before,
      they can only refer to names that came before (TODO: prove)*)
    apply find_ts_in_ctx_some in Hfind. destruct Hfind as [m1_in [a1_in Hts]].
    (*Common in both cases: anything previously defined in the context cannot
      overlap with a definition in m*)
    assert (Hdisj': forall ts', In ts' (sig_t g') -> ~ In ts' (typesyms_of_mut m)).
    {
      intros ts' Hints'.
      assert (Hinid: In (ts_name ts') (idents_of_context g')). {
        apply sig_t_in_idents. apply in_map. auto.
      }
      intros Hints2.
      apply (Hdisj (ts_name ts')). split; auto.
      destruct d; try discriminate. inversion Hmut; subst. unfold idents_of_def; simpl.
      rewrite in_app_iff. right. apply in_map; auto.
    }
    apply map_ext_in. intros [ts' tys'] Hin. simpl fst. simpl snd. f_equal.
    + apply Hnotints. (*by [mut_ts_pairs_ts_in_ctx], ts' is in sig_t of g',
      so it will contradict disjointness*)
      pose proof (mut_ts_pairs_ts_in_ctx Hval m1_in Hin) as Hints.
      apply Hdisj'; auto.
    + (*Similarly, no ts in m can appear in tys'*) f_equal. apply map_ext_in. intros a Hina.
      apply Hnotinty.
      intros ts1 Hints1 Hinty.
      apply (Hdisj' ts1); auto.
      apply (mut_ts_pairs_in_tys_in_ctx Hval m1_in Hin _ _ Hina); auto.
Qed.

(* 
Lemma size_ts_rewrite gamma ts:
  size_ts gamma ts =
  match gamma with
  | nil => 0
  | abs_type t :: g' => if typesym_eq_dec ts t then 1 else size_ts g' ts
  | datatype_def m :: g' => if in_dec typesym_eq_dec ts (typesyms_of_mut m) then
      1 + sum (map (fun x => size_ty g' (vty_cons (fst x) (snd x))) (mut_ts_pairs (adts m)))
    else size_ts g' ts
  | _ :: g' => size_ts g' ts
  end.
 *)

Lemma in_sum_le {A: Type} (f: A -> nat) {l: list A} {x: A}:
  In x l ->
  f x <= sum (map f l).
Proof.
  induction l as [| h t IH]; simpl; auto; [contradiction|].
  intros [Hh | Ht]; subst; try lia. specialize (IH Ht); lia.
Qed.

(*Now this is why we needed the convoluted method of computing the size of a typesym:
  suppose a is in the typesyms of m. Then for any
  for any (ts, tys') in [mut_ts_pairs m], we have that |a| > |ts| + max | tys'| *)
Lemma mut_ts_pairs_size {gamma m a ts' tys'}
  (gamma_valid: valid_context gamma)
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hin: In (ts', tys') (mut_ts_pairs (adts m))):
  size_ts gamma ts' + size_tys gamma tys' < size_ts gamma (adt_name a).
Proof.
  rewrite (size_ts_eq gamma (adt_name a)) by assumption.
  assert (Hfind: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
    apply find_ts_in_ctx_iff; auto. }
  rewrite Hfind.
  pose proof (in_sum_le (fun x => size_ts gamma (fst x) + list_max (map (size_ty gamma) (snd x))) Hin) as Hle.
  simpl in Hle. unfold size_tys at 1. lia.
Qed.

Lemma size_sort_cons gamma t srts:
  size_sort gamma (s_cons t srts) = 1 + size_ts gamma t + size_sorts gamma srts.
Proof.
  unfold size_sorts. reflexivity.
Qed.


Lemma mut_ts_pairs_subst_smaller {gamma m a} (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) ts' tys' srts
  (Hin: In (ts', tys') (mut_ts_pairs (adts m))):
  size_sort gamma (s_cons ts' (map (ty_subst_s (m_params m) srts) tys')) <
  size_sort gamma (s_cons (adt_name a) srts).
Proof.
  rewrite !size_sort_cons.
  pose proof (size_subst gamma (m_params m) srts tys').
  pose proof (mut_ts_pairs_size gamma_valid m_in a_in Hin). lia.
Qed.

End TestDepth.


Definition ts_map_to_pd (f: typesym -> list sort -> Set) : sort -> Set :=
  fun s =>
  match s with
  | s_int => Z
  | s_real => R
  | s_cons ts srts => f ts srts
  end.

(* Lemma ts_map_to_pd_domain f:
   *)

Require Import IndTypes.

Definition adt_rep' (m: mut_adt) (srts: list sort) (d1 d2: sort -> Set) (a: alg_datatype)
  (a_in: adt_in_mut a m) :=
  mk_adts (var_map m srts d1) (typesym_map m srts d2) (adts m) (get_idx adt_dec a (adts m) a_in).

Fixpoint mk_ts_map (gamma: context) (pd: sort -> Set) (n: nat) (ts: typesym) (srts: list sort) : Set :=
  match n with
  | O => pd (s_cons ts srts)
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
    | None => fun _ => pd (s_cons ts srts)
    end eq_refl
    end.

Definition mk_pd_aux (gamma: context) (pd: sort -> Set) (n: list sort -> nat) (s: sort) : Set :=
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n srts) ts srts) s.

(*Idea: should be invariant as long as n larger than max depth of sort*)
Fixpoint sort_depth (n: typesym -> nat) (s: sort) : nat :=
  match s with
  | s_int => 1
  | s_real => 1
  | s_cons ts srts => 1 + n ts * list_max (map (sort_depth n) srts)
  end.

Definition sorts_depth n (s: list sort) : nat := list_max (map (sort_depth n) s).


Definition funsym_vars (f: funsym) : aset typevar :=
  aset_big_union type_vars (s_args f).
Definition adt_vars (a: alg_datatype) : aset typevar :=
  aset_big_union funsym_vars (adt_constr_list a).
Definition mut_vars (l: list (alg_datatype)) : aset typevar :=
  aset_big_union adt_vars l.


(*The total bound, with var bound given by n*)
(* Fixpoint vty_size (n: typesym -> nat) (v: vty) :=
  match v with
  | vty_int => 1
  | vty_real => 1
  | vty_var _ => 1
  | vty_cons t ts => 1 + (n t) * list_max (map (vty_size n) ts)
  end.


Definition constr_depth (gamma:context) :=
  1 + list_max (map (fun x => 1 + list_max (map ((vty_size (fun ts => index typesym_eq_dec ts (typesyms_of_context gamma))))
  (snd x))) (mut_ts_pairs (adts_of_context gamma))).

Lemma constr_depth_pos gamma: constr_depth gamma >= 1.
Proof. unfold constr_depth. lia. Qed.

Definition depth_aux gamma s :=
  sort_depth (fun ts => (index typesym_eq_dec ts (typesyms_of_context gamma)) * (constr_depth gamma)) s.

Definition depth gamma srts :=
  list_max (map (depth_aux gamma) srts). *)


Fixpoint depth_alt gamma s :=
   match s with
  | s_int => 0
  | s_real => 0
  | s_cons ts srts =>
       1 + ((index typesym_eq_dec ts (typesyms_of_context gamma))) + 
      list_max (map (depth_alt gamma) srts)
      (* max ((index typesym_eq_dec ts (typesyms_of_context gamma)))
      (list_max (map (depth_alt gamma) srts)) *)
  end.

Definition depth gamma srts :=
  list_max (map (depth_alt gamma) srts).


Definition mk_ts_full gamma pd ts srts :=
  mk_ts_map gamma pd (size_sorts gamma srts) ts srts.

Print index.

Definition max_depth gamma srts :=
  3 + list_max (map (size_ts gamma) (typesyms_of_context gamma)) + size_sorts gamma srts.
(*   3 + (length (typesyms_of_context gamma)) + max (length (typesyms_of_context gamma)) (depth gamma srts). *)

Lemma index_leq_length {A: Type} eq_dec (x: A) (l: list A):
  index eq_dec x l <= length l.
Proof.
  induction l; simpl; auto.
  destruct (eq_dec _ _); lia.
Qed.

(*TODO: move above*)
Lemma ts_notin_size {gamma ts}:
  ~ In ts (typesyms_of_context gamma) ->
  size_ts gamma ts = 0.
Proof.
  intros Hnotin. generalize dependent ts.
  induction gamma as [| d g' IH]; auto.
  intros ts Hnotin.
  rewrite size_ts_rewrite.
  unfold typesyms_of_context in *.
  simpl in Hnotin.
  destruct (is_def_mut d) as [m1|] eqn : Hmut.
  - destruct d; inversion Hmut; subst.
    simpl in Hnotin. rewrite in_app_iff in Hnotin.
    not_or Hnotin.
    destruct (in_dec typesym_eq_dec ts (typesyms_of_mut m1)); auto.
    contradiction.
  - destruct d; try discriminate; simpl in Hnotin; auto.
Qed. 

Lemma max_depth_max gamma:
  forall ts srts, 1 + size_sort gamma (s_cons ts srts) < max_depth gamma srts.
Proof.
  intros ts srts. unfold max_depth. simpl. unfold size_sorts.
  assert (Hsz: size_ts gamma ts <= list_max (map (size_ts gamma) (typesyms_of_context gamma))); [|lia].
  destruct (in_dec typesym_eq_dec ts (typesyms_of_context gamma)).
  - apply list_map_map_In_le; auto.
  - rewrite ts_notin_size; auto. lia.
Qed. 

Definition mk_pd (gamma: context) (pd: sort -> Set) (s: sort) : Set :=
  mk_pd_aux gamma pd (fun srts => max_depth gamma srts) s.


(*pd with all typesym_to_sort set correctly to the corresponidng W-type*)
Definition pd_full (gamma: context) (pd: sort -> Set) := forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m),
    pd (s_cons (adt_name a) srts) =
    adt_rep m srts pd a Hin.

Definition pd_full_aux (gamma: context) (pd: sort -> Set) (n: list sort -> nat) := 
    (forall ts srts1, 1 + size_sort gamma (s_cons ts srts1) < n srts1) ->
    forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m) ,
    pd (s_cons (adt_name a) srts) =
    adt_rep m srts pd a Hin.
(* 
(*TODO: move this*)
Print mk_adts.

(*Get vars in mutual datatype (note: by well-typing, should be in m_params m)*)
Print alg_datatype.

Print funsym.
Print fpsym.
Print f_sym. *)


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


Print sort_depth.
Lemma sort_depth_cons n ts srts:
  sort_depth n (s_cons ts srts) = 1 + n ts * sorts_depth n srts.
Proof. reflexivity. Qed.

(*Hmm, not sure if this is true*)
(*TODO: can remove 1+ if we make depth of int 0 (I think)*)
(* Lemma sort_depth_subst n params srts x:
  sort_depth n (ty_subst_s params srts x) <= 1 + (vty_size n x) * (sorts_depth n srts).
Proof.
  induction x as [| | x | ts tys IH]; simpl; try lia.
  - unfold ty_subst_s. simpl.
    destruct (ty_subst_fun_cases params srts s_int x) as [Hin | Hint].
    + rewrite Nat.add_0_r. unfold sorts_depth.
      apply (list_map_map_In_le (sort_depth n)) in Hin. lia.
    + rewrite Hint. simpl. lia.
  - apply le_n_S. rewrite map_map.
    assert (list_max (map (fun x : vty => sort_depth n (v_subst (ty_subst_fun params srts s_int) x)) tys) <= 
      1 + list_max (map (vty_size n) tys) * sorts_depth n srts).
    { apply list_max_le. rewrite Forall_map. revert IH. apply Forall_impl_strong. intros a Hina Hle.
      unfold ty_subst_s in Hle.
      assert (vty_size n a <= list_max (map (vty_size n) tys)). {
        apply list_map_map_In_le. auto.
      }
      nia.
    }
    Admitted. *)
(*     
Lemma sorts_depth_sigma gamma m ts tys (m_in: mut_in_ctx m gamma) n srts
  (Hin: In (ts, tys) (mut_ts_pairs (adts m))):
  sorts_depth n (map (ty_subst_s (m_params m) srts) tys) <=
  1 + constr_depth gamma * sorts_depth n srts.
Proof.
  unfold sorts_depth.
  rewrite !map_map.
  apply list_max_le.
  rewrite Forall_map, Forall_forall. intros x Hinx.



  Search list_max (_ <= _).

 
  induction tys as [| t1 tys IHty]; simpl; try lia. *)
  


(*What about: in typesym to sort (ONLY) can be lexicographic
  no, not true -only at top level
  should depend on index
  cannot keep going forever - idea: eventually get to ADT that has no previously defined typesyms*)


(*Test*)
Require Import Stdlib.Arith.Wf_nat.


(* 

Lemma mut_ts_pairs_subst_smaller {gamma m a} (gamma_valid: valid_context gamma) n (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) ts' tys' srts
  (Hn: n >= depth_tys gamma 
  (Hin: In (ts', tys') (mut_ts_pairs (adts m))):



Lemma depth_alt_in gamma n {s srts}:
  In s srts ->
  depth_alt gamma n s <= depth gamma n srts.
Proof.
  intros Hin. unfold depth. 
  apply list_map_map_In_le; auto.
Qed. *)

  

(* 



Fixpoint depth_alt gamma n s :=
   match s with
  | s_int => 0
  | s_real => 0
  | s_cons ts srts =>
       1 + (n * ((index typesym_eq_dec ts (typesyms_of_context gamma)))) + 
      list_max (map (depth_alt gamma n) srts)
      (* max ((index typesym_eq_dec ts (typesyms_of_context gamma)))
      (list_max (map (depth_alt gamma) srts)) *)
  end.

Definition depth gamma n srts :=
  list_max (map (depth_alt gamma n) srts). *)
(* 
Lemma depth_alt_cons_bound gamma n ts srts:
  depth gamma n srts < depth_alt gamma n (s_cons ts srts).
Proof.
  simpl.
  unfold depth. lia.
Qed.

Lemma depth_alt_in gamma n {s srts}:
  In s srts ->
  depth_alt gamma n s <= depth gamma n srts.
Proof.
  intros Hin. unfold depth. 
  apply list_map_map_In_le; auto.
Qed. *)
(* 
Fixpoint depth_ty (gamma: context) n (ty: vty) : nat :=
  match ty with
  | vty_cons ts tys => 
    1 + (n * index typesym_eq_dec ts (typesyms_of_context gamma)) +
      (list_max (map (depth_ty gamma n) tys))
      (* Init.Nat.max (index typesym_eq_dec ts (typesyms_of_context gamma))
        (list_max (map (depth_ty gamma) tys)) *)
  | _ => 0
  end.

Definition depth_tys gamma n tys :=
  list_max (map (depth_ty gamma n) tys).

Lemma depth_ty_in gamma n {t tys}:
  In t tys ->
  depth_ty gamma n t <= depth_tys gamma n tys.
Proof.
  intros Hin. unfold depth. 
  apply list_map_map_In_le; auto.
Qed.


(*Let's just try*)
Lemma depth_subst_single gamma n params srts ty:
  depth_alt gamma n (ty_subst_s params srts ty) <= depth_ty gamma n ty + (depth gamma n srts).
Proof.
  induction ty as [| | x | ts tys IH]; simpl; try lia.
  - unfold ty_subst_s. simpl.
    destruct (ty_subst_fun_cases params srts s_int x) as [Hin | Hint].
    + apply depth_alt_in; auto.
    + rewrite Hint. simpl. lia.
  - assert (list_max (map (depth_alt gamma n) (map (v_subst (ty_subst_fun params srts s_int)) tys)) <=
      list_max (map (depth_ty gamma n) tys) + depth gamma n srts); [|lia].
    apply list_max_le. rewrite !Forall_map. rewrite Forall_forall in IH |- *. intros x Hinx.
    specialize (IH x Hinx). unfold ty_subst_s in IH.
    pose proof (depth_ty_in gamma n Hinx) as Hle. unfold depth_tys in Hle. lia.
Qed.

Lemma depth_subst gamma n params srts tys:
  depth gamma n (map (ty_subst_s params srts) tys) <= depth_tys gamma n tys + (depth gamma n srts).
Proof.
  unfold depth at 1. apply list_max_le.
  rewrite !Forall_map, Forall_forall. intros x Hinx.
  pose proof (depth_subst_single gamma n params srts x) as Hd.
  pose proof (depth_ty_in gamma n Hinx). lia.
Qed.

Lemma mut_ts_pairs_subst_smaller {gamma m a} (gamma_valid: valid_context gamma) n (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) ts' tys' srts
  (Hn: n >= depth_tys gamma 
  (Hin: In (ts', tys') (mut_ts_pairs (adts m))):
  depth_alt gamma n (s_cons ts' (map (ty_subst_s (m_params m) srts) tys')) <
  depth_alt gamma n (s_cons (adt_name a) srts).
Proof.
  simpl.
  assert (Hts: index typesym_eq_dec ts' (typesyms_of_context gamma) < 
    index typesym_eq_dec (adt_name a) (typesyms_of_context gamma)). { admit. }
  pose proof (depth_subst gamma n (m_params m) srts tys') as Hsubst.
  
  

  assert (Hsubst: (list_max (map (depth_alt gamma) (map (ty_subst_s (m_params m) srts) tys'))) <=
    max (list_max (map (depth_alt gamma) srts)) (list_max (map (depth_ty gamma) tys'))).
  { admit. }
  (*Problem: NOT index*)
  Print depth_alt.
  assert (Htys: (list_max (map (depth_ty gamma) tys') <= 
 *)
(*  Admitted. *)
(*Idea: index of ts' is smaller than index of ts, and indices in tys' MUST be 
      smaller than index of ts as well (by well-typed context)
      and obviously everythign in srts smaller than srts, so I think we are good
      *)
    (* apply PeanoNat.lt_S_n in Hn1, Hn2.
    assert ( Hindex: index typesym_eq_dec ts' (typesyms_of_context gamma) < 
      index typesym_eq_dec ts (typesyms_of_context gamma)). { admit. } *)
    (*Idea: (list_max (map (depth_alt gamma) (map (sigma m srts) tys'))) <=
      max (list_max (map (depth_alt gamma) srts)) (list_max (map (depth_vty gamma) tys'))
      by subst properties (maybe we need assumption about params in bounds but that is OK*)
    (*Then, have that (list_max (map (depth_vty gamma) tys') <= (index typesym_eq_dec ts') by 
        well-typing of constructors (need valid context) *)
    (*So, max (index ts') (max (list_map srts) (index ts')) = max (index ts') (max (list_map srts))*)
    (*And we know that index ts' < index ts', so the result follows*)
    (*I believe that this should work*)

(*Maybe: prove 2 things: non-dependent and dependent versions*)

Lemma mk_ts_map_invar_const {gamma} (gamma_valid: valid_context gamma) pd n1 n2 (s: sort):
  size_sort gamma s < n1 ->
  size_sort gamma s < n2 ->
  ts_map_to_pd (mk_ts_map gamma pd n1) s = ts_map_to_pd (mk_ts_map gamma pd n2) s.
Proof.
  generalize dependent n2. generalize dependent s. induction n1 as [| n1 IHn1].
  { intros; lia. }
  intros s [| n2]; [lia | intros Hn1 Hn2].
  destruct s as [| | ts srts]; simpl; auto.
  generalize dependent (find_ts_in_ctx_some gamma ts).
  destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind; auto.
  intros H. generalize dependent (proj1 (proj2 (H m a eq_refl))).
  specialize (H m a eq_refl). destruct H as [m_in [a_in Hts]].
  intros a_in'. assert (a_in' = a_in) by (apply bool_irrelevance); subst.
  (*TODO: separate lemma*) unfold adt_rep.
  assert (Hveq: (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n1))) = 
    (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n2)))). {
    (*This should be separate lemma*)
    apply functional_extensionality. intros x.
    unfold var_map. unfold domain. unfold sigma. simpl. unfold ty_subst_s.
    simpl. 
    destruct (ty_subst_fun_cases (m_params m) srts s_int x) as [Hin | Hd].
    + remember (ty_subst_fun (m_params m) srts s_int x) as t.
      destruct (sort_to_ty t) eqn : Hs; auto.
      { (*sort not var*) destruct t; simpl in Hs; discriminate. }
      simpl in Hn1, Hn2.
      pose proof (list_map_map_In_le (size_sort gamma) Hin).
      apply IHn1; lia.
      
(*       admit. *)
      (* unfold depth_aux in Hn1, Hn2.
      simpl in Hn1.
      simpl sort_depth in Hn1, Hn2.
      assert (Hn1': list_max (map (sort_depth (constr_depth gamma)) srts) < n1) by nia.
      assert (Hn2': list_max (map (sort_depth (constr_depth gamma)) srts) < n2) by nia.
      pose proof (list_map_map_In_le (sort_depth (constr_depth gamma)) Hin). *)
(*       apply IHn1; lia. *)
    + rewrite Hd; auto.
  }
  rewrite Hveq.
  (*Now prove typesym_map equality*)
  erewrite mk_adts_ext; [reflexivity|].
  intros ts' tys' Hin'. unfold typesym_map.
  (*So we know (if we change bounds) that sort depth is smaller*)
  unfold domain. simpl.
  specialize (IHn1 (s_cons ts' (map (sigma m srts) tys')) n2).
(*   simpl sort_depth in Hn1, Hn2. *)
  (*Know here that ts' is NON-recursive instance - so it MUST appear BEFORE in gamma*)
(*  apply PeanoNat.lt_S_n in Hn1, Hn2. *)
  pose proof (mut_ts_pairs_subst_smaller gamma_valid m_in a_in ts' tys' srts Hin').
  apply IHn1; unfold sigma; lia.
Qed.

(*Definition depth_func (gamma: context) (s: sort)*)
(*TODO: need to figure out if other version (with fixed nat) is enough?*)
Lemma mk_ts_map_invar {gamma} (gamma_valid : valid_context gamma) pd n1 n2 (s: sort):
  (* (forall srts, 0 < n1 srts) ->
  (forall srts, 0 < n2 srts) -> *)
  (forall ts srts, size_sort gamma (s_cons ts srts) < n1 srts) ->
  (forall ts srts, size_sort gamma (s_cons ts srts) < n2 srts) ->
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n1 srts) ts srts) s = 
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n2 srts) ts srts) s.
Proof.
  intros Hn1 Hn2. destruct s as [| | ts srts]; simpl; auto.
  pose proof (mk_ts_map_invar_const gamma_valid pd (n1 srts) (n2 srts) (s_cons ts srts)) as Heq.
  simpl ts_map_to_pd in Heq. apply Heq; auto.
Qed.


Lemma mk_ts_map_invar'  {gamma} (gamma_valid : valid_context gamma) pd n1 n2 (s: sort):
  (* (forall srts, 0 < n1 srts) ->
  (forall srts, 0 < n2 srts) -> *)
  (forall ts srts, size_sort gamma (s_cons ts srts) < n1 srts) ->
  (size_sort gamma s < n2) ->
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n1 srts) ts srts) s = 
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd n2 ts srts) s.
Proof.
  intros Hn1 Hn2. destruct s as [| | ts srts]; simpl; auto.
  pose proof (mk_ts_map_invar_const gamma_valid pd (n1 srts) n2 (s_cons ts srts)) as Heq.
  simpl ts_map_to_pd in Heq. apply Heq; auto.
Qed.
 (*  simpl.

   assert (Hn1' := Hn1 srts).
  assert (Hn2' := Hn2 srts).
  destruct (n1 srts) as [|n1'] eqn : Hn1s; [lia|].
  destruct (n2 srts) as [|n2'] eqn : Hn2s; [lia|].
  simpl.
  generalize dependent (find_ts_in_ctx_some gamma ts).
  destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind; auto.
  intros H. generalize dependent (proj1 (proj2 (H m a eq_refl))).
  specialize (H m a eq_refl). destruct H as [m_in [a_in Hts]].
  intros a_in'. assert (a_in' = a_in) by (apply bool_irrelevance). subst. 
  unfold adt_rep.


  revert n1 n2.
  remember (depth_alt gamma s) as n.
  generalize dependent s.
  induction n using lt_wf_ind.
  assert (IH: forall s: sort,
    depth_alt gamma s < n ->
    forall n1 n2,
    (forall srts, 0 < n1 srts) ->
    (forall srts, 0 < n2 srts) ->
    (*(forall srts : list sort, depth gamma srts < n1 srts) ->
    (forall srts : list sort, depth gamma srts < n2 srts) ->*)
    ts_map_to_pd (fun (ts : typesym) (srts : list sort) => mk_ts_map gamma pd (n1 srts) ts srts) s =
    ts_map_to_pd (fun (ts : typesym) (srts : list sort) => mk_ts_map gamma pd (n2 srts) ts srts) s).
  { intros s Hn. apply H with (m:=depth_alt gamma s); auto. }
  clear H.
  intros s Hn n1 n2 Hn1 Hn2. subst.
  destruct s as [| | ts srts]; simpl; auto.
  assert (Hn1' := Hn1 srts).
  assert (Hn2' := Hn2 srts).
  destruct (n1 srts) as [|n1'] eqn : Hn1s; [lia|].
  destruct (n2 srts) as [|n2'] eqn : Hn2s; [lia|].
  simpl.
  generalize dependent (find_ts_in_ctx_some gamma ts).
  destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind; auto.
  intros H. generalize dependent (proj1 (proj2 (H m a eq_refl))).
  specialize (H m a eq_refl). destruct H as [m_in [a_in Hts]].
  intros a_in'. assert (a_in' = a_in) by (apply bool_irrelevance). subst. 
  unfold adt_rep.
  assert (Hveq: (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n1'))) = 
    (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n2')))). {
    (*This should be separate lemma*)
    apply functional_extensionality. intros x.
    unfold var_map. unfold domain. unfold sigma. unfold ty_subst_s.
    simpl. 
    destruct (ty_subst_fun_cases (m_params m) srts s_int x) as [Hin | Hd].
    + remember (ty_subst_fun (m_params m) srts s_int x) as t.
      destruct (sort_to_ty t) eqn : Hs; auto.
      { (*sort not var*) destruct t; simpl in Hs; discriminate. }
      (*We have to change n1 and n2, but we use the fact that it is bounded (I hope)*)
      pose proof (depth_alt_in gamma Hin).
      pose proof (depth_alt_cons_bound gamma (adt_name a) srts).
      apply (IH t); auto; try lia.
    + rewrite Hd; auto.
  }
  rewrite Hveq.
  (*Now prove typesym_map equality*)
  erewrite mk_adts_ext; [reflexivity|].
  intros ts' tys' Hin'. unfold typesym_map.
  (*So we know (if we change bounds) that sort depth is smaller*)
  unfold domain. simpl.
  specialize (IH (s_cons ts' (map (sigma m srts) tys'))).
  simpl ts_map_to_pd in IH.
  assert (Hdepth: depth_alt gamma (s_cons ts' (map (sigma m srts) tys')) < depth_alt gamma (s_cons (adt_name a) srts)).
  {
    (*Idea: (list_max (map (depth_alt gamma) (map (sigma m srts) tys'))) <=
      max (list_max (map (depth_alt gamma) srts)) (list_max (map (depth_vty gamma) tys'))
      by subst properties (maybe we need assumption about params in bounds but that is OK*)
    (*Then, have that (list_max (map (depth_vty gamma) tys') <= (index typesym_eq_dec ts') by 
        well-typing of constructors (need valid context) *)
    (*So, max (index ts') (max (list_map srts) (index ts')) = max (index ts') (max (list_map srts))*)
    (*And we know that index ts' < index ts', so the result follows*)
    (*I believe that this should work*)
    admit.
  }
  specialize (IH Hdepth (fun _ => n1') (fun _ => n2')).
(*   simpl sort_depth in Hn1, Hn2. *)
  (*Know here that ts' is NON-recursive instance - so it MUST appear BEFORE in gamma*)
(*  apply PeanoNat.lt_S_n in Hn1, Hn2. *)
  apply IH; try lia.
Admitted. *)

(*NOTE: Working version (mod bound) but with bad hypothesis*)
(*
Lemma mk_ts_map_invar gamma pd n1 n2 (s: sort):
  (forall srts, depth_alt gamma s < n1 srts) ->
  (forall srts, depth_alt gamma s < n2 srts) ->
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n1 srts) ts srts) s = 
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n2 srts) ts srts) s.
Proof.
  revert n1 n2.
  remember (depth_alt gamma s) as n.
  generalize dependent s.
  induction n using lt_wf_ind.
  assert (IH: forall s: sort,
    depth_alt gamma s < n ->
    forall n1 n2,
    (forall srts : list sort, depth_alt gamma s < n1 srts) ->
    (forall srts : list sort, depth_alt gamma s < n2 srts) ->
    ts_map_to_pd (fun (ts : typesym) (srts : list sort) => mk_ts_map gamma pd (n1 srts) ts srts) s =
    ts_map_to_pd (fun (ts : typesym) (srts : list sort) => mk_ts_map gamma pd (n2 srts) ts srts) s).
  { intros s Hn. apply H; auto. }
  clear H.
  intros s Hn n1 n2 Hn1 Hn2. subst.
  destruct s as [| | ts srts]; simpl; auto.
  assert (Hn1' := Hn1 srts).
  assert (Hn2' := Hn2 srts).
  destruct (n1 srts) as [|n1'] eqn : Hn1s; [lia|].
  destruct (n2 srts) as [|n2'] eqn : Hn2s; [lia|].
  simpl.
  generalize dependent (find_ts_in_ctx_some gamma ts).
  destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind; auto.
  intros H. generalize dependent (proj1 (proj2 (H m a eq_refl))).
  specialize (H m a eq_refl). destruct H as [m_in [a_in Hts]].
  intros a_in'. assert (a_in' = a_in) by (apply bool_irrelevance). subst. 
  unfold adt_rep.
  assert (Hveq: (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n1'))) = 
    (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n2')))). {
    (*This should be separate lemma*)
    apply functional_extensionality. intros x.
    unfold var_map. unfold domain. unfold sigma. unfold ty_subst_s.
    simpl. 
    destruct (ty_subst_fun_cases (m_params m) srts s_int x) as [Hin | Hd].
    + remember (ty_subst_fun (m_params m) srts s_int x) as t.
      destruct (sort_to_ty t) eqn : Hs; auto.
      { (*sort not var*) destruct t; simpl in Hs; discriminate. }
      (*We have to change n1 and n2, but we use the fact that it is bounded (I hope)*)
      pose proof (depth_alt_in gamma Hin).
        pose proof (depth_alt_cons_bound gamma (adt_name a) srts).
      apply (IH t); auto; lia.
    + rewrite Hd; auto.
  }
  rewrite Hveq.
  (*Now prove typesym_map equality*)
  erewrite mk_adts_ext; [reflexivity|].
  intros ts' tys' Hin'. unfold typesym_map.
  (*So we know (if we change bounds) that sort depth is smaller*)
  unfold domain. simpl.
  specialize (IH (s_cons ts' (map (sigma m srts) tys'))).
  simpl ts_map_to_pd in IH.
  assert (Hdepth: depth_alt gamma (s_cons ts' (map (sigma m srts) tys')) < depth_alt gamma (s_cons (adt_name a) srts)).
  {
    (*Idea: (list_max (map (depth_alt gamma) (map (sigma m srts) tys'))) <=
      max (list_max (map (depth_alt gamma) srts)) (list_max (map (depth_vty gamma) tys'))
      by subst properties (maybe we need assumption about params in bounds but that is OK*)
    (*Then, have that (list_max (map (depth_vty gamma) tys') <= (index typesym_eq_dec ts') by 
        well-typing of constructors (need valid context) *)
    (*So, max (index ts') (max (list_map srts) (index ts')) = max (index ts') (max (list_map srts))*)
    (*And we know that index ts' < index ts', so the result follows*)
    (*I believe that this should work*)
    admit.
  }
  specialize (IH Hdepth (fun _ => n1') (fun _ => n2')).
(*   simpl sort_depth in Hn1, Hn2. *)
  (*Know here that ts' is NON-recursive instance - so it MUST appear BEFORE in gamma*)
(*  apply PeanoNat.lt_S_n in Hn1, Hn2. *)
  apply IH; try lia.
Admitted.*)

(* 
  - simpl in Hn1, Hn2 |- *.
    (*Idea: index of ts' is smaller than index of ts, and indices in tys' MUST be 
      smaller than index of ts as well (by well-typed context)
      and obviously everythign in srts smaller than srts, so I think we are good
      *)
    apply PeanoNat.lt_S_n in Hn1, Hn2.
    assert ( Hindex: index typesym_eq_dec ts' (typesyms_of_context gamma) < 
      index typesym_eq_dec ts (typesyms_of_context gamma)). { admit. }


      - pose proof (depth_alt_in gamma Hin).
        pose proof (depth_alt_cons_bound gamma (adt_name a) srts).
        lia.
      - intros _. 




 simpl.
      simpl in Hn1, Hn2.
      pose proof (list_map_map_In_le (depth_alt gamma) Hin).
      apply IHn1; lia.
      
(*       admit. *)
      (* unfold depth_aux in Hn1, Hn2.
      simpl in Hn1.
      simpl sort_depth in Hn1, Hn2.
      assert (Hn1': list_max (map (sort_depth (constr_depth gamma)) srts) < n1) by nia.
      assert (Hn2': list_max (map (sort_depth (constr_depth gamma)) srts) < n2) by nia.
      pose proof (list_map_map_In_le (sort_depth (constr_depth gamma)) Hin). *)
(*       apply IHn1; lia. *)
    + rewrite Hd; auto.
  }
  

 clear H.
  intros a_in. (*TODO: separate lemma*) unfold adt_rep.

  unfold mk_ts_map.
  
  Check PeanoNat.Nat.lt_wf_induction.
  Check Nat.strong_ind.

  generalize dependent n2. generalize dependent s. induction n1 as [| n1 IHn1].
  { intros; lia. }
  intros s [| n2]; [lia | intros Hn1 Hn2].
  destruct s as [| | ts srts]; simpl; auto.
  generalize dependent (find_ts_in_ctx_some gamma ts).
  destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind; auto.
  intros H. generalize dependent (proj1 (proj2 (H m a eq_refl))). clear H.
  intros a_in. (*TODO: separate lemma*) unfold adt_rep.
  assert (Hveq: (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n1))) = 
    (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n2)))). {
    (*This should be separate lemma*)
    apply functional_extensionality. intros x.
    unfold var_map. unfold domain. unfold sigma. simpl. unfold ty_subst_s.
    simpl. 
    destruct (ty_subst_fun_cases (m_params m) srts s_int x) as [Hin | Hd].
    + remember (ty_subst_fun (m_params m) srts s_int x) as t.
      destruct (sort_to_ty t) eqn : Hs; auto.
      { (*sort not var*) destruct t; simpl in Hs; discriminate. }
      simpl in Hn1, Hn2.
      pose proof (list_map_map_In_le (depth_alt gamma) Hin).
      apply IHn1; lia.
      
(*       admit. *)
      (* unfold depth_aux in Hn1, Hn2.
      simpl in Hn1.
      simpl sort_depth in Hn1, Hn2.
      assert (Hn1': list_max (map (sort_depth (constr_depth gamma)) srts) < n1) by nia.
      assert (Hn2': list_max (map (sort_depth (constr_depth gamma)) srts) < n2) by nia.
      pose proof (list_map_map_In_le (sort_depth (constr_depth gamma)) Hin). *)
(*       apply IHn1; lia. *)
    + rewrite Hd; auto.
  }
  rewrite Hveq.
  (*Now prove typesym_map equality*)
  erewrite mk_adts_ext; [reflexivity|].
  intros ts' tys' Hin'. unfold typesym_map.
  (*So we know (if we change bounds) that sort depth is smaller*)
  unfold domain. simpl.
  specialize (IHn1 (s_cons ts' (map (sigma m srts) tys')) n2).
(*   simpl sort_depth in Hn1, Hn2. *)
  (*Know here that ts' is NON-recursive instance - so it MUST appear BEFORE in gamma*)
(*  apply PeanoNat.lt_S_n in Hn1, Hn2. *)
  apply IHn1.
  - simpl in Hn1, Hn2 |- *.
    (*Idea: index of ts' is smaller than index of ts, and indices in tys' MUST be 
      smaller than index of ts as well (by well-typed context)
      and obviously everythign in srts smaller than srts, so I think we are good
      *)
    apply PeanoNat.lt_S_n in Hn1, Hn2.
    assert ( Hindex: index typesym_eq_dec ts' (typesyms_of_context gamma) < 
      index typesym_eq_dec ts (typesyms_of_context gamma)). { admit. }
    (*Idea: (list_max (map (depth_alt gamma) (map (sigma m srts) tys'))) <=
      max (list_max (map (depth_alt gamma) srts)) (list_max (map (depth_vty gamma) tys'))
      by subst properties (maybe we need assumption about params in bounds but that is OK*)
    (*Then, have that (list_max (map (depth_vty gamma) tys') <= (index typesym_eq_dec ts') by 
        well-typing of constructors (need valid context) *)
    (*So, max (index ts') (max (list_map srts) (index ts')) = max (index ts') (max (list_map srts))*)
    (*And we know that index ts' < index ts', so the result follows*)
    (*I believe that this should work*)
    admit.
  - admit.
Admitted.

Lemma mk_ts_map_invar gamma pd n1 n2 (s: sort):
  depth_alt gamma s < n1 ->
  depth_alt gamma s < n2 ->
  ts_map_to_pd (mk_ts_map gamma pd n1) s = ts_map_to_pd (mk_ts_map gamma pd n2) s.
Proof.
  generalize dependent n2. generalize dependent s. induction n1 as [| n1 IHn1].
  { intros; lia. }
  intros s [| n2]; [lia | intros Hn1 Hn2].
  destruct s as [| | ts srts]; simpl; auto.
  generalize dependent (find_ts_in_ctx_some gamma ts).
  destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind; auto.
  intros H. generalize dependent (proj1 (proj2 (H m a eq_refl))). clear H.
  intros a_in. (*TODO: separate lemma*) unfold adt_rep.
  assert (Hveq: (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n1))) = 
    (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n2)))). {
    (*This should be separate lemma*)
    apply functional_extensionality. intros x.
    unfold var_map. unfold domain. unfold sigma. simpl. unfold ty_subst_s.
    simpl. 
    destruct (ty_subst_fun_cases (m_params m) srts s_int x) as [Hin | Hd].
    + remember (ty_subst_fun (m_params m) srts s_int x) as t.
      destruct (sort_to_ty t) eqn : Hs; auto.
      { (*sort not var*) destruct t; simpl in Hs; discriminate. }
      simpl in Hn1, Hn2.
      pose proof (list_map_map_In_le (depth_alt gamma) Hin).
      apply IHn1; lia.
      
(*       admit. *)
      (* unfold depth_aux in Hn1, Hn2.
      simpl in Hn1.
      simpl sort_depth in Hn1, Hn2.
      assert (Hn1': list_max (map (sort_depth (constr_depth gamma)) srts) < n1) by nia.
      assert (Hn2': list_max (map (sort_depth (constr_depth gamma)) srts) < n2) by nia.
      pose proof (list_map_map_In_le (sort_depth (constr_depth gamma)) Hin). *)
(*       apply IHn1; lia. *)
    + rewrite Hd; auto.
  }
  rewrite Hveq.
  (*Now prove typesym_map equality*)
  erewrite mk_adts_ext; [reflexivity|].
  intros ts' tys' Hin'. unfold typesym_map.
  (*So we know (if we change bounds) that sort depth is smaller*)
  unfold domain. simpl.
  specialize (IHn1 (s_cons ts' (map (sigma m srts) tys')) n2).
(*   simpl sort_depth in Hn1, Hn2. *)
  (*Know here that ts' is NON-recursive instance - so it MUST appear BEFORE in gamma*)
(*  apply PeanoNat.lt_S_n in Hn1, Hn2. *)
  apply IHn1.
  - simpl in Hn1, Hn2 |- *.
    (*Idea: index of ts' is smaller than index of ts, and indices in tys' MUST be 
      smaller than index of ts as well (by well-typed context)
      and obviously everythign in srts smaller than srts, so I think we are good
      *)
    apply PeanoNat.lt_S_n in Hn1, Hn2.
    assert ( Hindex: index typesym_eq_dec ts' (typesyms_of_context gamma) < 
      index typesym_eq_dec ts (typesyms_of_context gamma)). { admit. }
    (*Idea: (list_max (map (depth_alt gamma) (map (sigma m srts) tys'))) <=
      max (list_max (map (depth_alt gamma) srts)) (list_max (map (depth_vty gamma) tys'))
      by subst properties (maybe we need assumption about params in bounds but that is OK*)
    (*Then, have that (list_max (map (depth_vty gamma) tys') <= (index typesym_eq_dec ts') by 
        well-typing of constructors (need valid context) *)
    (*So, max (index ts') (max (list_map srts) (index ts')) = max (index ts') (max (list_map srts))*)
    (*And we know that index ts' < index ts', so the result follows*)
    (*I believe that this should work*)
    admit.
  - admit.
Admitted. *)
 (*    lia.

 by admit.

    (*Problem is extra +1 - is it actually smaller or could it just be the same?*)
    (*with + version, can remove the s because ts' is smaller, but then, the max could
      be as large as max (index ts', srts)*)
    Search (S ?x < S ?y).


 (*Idea: index of*) unfold depth_aux in Hn1 |-*. rewrite sort_depth_cons in Hn1 |- *.
    unfold sigma.




Lemma sorts_depth_bound n srts b
  (forall x, In x srts -> sort_depth n x < b) ->
  

Lemma 


    rewrite map_map.
    (*Idea: index ts' < index ts, *)

    

 simpl sort_depth.

 simpl sort_depth.

    Print sigma.  
    

  simpl in IHn1.

  Print ts_map_to_pd.

  unfold mk_ts_map.
  Check mk_ts_map.
  


  destruct (sort_to_ty (typesym_to_sort ts' (seq.map (sigma m srts) tys'))) eqn : Hty; auto.
  { (*contradiction*) exfalso. apply (var_not_sort t). rewrite <- Hty; auto.
    destruct (typesym_to_sort ts' (seq.map (sigma m srts) tys')); auto.
  }
  (*Idea is that we need to show (ultimately) that this sort is small enough*)
  apply IHn1.
  (*TODO: come back once I fix sorts *)
  admit.
  admit.
      * 

 unfold sort_to_ty in Hs. 
        destruct (nth n srts s_int); simpl in Hs; discriminate.


 destruct (ty_subst_fun (m_params m) srts s_int x) as [| | ts' srts'] eqn : Hty; auto.
      remember (s_cons ts' srts') as s.
      unfold ts_map_to_pd in IHn1. apply IHn1.
      apply IHn1.
      
    destruct (in_dec string_dec x (m_params m)) as [Hin| Hin].
    + (*Case 1: if var in list, maps to corresponding sort, which has smaller size than n1 and n2,
        so use IH*)
      (*Note: we need a lemma that doesnt require length eq, as long as in both lists, otherwise prove default
        for now just admit*)
      (*TODO: need lemma that says we can find first instance - then case on whether this is in bounds
        of second or not*)
     (*  Search In nth.
      Search index.
      destruct (In_nth _ _ EmptyString Hin) as [n [Hn Hx]].
      Search ty_subst_fun List.nth.



ty_subst_fun_nth_gen:
  forall {A : Type} (vars : list typevar) (vs : list A) (d : A) (n : nat) (a : typevar) (s : A),
  n < Datatypes.length vars ->
  n < Datatypes.length vs -> NoDup vars -> ty_subst_fun vars vs d (nth n vars a) = nth n vs s *)

      destruct (In_nth _ _ EmptyString Hin) as [n [Hn Hx]].
      subst. unfold ty_subst_s. simpl. rewrite ty_subst_fun_nth with (s:=s_int); auto.
      2: { (*here*) admit. }
      2: { apply m_params_Nodup. }
      destruct (sort_to_ty (nth n srts s_int)) eqn : Hs; auto.
      { (*sort not var*) unfold sort_to_ty in Hs. 
        destruct (nth n srts s_int); simpl in Hs; discriminate.
      }
      simpl in Hn1, Hn2.
      apply IHn1.
      * Search list_max. (*TODO: lemma for In*)
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

 *)

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

(* Check adt_rep.
Lemma adt_rep_eq m srts pd a a_in:
  adt_rep' m srts pd pd a a_in = adt_rep m srts pd a a_in.
Proof. reflexivity. Qed. *)

(*Now we will try to prove for the generalized version*)

Lemma mk_pd_aux_full gamma pd n: valid_context gamma -> pd_full_aux gamma (mk_pd_aux gamma pd n) n.
Proof.
  intros gamma_valid.
  unfold pd_full_aux, mk_pd_aux. unfold ts_map_to_pd at 1. intros Hn m srts a m_in a_in.
(*   rewrite sort_rect_typesym_to_sort. *)
  (*TODO: could I prove that this equals mk_ts ... (pred n) (bc if n large enough, doesn't change)
    *)
  assert (Htest: adt_rep m srts (fun s : sort => ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n srts) ts srts) s) a a_in =
    adt_rep m srts (fun s : sort => ts_map_to_pd (mk_ts_map gamma pd (pred (n srts))) s) a a_in).
  {
   (*  pose proof (mk_ts_map_invar' gamma pd (fun x => S (n x)) (S (pred (n srts))) (s_cons (adt_name a) srts)) as Hinvar.
    prove_hyp Hinvar. { intros x1 x2. specialize (Hn x1 x2); lia. }
    prove_hyp Hinvar. { specialize (Hn (adt_name a) srts). lia. }
    simpl in Hinvar. 
    generalize dependent (find_ts_in_ctx_some gamma (adt_name a)).
    assert (Hfind: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
      apply find_ts_in_ctx_iff; auto.
    }
    rewrite Hfind.
    intros H.
    assert (Heq: (proj1 (proj2 (H m a eq_refl))) = a_in) by (apply bool_irrelevance).
    rewrite Heq. intros Heq1. rewrite <- Heq1.


 intros Heq1; apply Heq1.

 auto.


mk_ts_map_invar' *)
   

    (*maybe we do need another proof here*)
    (* unfold adt_rep.
    f_equal.
    - unfold var_map. apply functional_extensionality. intros x. unfold sigma, ty_subst_s, domain. simpl.
      Check mk_ts_map_invar.

    apply mk_adts_ext.
    Search mk_adts. 
    f_equal.

    Check mk_ts_map_invar.    (*ok, do this later*) *)
    Check mk_ts_map_invar.

    unfold adt_rep.
    assert (Hvar: (var_map m srts
     (fun s : sort =>
      ts_map_to_pd (fun (ts : typesym) (srts0 : list sort) => mk_ts_map gamma pd (n srts0) ts srts0) s)) =
      (var_map m srts (fun s : sort => ts_map_to_pd (mk_ts_map gamma pd (Init.Nat.pred (n srts))) s))).
    {
      apply functional_extensionality. intros x. unfold var_map. unfold domain, sigma, ty_subst_s. simpl.
      destruct (ty_subst_fun_cases (m_params m) srts s_int x) as [Hin | Hd].
      + remember (ty_subst_fun (m_params m) srts s_int x) as t.
        destruct (sort_to_ty t) as [| | | ts tys] eqn : Hs; auto.
        { (*sort not var*) destruct t; simpl in Hs; discriminate. }
        pose proof (sort_size_in gamma Hin).
        pose proof (size_sorts_cons_bound gamma (adt_name a) srts).
        apply mk_ts_map_invar'; auto.
        * intros ts' s. specialize (Hn ts' s). lia.
        * specialize (Hn (adt_name a) srts). lia.
      + rewrite Hd; auto.
    }
    (*   (var_map m srts
     (fun s : sort =>
      ts_map_to_pd
        (fun (ts : typesym) (srts0 : list sort) => mk_ts_map gamma pd (Init.Nat.pred (n srts0)) ts srts0)
        s))).
    { apply functional_extensionality. intros x. unfold var_map. unfold domain, sigma, ty_subst_s. simpl.
      destruct (ty_subst_fun_cases (m_params m) srts s_int x) as [Hin | Hd].
      + remember (ty_subst_fun (m_params m) srts s_int x) as t.
        destruct (sort_to_ty t) as [| | | ts tys] eqn : Hs; auto.
        { (*sort not var*) destruct t; simpl in Hs; discriminate. }
        pose proof (depth_alt_in gamma Hin).
        pose proof (depth_alt_cons_bound gamma (adt_name a) srts).
        apply mk_ts_map_invar.
        * intros s. specialize (Hn s). lia.
        * intros s. specialize (Hn s). lia.
      + rewrite Hd; auto.
    } *)
    rewrite <- Hvar. clear Hvar.
    erewrite mk_adts_ext; [reflexivity|].
    intros ts' tys' Hin'. unfold typesym_map.
    (*So we know (if we change bounds) that sort depth is smaller*)
    unfold domain. simpl.
    pose proof (mk_ts_map_invar_const gamma_valid pd (n (map (sigma m srts) tys'))
      (Init.Nat.pred (n srts)) (s_cons ts' (map (sigma m srts) tys'))) as Hts.



    assert (Hdepth: size_sort gamma (s_cons ts' (map (sigma m srts) tys')) < size_sort gamma (s_cons (adt_name a) srts)).
    { apply mut_ts_pairs_subst_smaller; auto. } 
    simpl ts_map_to_pd in Hts. apply Hts.
    - specialize (Hn ts' (map (sigma m srts) tys')). lia.
    - specialize (Hn (adt_name a) srts). lia.
  }
  rewrite Htest. clear Htest.
  destruct (n srts) as [| n'] eqn : Hn'.
  - specialize (Hn (adt_name a) srts); lia.
  - simpl. 
    generalize dependent (find_ts_in_ctx_some gamma (adt_name a)).
    assert (Hfind: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
      apply find_ts_in_ctx_iff; auto.
    }
    rewrite Hfind.
    intros H.
    assert (Heq: (proj1 (proj2 (H m a eq_refl))) = a_in) by (apply bool_irrelevance).
    rewrite Heq. auto.
Qed.
(* 
    simpl in Hts.
    apply mk_ts_map_invar with (n1:=fun _ => (n (map (sigma m srts) tys')))
    (n2:= fun _ => (Init.Nat.pred (n (map (sigma m srts) tys')))).
    Check mk_ts_map_invar.

    specialize (IH (s_cons ts' (map (sigma m srts) tys'))).
    simpl ts_map_to_pd in IH.
    assert (Hdepth: depth_alt gamma (s_cons ts' (map (sigma m srts) tys')) < depth_alt gamma (s_cons (adt_name a) srts)).
    {
      (*Idea: (list_max (map (depth_alt gamma) (map (sigma m srts) tys'))) <=
        max (list_max (map (depth_alt gamma) srts)) (list_max (map (depth_vty gamma) tys'))
        by subst properties (maybe we need assumption about params in bounds but that is OK*)
      (*Then, have that (list_max (map (depth_vty gamma) tys') <= (index typesym_eq_dec ts') by 
          well-typing of constructors (need valid context) *)
      (*So, max (index ts') (max (list_map srts) (index ts')) = max (index ts') (max (list_map srts))*)
      (*And we know that index ts' < index ts', so the result follows*)
      (*I believe that this should work*)
      admit.
    }
    specialize (IH Hdepth (fun _ => n1') (fun _ => n2')).
  (*   simpl sort_depth in Hn1, Hn2. *)
    (*Know here that ts' is NON-recursive instance - so it MUST appear BEFORE in gamma*)
  (*  apply PeanoNat.lt_S_n in Hn1, Hn2. *)
    apply IH; try lia.
    apply mk_adts_ext.

    pose proof (mk_ts_map_invar gamma pd (fun x => S (n x)) (fun x =>  S (pred (n x))) (s_cons (adt_name a) srts)) as Hts.
    prove_hyp Hts.
    { intros s. specialize (Hn s). lia. }
    prove_hyp Hts. { intros s. specialize (Hn s). lia. }
    unfold ts_map_to_pd in Hts. simpl in Hts.
    generalize dependent (find_ts_in_ctx_some gamma (adt_name a)).
    assert (Hfind: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
      apply find_ts_in_ctx_iff; auto.
    }
    rewrite Hfind. intros H. generalize dependent ((proj1 (proj2 (H m a eq_refl)))). clear H.
    intros a_in'. assert (a_in = a_in') by (apply bool_irrelevance). subst.
    intros Heq.
    replace (fun (ts : typesym) (srts0 : list sort) => mk_ts_map gamma pd (n srts0) ts srts0) with
    (mk_ts_map gamma pd (n srts)).
    2: { repeat (apply functional_extensionality; intros); auto.

 apply Heq. auto.
  }
  auto.
  rewrite Htest. clear Htest.
  destruct n as [| n'].
  - intros; lia.
  - simpl. 
    generalize dependent (find_ts_in_ctx_some gamma (adt_name a)).
    assert (Hfind: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
      apply find_ts_in_ctx_iff; auto.
    }
    rewrite Hfind.
    intros H.
    assert (Heq: (proj1 (proj2 (H m a eq_refl))) = a_in) by (apply bool_irrelevance).
    rewrite Heq. auto.
Qed. *)

Check mk_pd_aux_full.
Print pd_full_aux.
Print pd_full.
(* Definition mk_pd' (gamma: context) (pd: sort -> Set) (s: sort) : Set :=
  mk_pd_aux gamma pd (fun srts => depth_alt gamma s) s. *)

Lemma mk_pd_full gamma pd: valid_context gamma -> pd_full gamma (mk_pd gamma pd).
Proof.
  intros gamma_valid. unfold pd_full, mk_pd. intros m srts a m_in a_in.
  apply mk_pd_aux_full; auto.
  apply max_depth_max.
Qed.
(*The next thing to prove (TODO): for any non-ADT, pd_full gamma (mk_pd gamma pd) = pd*)


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

