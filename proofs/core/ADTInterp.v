Require Import IndTypes.
Require Import Stdlib.Arith.Wf_nat.



(*The construction of the interpretation is very complicated, since it must
  be defined in terms of itself. There is no obvious recursive argument; instead
  we use fuel and define a bound. However, in order to reason about this,
  we need a measure on typesyms, sorts, and tys that satisfies several properties
  simultaneously:
  1. If s in srts, |s| <= |srts|
  2. |srts| < | s_cons ts srts |
  3. for any (ts, tys) appearing in a constructor of ADT a, and for any sorts,
     | s_cons ts (sigma tys) | < | s_cons a srts |, where sigma maps the ADT params to srts

  It is not easy to satisfy these conditions. For example, suppose we have type A a and then
  type B a that has a constructor taking in A a. By these conditions, it must be the case that:
  | B int | < | A (B int) | < |B (B int) |
  This rules out any lexicographic-type approach based on the ordering of typesyms, since
  A and B are directly comparable.
  
  Instead, we need a more complex measure: we define the size of a typesym to be
  the sum of the sizes of ALL (non-recursive) types appearing in the constructors
  of the ADTs in the mutual block to which the typesym belongs, and simulateously
  define the size of a type (for the cons case) as 1 + | ts | + max_{t in ty} | t |.
  Note that this is self-referrential, so we define via the context.
  The crucial ingredient to make this well-founded is that types in a context are defined
  only via previously-defined types (since we consider non-recursive occurrences only).

  This takes quite a bit of work to show: we define the various size metrics,
  prove the key lemma that demonstrates the well-foundedness, and then prove the 3 needed results
*)

Section Size.

(*To avoid case analysis*)
Definition is_def_mut (d: def) : option mut_adt :=
  match d with
  | datatype_def m => Some m
  | _ => None
  end.

(*The size of a typesym*)
Fixpoint size_ts (gamma: context) (ts: typesym) :=
  match gamma with
  | nil => 0
  | d :: g' =>
    match is_def_mut d with
    | Some m =>
      if in_dec typesym_eq_dec ts (typesyms_of_mut m) then
      let fix size_ty (t: vty) : nat :=
        match t with
        | vty_real => 0
        | vty_int => 0
        | vty_var _ => 0
        | vty_cons ts tys => 1 + size_ts g' ts + list_max (map size_ty tys) (*Crucial: only nonind types!*)
        end in 
      1 + sum (map (fun x => size_ts g' (fst x) + list_max (map size_ty (snd x))) (mut_ts_pairs (adts m)))
      else size_ts g' ts
    | None => size_ts g' ts
    end
  end.

(*The size of a type*)
Fixpoint size_ty (gamma: context) (t: vty) : nat :=
  match t with
  | vty_real => 0
  | vty_int => 0
  | vty_var _ => 0
  | vty_cons ts tys => 1 + size_ts gamma ts + list_max (map (size_ty gamma) tys)
  end.

Lemma size_ty_cons gamma ts tys:
  size_ty gamma (vty_cons ts tys) = 1 + size_ts gamma ts + list_max (map (size_ty gamma) tys).
Proof. reflexivity. Qed.

(*The size of a list of types*)
Definition size_tys (gamma: context) (tys: list vty) : nat :=
  list_max (map (size_ty gamma) tys).

(*A rewrite lemma to avoid the nested fix*)
Lemma size_ts_rewrite gamma ts:
  size_ts gamma ts =
  match gamma with
  | nil => 0
  | d :: g' =>
    match is_def_mut d with
    | Some m =>
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

(*Size of a sort*)
Fixpoint size_sort (gamma: context) (s: sort) : nat :=
  match s with
  | s_int => 0
  | s_real => 0
  | s_cons ts srts => 1 + size_ts gamma ts + list_max (map (size_sort gamma) srts)
  end.

(*Size of a list of sorts*)
Definition size_sorts gamma srts := list_max (map (size_sort gamma) srts).

(*The big result: our recursion on the context is justified, and we can instead
  consider it to have been defined over the entire context*)
Section Context.

(*We need several helper lemmas first*)

(*If d is not a mutual block, size_ts is unaffected*)
Lemma size_ts_not_mut g d (Hd: is_def_mut d = None):
  forall ts, size_ts (d :: g) ts = size_ts g ts.
Proof.
  intros ts. rewrite size_ts_rewrite. rewrite Hd. auto.
Qed.

(*If ts' not in m, then adding d does not change the size of ts'*)
Lemma size_ts_notin {g d m} (Hd: is_def_mut d = Some m):
  forall ts' (Hnotin: ~ In ts' (typesyms_of_mut m)),
  size_ts g ts' = size_ts (d :: g) ts'.
Proof.
  intros ts1 Hnotin1. rewrite (size_ts_rewrite (d :: g)), Hd.
  destruct (in_dec typesym_eq_dec ts1 (typesyms_of_mut m)); auto.
  contradiction.
Qed.

(*If no ts in m appears in ty, then size_ty is unaffected by adding d*)
Lemma size_ty_notin {g d m} (Hd: is_def_mut d = Some m):
  forall ty
  (Hnotin: forall ts : typesym, In ts (typesyms_of_mut m) -> ~ is_true (typesym_in_ty ts ty)),
  size_ty g ty = size_ty (d :: g) ty.
Proof.
  intros ty'; induction ty' as [| | x | ts1 tys1 IHty]; auto.
  intros Hnotin'. rewrite !size_ty_cons, <- !Nat.add_assoc. f_equal.
  f_equal.
  - apply (size_ts_notin Hd). intros C. apply (Hnotin' ts1 C). simpl. destruct (typesym_eq_dec ts1 ts1); auto.
  - f_equal. apply map_ext_in. intros x Hinx.
    rewrite Forall_forall in IHty. apply IHty; auto. intros ts2 Hints2 C.
    apply (Hnotin' ts2 Hints2). simpl. apply orb_true_iff. right.
    rewrite existsb_exists. exists x. auto.
Qed.

(*Structural result about [mut_ts_pairs]*)
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

(*The following lemmas give us the disjointness results we need*)

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

(*The full theorem:*)

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
      apply (size_ts_notin Hmut). apply (mut_ts_pairs_notin_ts Hin); auto. (*contradicts only nonind tys*)
    + (*And similar for the tys*)
      f_equal. apply map_ext_in. intros ty Hinty.
      apply (size_ty_notin Hmut). intros ts Hints.
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
    clear Hfind IH.
    destruct (find_ts_in_ctx g' ts) as [[m1 a1]|] eqn : Hfind; auto.
    f_equal. f_equal.
    (*Now we have a similar proof, but now we know that because they are defined before,
      they can only refer to names that came before*)
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
    + apply (size_ts_notin Hmut). 
      (*by [mut_ts_pairs_ts_in_ctx], ts' is in sig_t of g',
      so it will contradict disjointness*)
      pose proof (mut_ts_pairs_ts_in_ctx Hval m1_in Hin) as Hints.
      apply Hdisj'; auto.
    + (*Similarly, no ts in m can appear in tys'*) f_equal. apply map_ext_in. intros a Hina.
      apply (size_ty_notin Hmut).
      intros ts1 Hints1 Hinty.
      apply (Hdisj' ts1); auto.
      apply (mut_ts_pairs_in_tys_in_ctx Hval m1_in Hin _ _ Hina); auto.
Qed.

End Context.

(*Now we prove the bounds via this measure*)
Section Bounds.

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

(*Substitution is the trickiest. The idea is that, since the type size ultimately calculates
  depth (i.e. the max chain of typesym size-sums), we can bound a substitution by a sum of
  the original tys and the substituted sorts (since sorts are substituted at a leaf)*)

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

(*And therefore, we get condition (3) above*)
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

(*We need one more result: any typesym not in the context has size 0
  (NOTE: this cannot depend on [valid_context]*)
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

End Bounds.
End Size.

(*Part 2: Define the interp

This is not easy, since it must be defined in terms of itself. Even the fuel can change during
recursive calls, since it is a function of the input sort/sorts. In a sense, the fuel is variable,
and then gets "fixed" and treated as a normal [nat] for the rest of the recursion. We need appropriate
bounds to ensure that this works, but it is very tricky.
*)

Definition ts_map_to_pd (f: typesym -> list sort -> Set) : sort -> Set :=
  fun s =>
  match s with
  | s_int => Z
  | s_real => R
  | s_cons ts srts => f ts srts
  end.

(*The core map: sends typesyms in the context to the correct [adt_rep].
  But for well-founded recursion, the [adt_rep] is defined in terms of a smaller fuel bound.
  Proving that we can ultimately equate this with the input [nat] (for large enough n)
  is the key challenge*)
Fixpoint mk_ts_map (gamma: context) (pd: sort -> Set) (n: nat) (ts: typesym) (srts: list sort) : Set :=
  match n with
  | O => pd (s_cons ts srts)
  | S n' =>
    let pd' := ts_map_to_pd (mk_ts_map gamma pd n')
    in
    match find_ts_in_ctx gamma ts as b return find_ts_in_ctx gamma ts = b -> _ with
    | Some (m, a) => fun Hfind => 
      if (length srts =? length (m_params m)) then
        adt_rep m srts pd' a (proj1 (proj2 (find_ts_in_ctx_some _ _ _ _ Hfind)))
      else unit (*any non-empty type works*)
    | None => fun _ => pd (s_cons ts srts)
    end eq_refl
    end.

(*The [pi_dom] defined with function for the size (based on input sorts)*)
Definition mk_pd_aux (gamma: context) (pd: sort -> Set) (n: list sort -> nat) (s: sort) : Set :=
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n srts) ts srts) s.

Definition mk_ts_full gamma pd ts srts :=
  mk_ts_map gamma pd (size_sorts gamma srts) ts srts.

(*Given a [srts], we need a max depth of any (s_cons ts srts). This is easy: just take the largest
  size typesym in the context (all others are 0) *)
Definition max_depth gamma srts :=
  3 + list_max (map (size_ts gamma) (typesyms_of_context gamma)) + size_sorts gamma srts.

Lemma max_depth_max gamma:
  forall ts srts, 1 + size_sort gamma (s_cons ts srts) < max_depth gamma srts.
Proof.
  intros ts srts. unfold max_depth. simpl. unfold size_sorts.
  assert (Hsz: size_ts gamma ts <= list_max (map (size_ts gamma) (typesyms_of_context gamma))); [|lia].
  destruct (in_dec typesym_eq_dec ts (typesyms_of_context gamma)).
  - apply list_map_map_In_le; auto.
  - rewrite ts_notin_size; auto. lia.
Qed. 

(*The complete interpretation: give [max_depth gamma srts] as the fuel bound for each [srts]*)
Definition mk_pd (gamma: context) (pd: sort -> Set) (s: sort) : Set :=
  mk_pd_aux gamma pd (fun srts => max_depth gamma srts) s.

(*Definitions of correctness:*)

(*pd with all typesym_to_sort set correctly to the corresponidng W-type*)
Definition pd_full (gamma: context) (pd: sort -> Set) := forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m) 
    (srts_len: length srts = length (m_params m)),
    pd (s_cons (adt_name a) srts) =
    adt_rep m srts pd a Hin.

(*The auxillary version. The [n] function must be large enough*)
Definition pd_full_aux (gamma: context) (pd: sort -> Set) (n: list sort -> nat) := 
    (forall ts srts1, 1 + size_sort gamma (s_cons ts srts1) < n srts1) ->
    forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m)
    (srts_len: length srts = length (m_params m)) ,
    pd (s_cons (adt_name a) srts) =
    adt_rep m srts pd a Hin.


Section InterpProofs.

(*The key result is that if the fuel is large enough, the interpretation is independent of
  the fuel. But we need both non-dependent (constant nat) and (sort -> nat) function versions,
  and a hybrid. The non-dependent version is the crucial one which we build the others atop.*)

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
  destruct (Nat.eqb_spec (length srts) (length (m_params m))) as [Hlen | Hlen]; auto.
  (*Prove the [adt_rep]s equal by proving the var maps equal and then
    using the ext lemma for the typesym interp*)
  unfold adt_rep.
  assert (Hveq: (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n1))) = 
    (var_map m srts (ts_map_to_pd (mk_ts_map gamma pd n2)))). {
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
    + rewrite Hd; auto.
  }
  rewrite Hveq.
  (*Now prove typesym_map equality*)
  erewrite mk_adts_ext; [reflexivity|].
  intros ts' tys' Hin'. unfold typesym_map.
  (*This is why we need the particular bound: since we are in a constructor
    argument type, it is smaller than the original sort*)
  unfold domain. simpl.
  specialize (IHn1 (s_cons ts' (map (sigma m srts) tys')) n2).
  pose proof (mut_ts_pairs_subst_smaller gamma_valid m_in a_in ts' tys' srts Hin').
  apply IHn1; unfold sigma; lia.
Qed.

(*The function version*)
Lemma mk_ts_map_invar {gamma} (gamma_valid : valid_context gamma) pd n1 n2 (s: sort):
  (forall ts srts, size_sort gamma (s_cons ts srts) < n1 srts) ->
  (forall ts srts, size_sort gamma (s_cons ts srts) < n2 srts) ->
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n1 srts) ts srts) s = 
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n2 srts) ts srts) s.
Proof.
  intros Hn1 Hn2. destruct s as [| | ts srts]; simpl; auto.
  pose proof (mk_ts_map_invar_const gamma_valid pd (n1 srts) (n2 srts) (s_cons ts srts)) as Heq.
  simpl ts_map_to_pd in Heq. apply Heq; auto.
Qed.

(*One side is function, the other is a constant*)
Lemma mk_ts_map_invar'  {gamma} (gamma_valid : valid_context gamma) pd n1 n2 (s: sort):
  (forall ts srts, size_sort gamma (s_cons ts srts) < n1 srts) ->
  (size_sort gamma s < n2) ->
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n1 srts) ts srts) s = 
  ts_map_to_pd (fun ts srts => mk_ts_map gamma pd n2 ts srts) s.
Proof.
  intros Hn1 Hn2. destruct s as [| | ts srts]; simpl; auto.
  pose proof (mk_ts_map_invar_const gamma_valid pd (n1 srts) n2 (s_cons ts srts)) as Heq.
  simpl ts_map_to_pd in Heq. apply Heq; auto.
Qed.

(*Now prove that this satisfies [pd_full_aux] for any [n]*)
Lemma mk_pd_aux_full gamma pd n: valid_context gamma -> pd_full_aux gamma (mk_pd_aux gamma pd n) n.
Proof.
  intros gamma_valid.
  unfold pd_full_aux, mk_pd_aux. unfold ts_map_to_pd at 1. intros Hn m srts a m_in a_in srts_len.
  (*Idea: we convert [adt_rep] of this function into one with a fixed [n] ([pred (n srts)]).
    Then we can case on n, unfold, and prove the equality. This uses the invar lemmas above, but
    we need to repeat parts of the proof*)
  assert (Htest: adt_rep m srts (fun s : sort => ts_map_to_pd (fun ts srts => mk_ts_map gamma pd (n srts) ts srts) s) a a_in =
    adt_rep m srts (fun s : sort => ts_map_to_pd (mk_ts_map gamma pd (pred (n srts))) s) a a_in).
  {
    unfold adt_rep.
    (*Prove var maps eq*)
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
    (*And typesym maps*)
    rewrite <- Hvar. clear Hvar.
    erewrite mk_adts_ext; [reflexivity|].
    intros ts' tys' Hin'. unfold typesym_map.
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
  (*We chose [pred(n srts)] before so that when we unfold 1 layer of the LHS (n srts), everything is equal*)
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
    apply Nat.eqb_eq in srts_len. rewrite srts_len.
    rewrite Heq. auto.
Qed.

(*The full theorem is a simple corollary, since we chose a large enough depth*)
Theorem mk_pd_full gamma pd: valid_context gamma -> pd_full gamma (mk_pd gamma pd).
Proof.
  intros gamma_valid. unfold pd_full, mk_pd. intros m srts a m_in a_in.
  apply mk_pd_aux_full; auto.
  apply max_depth_max.
Qed.

End InterpProofs.

(*Part 3: Prove resulting domain is inhabited (TODO: maybe change dependencies*)

Require Import Interp.

(*Need for Type proofs (NOTE: opaque)*)
Lemma existsb_exists_strong {A: Type} (f: A -> bool) (l: list A):
  existsb f l = true ->
  {x | In x l /\ f x = true}.
Proof.
  induction l as [| h t IH]; simpl; [discriminate|].
  destruct (f h) eqn : Hfh; simpl.
  - intros _. apply (exist _ h). auto.
  - intros Ht. apply IH in Ht. destruct Ht as [x [Hinx Hfx]].
    apply (exist _ x); auto.
Qed.


(*Steps:
  1. Prove that any typesym not a mut, mk_pd ts srts = pd ts srts
  2. Prove, under assumption that (forall srts, inhab ts srts) for ts not in mut,
    all ts srts are inhabited (involves a lemma for subst in vty)
  3. Prove that this means that [mk_pd] always produces inhabited types given a pi_dom
  4. Prove that we can construct new pi_dom, which is full
*)

(*1. Prove that any typesym not a mut, mk_pd ts srts = pd ts srts *)

Lemma mk_ts_map_nonadt gamma pd n ts srts (Hts: find_ts_in_ctx gamma ts = None):
  mk_ts_map gamma pd n ts srts = pd (s_cons ts srts).
Proof.
  destruct n as [| n']; simpl; auto.
  generalize dependent (find_ts_in_ctx_some gamma ts).
  rewrite Hts. auto.
Qed.

Lemma mk_pd_aux_nonadt gamma pd n ts srts (Hts: find_ts_in_ctx gamma ts = None):
  mk_pd_aux gamma pd (fun srts => n srts) (s_cons ts srts) = pd (s_cons ts srts).
Proof. apply mk_ts_map_nonadt; auto. Qed.

Lemma mk_pd_nonadt gamma pd ts srts (Hts: find_ts_in_ctx gamma ts = None):
  mk_pd gamma pd (s_cons ts srts) = pd (s_cons ts srts).
Proof. apply mk_pd_aux_nonadt; auto. Qed.

(*1.5 Similar for adt and wrong sorts*)
Lemma mk_ts_map_adt_nolen {gamma m a} 
  ts pd n (Hts: find_ts_in_ctx gamma ts = Some (m, a)) srts
  (Hsrts: length srts <> length (m_params m)):
  ((mk_ts_map gamma pd n ts srts = pd (s_cons ts srts)) +
  (mk_ts_map gamma pd n ts srts = unit))%type.
Proof.
  destruct n as [| n']; simpl; auto.
  generalize dependent (find_ts_in_ctx_some gamma ts).
  rewrite Hts. intros H.
  apply Nat.eqb_neq in Hsrts. rewrite Hsrts. auto.
Qed.

Lemma mk_pd_aux_adt_nolen {gamma m a} pd n ts srts (Hts: find_ts_in_ctx gamma ts = Some (m, a))
  (Hsrts: length srts <> length (m_params m)):
  ((mk_pd_aux gamma pd (fun srts => n srts) (s_cons ts srts) = pd (s_cons ts srts)) +
  (mk_pd_aux gamma pd (fun srts => n srts) (s_cons ts srts) = unit)).
Proof. eapply mk_ts_map_adt_nolen; eauto. Qed.

Lemma mk_pd_adt_nolen {gamma m a} pd ts srts (Hts: find_ts_in_ctx gamma ts = Some (m, a))
  (Hsrts: length srts <> length (m_params m)):
  ((mk_pd gamma pd (s_cons ts srts) = pd (s_cons ts srts)) +
  (mk_pd gamma pd (s_cons ts srts) = unit)).
Proof. eapply mk_pd_aux_adt_nolen; eauto. Qed.


(*Need a version in Type*)
Lemma ty_subst_fun_cases_strong {A: Type}: forall params tys (d: A) v,
  (In (ty_subst_fun params tys d v) tys) +
  (ty_subst_fun params tys d v = d).
Proof.
  intros. unfold ty_subst_fun.
  destruct (get_assoc_list _ _ _) eqn : Ha; auto.
  apply get_assoc_list_some in Ha. 
  apply in_combine_r in Ha. auto.
Qed.

(*Main lemma: if all non-adts are inhabited and all typesyms applied to wrong length args are inhabited,
  then all typesyms applied to inhabited types are inhabited as long as [typesym_inhab_fun] holds for 
  large enough n*)
Lemma typesym_inhab_fun_aux {gamma} (gamma_valid: valid_context gamma) pd
  (Hpd1: forall ts srts (Hts: find_ts_in_ctx gamma ts = None), domain_nonempty (domain pd) (s_cons ts srts))
  (Hpd2: forall m a ts srts (Hts: find_ts_in_ctx gamma ts = Some (m, a)), length srts <> length (m_params m) -> 
    domain_nonempty (domain pd) (s_cons ts srts))
  (pd_full: pd_full gamma pd) n:
   (forall ts srts seen
      (Hn: n >= length (sig_t gamma) - length seen)
      (Hinhab: typesym_inhab_fun gamma seen ts n)
      (Hsrts: ForallT (fun s => domain_nonempty (domain pd) s) srts),
      domain_nonempty (domain pd) (s_cons ts srts)).
Proof.
  induction n as [| n' IHn]; [discriminate|].
  intros ts srts seen Hn. rewrite typesym_inhab_fun_eq.
  destruct (in_dec typesym_eq_dec ts (sig_t gamma)) as [Hina|]; [|discriminate].
  destruct (in_dec typesym_eq_dec ts seen) as [| Hnotins]; [discriminate|].
  simpl.
  destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hfind.
  2: { intros _ Hall. apply Hpd1. auto. } assert (Hfind':=Hfind).
  apply find_ts_in_ctx_some in Hfind. destruct Hfind as [m_in [a_in Hts]]; subst.
  destruct (null (adt_constr_list a)) eqn : Hnull; [discriminate|].
  simpl. intros Hex. apply existsb_exists_strong in Hex.
  destruct Hex as [c [Hinc Hinhab]].
  unfold constr_inhab_fun in Hinhab. rewrite forallb_forall in Hinhab.
  intros Hsrts.
  assert (c_in: constr_in_adt c a) by (apply constr_in_adt_eq; auto).
  destruct (Nat.eqb_spec (length srts) (length (m_params m))) as [srts_len | Hlen].
  2: { eapply Hpd2; eauto. }
  constructor.
  assert (Heq: domain pd (s_cons (adt_name a) srts) = IndTypes.adt_rep m srts pd a a_in).
  { rewrite <- pd_full; auto. }
  rewrite Heq.
  (*Idea: we use the corresponding [constr_rep] (since we assumed [full]). What remains is
    to construct the [adt_rep], which we do inductively*)
  apply (IndTypes.constr_rep gamma_valid m m_in srts srts_len pd a a_in c c_in).
  { intros a' m_in' a_in' Hlen'. apply pd_full; auto. }
  unfold sym_sigma_args.

  (*Directly construct arg_list with inducton*)
  induction (s_args c) as [| h t IH]; simpl; [constructor|].
  constructor.
  2: { apply IH. simpl in Hinhab; auto. }
  specialize (Hinhab h (ltac:(simpl; auto))).
  assert (Htys: forall params ty (Hinhab: vty_inhab_fun gamma (adt_name a :: seen) ty n'),
    domain pd (ty_subst_s params srts ty)).
  {
    intros params. induction ty as [| | x | ts tys IHty] using vty_rect; simpl.
    - intros _. unfold ty_subst_s. simpl. exact 0%Z.
    - intros _. unfold ty_subst_s. simpl. exact 0%R.
    - intros _. unfold ty_subst_s. simpl.
      destruct (ty_subst_fun_cases_strong params srts s_int x) as [Hin | Hint].
      + (*Use ForallT assumption*)
        apply ForallT_In with (x:=(ty_subst_fun params srts s_int x)) in Hsrts; auto; [|apply sort_eq_dec].
        destruct Hsrts as [y]; apply y.
      + rewrite Hint. exact 0%Z.
    - (*Here, use original IH*)
      intros Hinhab'. apply andb_true in Hinhab'. destruct Hinhab' as [Hall Htsinhab].
      unfold ty_subst_s. simpl.
      apply (IHn ts (map (v_subst (ty_subst_fun params srts s_int)) tys) (adt_name a :: seen)
        (ltac:(simpl; lia)) Htsinhab).
      unfold is_true in Hall. rewrite forallb_forall in Hall.
      revert IHty Hall. clear.
      (*Easy goal, need induction for ForallT*)
      induction tys as [| h t IH]; simpl; intros Hall1 Hall; [constructor|]. 
      inversion Hall1 as [| ? ? Hh Ht]; subst.
      assert (Hh' := Hall h (ltac:(auto))). constructor; auto.
      specialize (Hh Hh'). constructor. apply Hh.
  }
  apply Htys. auto.
Qed.

(*TODO: remove inhab lemmas from Typing*)


(*Corollary: for any full interp in a well-typed context, if non-ADTs are inhabited and 
  ADTs applied to the wrong number of arguments are inhabited, then
  all ADTs are inhabited*)
Theorem all_adts_inhab {gamma} (gamma_valid: valid_context gamma) (pd: sort -> Set)
  (Hpd1: forall ts srts (Hts: find_ts_in_ctx gamma ts = None), domain_nonempty (domain pd) (s_cons ts srts))
  (Hpd2: forall m a ts srts (Hts: find_ts_in_ctx gamma ts = Some (m, a)), length srts <> length (m_params m) -> 
    domain_nonempty (domain pd) (s_cons ts srts))
  (Hpdf: pd_full gamma pd)
  srts (Hsrts: ForallT (fun s : sort => domain_nonempty (domain pd) s) srts)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (srts_len: length srts = length (m_params m)):
  IndTypes.adt_rep m srts pd a a_in.
Proof. 
  assert (Htsinhab: typesym_inhab gamma (adt_name a)). {
    apply valid_context_defs in gamma_valid.
    rewrite Forall_forall in gamma_valid.
    rewrite mut_in_ctx_eq2 in m_in.
    specialize (gamma_valid _ m_in).
    simpl in gamma_valid.
    destruct gamma_valid as [_ [Hinhab _]].
    rewrite Forall_forall in Hinhab.
    apply (Hinhab _ (in_bool_In _ _ _ a_in)).
  }
  pose proof (typesym_inhab_fun_aux gamma_valid pd Hpd1 Hpd2 Hpdf
    (length (sig_t gamma)) (adt_name a) srts []
    (ltac:(simpl; lia)) Htsinhab Hsrts) as x.
  destruct x as [x].
  rewrite <- Hpdf; auto.
Qed.


(*Corollary: all adts in context applied to inhabited sorts are inhabited*)
Theorem mk_pdf_adts_inhab {gamma} (gamma_valid: valid_context gamma) (pd: sort -> Set)
  (Hpd1: forall ts srts (Hts: find_ts_in_ctx gamma ts = None), domain_nonempty (domain pd) (s_cons ts srts))
  (Hpd2: forall m a ts srts (Hts: find_ts_in_ctx gamma ts = Some (m, a)), length srts <> length (m_params m) -> 
    domain_nonempty (domain pd) (s_cons ts srts))
  srts (Hsrts: ForallT (fun s : sort => domain_nonempty (domain (mk_pd gamma pd)) s) srts)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (srts_len: length srts = length (m_params m)):
  IndTypes.adt_rep m srts (mk_pd gamma pd) a a_in.
Proof. 
  assert (Hpd1': forall ts srts (Hts: find_ts_in_ctx gamma ts = None), 
    domain_nonempty (domain (mk_pd gamma pd)) (s_cons ts srts)).
  {
    intros t' s' Ht'.
    constructor.
    assert (Heq:domain (mk_pd gamma pd) (s_cons t' s') = mk_pd gamma pd (s_cons t' s')) by reflexivity.
    rewrite Heq.
    rewrite mk_pd_nonadt; auto.
    apply Hpd1; auto.
  }
  assert (Hpd2': forall m a ts srts (Hts: find_ts_in_ctx gamma ts = Some (m, a)), 
    length srts <> length (m_params m) -> 
    domain_nonempty (domain (mk_pd gamma pd)) (s_cons ts srts)).
  {
    intros m' a' t' s' Ht' Hlen'.
    constructor.
    assert (Heq:domain (mk_pd gamma pd) (s_cons t' s') = mk_pd gamma pd (s_cons t' s')) by reflexivity.
    rewrite Heq.
    destruct (mk_pd_adt_nolen pd t' s' Ht' Hlen') as [Heq' | Heq'].
    + rewrite Heq'.
      specialize (Hpd2 _ _ _ s' Ht' Hlen'). destruct Hpd2 as [x]. exact x.
    + rewrite Heq'. exact tt.
  }
  apply (all_adts_inhab gamma_valid (mk_pd gamma pd) Hpd1' Hpd2' (mk_pd_full _ pd gamma_valid) srts Hsrts); auto.
Qed.

(*And therefore, all types from [mk_pd] are inhabited if pd is full*)
Theorem mk_pd_inhab {gamma} (gamma_valid: valid_context gamma) pd
  (Hpdi: forall s, domain_nonempty (domain pd) s) :
  forall s : sort, domain_nonempty (domain (mk_pd gamma pd)) s.
Proof.
  intros s. induction s as [| | ts srts IH].
  - constructor. unfold domain. simpl. exact 0%Z.
  - constructor. unfold domain. simpl. exact 0%R.
  - constructor. unfold domain. simpl sort_to_ty.
    assert (Hpd: mk_pd gamma pd (s_cons ts srts)); [|auto].
    (*Here, case on whether ADT or not*)
    destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : Hts.
    + assert (Hfind:=Hts). apply find_ts_in_ctx_some in Hts. destruct Hts as [m_in [a_in Hts]]. subst.
      destruct (Nat.eqb_spec (length srts) (length (m_params m))) as [Hlen | Hlen].
      * rewrite mk_pd_full with (m:=m)(Hin:=a_in); auto.
        apply mk_pdf_adts_inhab; auto.
      * destruct (mk_pd_adt_nolen pd (adt_name a) srts Hfind Hlen) as [Heq' | Heq'].
        -- rewrite Heq'. specialize (Hpdi (s_cons (adt_name a) srts)). apply Hpdi.
        -- rewrite Heq'. exact tt.
    + rewrite (mk_pd_nonadt gamma pd ts srts Hts). specialize (Hpdi (s_cons ts srts)). apply Hpdi.
Qed.

(*And finally, we can construct a [pi_dom] that is full given any base [pi_dom]*)

Definition mk_pi_dom {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom) : pi_dom :=
  {| dom_aux := mk_pd gamma (dom_aux pd); domain_ne := mk_pd_inhab gamma_valid (dom_aux pd) (domain_ne pd) |}.

Definition mk_pi_dom_full {gamma} (gamma_valid: valid_context gamma) 
  (pd: pi_dom)  : pi_dom_full gamma (mk_pi_dom gamma_valid pd) := 
  Build_pi_dom_full gamma (mk_pi_dom gamma_valid pd) 
    (mk_pd_full gamma (dom_aux pd) gamma_valid).
