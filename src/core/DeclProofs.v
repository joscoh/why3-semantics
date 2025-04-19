(*Here is a proof that justifies checking equality in
  the uniformity check in [check_decrease_fun] instead of
  getting the map and checking that it is uniform*)

From Proofs.core Require Import Typing.

Lemma ty_unif_equiv_aux (params: list typevar) (t: vty) (subs: list vty) (i: nat)
  (Hlen: length params = length subs)
  (Hn: NoDup params)
  (Hi: i < length params)
  (Hinith: aset_mem (nth i params ""%string) (type_vars t))
  (Heq: t = ty_subst params subs t):
  nth i subs vty_int = vty_var (nth i params ""%string).
Proof.
  induction t; try solve[inversion Hinith].
  - simpl in Hinith. simpl_set. subst.
    unfold ty_subst in Heq; simpl in Heq.
    rewrite ty_subst_fun_nth with (s:=vty_int) in Heq; auto.
  - rewrite ty_subst_cons in Heq.
    injection Heq. intros Hvs.
    (*Get the type that this var is in*)
    simpl in Hinith. simpl_set.
    destruct Hinith as [t1 [Hint1 Hinvar]].
    rewrite Forall_forall in H.
    specialize (H t1 Hint1 Hinvar).
    apply H.
    (*Now just use property of map*)
    destruct (In_nth _ _ vty_int Hint1) as [j [Hj Ht1]]; subst.
    rewrite Hvs at 1.
    rewrite map_nth_inbound with (d2:=vty_int); auto.
Qed.

(*If the types of the arguments being applied are equal to the
  funsym type, the substitution is the identity one*)
Lemma ty_unif_equiv (args: list vty) (params: list typevar) 
  (subs: list vty)
  (Hlen: length params = length subs)
  (Hn: NoDup params)
  (Hvars: forall x, In x params -> exists t, In t args /\ aset_mem x (type_vars t))
  (Heq: args = map (ty_subst params subs) args):
  subs = map vty_var params.
Proof.
  apply list_eq_ext'; [rewrite length_map; auto |].
  intros n d Hn'.
  rewrite nth_indep with (d':=vty_int); auto.
  assert (Hn1: n < length params) by lia.
  rewrite map_nth_inbound with (d2:=(""%string : typevar)) by auto.
  specialize (Hvars (nth n params ""%string) (nth_In params _ Hn1)).
  destruct Hvars as [t1 [Hint1 Hinnth]].
  apply ty_unif_equiv_aux with (params:=params)(t:=t1); auto.
  (*Again, need to find t1 position*)
  destruct (In_nth _ _ vty_int Hint1) as [j [Hj Ht1]]; subst.
  rewrite Heq at 1.
  rewrite map_nth_inbound with (d2:=vty_int); auto.
Qed.