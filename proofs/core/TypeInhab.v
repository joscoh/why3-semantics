(*Separate out proofs for inhabited types*)
Require Import Syntax.
Require Import Types.
Require Import Typing.


(*First, we give a function version of this*)
(*Give fuel for termination*)
(*This is a terrible definition because we need to convince Coq that it terminates.
So we need lots of manual "fix" rather than existsb, forallb, fold_right, etc*)
Fixpoint typesym_inhab_fun (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (ts: typesym) (n: nat) : bool :=
match n with
| O => false
| S(n') =>
  in_dec typesym_eq_dec ts (sig_t s) && 
  negb (in_dec typesym_eq_dec ts seen_typesyms) &&
  match (find_constrs gamma ts) with
  | None => null ninhab_vars
  | Some constrs => negb (null constrs) && 
    (fix exists_constr (l: list funsym) : bool :=
      match l with
      | nil => false
      | c :: tl => 
        ((fix forall_ty (lt: list vty) : bool :=
          match lt with
          | nil => true
          | t :: ttl =>
            ((fix check_type (t: vty) : bool :=
              match t with
              | vty_int => true
              | vty_real => true
              | vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
              | vty_cons ts' vtys =>
                let bvars : list typevar :=
                  ((fix bad_vars (lvty: list vty) (lsym: list typevar) : list typevar :=
                  match lvty, lsym with
                  | x1 :: t1, x2 :: t2 => if check_type x1 then bad_vars t1 t2 else
                    x2 :: bad_vars t1 t2
                  | _, _ => nil
                  end) vtys (ts_args ts'))
                in
                typesym_inhab_fun bvars (ts :: seen_typesyms) ts' n'
              end) t) && forall_ty ttl
          end) (s_args c)) || (exists_constr tl)
      end) constrs
    end
  end.

(*We didn't want to write it with mutual recursion, but we can simplify now:*)
Fixpoint vty_inhab_fun (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (t: vty) (n: nat) :=
match t with
| vty_int => true
| vty_real => true
| vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
| vty_cons ts' vtys =>
    let bvars : list typevar :=
    ((fix bad_vars (lvty: list vty) (lsym: list typevar) : list typevar :=
    match lvty, lsym with
    | nil, nil => nil
    | x1 :: t1, x2 :: t2 => if vty_inhab_fun ninhab_vars seen_typesyms x1 n 
      then bad_vars t1 t2 else x2 :: bad_vars t1 t2
    | _, _ => nil
    end) vtys (ts_args ts')) in
  typesym_inhab_fun bvars (seen_typesyms) ts' n
end.

Fixpoint bad_vars (lvty: list vty) (lsym: list typevar) (f: vty -> bool) : list typevar :=
  match lvty, lsym with
  | x1 :: t1, x2 :: t2 => if f x1 then bad_vars t1 t2 f else
    x2 :: bad_vars t1 t2 f
  | _, _ => nil
  end.

Lemma bad_vars_eq: forall lvty lsym f,
  bad_vars lvty lsym f = map snd (filter (fun x => negb (f (fst x))) (combine lvty lsym)).
Proof.
  intros lvty lsym f; revert lsym; induction lvty; simpl; intros; auto.
  destruct lsym; auto.
  destruct (f a) eqn : Hfa; simpl; rewrite Hfa; simpl; try f_equal; auto.
Qed.
(*
Definition filter_combine {A B: Type} (l: list A) (l2: list B) (f: A -> bool) : list ( A * B) :=
    filter (fun x => f (fst x)) (combine l l2).
*)

Lemma vty_inhab_fun_eq: forall ninhab_vars seen_typesyms t n,
vty_inhab_fun ninhab_vars seen_typesyms t n =
((fix check_type (t: vty) : bool :=
match t with
| vty_int => true
| vty_real => true
| vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
| vty_cons ts' vtys =>
  (*A super awkward way to get around Coq's termination checker without a nested fixpoint*)
  (*let test : list vty :=
    filter check_type vtys in
  let bvars := map snd (filter (fun x => in_dec vty_eq_dec (fst x) test) 
    (combine vtys (ts_args ts'))) in*)


  (*let bvars := map snd (filter2 vtys (ts_args ts') (fun x => check_type x)) in*)
  (*let bvars : list typevar := nil
    (*bad_vars vtys (ts_args ts') check_type*)
    (*map snd (filter_combine vtys (ts_args ts') check_type)*)
    
    (filter (fun x => check_type (fst x)) (combine vtys (ts_args ts')))*)
    (*bad_vars vtys (ts_args ts') (check_type)*)
    let bvars :=
    ((fix bad_vars (lvty: list vty) (lsym: list typevar) : list typevar :=
    match lvty, lsym with
    | x1 :: t1, x2 :: t2 => if check_type x1 then bad_vars t1 t2 else
      x2 :: bad_vars t1 t2
    | _, _ => nil
    end) vtys (ts_args ts'))
  in
  typesym_inhab_fun bvars seen_typesyms ts' n
end) t).
Proof.
intros. unfold vty_inhab_fun. induction t; try reflexivity.
f_equal. simpl. generalize dependent (ts_args tsym).
induction vs as [| h tl IH]; intros; simpl; try reflexivity.
destruct l eqn : Hargs; try reflexivity.
inversion H; subst. rewrite H2.
destruct l; try reflexivity.
match goal with
| |- context [if ?b then ?c else ?d] => destruct b
end. simpl in IH.
rewrite IH; auto. rewrite IH; auto.
Qed.

Definition constr_inhab_fun (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (c: funsym) (n: nat) :=
forallb (fun t => vty_inhab_fun ninhab_vars seen_typesyms t n) (s_args c).

Lemma constr_inhab_fun_eq: forall ninhab_vars seen_typesyms c n,
constr_inhab_fun ninhab_vars seen_typesyms c n =
((fix forall_ty (lt: list vty) : bool :=
    match lt with
    | nil => true
    | t :: ttl => vty_inhab_fun ninhab_vars seen_typesyms t n && forall_ty ttl
    end) (s_args c)).
Proof.
intros. unfold constr_inhab_fun, forallb. reflexivity.
Qed.

Lemma existsb_ext: forall {A: Type} (f g: A -> bool) (l: list A),
  (forall x, f x = g x) ->
  existsb f l = existsb g l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma forallb_ext: forall {A: Type} (f g: A -> bool) (l: list A),
  (forall x, f x = g x) ->
  forallb f l = forallb g l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

(*A much more usable definition*)
Lemma typesym_inhab_fun_eq: forall (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (ts: typesym) (n: nat),
typesym_inhab_fun ninhab_vars seen_typesyms ts n =
match n with
| O => false
| S(n') =>
  in_dec typesym_eq_dec ts (sig_t s) && 
  negb (in_dec typesym_eq_dec ts seen_typesyms) &&
  match (find_constrs gamma ts) with
  | None => null ninhab_vars
  | Some constrs => negb (null constrs) && 
    existsb (fun c => constr_inhab_fun ninhab_vars (ts :: seen_typesyms) c n') constrs
  end
end.
Proof.
intros. unfold typesym_inhab_fun.
destruct n; try reflexivity.
destruct (in_dec typesym_eq_dec ts (sig_t s)); try reflexivity.
destruct (in_dec typesym_eq_dec ts seen_typesyms); try reflexivity; simpl.
destruct (find_constrs gamma ts) eqn : Hcon; try reflexivity.
destruct (null l) eqn : Hnull; try reflexivity; simpl.
apply existsb_ext. intros c.
rewrite constr_inhab_fun_eq.
apply forallb_ext. intros v.
rewrite vty_inhab_fun_eq. reflexivity. 
Qed.

(*First, we prove equivalence between the inductive and fixpoint definitions*)

Lemma sublist_greater: forall {A: Type}
(eq_dec: forall (x y : A), {x = y} + {x <> y}) (l1 l2: list A),
sublist l1 l2 ->
length l1 >= length l2 ->
NoDup l1 ->
sublist l2 l1.
Proof.
intros A eq_dec l1. induction l1; simpl; intros.
- assert (length l2 = 0) by lia.
  rewrite length_zero_iff_nil in H2.
  subst. auto.
- inversion H1; subst. unfold sublist.
  intros x Hinx.
  destruct (eq_dec x a); subst. left; reflexivity.
  right. apply (IHl1 (remove eq_dec a l2)); auto.
  + unfold sublist. intros y Hiny.
    destruct (eq_dec y a); subst. contradiction.
    apply in_in_remove; auto. apply H. right. auto.
  + assert (Hlen: In a l2). apply H. left; reflexivity.
    apply (remove_length_lt eq_dec) in Hlen. lia.
  + apply in_in_remove; auto.
Qed.

Lemma existsb_false: forall {A: Type} (f: A -> bool) (l: list A),
  (existsb f l = false) <-> (forall x : A, In x l -> f x = false).
Proof.
  intros; induction l; simpl; split; intros; auto. destruct H0.
  apply orb_false_elim in H. destruct H. destruct H0; subst; auto.
  apply IHl; auto.
  apply orb_false_intro. apply H. left; auto.
  apply IHl; auto.
Qed.

Lemma forallb_false: forall {A: Type} (f: A -> bool) (l: list A),
  (forallb f l = false) <-> (exists x : A, In x l /\ f x = false).
Proof.
  intros. induction l; simpl; split; intros; auto. inversion H. 
  destruct H as [x [[] _]].
  - apply andb_false_iff in H. destruct H.
    + exists a. split; auto.
    + apply IHl in H. destruct H as [x [Hinx Hx]]. exists x; split; auto.
  - apply andb_false_iff. destruct H as [x [[Ha|Hinx] Hx]]; subst.
    left; auto. right; apply IHl. exists x; split; auto.
Qed.


(*Proving equivalence is annoying because of the mutual recursion. We prove
  2 intermediate lemmas that rely on the IH of the 3rd, main lemma. Then,
  we use this 3rd lemma to give general versions of the first two:*)
Lemma vty_inhab_iff_aux: forall (recs: list typesym) (badvars: list typevar) (v: vty) (n: nat),
  (forall (badvars : list typevar) (ts : typesym),
  typesym_inhab recs badvars ts (typesym_inhab_fun badvars recs ts n)) ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  vty_inhab recs badvars v (vty_inhab_fun badvars recs v n).
Proof.
  intros recs b2 v n IH Hsub Hnodup Hn.
  induction v; simpl; try solve[constructor].
  + destruct (in_dec typevar_eq_dec v b2); simpl; constructor; auto.
  + match goal with | |- vty_inhab ?ts ?bs ?v (typesym_inhab_fun ?bb ?x ?y ?n) =>
    remember bb as bvars eqn : Hbad end.
    assert (bvars = bad_vars vs (ts_args tsym) (fun x => vty_inhab_fun b2 recs x n)). {
      subst. clear. generalize dependent (ts_args tsym). clear.
      induction vs; simpl; intros; auto.
      destruct l; auto.
      destruct l; auto.
      destruct (vty_inhab_fun b2 recs a n); try f_equal; auto.
    }
    clear Hbad.
    rewrite bad_vars_eq in H0.
    (*Both cases similar*)
    assert (Hcomb1: forall (x : vty) (y : typevar),
      In (x, y) (combine vs (ts_args tsym)) ->
      ~ In y bvars -> vty_inhab recs b2 x true). {
        subst. intros x y Hinxy C. rewrite in_map_iff in C. 
        destruct (vty_inhab_fun b2 recs x n) eqn : Hinhab.
        - rewrite <- Hinhab. rewrite Forall_forall in H.
          apply H. apply in_combine_l in Hinxy. auto.
        - exfalso. apply C. exists (x, y).
          split; simpl; auto. apply filter_In.
          split; auto. simpl. rewrite Hinhab; auto.
      }
    assert (Hcomb2: forall (x : vty) (y : typevar),
      In (x, y) (combine vs (ts_args tsym)) ->
      In y bvars -> vty_inhab recs b2 x false). { subst.
        intros x y Hinxy. rewrite in_map_iff. intros [[x' y'] [Hy Hin]].
        simpl in Hy; subst. rewrite filter_In in Hin. simpl in Hin; destruct Hin.
        assert (x = x'). {
          eapply combine_NoDup_r. 2: apply Hinxy. all: auto. destruct tsym; simpl.
          apply (reflect_iff _ _ (nodup_NoDup typevar_eq_dec ts_args)). auto.
        }
        subst. rewrite negb_true_iff in H1. rewrite <- H1.
        rewrite Forall_forall in H. apply H. apply in_combine_l in Hinxy. auto.
    }
    destruct (typesym_inhab_fun bvars recs tsym n) eqn : Hts;
      [apply vty_check_consT with (new_tvs:=bvars) | 
        apply vty_check_consF with (new_tvs:=bvars)  ]; auto; rewrite <- Hts;
      apply IH.
Qed.

Lemma constr_inhab_iff_aux: forall (recs: list typesym) (badvars: list typevar)
  (c: funsym) (n: nat),
  (forall (badvars : list typevar) (ts : typesym),
  typesym_inhab recs badvars ts (typesym_inhab_fun badvars recs ts n)) ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  constr_inhab recs badvars c
    (constr_inhab_fun badvars recs c n).
Proof.
  intros recs b1 c n IH Hsub Hnodup Hn.
  unfold constr_inhab_fun.
  destruct (forallb (fun t : vty => vty_inhab_fun b1 recs t n) (s_args c)) eqn : Hvall.
  - rewrite forallb_forall in Hvall.
    constructor. intros v Hv. rewrite <- (Hvall _ Hv). apply vty_inhab_iff_aux; auto.
  - apply forallb_false in Hvall.
    destruct Hvall as [v [Hinv Hv]].
    apply constr_checkF. exists v; split; auto. rewrite <- Hv.
    apply vty_inhab_iff_aux; auto.
Qed. 

Lemma typesym_inhab_iff: forall (recs: list typesym) (badvars: list typevar)
  (ts: typesym) (n:nat),
  wf_context s gamma ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  typesym_inhab recs badvars ts (typesym_inhab_fun badvars recs ts n).
Proof.
  intros recs badvars ts n Hwf. revert recs badvars ts.
  induction n; intros;[simpl|]. 
  - assert (sublist (sig_t s) recs) by 
    (apply (sublist_greater typesym_eq_dec _ _ H); auto; lia).
    destruct (in_dec typesym_eq_dec ts (sig_t s)); [|apply ts_check_empty; auto].
    apply ts_check_rec; auto.
  - rewrite typesym_inhab_fun_eq.
    destruct (in_dec typesym_eq_dec ts (sig_t s)); [simpl| apply ts_check_empty; auto].
    destruct (in_dec typesym_eq_dec ts recs); [apply ts_check_rec; auto|simpl].
    destruct (find_constrs gamma ts) eqn : Hcon.
    2 : {
      apply find_constrs_none in Hcon. destruct (null badvars) eqn : Hnull.
      - apply ts_check_typeT; auto.
      - apply ts_check_typeF; auto. rewrite Hnull; auto.
    }
    apply find_constrs_some in Hcon; [| apply Hwf].
    rename l into constrs.
    destruct (null constrs) eqn : Hnull; simpl.
      apply ts_check_adtF1 with(constrs:=constrs); auto.
    (*Now, we need a nested lemma for the constructors - TODO: separate?*)
    assert (Hconstrs: forall badvars (c: funsym),
      constr_inhab (ts :: recs) badvars c (constr_inhab_fun badvars (ts :: recs) c n)). {
      intros b1 c. assert (NoDup (ts :: recs)) by (constructor; auto).
      assert (sublist (ts :: recs) (sig_t s)) by (unfold sublist; simpl;
        intros x; simpl; intros [Hxts| Hxin]; subst; auto).
      apply constr_inhab_iff_aux; auto; simpl; try lia.
      intros. apply IHn; auto. simpl; lia.
    }
    destruct (existsb (fun c : funsym => constr_inhab_fun badvars (ts :: recs) c n) constrs) eqn : Hexcon.
    + apply existsb_exists in Hexcon. destruct Hexcon as [c [Hinc Hc]].
      apply ts_check_adtT with(constrs:=constrs); auto. rewrite Hnull; auto.
      exists c. split; auto. rewrite <- Hc. apply Hconstrs.
    + rewrite existsb_false in Hexcon.
      apply ts_check_adtF2 with(constrs:=constrs); auto.
      rewrite Hnull; auto. intros c Hc. rewrite <- (Hexcon _ Hc). apply Hconstrs.
Qed.

(*One more result: can't be true and false*)
(*TODO (might need all again)*)

(*Some corollaries of the above*)
Corollary constr_inhab_iff: forall (recs: list typesym) (badvars: list typevar)
(c: funsym) (n: nat),
  wf_context s gamma ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  constr_inhab recs badvars c (constr_inhab_fun badvars recs c n).
Proof.
  intros. apply constr_inhab_iff_aux; auto.
  intros. apply typesym_inhab_iff; auto.
Qed.

Corollary vty_inhab_iff: forall (recs: list typesym) (badvars: list typevar) (v: vty) (n: nat),
  wf_context s gamma ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  vty_inhab recs badvars v (vty_inhab_fun badvars recs v n).
Proof.
  intros. apply vty_inhab_iff_aux; auto.
  intros. apply typesym_inhab_iff; auto.
Qed.

(*Decidability*)

Corollary typesym_inhab_dec: forall (recs: list typesym) (badvars: list typevar)
  (ts: typesym) (n: nat),
  wf_context s gamma ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  {typesym_inhab recs badvars ts true} + {typesym_inhab recs badvars ts false}.
Proof.
  intros. destruct (typesym_inhab_fun badvars recs ts n) eqn : Hfun.
  left. rewrite <- Hfun. apply typesym_inhab_iff; auto.
  right. rewrite <- Hfun. apply typesym_inhab_iff; auto.
Defined.

(*TODO: show both cannot be true*)

(*Now, we want to show that this actually corresponds to inhabited types*)


 