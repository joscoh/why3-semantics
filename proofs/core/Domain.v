(*Work with type pre-interpretation, which we call domain.
  In this file, we define domains, casting domains, and casting hlists of domains
  (which we call [arg_lists])*)
Require Import Types Hlist.
Require Export Coq.Reals.Reals.
From Equations Require Import Equations.
Set Bullet Behavior "Strict Subproofs".

Definition arg_list (domain: Types.sort -> Set) := hlist domain.

Definition domain (dom_aux: sort -> Set) (s: Types.sort) : Set :=
  match sort_to_ty s with
  | vty_int => Z
  | vty_real => R
  | _ => dom_aux s
  end.

(*Casting domains - will be VERY useful*)
Section DomCast.

Variable dom_aux : sort -> Set.
Notation domain := (domain dom_aux).

Definition dom_cast {v1 v2: Types.sort} (Heq: v1 = v2) (x: domain v1) : 
  domain v2 :=
  scast (f_equal domain Heq) x.

Lemma dom_cast_twice: forall {v1 v2: Types.sort} (Heq: v1 = v2) x,
  dom_cast Heq (dom_cast (eq_sym Heq) x) = x.
Proof.
  intros. destruct Heq; reflexivity.
Qed.

Lemma dom_cast_inj: forall {v1 v2: Types.sort} (Heq: v1 = v2) (x1 x2: domain v1),
  dom_cast Heq x1 = dom_cast Heq x2 ->
  x1 = x2.
Proof.
  intros. destruct Heq. apply H.
Qed.

Lemma dom_cast_compose {s1 s2 s3: Types.sort}
  (Heq1: s2 = s3) (Heq2: s1 = s2) x:
  dom_cast Heq1 (dom_cast Heq2 x) =
  dom_cast (eq_trans Heq2 Heq1) x.
Proof.
  subst. reflexivity.
Qed.

Lemma dom_cast_eq {s1 s2: Types.sort} (H1 H2: s1 = s2) x:
  dom_cast H1 x = dom_cast H2 x.
Proof.
  subst. unfold dom_cast. simpl.
  assert (H2 = eq_refl). apply UIP_dec. apply sort_eq_dec.
  rewrite H.
  reflexivity.
Qed.

Lemma dom_cast_eq'(s1 s2: Types.sort)
  (H1 H2: s1 = s2) (x y: domain s1):
  x = y ->
  dom_cast H1 x = dom_cast H2 y.
Proof.
  intros; subst. apply dom_cast_eq.
Qed.

Lemma dom_cast_refl {s1} (H: s1 = s1) x:
  dom_cast H x = x.
Proof.
  assert (H = eq_refl). apply UIP_dec. apply sort_eq_dec.
  subst; reflexivity.
Qed.

Lemma rewrite_dom_cast: forall (v1 v2: Types.sort) (Heq: v1 = v2)
  x,
  scast (f_equal domain Heq) x = dom_cast Heq x.
Proof.
  intros. reflexivity.
Qed.

Lemma move_dom_cast (v1 v2 v3: Types.sort)
  (H1: v1 = v3) (H2: v2 = v3) (x1: domain v1) (x2: domain v2):
  x1 = dom_cast (eq_trans H2 (Logic.eq_sym H1)) x2 ->
  dom_cast H1 x1 = dom_cast H2 x2.
Proof.
  intros.
  subst. reflexivity.
Qed.

End DomCast.

(*Define casting arg_lists*)
Section Cast.

(*Cast an [arg_list] - here we use a type with decidable equality*)
Definition cast_arg_list {domain: Types.sort -> Set} {l1 l2}
  (Heq: l1 = l2) (x: arg_list domain l1) : arg_list domain l2 :=
  scast (f_equal (fun x => arg_list domain x) Heq) x.

Lemma cast_arg_list_eq {d: Types.sort -> Set} {l1 l2: list Types.sort} (Heq1 Heq2: l1 = l2) 
  (a: arg_list d l1):
  cast_arg_list Heq1 a = cast_arg_list Heq2 a.
Proof.
  subst. assert (Heq2 = eq_refl). apply UIP_dec. apply list_eq_dec.
  apply sort_eq_dec. subst. reflexivity.
Qed.

Lemma cast_arg_list_inj: forall {domain: Types.sort -> Set} 
  {l1 l2: list Types.sort} (Heq: l1 = l2) (a1 a2: arg_list domain l1),
  cast_arg_list Heq a1 = cast_arg_list Heq a2 ->
  a1 = a2.
Proof.
  intros. destruct Heq. apply H.
Qed.

Definition cast_nth_eq {A: Set} {l1 l2: list A} (Heq: l1 = l2)
  (i: nat) (d: A) : List.nth i l1 d = List.nth i l2 d :=
  f_equal (fun (x: list A) => List.nth i x d) Heq.

Lemma hnth_cast_arg_list {domain: Types.sort -> Set} {l1 l2}
(Heq: l1 = l2) (x: arg_list domain l1) (i: nat) (d: Types.sort)
  (d1: domain d):
  hnth i (cast_arg_list Heq x) d d1 =
  scast (f_equal domain (cast_nth_eq Heq i d)) (hnth i x d d1).
Proof.
  destruct Heq. reflexivity.
Qed.

Lemma cons_inj_hd {A: Type} {x y: A} {l1 l2: list A}
  (C: x :: l1 = y :: l2):
  x = y.
Proof.
  injection C; auto.
Defined.

Lemma cons_inj_tl {A: Type} {x y : A} {l1 l2: list A}:
  x :: l1 = y :: l2 ->
  l1 = l2.
Proof.
  intros C. injection C. auto.
Defined.

Lemma cast_arg_list_cons {h1 h2: Types.sort} {d: Types.sort -> Set} {s1 s2: list Types.sort} 
  {x} {a}
  (Heq: h1 :: s1 = h2 :: s2):
  cast_arg_list Heq (HL_cons _ h1 s1 x a) =
  HL_cons d h2 s2 (scast (f_equal d (cons_inj_hd Heq)) x) 
    (cast_arg_list (cons_inj_tl Heq) a).
Proof.
  inversion Heq. subst.
  assert (Heq = eq_refl).
  apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
  subst. reflexivity. 
Qed.

Lemma hlist_tl_cast {d} {s1 s2: Types.sort} {t1 t2: list Types.sort}  
  (Heq: (s1:: t1) = (s2:: t2)) a:
  hlist_tl (cast_arg_list Heq a) = 
    @cast_arg_list d _ _ (cons_inj_tl Heq) (hlist_tl a).
Proof.
  inversion Heq. subst.
  assert (Heq = eq_refl). apply UIP_dec. apply list_eq_dec.
    apply sort_eq_dec. subst. reflexivity.
Qed.

Lemma hlist_hd_cast {d: Types.sort -> Set} 
  {s1 s2: Types.sort} {t1 t2: list Types.sort}
  {a: arg_list d (s1 :: t1)}
  (Heq1: s1 :: t1 = s2 :: t2)
  (Heq2: s1 = s2):
  hlist_hd (cast_arg_list Heq1 a) =
  scast (f_equal d Heq2) (hlist_hd a).
Proof.
  subst. inversion Heq1; subst.
  assert (Heq1 = eq_refl).
    apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
  subst. reflexivity.
Qed. 

Lemma cast_arg_list_compose {d: Types.sort -> Set} 
  {l1 l2 l3: list Types.sort} (Heq: l1 = l2)
  (Heq2: l2 = l3)
  (x: arg_list d l1):
  cast_arg_list Heq2 (cast_arg_list Heq x) =
  cast_arg_list (eq_trans Heq Heq2) x.
Proof.
  unfold cast_arg_list. rewrite scast_scast.
  rewrite eq_trans_map_distr. reflexivity.
Qed.

Lemma cast_arg_list_same {d: Types.sort -> Set} {l: list Types.sort}
  (Heq: l = l) (a: arg_list d l):
  cast_arg_list Heq a = a.
Proof.
  assert (Heq = Logic.eq_refl). apply UIP_dec. apply list_eq_dec.
  apply sort_eq_dec.
  subst. reflexivity.
Qed.

Lemma cast_arg_list_twice {domain: Types.sort -> Set} {l1 l2}
  (Heq: l1 = l2) (x: arg_list domain l2) :
  cast_arg_list Heq (cast_arg_list (eq_sym Heq) x) = x.
Proof.
  rewrite cast_arg_list_compose. apply cast_arg_list_same.
Qed.

Lemma cast_arg_list_switch {dom} {l1 l2: list sort} (Heq: l1 = l2) (a: arg_list dom l1) (a2: arg_list dom l2):
  cast_arg_list Heq a = a2 ->
  a = cast_arg_list (eq_sym Heq) a2.
Proof.
  intros; subst. reflexivity.
Qed.

(*Results we will need later for PatternProofs. These results hold in general,
  but we can give nicer casting results (dom_cast) if we assume arg_lists rather
  than arbitrary hlists*)

Lemma hlist_app_cast1 {f: sort -> Set} (l1 l2 l3: list sort) (h: arg_list f l1) h2 (Heq: l1 = l2):
  hlist_app f l2 l3 (cast_arg_list Heq h) h2 =
  cast_arg_list (f_equal (fun x => x ++ l3) Heq) (hlist_app f l1 l3 h h2).
Proof.
  subst. simpl. unfold cast_arg_list; simpl. reflexivity.
Qed.

Lemma hlist_rev_cast {f: sort -> Set} (l1 l2: list sort) (Heq: l1 = l2) (h1: arg_list f l1):
  hlist_rev f l2 (cast_arg_list Heq h1) =
  cast_arg_list (f_equal (fun x => rev x) Heq) (hlist_rev f l1 h1).
Proof.
  subst. reflexivity.
Qed.

Lemma hlist_app_hnth1 (dom: sort -> Set) tys1 tys2 (h1 : arg_list (domain dom) tys1) (h2: arg_list (domain dom) tys2) d1 d2 n:
  n < length tys1 ->
  exists Heq,
  hnth n (hlist_app _ tys1 tys2 h1 h2) d1 d2 =
  dom_cast _ Heq (hnth n h1 d1 d2).
Proof.
  revert n.
  induction tys1 as [| ty1 tys IH]; simpl.
  - intros n Hn. lia.
  - intros [| n'] Hn.
    + exists eq_refl. rewrite (hlist_inv h1). reflexivity.
    + destruct (IH (hlist_tl h1) n' (ltac:(lia))) as [Heq Hnth].
      exists Heq. rewrite (hlist_inv h1). simp hlist_app. simpl. auto.
Qed.

Lemma hlist_app_hnth2 (dom: sort -> Set) tys1 tys2 (h1 : arg_list (domain dom) tys1) (h2: arg_list (domain dom) tys2) d1 d2 n:
  n >= length tys1 ->
  exists Heq,
  hnth n (hlist_app _ tys1 tys2 h1 h2) d1 d2 =
  dom_cast _ Heq (hnth (n - length tys1) h2 d1 d2).
Proof.
  revert n.
  induction tys1; simpl.
  - intros n Hn. rewrite Nat.sub_0_r. exists eq_refl. reflexivity.
  - intros n Hn.
    remember (n - S (Datatypes.length tys1)) as j eqn : Hj.
    destruct j as [| j']; simpl.
    + assert (n = S (length tys1)) by lia. subst. 
      destruct (IHtys1 (hlist_tl h1) (length tys1) (ltac:(lia))) as [Heq1 IH].
      revert Heq1 IH. rewrite Nat.sub_diag. intros. exists Heq1.
      rewrite (hlist_inv h1). simp hlist_app. simpl. auto.
    + (*assert (Hngt: n > S (length tys1)) by lia.*) destruct n as [| n']; [discriminate|].
      assert (Hn': n' >= length tys1) by lia.
      destruct (IHtys1 (hlist_tl h1) n' Hn') as [Heq1 IH].
      revert Heq1 IH.
      replace (n' - length tys1) with (S j') by lia.
      intros. exists Heq1. rewrite (hlist_inv h1). simp hlist_app. simpl. auto.
Qed.

Lemma hlist_rev_hnth (dom: sort -> Set) i tys (h: arg_list (domain dom) tys) d1 d2:
  i < length tys ->
  exists Heq,
  hnth i (hlist_rev (domain dom) tys h) d1 d2 =
  dom_cast dom Heq (hnth (length tys - S i) h d1 d2).
Proof.
  revert i. induction tys as [| ty1 tys IH]; simpl.
  - intros i Hi; lia.
  - intros i Hi. remember (length tys - i) as j eqn : Hj. 
    destruct j as [| j'].
    + assert (i = length tys) by lia. subst.
      (*Use app2 lemma*)
      destruct (hlist_app_hnth2 dom _ _ (hlist_rev (domain dom) tys (hlist_tl h)) 
        (HL_cons (domain dom) ty1 [] (hlist_hd h) (HL_nil (domain dom))) d1 d2 (length tys)
        (ltac:(solve_len))) as [Heq1 Happ].
      revert Heq1 Happ. rewrite length_rev, Nat.sub_diag. simpl. intros.
      exists Heq1. rewrite (hlist_inv h). simp hlist_rev. simpl; auto.
    + (*Need IH and app1*)
      assert (Heq: nth j' tys d1 = nth i (rev tys ++ [ty1]) d1).
      {
        rewrite app_nth1 by solve_len.
        rewrite rev_nth; try lia. 
        f_equal. lia.
      }
      exists Heq.
      rewrite (hlist_inv h).
      simp hlist_rev.
     (*use app1 lemma*)
      destruct (hlist_app_hnth1 dom _ _ (hlist_rev (domain dom) tys (hlist_tl h)) 
        (HL_cons (domain dom) ty1 [] (hlist_hd h) (HL_nil (domain dom))) d1 d2 i
        (ltac:(solve_len))) as [Heq1 Happ].
      rewrite Happ.
      destruct (IH (hlist_tl h) i ltac:(lia)) as [Heq2 IH2].
      rewrite IH2. rewrite !dom_cast_compose.
      simpl. generalize dependent (eq_trans Heq2 Heq1).
      replace (length tys - S i) with j' by lia. intros.
      apply dom_cast_eq.
Qed.

End Cast.

Ltac gen_dom_cast := repeat match goal with |- context [dom_cast ?pd ?Heq ?x] =>
            let y := fresh "y" in
            set (y := dom_cast pd Heq x) in *; 
            generalize dependent Heq 
          end; simpl.