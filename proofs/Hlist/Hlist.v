Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Export Cast.
(*Heterogenous list*)
Inductive hlist {A: Type} (f: A -> Type) : list A -> Type :=
  | HL_nil: hlist f nil
  | HL_cons: forall x tl,
    f x ->
    hlist f tl ->
    hlist f (x :: tl).

(*"inversion" for htlists - these lemmas allow us to avoid introducing
  extra axioms with "dependent destruction"*)

Definition hlist_hd {A: Type} {f: A -> Type} {hd: A} {tl: list A} 
  (h: hlist f (hd :: tl)) : f hd :=
  match h with
  | HL_nil _ => idProp
  | HL_cons _ _ _ hd tl => hd
  end.

Lemma hlist_hd_cons {A: Type} (f: A -> Type) {hd: A} {tl: list A}
  (hhd: f hd) (htl: hlist f tl):
  hlist_hd (HL_cons f hd tl hhd htl) = hhd.
Proof.
  reflexivity.
Qed.

Definition hlist_tl {A: Type} {f: A -> Type} {hd: A} {tl: list A} 
  (h: hlist f (hd :: tl)) : hlist f tl :=
  match h with
  | HL_nil _ => idProp
  | HL_cons _ _ _ hd tl => tl
  end.

Lemma hlist_tl_cons {A: Type} (f: A -> Type) {hd: A} {tl: list A}
  (hhd: f hd) (htl: hlist f tl):
  hlist_tl (HL_cons f hd tl hhd htl) = htl.
Proof.
  reflexivity.
Qed.

Definition hlist_inv {A: Type} {f: A -> Type} {hd: A} {tl: list A}
  (h: hlist f (hd :: tl)) : h = HL_cons f hd tl (hlist_hd h) (hlist_tl h) :=
  match h with
  | HL_nil _ => idProp
  | HL_cons _ _ _ _ _ => eq_refl
  end.

(*Need to prove awkwardly because "inversion" requires UIP; we want
  axiom-free*)
Lemma hlist_cons_inj {A: Type} (f: A -> Type) {hd: A} {tl: list A}
  (hhd1 hhd2: f hd) (htl1 htl2: hlist f tl)
  (Heq: HL_cons f hd tl hhd1 htl1 = HL_cons f hd tl hhd2 htl2):
  hhd1 = hhd2 /\ htl1 = htl2.
Proof.
  assert (Hhd:=Heq).
  apply (f_equal hlist_hd) in Hhd.
  rewrite !hlist_hd_cons in Hhd.
  subst; split; auto.
  apply (f_equal hlist_tl) in Heq.
  rewrite !hlist_tl_cons in Heq.
  auto.
Qed.

Definition hlist_nil {A: Type} {f: A -> Type}
  (h: hlist f nil) : h = HL_nil f :=
  match h with
  | HL_nil _ => eq_refl
  | HL_cons _ _ _ _ _ => idProp
  end.


(*Operations on hlists*)

(*Length*)
Fixpoint hlength {A: Type} {f: A -> Type} {l: list A} (h: hlist f l) : nat :=
  match h with
  | HL_nil _ => 0
  | HL_cons _ _ _ hd tl => 1 + hlength tl
  end.

Lemma hlength_eq {A: Type} {f: A -> Type} {l: list A} (h: hlist f l) :
  hlength h = length l.
Proof.
  induction h; simpl; auto.
Qed.

(*nth*)
Fixpoint hnth {A: Type} {f: A -> Type} {l: list A} (i: nat) (h: hlist f l)
  (d: A) (d': f d) : f (nth i l d) :=
  match l as l' return hlist f l' -> f (List.nth i l' d) with
  | nil => fun _ =>
    match i with
    | O => d'
    | S _ => d'
    end
  | hd :: tl => fun h =>
    match i with
    | O => hlist_hd h
    | S i' => hnth i' (hlist_tl h) d d'
    end
  end h.

(*filter*)
(*
Fixpoint hfilter {A: Type} {f: A -> Type} {l: list A} (g: A -> bool) (h: hlist f l)  :
  hlist f (filter g l) :=
  match l as l' return hlist f l' -> hlist f (filter g l') with
  | nil => fun _ => (@HL_nil _ _)
  | hd :: tl => fun h =>
    match (g hd) as b return hlist f (if b then hd :: filter g tl else filter g tl) with
    | true => HL_cons _ _ _ (hlist_hd h) (hfilter g (hlist_tl h))
    | false => hfilter g (hlist_tl h)
    end
  end h.

(*hlist to list*)
Fixpoint hlist_to_list {A: Type} {f: A -> Type} {l: list A} (h: hlist f l)
  {a: A} (Hall: Forall (fun x => x = a) l) :
  list (f a) :=
  match l as l' return hlist f l' -> Forall (fun x => x = a) l' ->
    list (f a) with
  | nil => fun _ _ => nil
  | hd :: tl => fun hl Hall =>
    (*need dependent typecast here*)
    cast (f_equal f (Forall_inv Hall)) (hlist_hd hl) :: hlist_to_list (hlist_tl hl) (Forall_inv_tail Hall)
  end h Hall.

Lemma hlist_to_list_length {A: Type} {f: A -> Type} {l: list A} (h: hlist f l)
  {a: A} (Hall: Forall (fun x => x = a) l) :
  length (hlist_to_list h Hall) = hlength h.
Proof.
  revert Hall.
  induction l; simpl; intros.
  rewrite (hlist_nil h). reflexivity.
  rewrite (hlist_inv h) at 2. simpl. f_equal.
  apply IHl.
Qed.

Lemma all_nth {A: Type} {P: A -> Prop} {l: list A} (Hall: Forall P l) 
  (i: nat) (d: A) (Hi: i < length l) :
  P (nth i l d).
Proof.
  rewrite Forall_forall in Hall. apply Hall.
  apply nth_In. apply Hi.
Qed.

(*Existential is because of weird UIP-related stuff*)
Lemma hlist_to_list_nth: forall {A: Type} {f: A -> Type} {l: list A}
  (h: hlist f l) {a: A} (Hall: Forall (fun x => x = a) l) (i: nat)
  (Hi: i < length l)
  (d: f a) (d1: A) (d2: f d1),
  exists Heq,
  List.nth i (hlist_to_list h Hall) d =
  cast Heq (hnth i h d1 d2).
Proof.
  intros A f l.
  induction l; simpl; intros; subst; simpl.
  - lia.
  - destruct i.
    + exists (f_equal f (Forall_inv Hall)). reflexivity.
    + apply IHl. lia.
Qed. 

(*Version for decidable equality*)

Lemma hlist_to_list_nth_dec: forall {A: Type} {f: A -> Type} {l: list A}
  (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (h: hlist f l) {a: A} (Hall: Forall (fun x => x = a) l) (i: nat)
  (Hi: i < length l)
  (d: f a) (d1: A) (d2: f d1) Heq,
  List.nth i (hlist_to_list h Hall) d =
  cast (f_equal f Heq) (hnth i h d1 d2).
Proof.
  intros A f l.
  induction l; simpl; intros; subst; simpl.
  - lia.
  - destruct i.
    + unfold cast.
      assert (Forall_inv Hall = eq_refl). {
        apply UIP_dec. apply eq_dec.
      }
      rewrite H. reflexivity.
    + apply IHl with (d1:=d1) (d2:=d2) (Heq:=eq_refl). apply eq_dec.
      lia.
Qed. 

Lemma hlist_to_list_nth_dec': forall {A: Type} {f: A -> Type} {l: list A}
  (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (h: hlist f l) {a: A} (Hall: Forall (fun x => x = a) l) (i: nat)
  (Hi: i < length l)
  (d: f a) (d1: A) (d2: f d1),
  List.nth i (hlist_to_list h Hall) d =
  cast (f_equal f (all_nth Hall i d1 Hi)) (hnth i h d1 d2).
Proof.
  intros. apply hlist_to_list_nth_dec. apply eq_dec. apply Hi.
Qed.

Lemma hlist_to_list_nth_dec_set: forall {A: Set} {f: A -> Set} {l: list A}
  (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (h: hlist f l) {a: A} (Hall: Forall (fun x => x = a) l) (i: nat)
  (Hi: i < length l)
  (d: f a) (d1: A) (d2: f d1) Heq,
  List.nth i (hlist_to_list h Hall) d =
  scast (f_equal f Heq) (hnth i h d1 d2).
Proof.
  intros A f l.
  induction l; simpl; intros; subst; simpl.
  - lia.
  - destruct i.
    + unfold cast.
      assert (Forall_inv Hall = eq_refl). {
        apply UIP_dec. apply eq_dec.
      }
      rewrite H. reflexivity.
    + apply IHl with (d1:=d1) (d2:=d2) (Heq:=eq_refl). apply eq_dec.
      lia.
Qed. 

Lemma hlist_to_list_nth_dec_set': forall {A: Set} {f: A -> Set} {l: list A}
  (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (h: hlist f l) {a: A} (Hall: Forall (fun x => x = a) l) (i: nat)
  (Hi: i < length l)
  (d: f a) (d1: A) (d2: f d1),
  List.nth i (hlist_to_list h Hall) d =
  scast (f_equal f (all_nth Hall i d1 Hi)) (hnth i h d1 d2).
Proof.
  intros. apply hlist_to_list_nth_dec_set. apply eq_dec. apply Hi.
Qed.

Lemma hlist_to_list_irrel: forall {A: Type} {f: A -> Type} {l: list A}
(eq_dec: forall (x y : A), {x = y} + {x <> y})
(h: hlist f l) {a: A} (Ha1 Ha2: Forall (fun x => x = a) l),
hlist_to_list h Ha1 = hlist_to_list h Ha2.
Proof.
  intros.
  revert Ha1 Ha2. induction l; simpl; intros. reflexivity.
  f_equal.
  apply cast_eq. apply eq_dec. 
  2: apply IHl.
  inversion h; subst.
  assert (a = a0). inversion Ha1; subst. reflexivity.
  subst. apply X.
Qed.

Lemma hlist_to_list_inj: forall {A: Type} {f: A -> Type} {l: list A}
(eq_dec: forall (x y : A), {x = y} + {x <> y})
(h1 h2: hlist f l) {a: A} (H: Forall (fun x => x = a) l),
hlist_to_list h1 H = hlist_to_list h2 H -> h1 = h2.
Proof.
  intros. induction l; simpl.
  - rewrite (hlist_nil h1), (hlist_nil h2). reflexivity.
  - rewrite (hlist_inv h1), (hlist_inv h2).
    rewrite (hlist_inv h1), (hlist_inv h2) in H0.
    simpl in H0. inversion H0; subst.
    f_equal. apply cast_inj in H2; auto.
    eapply IHl. apply H3.
Qed.*)

(*extensional equality for hlists*)
Lemma hlist_ext_eq {A: Type} {f: A -> Type} {l: list A}
  (h1 h2: hlist f l) (d: A) (d': f d) :
  (forall i, (i < length l) -> hnth i h1 d d' = hnth i h2 d d') ->
  h1 = h2.
Proof.
  revert h2.
  induction h1; simpl; intros.
  - rewrite (hlist_nil h2). reflexivity.
  - rewrite (hlist_inv h2).
    assert (f0 = hlist_hd h2). {
      assert (0 < S (length tl)) by lia.
      specialize (H _ H0). apply H.
    }
    rewrite H0. f_equal.
    apply IHh1. intros i Hi.
    assert (S i < S (length tl)) by lia.
    specialize (H _ H1). apply H.
Qed.

(*One specialized definition we need*)
(*Fixpoint hlist_map_filter {A B: Type} {f: A -> Type} {l: list B}
  (f1: B -> A) (h: hlist f (map f1 l)) (g: B -> bool) :
  hlist f (map f1 (filter g l)) :=
  match l as l' return hlist f (map f1 l') -> 
    hlist f (map f1 (filter g l')) with
  | nil => fun _ => (@HL_nil _ _)
  | hd :: tl => fun hmap =>
    match (g hd) as b return 
      hlist f (map f1 (if b then hd :: (filter g tl) else (filter g tl))) with
    | true => HL_cons _ _ _ (hlist_hd hmap) (hlist_map_filter f1 (hlist_tl hmap) g)
    | false => (hlist_map_filter f1 (hlist_tl hmap) g)
    end
  end h.*)

Require Export HlistUtil.

(*Given an element in a list and an hlist, get the corresponding element
  of the hlist*)
Fixpoint get_hlist_elt {A: Type} (eq_dec: forall x y, {x = y} + {x <> y}) 
  {f: A -> Type} {l: list A}
  (h: hlist f l) (x: A)
  (Hinx: inb eq_dec x l) : f x :=
  (match l as l' return inb eq_dec x l' -> hlist f l' -> f x with
  | nil => fun Hin _ => is_false Hin
  | y :: tl => fun Hin h' =>
    (match (eq_dec x y) as b return b || inb eq_dec x tl ->
      f x with
    | left Heq => fun _ => ltac:(rewrite Heq; exact (hlist_hd h'))
    | right Hneq => fun Hin' => 
      get_hlist_elt eq_dec (hlist_tl h') x Hin'
    end) Hin
  end) Hinx h.

Section Gen.

Fixpoint gen_hlist {A: Type} (f: A -> Type) (g: forall (a: A), f a)
  (l: list A) :
  hlist f l :=
  match l as l' return hlist f l' with
  | nil => HL_nil _
  | x :: xs => HL_cons _ x xs (g x) (gen_hlist f g xs)
  end.

Lemma gen_hlist_get_elt {A: Type}
  (eq_dec: forall x y, {x = y} + {x <> y}) 
  {f: A -> Type} {g: forall (a: A), f a} {l: list A} (x: A)
  (Hinx: inb eq_dec x l):
  get_hlist_elt eq_dec (gen_hlist f g l) x Hinx = g x.
Proof.
  induction l; simpl. inversion Hinx.
  simpl in Hinx.
  destruct (eq_dec x a); subst; auto.
Qed.

Lemma gen_hlist_hnth {A: Type} {f: A -> Type} {g: forall a, f a}
  {l: list A} (d1: A) (d2: f d1) (i: nat) (Hi: i < length l):
  hnth i (gen_hlist f g l) d1 d2 =
  g (nth i l d1).
Proof.
  generalize dependent i.
  induction l; simpl; intros; destruct i; auto; try lia.
  apply IHl. lia.
Qed.

End Gen.

Section GenI.

Fixpoint gen_hlist_i {A: Type} (f: A -> Type) (l: list A) (d: A)
  (g: forall (i: nat), Nat.ltb i (length l) -> f (nth i l d)) : hlist f l :=
  match l as l' return (forall (i: nat), Nat.ltb i (length l') -> f (nth i l' d)) -> hlist f l' with
  | nil => fun _ => HL_nil _
  | x :: xs => fun g => HL_cons _ x xs (g 0 eq_refl) (gen_hlist_i f xs d 
    (fun i Hi => g (S i) Hi))
  end g.

Lemma gen_hlist_i_nth {A: Type} {f: A -> Type} {l: list A} {d: A}
  {g: forall (i: nat), Nat.ltb i (length l) -> f (nth i l d)} {i: nat} d2 
  (Hi: Nat.ltb i (length l)):
  hnth i (gen_hlist_i f l d g) d d2 = g i Hi.
Proof.
  revert g.
  generalize dependent i. induction l; simpl; intros.
  - assert (i < 0) by (apply Nat.ltb_lt; auto).
    inversion H.
  - destruct i; auto.
    + (*Booleans help us to get proof irrelevance here*)
      f_equal. apply bool_irrelevance.
    + erewrite IHl. reflexivity.
Qed. 

End GenI.

(*Convert between tuples and hlists*)
Section Tup.

(*Iterated tuple*)
Fixpoint big_sprod (l: list Set) : Set :=
  match l with
  | nil => unit
  | x :: xs => (x * (big_sprod xs))%type
  end.

(*Convert between a [big_sprod] and an [hlist]*)

Fixpoint big_sprod_to_hlist {A: Set} {f: A -> Set} {l: list A} (x: big_sprod (map f l))
  {struct l} : hlist f l :=
  match l as l' return big_sprod (map f l') -> hlist f l' with
  | nil => fun _ => HL_nil _
  | x :: xs => fun p => HL_cons _ x xs (fst p) (big_sprod_to_hlist (snd p))
  end x.

Fixpoint hlist_to_big_sprod {A: Set} {f: A -> Set} {l: list A} (h: hlist f l) :
  big_sprod (map f l) :=
  match l as l' return hlist f l' -> big_sprod (map f l') with
  | nil => fun _ => tt
  | x :: xs => fun h => (hlist_hd h, hlist_to_big_sprod (hlist_tl h))
  end h.

Lemma hlist_to_big_sprod_inv {A: Set} {f: A -> Set} {l: list A} (x: big_sprod (map f l)):
  hlist_to_big_sprod (big_sprod_to_hlist x) = x.
Proof.
  induction l; simpl; [| rewrite IHl]; destruct x; reflexivity.
Qed.

Lemma big_sprod_to_hlist_inv {A: Set} {f: A -> Set} {l: list A} (h: hlist f l):
  big_sprod_to_hlist (hlist_to_big_sprod h) = h.
Proof.
  induction l; simpl.
  - symmetry. apply hlist_nil.
  - rewrite IHl. symmetry. apply hlist_inv.
Qed.


(*It is easier to convert to an hlist and use hnth than to find the ith
  element of a big_tuple directly*)
(*Get the ith element of a [big_sprod]*)
Definition big_sprod_ith {A: Set} {f: A -> Set} {l: list A} 
  (x: big_sprod (map f l)) (i: nat) (d1: A) (d2: f d1) : f (nth i l d1) :=
  hnth i (big_sprod_to_hlist x) d1 d2.

Lemma big_sprod_ext {A: Set} {f: A -> Set} (l: list A) 
  (x1 x2: big_sprod (map f l)) (d1: A) (d2: f d1)
  (Hext: forall i, i < length l -> big_sprod_ith x1 i d1 d2 = big_sprod_ith x2 i d1 d2):
  x1 = x2.
Proof.
  (*Use inverse functions*)
  rewrite <- (hlist_to_big_sprod_inv x1), <- (hlist_to_big_sprod_inv x2).
  f_equal.
  apply hlist_ext_eq with (d:=d1)(d':=d2).
  apply Hext.
Qed.

End Tup.