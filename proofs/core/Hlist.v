Require Import Coq.Lists.List.
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

Definition hlist_inv {A: Type} {f: A -> Type} {hd: A} {tl: list A}
  (h: hlist f (hd :: tl)) : h = HL_cons f hd tl (hlist_hd h) (hlist_tl h) :=
  match h with
  | HL_nil _ => idProp
  | HL_cons _ _ _ _ _ => eq_refl
  end.

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

(*TODO: Do we need the type version?*)
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
Qed.

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
Fixpoint hlist_map_filter {A B: Type} {f: A -> Type} {l: list B}
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
  end h.

Require Import Common.

(*Given an element in a list and an hlist, get the corresponding element
  of the hlist*)
Fixpoint get_hlist_elt {A: Type} (eq_dec: forall x y, {x = y} + {x <> y}) 
  {f: A -> Type} {l: list A}
  (h: hlist f l) (x: A)
  (Hinx: in_bool eq_dec x l) : f x :=
  (match l as l' return in_bool eq_dec x l' -> hlist f l' -> f x with
  | nil => fun Hin _ => False_rect _ (not_false Hin)
  | y :: tl => fun Hin h' =>
    (match (eq_dec x y) as b return b || in_bool eq_dec x tl ->
      f x with
    | left Heq => fun _ => ltac:(rewrite Heq; exact (hlist_hd h'))
    | right Hneq => fun Hin' => 
      get_hlist_elt eq_dec (hlist_tl h') x Hin'
    end) Hin
  end) Hinx h.