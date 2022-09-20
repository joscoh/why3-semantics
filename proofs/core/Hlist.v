Require Import Coq.Lists.List.
Require Import Lia.
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

Definition cast {A1 A2: Type} (H: A1 = A2) (x: A1) : A2 :=
  match H with
  | eq_refl => x
  end.

  Require Import Coq.Logic.Eqdep_dec.
Lemma cast_eq: forall {A: Type} {f: A -> Type} 
  (eq_dec: forall (x y : A), { x =y} + { x <> y}) {x1 x2: A}
  (Heq1 Heq2: x1 = x2)
  (y1: f x1) (y2: f x2),
  cast (f_equal f Heq1) y1 = cast (f_equal f Heq2) y1.
Proof.
  intros. unfold cast. subst. simpl.
  assert (Heq2 = eq_refl). {
    apply UIP_dec. apply eq_dec.
  }
  rewrite H. reflexivity.
Qed.

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
  match l as l' return hlist f (map f1 l') -> hlist f (map f1 (filter g l')) with
  | nil => fun _ => (@HL_nil _ _)
  | hd :: tl => fun hmap =>
    match (g hd) as b return 
      hlist f (map f1 (if b then hd :: (filter g tl) else (filter g tl))) with
    | true => HL_cons _ _ _ (hlist_hd hmap) (hlist_map_filter f1 (hlist_tl hmap) g)
    | false => (hlist_map_filter f1 (hlist_tl hmap) g)
    end
  end h.

Definition hcast {A: Type} {f: A -> Type} {l1 l2: list A}
  (Heq: l1 = l2) (x: hlist f l1) : hlist f l2 :=
  match Heq with
  | eq_refl => x
  end.

  
(*
Lemma hlist_map_filter_eq {A B: Type} {f: A -> Type} {l1 l2: list B}
  (eq_dec: forall (x y: A), { x = y} + {x <> y})
  (f1: B -> A) (h1: hlist f (map f1 l1)) (h2: hlist f (map f1 l2))
  (g: B -> bool) (Heq: filter g l1 = filter g l2):
  hlist_map_filter f1 h1 g = hcast (f_equal (map f1) (eq_sym Heq)) 
    (hlist_map_filter f1 h2 g).
Proof.
  generalize dependent (f_equal (map f1) (eq_sym Heq)).
  generalize dependent l2. revert f1 h1 g.
  induction l1; simpl; intros; subst; simpl.
  - destruct l2; simpl in *.
    + unfold hcast.
      assert (e = eq_refl) by (apply UIP_dec; apply list_eq_dec; apply eq_dec).
      rewrite H. reflexivity.
    + destruct (g b); simpl.
      * inversion Heq.
      * unfold hcast.
        destruct e.
        assert (e = eq_refl).
      
      
      
      set (h3:=(hlist_map_filter f1 (hlist_tl h2) g)) in |- *.
        rewrite <- Heq in h3.
        
        
        
        set (x :=filter g l2) in *.  rewrite <- Heq. subst. subst Heq.  subst Heq. rewrite <- Heq in e |- *.
      
      
      rewrite <- Heq in e. subst. assert ((map f1 (filter g l2)) = nil). rewrite <- Heq. reflexivity.
        unfold hcast.
        destruct (hlist_map_filter f1 (hlist_tl h2) g) eqn : Hh.
        Search 
        destruct Heq.
        rewrite H.
        subst. assert ((hlist_map_filter f1 (hlist_tl h2) g) = HL_nil f).  
      
      
      
      unfold hcast. simpl.
      
      
      
      inver
    
    
    
    reflexivity. subst.*)