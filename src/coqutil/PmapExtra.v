(*Additional Theorems about Pmaps/Zmaps*)
From stdpp Require pmap zmap. 
Require Import CoqUtil.

Import pmap zmap.

(*Boolean Equality for pmaps (with NO proofs)*)
Section PmapEq.
Context {A: Type} (eqb : A -> A -> bool).
Fixpoint pmap_ne_eqb (p1 p2: Pmap_ne A) : bool :=
  match p1, p2 with
  | PNode001 p1, PNode001 p2 => pmap_ne_eqb p1 p2
  | PNode010 x1, PNode010 x2 => eqb x1 x2
  | PNode011 x1 p1, PNode011 x2 p2 => eqb x1 x2 && pmap_ne_eqb p1 p2
  | PNode100 p1, PNode100 p2 => pmap_ne_eqb p1 p2
  | PNode101 p1 p2, PNode101 p3 p4 => pmap_ne_eqb p1 p3 && pmap_ne_eqb p2 p4
  | PNode110 p1 x1, PNode110 p2 x2 => eqb x1 x2 && pmap_ne_eqb p1 p2
  | PNode111 p1 x1 p2, PNode111 p3 x2 p4 => eqb x1 x2 && pmap_ne_eqb p1 p3 && pmap_ne_eqb p2 p4
  | _, _ => false
  end.

Definition pmap_eqb (p1 p2: Pmap A) : bool :=
  match p1, p2 with
  | PEmpty, PEmpty => true
  | PNodes p1, PNodes p2 => pmap_ne_eqb p1 p2
  | _, _ => false
  end.

(*Now we prove equivalence*)
Lemma pmap_ne_eqb_spec_aux (Heqb: forall (x y: A), x = y <-> eqb x y = true)
  (p1 p2: Pmap_ne A) (s: forall x y, {x = y} + {x <> y}) (Hs:
    forall x y, proj_sumbool _ _ (s x y) = eqb x y):
  pmap_ne_eqb p1 p2 = @Pmap_ne_eq_dec _ s p1 p2.
Proof.
  generalize dependent s.
  revert p2.
  induction p1; simpl; intros; destruct p2; auto;
  unfold sumbool_rec, sumbool_rect, decide_rel;
  try (rewrite IHp1 with (s:=s));
  try (rewrite <- Hs); 
  try (rewrite IHp1_1 with (s:=s));
  try (rewrite IHp1_2 with (s:=s));
  auto;
  try progress(destruct (Pmap_ne_eq_dec p1 p2)); auto;
  try progress(destruct (s a a0)); auto;
  try progress(destruct (Pmap_ne_eq_dec p1_1 p2_1)); auto;
  destruct(Pmap_ne_eq_dec p1_2 p2_2); reflexivity.
Qed.

Lemma pmap_ne_eqb_spec (Heqb: forall (x y: A), x = y <-> eqb x y = true)
  (p1 p2: Pmap_ne A):
  pmap_ne_eqb p1 p2 = @Pmap_ne_eq_dec _ (dec_from_eqb eqb Heqb) p1 p2.
Proof.
  apply pmap_ne_eqb_spec_aux, dec_from_eqb_spec; auto.
Qed.

Lemma pmap_eqb_spec (Heqb: forall (x y: A), x = y <-> eqb x y = true)
  (p1 p2: Pmap A):
  pmap_eqb p1 p2 = @Pmap_eq_dec _ (dec_from_eqb eqb Heqb) p1 p2.
Proof.
  unfold pmap_eqb, Pmap_eq_dec.
  destruct p1; destruct p2; auto.
  unfold sumbool_rec, sumbool_rect, decide_rel.
  rewrite pmap_ne_eqb_spec_aux with (s:=(dec_from_eqb eqb Heqb)); auto.
  - destruct (Pmap_ne_eq_dec p p0); reflexivity.
  - apply dec_from_eqb_spec.
Qed.

Definition zmap_eqb (z1 z2: Zmap A) : bool :=
  option_eqb eqb (Zmap_0 z1) (Zmap_0 z2) &&
  pmap_eqb (Zmap_pos z1) (Zmap_pos z2) &&
  pmap_eqb (Zmap_neg z1) (Zmap_neg z2).

Lemma zmap_eqb_spec (Heqb: forall (x y: A), x = y <-> eqb x y = true)
  (z1 z2: Zmap A):
  zmap_eqb z1 z2 = @Zmap_eq_dec _ (dec_from_eqb eqb Heqb) z1 z2.
Proof.
  unfold zmap_eqb, Zmap_eq_dec.
  destruct z1 as [z01 zp1 zn1].
  destruct z2 as [z02 zp2 zn2].
  simpl.
  unfold decide, decide_rel.
  rewrite option_eqb_spec with (Heqb:=Heqb).
  destruct (option_eq_dec z01 z02); simpl; auto.
  rewrite !pmap_eqb_spec with (Heqb:=Heqb).
  destruct (Pmap_eq_dec zp1 zp2); simpl; auto.
  destruct (Pmap_eq_dec zn1 zn2); reflexivity.
Qed.

End PmapEq.

(*A "Forall" Predicate for Pmap/Zmap*)
Section PmapForall.

Inductive pmap_ne_Forall {A: Type} (P: A -> Prop) : Pmap_ne A -> Prop :=
  | pforall001 p: pmap_ne_Forall P p -> pmap_ne_Forall P (PNode001 p)
  | pforall010 x: P x -> pmap_ne_Forall P (PNode010 x)
  | pforall011 x p: P x -> pmap_ne_Forall P p -> pmap_ne_Forall P (PNode011 x p)
  | pforall100 p: pmap_ne_Forall P p -> pmap_ne_Forall P (PNode100 p)
  | pforall101 p1 p2: pmap_ne_Forall P p1 -> pmap_ne_Forall P p2 -> 
      pmap_ne_Forall P (PNode101 p1 p2)
  | pforall110 p x:P x -> pmap_ne_Forall P p -> pmap_ne_Forall P (PNode110 p x)
  | pforall111 p1 x p2: P x -> pmap_ne_Forall P p1 -> pmap_ne_Forall P p2 -> 
      pmap_ne_Forall P (PNode111 p1 x p2).

Inductive pmap_Forall {A: Type} (P: A -> Prop): Pmap A -> Prop :=
  | pforall_empty: pmap_Forall P PEmpty
  | pforall_nodes p: pmap_ne_Forall P p -> pmap_Forall P (PNodes p).

Definition option_Forall {A: Type} (P: A -> Prop) (o: option A) : Prop :=
  match o with
  | Some y => P y
  | None => True
  end.

Definition Zmap_Forall {A: Type} (P: A -> Prop) (z: Zmap A) : Prop :=
  option_Forall P z.(Zmap_0) /\
  pmap_Forall P z.(Zmap_pos) /\
  pmap_Forall P z.(Zmap_neg).

(*Then, a version amenable for nested induction*)

Definition mk_pmap_ne_Forall {A: Type} {P: A -> Prop} :=
  fun (f: forall x, P x) =>
  fix mk_Forall (p: Pmap_ne A) {struct p} : pmap_ne_Forall P p :=
    match p with
    | PNode001 p => pforall001 _ _ (mk_Forall p)
    | PNode010 x => pforall010 _ _ (f x)
    | PNode011 x p => pforall011 _ _ _ (f x) (mk_Forall p)
    | PNode100 p =>  pforall100 _ _ (mk_Forall p)
    | PNode101 p1 p2 => pforall101 _ _ _ (mk_Forall p1) (mk_Forall p2)
    | PNode110 p x => pforall110 _ _ _ (f x) (mk_Forall p)
    | PNode111 p1 x p2 => pforall111 _ _ _ _ (f x) (mk_Forall p1) (mk_Forall p2)
    end.

Definition mk_pmap_Forall  {A: Type} {P: A -> Prop} 
   (f: forall x, P x) (p: Pmap A) : pmap_Forall P p :=
   match p with
   | PEmpty => pforall_empty _
   | PNodes p => pforall_nodes _ _ (mk_pmap_ne_Forall f p)
   end.

Definition mk_option_Forall {A: Type} {P: A -> Prop}
  (f: forall x, P x) (o: option A) : option_Forall P o :=
  match o with
  | Some y => f y
  | None => I
  end.

Definition mk_Zmap_Forall {A: Type} {P: A -> Prop}
  (f: forall x, P x) (z: Zmap A) : Zmap_Forall P z :=
  conj (mk_option_Forall f z.(Zmap_0))
    (conj (mk_pmap_Forall f z.(Zmap_pos))
      (mk_pmap_Forall f z.(Zmap_neg))).

(*Prove Equality from Forall*)

Lemma option_eqb_Forall {A: Type} {eqb: A -> A -> bool} {o1: option A}
  (Hall: option_Forall (fun x => forall y, x = y <-> eqb x y) o1) o2:
  o1 = o2 <-> option_eqb eqb o1 o2.
Proof.
  destruct o1 as [y1|]; destruct o2 as [y2|]; simpl in *;
  try solve[solve_eqb_eq].
  rewrite <- Hall; solve_eqb_eq.
Qed.

Lemma pmap_ne_eqb_Forall {A: Type} {eqb: A -> A -> bool} {p1: Pmap_ne A}
  (Hall: pmap_ne_Forall (fun x => forall y, x = y <-> eqb x y) p1) p2:
  p1 = p2 <-> pmap_ne_eqb eqb p1 p2.
Proof.
  revert p2. induction p1; destruct p2; try solve[solve_eqb_eq]; simpl;
  inversion Hall; subst. 
  - rewrite <- IHp1; auto. solve_eqb_eq.
  - rewrite <- H0; solve_eqb_eq.
  - rewrite !andb_true, <- H1, <- IHp1; auto. solve_eqb_eq.
  - rewrite <- IHp1; auto. solve_eqb_eq.
  - rewrite !andb_true, <- IHp1_1, <- IHp1_2; auto. solve_eqb_eq.
  - rewrite andb_true, <- H1, <- IHp1; auto. solve_eqb_eq.
  - rewrite !andb_true, <- H2, <- IHp1_1, <- IHp1_2; auto. solve_eqb_eq.
Qed. 

Lemma pmap_eqb_Forall {A: Type} {eqb: A -> A -> bool} {p1: Pmap A}
  (Hall: pmap_Forall (fun x => forall y, x = y <-> eqb x y) p1) p2:
  p1 = p2 <-> pmap_eqb eqb p1 p2.
Proof.
  unfold pmap_eqb.
  destruct Hall as [| p1 Hall]; destruct p2 as [| p2]; auto;
  try solve[solve_eqb_eq].
  rewrite <- (pmap_ne_eqb_Forall Hall). solve_eqb_eq.
Qed.


Lemma zmap_eqb_Forall {A: Type} {eqb: A -> A -> bool} {z1: Zmap A}
  (Hall: Zmap_Forall (fun x => forall y, x = y <-> eqb x y) z1) z2:
  z1 = z2 <-> zmap_eqb eqb z1 z2.
Proof. 
  destruct Hall as [Ho [Hz Hp]].
  destruct z1 as [o p n]; destruct z2 as [o2 p2 n2]; 
  unfold zmap_eqb; simpl in *.
  rewrite !andb_true, <- (option_eqb_Forall Ho), 
  <- (pmap_eqb_Forall Hz), <- (pmap_eqb_Forall Hp).
  solve_eqb_eq.
Qed.

End PmapForall.

(*Now, "In" Predicate*)
Section PmapIn.

Fixpoint pmap_ne_In {A: Type} (x: A) (p: Pmap_ne A) : Prop :=
  match p with
  | PNode001 p => pmap_ne_In x p
  | PNode010 y => x = y
  | PNode100 p => pmap_ne_In x p
  | PNode011 y p => x = y \/ pmap_ne_In x p
  | PNode110 p y => x = y \/ pmap_ne_In x p
  | PNode101 p1 p2 => pmap_ne_In x p1 \/ pmap_ne_In x p2
  | PNode111 p1 y p2 => x = y \/ pmap_ne_In x p1 \/ pmap_ne_In x p2
  end.

Definition pmap_In {A: Type} (x: A) (p: Pmap A) : Prop :=
  match p with
  | PEmpty => False
  | PNodes p => pmap_ne_In x p
  end.

Definition option_In {A: Type} (x: A) (o: option A) : Prop :=
  match o with
  | Some y => x = y
  | None => False
  end.

Definition Zmap_In {A: Type} (x: A) (z: Zmap A) : Prop :=
  option_In x z.(Zmap_0) \/
  pmap_In x z.(Zmap_pos) \/
  pmap_In x z.(Zmap_neg).

(*Relation between "In" and "Forall"*)

Lemma pmap_ne_Forall_In {A: Type} (P: A -> Prop) (p: Pmap_ne A):
  pmap_ne_Forall P p <-> forall x, pmap_ne_In x p -> P x.
Proof.
  induction p; simpl; (split; [intros Hall; inversion Hall; subst |
    intros; constructor]); try solve[intros; subst; auto; apply IHp; auto];
  try solve[intros; destruct_all; subst; auto;
    (apply IHp + apply IHp1 + apply IHp2); auto].
Qed.

Lemma pmap_Forall_In {A: Type} (P: A -> Prop) (p: Pmap A):
  pmap_Forall P p <-> forall x, pmap_In x p -> P x.
Proof.
  destruct p as [| p]; simpl.
  - split; intros Heq; intros; [contradiction |constructor].
  - split.
    + intros Hall; inversion Hall; subst. apply pmap_ne_Forall_In; auto.
    + intros Hall. constructor. apply pmap_ne_Forall_In; auto.
Qed.

Lemma option_Forall_In {A: Type} (P: A -> Prop) (o: option A):
  option_Forall P o <-> forall x, option_In x o -> P x.
Proof.
  destruct o; simpl; split; intros; subst; auto; contradiction.
Qed.

Lemma Zmap_Forall_In {A: Type} (P: A -> Prop) (z: Zmap A):
  Zmap_Forall P z <-> forall x, Zmap_In x z -> P x.
Proof.
  destruct z as [o p n]; simpl; unfold Zmap_Forall, Zmap_In; simpl.
  rewrite option_Forall_In, !pmap_Forall_In.
  split; intros; destruct_all; split_all; auto.
Qed.

End PmapIn.

(*And the implication rule*)
Lemma pmap_Forall_impl {A: Type} {P Q: A -> Prop} (z: Pmap A):
  pmap_Forall P z -> (forall x, pmap_In x z -> P x -> Q x) ->
  pmap_Forall Q z.
Proof.
  intros Hall Himpl.
  rewrite pmap_Forall_In in Hall |- *.
  intros x Hinx. auto.
Qed.

Lemma Zmap_Forall_impl {A: Type} {P Q: A -> Prop} (z: Zmap A):
  Zmap_Forall P z -> (forall x, Zmap_In x z -> P x -> Q x) ->
  Zmap_Forall Q z.
Proof.
  intros Hall Himpl.
  rewrite Zmap_Forall_In in Hall |- *.
  intros x Hinx. auto.
Qed.
