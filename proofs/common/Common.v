Require Export CommonTactics CommonBool CommonOption CommonList aset Tactics2.

(** Generally useful definitions, lemmas, and tactics *)

(*Why is this not in Coq stdlib?*)
Inductive Either (A B: Set) : Set :=
  | Left: A -> Either A B
  | Right: B -> Either A B. 

Lemma nat_eq_refl {n m: nat} (H1 H2: n = m) : H1 = H2.
Proof.
  destruct H1. apply UIP_dec. apply Nat.eq_dec.
Qed.

(*Non-empty lists*)
Section NEList.

(*Our list of constructors are non-empty, and if we just use regular lists,
  we will need to pattern match on nil, [x], and x :: t. This makes the
  dependent pattern match much more complicated and leads to huge proof terms.
  So instead we define a non-empty list as a custom Inductive type, and have simple
  ways to transform between this and the standard list.*)

Inductive ne_list (A: Set) : Set :=
  | ne_hd : A -> ne_list A
  | ne_cons : A -> ne_list A -> ne_list A.

Global Arguments ne_hd {A}.
Global Arguments ne_cons {A}.

Definition list_to_ne_list {A: Set} (l: list A) (Hl: negb (null l)) : ne_list A. 
induction l.
- exact (False_rect _ (not_false Hl)).
- destruct l.
  + exact (ne_hd a).
  + exact (ne_cons a (IHl isT)).
Defined.

(*rewrite lemma*)
Lemma list_to_ne_list_cons: forall {A: Set} (hd: A) (tl: list A) (H: negb (null (hd :: tl))),
  list_to_ne_list (hd :: tl) H =
  match tl with
  | nil => ne_hd hd
  | a :: t => ne_cons hd (list_to_ne_list (a :: t) isT)
  end.
Proof.
  intros.
  destruct tl; auto.
Qed.

Fixpoint ne_list_to_list {A: Set} (l: ne_list A) : list A :=
  match l with
  | ne_hd x => [x]
  | ne_cons x tl => x :: ne_list_to_list tl
  end.

Lemma ne_list_to_list_size: forall {A: Set} (l: ne_list A),
  negb (null (ne_list_to_list l)).
Proof.
  intros. destruct l; reflexivity.
Qed.

Lemma ne_list_to_list_nil {A: Set} (l: ne_list A):
  ne_list_to_list l <> nil.
Proof.
  destruct l; simpl; intro C; inversion C.
Qed.


Lemma ne_list_to_list_cons: forall {A: Set} (x: A) (l: ne_list A),
  ne_list_to_list (ne_cons x l) = x :: ne_list_to_list l.
Proof.
  intros. reflexivity.
Qed.

Lemma list_ne_list_inv: forall {A: Set} (l: list A) (Hl: negb (null l)),
  ne_list_to_list (list_to_ne_list l Hl) = l.
Proof.
  intros. induction l.
  - inversion Hl.
  - destruct l.
    + reflexivity.
    + rewrite list_to_ne_list_cons, ne_list_to_list_cons. f_equal.
      apply IHl.
Qed.

Lemma ne_list_list_inv: forall {A: Set} (l: ne_list A),
  list_to_ne_list (ne_list_to_list l) (ne_list_to_list_size l) = l.
Proof.
  intros. generalize dependent (ne_list_to_list_size l). induction l; intros.
  - reflexivity.
  - simpl in i. destruct l; simpl in *; try reflexivity.
    specialize (IHl isT).
    destruct (ne_list_to_list l). inversion IHl.
    f_equal. apply IHl.
Qed.

Lemma ne_list_list_inj {A: Set} {l1 l2: ne_list A}:
  ne_list_to_list l1 = ne_list_to_list l2 ->
  l1 = l2.
Proof.
  revert l2. induction l1; simpl; intros;
  destruct l2; inversion H; subst; auto.
  - exfalso; apply (ne_list_to_list_nil l2); auto.
  - exfalso; apply (ne_list_to_list_nil l1); auto.
  - f_equal. apply IHl1; auto.
Qed.

Lemma ne_list_nonemp {A: Set} (n: ne_list A):
  exists x, In x (ne_list_to_list n).
Proof.
  destruct n as [a | a tl]; exists a; simpl; auto.
Qed.

Fixpoint in_bool_ne {A: Set} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (x: A) (l: ne_list A) : bool :=
  match l with
  | ne_hd y => eq_dec x y
  | ne_cons y tl => eq_dec x y || in_bool_ne eq_dec x tl
  end.

Lemma in_bool_ne_equiv: forall {A: Set} (eq_dec: forall (x y: A), { x = y} + {x <> y})
  (x: A) (l: ne_list A),
  in_bool_ne eq_dec x l = in_bool eq_dec x (ne_list_to_list l).
Proof.
  intros. induction l; simpl; [rewrite orb_false_r | rewrite IHl ]; reflexivity.
Qed.

Lemma in_bool_ne_In {A: Set} (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (x: A) (l: ne_list A):
  in_bool_ne eq_dec x l ->
  In x (ne_list_to_list l).
Proof.
  rewrite in_bool_ne_equiv. intros.
  apply (in_bool_In _ _ _ H).
Qed.

Fixpoint lists_to_ne_lists {A: Set} (l: list (list A)) 
  (Hall: forallb (fun x => negb (null x)) l) :
  list (ne_list A) :=
  match l as l' return (forallb (fun x => negb (null x)) l') -> list (ne_list A) with
  | nil => fun _ => nil
  | hd :: tl => fun Hnull =>
    match (andb_prop _ (forallb (fun x => negb (null x)) tl) Hnull) with
    | conj Hhd Htl =>
      (list_to_ne_list hd Hhd) :: lists_to_ne_lists tl Htl
    end
  end Hall.

(*hopefully we don't need to run this, if we do, make nicer*)
Definition ne_list_eq_dec {A: Set} 
  (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (l1 l2: ne_list A) :
  {l1 = l2} + { l1 <> l2}.
Proof.
  revert l2.
  induction l1 as [hd1|hd1 tl1 IH]; intros [hd2|hd2 tl2]; try right_dec;
  destruct (eq_dec hd1 hd2); try right_dec; rewrite e; clear e.
  - left. reflexivity.
  - destruct (IH tl2); [|right_dec]. rewrite e. left; reflexivity.
Defined.

Fixpoint map_ne_list {A B: Set} (f: A -> B) (l: ne_list A) : ne_list B :=
  match l with
  | ne_hd x => ne_hd (f x)
  | ne_cons x tl => ne_cons (f x) (map_ne_list f tl)
  end.

Lemma map_ne_list_spec {A B: Set} (f: A -> B) (l: ne_list A):
  ne_list_to_list (map_ne_list f l) = map f (ne_list_to_list l).
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

End NEList.

(*Other lemmas*)
Lemma Nat_eqb_S (n1 n2: nat):
  S n1 <? S n2 = (n1 <? n2).
Proof.
  destruct (Nat.ltb_spec0 n1 n2);
  destruct (Nat.ltb_spec0 (S n1) (S n2)); auto; try lia.
Qed.

Ltac dec H :=
  destruct H; [ simpl | apply ReflectF; intro C; inversion C; subst; contradiction].

Ltac refl_t := solve[apply ReflectT; subst; auto].

Section Tup.

Definition tuple_eqb {A B: Type}
  (eq1: A -> A -> bool)
  (eq2: B -> B -> bool)
  (x y: A * B) : bool :=
  eq1 (fst x) (fst y) &&
  eq2 (snd x) (snd y).

Lemma tuple_eqb_spec {A B: Type}
  {eq1 eq2}
  (Heq1: forall (x y: A), reflect (x = y) (eq1 x y))
  (Heq2: forall (x y: B), reflect (x = y) (eq2 x y)):
  forall (x y: A * B), reflect (x = y) (tuple_eqb eq1 eq2 x y).
Proof.
  intros.
  unfold tuple_eqb. dec (Heq1 (fst x) (fst y)).
  dec (Heq2 (snd x) (snd y)).
  destruct x; destruct y; simpl in *; subst; refl_t.
Qed.

Definition tuple_eq_dec' {A B: Type}
  {eq1 eq2}
  (Heq1: forall (x y: A), reflect (x = y) (eq1 x y))
  (Heq2: forall (x y: B), reflect (x = y) (eq2 x y))
  (x y: A * B) : {x = y} + {x <> y} :=
  reflect_dec' (tuple_eqb_spec Heq1 Heq2 x y).

(*Not guaranteed to be computable.
  TODO: create computable version?*)
Definition tuple_eq_dec {A B: Type} (eq1: forall (x y: A), { x = y } + {x <> y})
  (eq2: forall (x y : B), {x=y} + {x<>y}) :
  (forall (x y : A * B), {x = y} + { x <> y}).
Proof.
  refine (fun '(x1, x2) '(y1, y2) =>
    match (eq1 x1 y1) with
    | left Heq =>
      match (eq2 x2 y2) with
      | left Heq2 => left _
      | right Hneq => right _
      end
    | right Hneq => right _
    end).
  - f_equal; assumption.
  - subst; intro C; injection C; intros; subst; contradiction.
  - intro C; injection C; intros; subst; contradiction.
Defined.

End Tup.


Lemma plus_minus (n m: nat):
  (n + m) - n = m.
Proof.
  lia.
Qed.

Lemma ltb_n_Sn {n1 n2}:
  n1 <? n2 ->
  S n1 <? S n2.
Proof.
  unfold is_true.
  rewrite !Nat.ltb_lt. lia.
Qed.

(*Strings*)

Require Import Coq.Strings.String.

Lemma str_app_assoc (s1 s2 s3: string):
  (s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3)%string.
Proof.
  induction s1 as [| c1 s1 IH]; simpl; auto.
  (*why does std++ block simpl here?*)
  clear -IH. cbv in *. f_equal; rewrite IH. auto.
Qed.

Lemma str_length_app (s1 s2: string):
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  induction s1; simpl; auto.
Qed.

Lemma append_inj (s1 s2 s3 s4 : string) :
  length s1 = length s2 ->
  (s1 ++ s3 = s2 ++ s4)%string ->
  s1 = s2 /\ s3 = s4.
Proof.
  revert s2. induction s1 as [| c1 s1 IH]; intros [| c2 s2]; try discriminate; simpl; auto.
  intros Hlen Happ.
  specialize (IH s2 ltac:(auto)).
  forward IH.
  { (*bc no simpl*) clear -Happ. cbv in Happ; inversion Happ; auto. }
  assert (c1 = c2) by (clear -Happ; cbv in Happ; inversion Happ; auto).
  destruct_all; subst; auto.
Qed.

Lemma str_app_inj_l (s1 s2 s3: string):
  (s1 ++ s2 = s1 ++ s3)%string ->
  s2 = s3.
Proof.
  intros Heq. apply append_inj in Heq; auto.
  apply Heq.
Qed.

Lemma str_app_inj_r (s1 s2 s3: string):
  (s1 ++ s2 = s3 ++ s2)%string ->
  s1 = s3.
Proof.
  intros Heq. apply append_inj in Heq; auto.
  apply Heq.
  apply (f_equal String.length) in Heq.
  rewrite !str_length_app in Heq. lia.
Qed.

Lemma str_app_assoc_22 (s1 s2 s3 s4: string):
  (s1 ++ s2 ++ s3 ++ s4)%string =
  ((s1 ++ s2) ++ s3 ++ s4)%string.
Proof.
  rewrite !str_app_assoc; reflexivity.
Qed.