Require Export Coq.Bool.Bool.
Require Export Coq.Logic.Eqdep_dec.
Require Export CommonTactics.
(*Reflection*)

(*Don't want to import ssreflect here*)
Section Reflect.

Lemma not_false: ~is_true false.
Proof.
  intro C; inversion C.
Qed.

Definition elimT {P: Prop} {b: bool} (Href: reflect P b) (B: is_true b) : P :=
  match Href in reflect _ b' return b' = true -> P with
  | ReflectT _ Hp => fun _ => Hp
  | ReflectF _ Hf => fun Hb => False_ind _ (not_false Hb)
  end B.

Definition notTf: true <> false.
Proof.
  discriminate.
Qed. 

Definition elimF {P: Prop} {b: bool} (Href: reflect P b) (B: b = false) : ~ P :=
  match Href in reflect _ b' return b' = false -> ~ P with
  | ReflectT _ Hp => fun Hb => False_ind _ (notTf Hb)
  | ReflectF _ Hf => fun _ => Hf
  end B.

(*Now we can transform "reflect" into computable "dec" EVEN if "reflect" is opaque.
  This is what we are missing in the ssreflect library. We do NOT match on
  "reflect"; we match on the boolean predicate directly*)
Definition reflect_dec' {P} {b} (H: reflect P b): {P} + {~P} :=
  match b as b1 return b = b1 -> _ with
  | true => fun Heq => left (elimT H Heq)
  | false => fun Hneq => right (elimF H Hneq)
  end eq_refl.

End Reflect.


(** Working with bool/props **)

Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
  if H then true else false.
Coercion is_true : bool >-> Sortclass.

Ltac simpl_sumbool :=
    match goal with
    | [H: is_true (proj_sumbool ?x ?y ?z) |- _ ] => destruct z; inversion H; clear H; subst; auto
    | [H: (proj_sumbool ?x ?y ?z) = true |- _ ] => destruct z; inversion H; clear H; subst; auto
    | |- is_true (proj_sumbool ?x ?y ?z) => destruct z; subst; auto
    | |- (proj_sumbool ?x ?y ?z) = true => destruct z; subst; auto
    | H: proj_sumbool ?x ?y ?z = false |- _ => destruct z; inversion H; clear H
    end.

Lemma bool_irrelevance: forall (b: bool) (p1 p2: b), p1 = p2.
Proof.
  intros b p1 p2. apply UIP_dec. apply bool_dec.
Defined.

Lemma is_true_eq (b1 b2: bool):
  b1 <-> b2 ->
  b1 = b2.
Proof.
  destruct b1; destruct b2; simpl; auto; intros;
  assert (false) by (apply H; reflexivity); discriminate.
Qed.

(*Note: in ssreflect*)
Lemma reflect_or: forall {b1 b2: bool} {p1 p2: Prop},
  reflect p1 b1 ->
  reflect p2 b2 ->
  reflect (p1 \/ p2) (b1 || b2).
Proof.
  intros. destruct H; simpl.
  - apply ReflectT. left; auto.
  - destruct H0; constructor; auto. intro C. destruct C; contradiction.
Qed.

Lemma isT : true.
Proof. reflexivity. Qed.

(*Not bool but close enough*)
Section Props.

Lemma or_false_r (P: Prop):
  (P \/ False) <-> P.
Proof.
  split; intros; auto. destruct H; auto. destruct H.
Qed.

Lemma or_idem (P: Prop):
  (P \/ P) <-> P.
Proof.
  split; intros; auto. destruct H; auto.
Qed.

Lemma or_iff (P1 P2 P3 P4: Prop) :
  (P1 <-> P3) ->
  (P2 <-> P4) ->
  (P1 \/ P2) <-> (P3 \/ P4).
Proof.
  intros. split; intros; destruct_all; tauto.
Qed.

Lemma demorgan_or (P Q: Prop):
  ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  tauto.
Qed.

End Props.


(*Lemmas about props/decidable eq*)
Section PropDec.
Lemma ex_in_eq {A: Type} (l: list A) (P1 P2: A -> Prop) :
  Forall (fun x => P1 x <-> P2 x) l ->
  (exists x, In x l /\ P1 x) <->
  (exists x, In x l /\ P2 x).
Proof.
  intros. rewrite Forall_forall in H. 
  split; intros [x [Hinx Hpx]]; exists x; split; auto;
  apply H; auto.
Qed.

Lemma eq_sym_iff {A: Type} (x y: A):
  x = y <-> y = x.
Proof.
  split; intros; subst; auto.
Qed.

Lemma dec_iff {P: Prop} {dec: {P} + { ~ P}}:
  dec <-> P.
Proof.
  destruct dec; simpl; split; intros; auto. inversion H.
Qed.

Lemma dec_negb_iff {P: Prop} {dec: {P} + {~ P}}:
  negb dec <-> ~ P.
Proof.
  destruct dec; simpl; split; intros; auto. inversion H.
Qed.

Lemma fold_is_true (b: bool):
  b = true <-> b.
Proof.
  reflexivity.
Qed.

Lemma eq_dec_sym {A: Type} {eq_dec: forall (x y: A), {x = y}+ {x <> y}}
  (x y: A):
  (@eq bool (eq_dec x y) (eq_dec y x)).
Proof.
  destruct (eq_dec x y); simpl; destruct (eq_dec y x); subst; auto.
  contradiction.
Qed.

Lemma eq_dec_refl {A: Type} {eq_dec: forall (x y: A), {x = y}+ {x <> y}}
  (x: A):
  (@eq bool (eq_dec x x) true).
Proof.
  destruct (eq_dec x x); auto.
Qed.

(*NOTE: don't use reflect because we want all proofs to be
  erased*)
Definition dec_from_eqb {A: Type} (f: A -> A -> bool) 
  (H: forall (x y: A), x = y <-> f x y = true) :
  forall (x y: A), {x = y} + {x <> y}.
Proof.
  intros x y.
  specialize (H x y).
  destruct (f x y).
  - left. apply H. reflexivity.
  - right. intro C. apply H in C. discriminate.
Defined.

Lemma dec_from_eqb_spec {A: Type} (eqb : A -> A -> bool) 
  (Heqb: forall (x y: A), x = y <-> eqb x y = true):
  forall x y, (proj_sumbool _ _ (dec_from_eqb eqb Heqb x y)) = eqb x y.
Proof.
  intros. unfold dec_from_eqb.
  generalize dependent (Heqb x y).
  generalize dependent (eqb x y).
  destruct b; reflexivity.
Qed.


End PropDec.

(*Other bool results*)

Section Orb.
Lemma orb_impl_l (b b1 b2: bool):
  (b1 -> b2) ->
  (b || b1 -> b || b2).
Proof.
  destruct b; simpl; auto.
Qed.

Lemma orb_congr b1 b2 b3 b4:
  b1 = b3 ->
  b2 = b4 ->
  b1 || b2 = b3 || b4.
Proof. intros; subst; reflexivity. Qed.

End Orb.

Lemma andb_true (b1 b2: bool) :
  b1 && b2 <-> b1 /\ b2.
Proof.
  unfold is_true. apply andb_true_iff.
Qed.



Ltac bool_to_prop :=
    repeat (progress (
    unfold is_true;
    (*First, convert bools to props*)
    repeat match goal with
    | |- context [(?b && ?b1) = true] =>
      rewrite andb_true_iff
    | |- context [(?b1 || ?b2) = true] =>
      rewrite orb_true_iff
    | |- context [existsb ?f ?l = true] =>
      rewrite existsb_exists
    end;
    (*Try to simplify*)
    repeat(
      apply or_iff_compat_l ||
      apply and_iff_compat_l
    );
    (*Put the goal in a nicer form*)
    repeat lazymatch goal with
    | |- ?P /\ ?Q <-> ?Q /\ ?R => rewrite (and_comm P Q)
    | |- ?P \/ ?Q <-> ?Q \/ ?R => rewrite (or_comm P Q)
    | |- ?P /\ ?Q <-> ?R /\ ?P => rewrite (and_comm R P)
    | |- ?P \/ ?Q <-> ?R /\ ?P => rewrite (or_comm R P)
    | |- context [ (?P \/ ?Q) \/ ?R] => rewrite or_assoc
    | |- ?P <-> ?P => reflexivity
    end)).

Ltac bool_hyps :=
    repeat match goal with
    | H: is_true (?b1 && ?b2) |- _ => unfold is_true in H
    | H: ?b1 && ?b2 = true |- _ => apply andb_true_iff in H; destruct H
    | H: is_true (?b1 || ?b2) |- _ => unfold is_true in H
    | H: ?b1 || ?b2 = true |- _ => apply orb_true_iff in H
    | H: is_true (negb ?b1) |- _ => unfold is_true in H
    | H: negb ?b1 = true |- _ => apply negb_true_iff in H
    | H: ?b1 && ?b2 = false |- _ => apply andb_false_iff in H
    | H: ?b1 || ?b2 = false |- _ => apply orb_false_iff in H; destruct H
    | H: negb (?b1) = false |- _ => apply negb_false_iff in H
    end.
  
  Ltac solve_negb :=
    match goal with
    | H: ?b = false |- is_true (negb ?b) => rewrite H; auto
    end.

  Ltac tf :=
  match goal with
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  end.

  Ltac simpl_bool :=
  repeat (progress (simpl;
  try rewrite !orb_assoc;
  try rewrite !andb_assoc;
  repeat match goal with
  | |- context [ ?b && true] => rewrite andb_true_r
  | |- context [?b || true] => rewrite orb_true_r
  | |- context [?b && false] => rewrite andb_false_r
  | |- context [?b || false] => rewrite orb_false_r
  end)).

Ltac solve_bool :=
  simpl_bool;
  (*Then brute force the solution*)
  repeat 
  (match goal with
  | |- ?b1 && ?b2 = ?z => destruct b2
  | |- ?b1 || ?b2 = ?z => destruct b2
  | |- ?z = ?b1 && ?b2 => destruct b2
  | |- ?z = ?b1 || ?b2 => destruct b2
  end; simpl_bool; try reflexivity).