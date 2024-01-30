Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Logic.Eqdep.
Require Export Coq.Logic.Eqdep_dec.
Require Export Lia.
From mathcomp Require all_ssreflect.
Export ListNotations.

Set Bullet Behavior "Strict Subproofs".

(*Working with Boolean Predicates*)

Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
  if H then true else false.
Coercion is_true : bool >-> Sortclass.

Lemma bool_irrelevance (b: bool) (p1 p2: b): p1 = p2.
Proof.
  apply UIP_dec, bool_dec.
Qed.

Lemma is_false {P: Type}: false -> P.
Proof.
discriminate.
Qed.

Lemma andb_conj {b1 b2: bool} (x: b1) (y: b2): b1 && b2.
Proof.
rewrite x, y. reflexivity.
Qed.

Definition proj2_bool {b1 b2: bool} (x: b1 && b2) : b2 :=
  proj2 (andb_prop _ _ x).

Definition proj1_bool {b1 b2: bool} (x: b1 && b2) : b1 :=
  proj1 (andb_prop _ _ x).

(*Forall for Type*)

Inductive ForallT {A: Type} (P: A -> Type) : list A -> Type :=
  | ForallT_nil: ForallT P nil
  | ForallT_cons: forall {x: A} {l: list A},
    P x -> ForallT P l -> ForallT P (x :: l).

Lemma ForallT_hd {A: Type} {P: A -> Type} {x: A} {l: list A}:
  ForallT P (x :: l) ->
  P x.
Proof.
  intros. inversion X; subst. apply X0.
Qed.

Lemma ForallT_tl {A: Type} {P: A -> Type} {x: A} {l: list A}:
  ForallT P (x :: l) ->
  ForallT P l.
Proof.
  intros. inversion X; auto.
Qed.

(*Some list definitions and lemmas*)

(*This awkward definition satisfies Coq's positivity checker
  for nested induction, unlike the normal one*)
Definition map2 {A B C: Type} :=
  fun (f: A -> B -> C) =>
    fix map2 (l1: list A) : list B -> list C :=
      match l1 with
      | nil => fun l2 => nil
      | x1 :: t1 =>
        fun l2 =>
        match l2 with
        | nil => nil
        | x2 :: t2 => f x1 x2 :: map2 t1 t2
        end
      end.

Lemma NoDup_map_in: forall {A B: Type} {f: A -> B} {l: list A} {x1 x2: A},
  NoDup (map f l) ->
  In x1 l -> In x2 l ->
  f x1 = f x2 ->
  x1 = x2.
Proof.
  intros A B f l x1 x2 Hn Hin1 Hin2 Hfeq.
  induction l; simpl.
  - destruct Hin1.
  - simpl in *. destruct Hin1; destruct Hin2; subst; auto;
    inversion Hn; subst;
    try solve[exfalso; apply H2; 
      (rewrite Hfeq + rewrite <- Hfeq); rewrite in_map_iff; 
      (solve[exists x2; auto] + solve[exists x1; auto])].
    apply IHl; assumption.
Qed.

(*More general than [map_nth] from the standard library because
  we don't require any knowledge of the default values as long
  as n is within bounds*)
Lemma map_nth_inbound: forall {A B: Type} (f: A -> B) (l: list A)
  (d1 : B) (d2 : A) (n: nat),
  n < length l ->
  nth n (List.map f l) d1 = f (nth n l d2).
Proof.
  intros A B f l d1 d2. induction l as [|h t IH]; simpl; try lia.
  intros n Hn.
  destruct n; auto. 
  apply IH. lia.
Qed. 

Inductive empty := .

(*In many places, we need the type {x : T | in x l} and the type T is
decidable. We give utilities here for this type*)

Section InTypeDef.
Variable (T: Set).
Variable (T_dec: forall (x y: T), {x = y} + {x <> y}).

Definition inb (x: T) (l: list T) : bool :=
  fold_right (fun y acc => ((T_dec x y) || acc)) false l.

Lemma inb_spec (x: T) (l: list T): reflect (In x l) (inb x l).
Proof.
  induction l; simpl.
  - apply ReflectF; auto.
  - apply ssr.ssrbool.orPP; auto.
    destruct (T_dec x a); subst; simpl;
    [apply ReflectT | apply ReflectF]; auto.
Qed.

Definition in_type (l: list T) : Set :=
  { x : T | inb x l }.

Definition build_in_type {x: T} {l: list T} (x_in: inb x l): in_type l :=
  exist _ x x_in.

Definition in_type_extra (l: list T) (f: T -> Set) : Set :=
  {t: in_type l & f (proj1_sig t)}.

Definition build_extra {l: list T} (x: in_type l) {f: T -> Set} (y: f (proj1_sig x)) :
  in_type_extra l f :=
  existT _ x y.

Lemma in_type_eq (l: list T) (x y: in_type l):
  x = y <-> proj1_sig x = proj1_sig y.
Proof.
  destruct x as [x inx]; destruct y as [y iny]; simpl.
  split; intros.
  - apply EqdepFacts.eq_sig_fst in H; assumption.
  - subst. assert (inx = iny) by (apply bool_irrelevance); subst; reflexivity.
Qed.

Lemma in_type_dec (l: list T) (x y: in_type l): {x = y} + {x <> y}.
Proof.
  destruct (T_dec (proj1_sig x) (proj1_sig y)).
  - left. apply in_type_eq in e; auto.
  - right. intro C; subst; contradiction.
Qed.

End InTypeDef.

Ltac reflF :=
  let C := fresh in
  intros; apply ReflectF; intro C; inversion C; subst; contradiction.

Section Eq.
Import all_ssreflect. 

(*A version of "reflect_dec" with better computational behavior:
it reduces even if the "reflect" predicate is opaque*)
Definition reflect_dec' {P} {b} (H: reflect P b): {P} + {~P} :=
  match b as b1 return b = b1 -> _ with
  | true => fun Heq => left (elimT H Heq)
  | false => fun Hneq => right (elimF H Hneq)
  end erefl.

(*Equality on lists*)
Fixpoint list_eqb {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(l1 l2: list A) : bool :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => eq_dec x1 x2 && list_eqb eq_dec t1 t2
  | nil, nil => true
  | _, _ => false
  end.

Lemma list_eqb_spec {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(l1 l2: list A) : reflect (l1 = l2) (list_eqb eq_dec l1 l2).
Proof.
  move: l2. elim: l1 => [[/=|/=]|x1 t1 IH [/=|x2 t2/=]]; try by reflF.
  - by apply ReflectT.
  - case: (eq_dec x1 x2)=>//=[->|]; last by reflF.
    by case: (IH t2)=>[->|]; [apply ReflectT | reflF].
Qed.

Definition list_eq_dec {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(l1 l2: list A) : {l1 = l2} + {l1 <> l2} := reflect_dec' (list_eqb_spec eq_dec l1 l2).

End Eq.
