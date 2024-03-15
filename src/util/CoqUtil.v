From stdpp Require Import -(coercions) numbers.
Require Export Coq.Strings.String.
Require Export Coq.Lists.List.
Require Import Coq.Init.Byte.
Require Import Lia.
From Proofs Require Export core.Common.

(*TODO: reduce duplication of this stuff: anything in Prop we can
  use COmmon*)

Definition pos_eq : EqDecision positive := Pos.eq_dec.

(** String to Positive **)
Section StrPos.
(*I think this is reversed but that's ok*)
Fixpoint bits_to_pos (l: list bool) : positive :=
  match l with
  | true :: tl => xI (bits_to_pos tl)
  | false :: tl => xO (bits_to_pos tl)
  | nil => xH
  end.

Fixpoint pos_to_bits (p: positive) : list bool :=
  match p with
  | xI p' => true :: pos_to_bits p'
  | xO p' => false :: pos_to_bits p'
  | xH => nil
  end.

Lemma bits_to_pos_to_bits p: bits_to_pos (pos_to_bits p) = p.
Proof.
  induction p; simpl; auto; rewrite IHp; auto.
Qed.

Lemma pos_to_bits_to_pos l: pos_to_bits (bits_to_pos l) = l.
Proof.
  induction l as [| [|] t]; simpl; auto; rewrite IHt; auto.
Qed.

Definition bittup_to_bits 
  (x:  bool * (bool * (bool * (bool * (bool * (bool * (bool * bool))))))) : list bool :=
  match x with
  | (b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) => [ b1; b2; b3; b4; b5; b6; b7; b8 ]
  end.

Definition byte_to_bits (b: byte) : list bool :=
  bittup_to_bits (to_bits b).

Definition str_to_pos (s: string) : positive :=
  bits_to_pos (concat (map byte_to_bits (list_byte_of_string s))).

(*Proof of injectivity*)
(*TODO: move proofs somewhere else*)

Lemma bits_to_pos_inj (l1 l2: list bool) : bits_to_pos l1 = bits_to_pos l2 -> l1 = l2.
Proof.
  intros Heq.
  apply (f_equal pos_to_bits) in Heq.
  rewrite !pos_to_bits_to_pos in Heq; exact Heq.
Qed.

Lemma app_inj {A: Type} (l1 l2 l3 l4: list A):
  length l1 = length l3 ->
  l1 ++ l2 = l3 ++ l4 ->
  l1 = l3 /\ l2 = l4.
Proof.
  revert l3. induction l1 as [| h1 t1]; simpl; intros [| h2 t2]; simpl; auto;
  try discriminate.
  intros Hlen Heq. injection Hlen; injection Heq. intros Heq' Hhd Hlen'; subst.
  specialize (IHt1 _ Hlen' Heq').
  destruct IHt1; subst; auto.
Qed.

Lemma concat_inj {A: Type} (l1 l2: list (list A)) n:
  0 < n ->
  Forall (fun x => length x = n) l1 ->
  Forall (fun x => length x = n) l2 ->
  concat l1 = concat l2 ->
  l1 = l2.
Proof.
  intros Hn0.
  revert l2. induction l1 as [| h1 t1]; simpl; intros [|h2 t2]; simpl; auto.
  - intros _ Hall Heq.
    pose proof (Forall_inv Hall) as Hh2; simpl in Hh2.
    destruct h2; simpl in *; auto; try lia; discriminate.
  - intros Hall _ Heq.
    pose proof (Forall_inv Hall) as Hh1; simpl in Hh1.
    destruct h1; simpl in *; auto; try lia; discriminate.
  - intros Hall1 Hall2 Heq.
    apply app_inj in Heq.
    + destruct Heq; subst; f_equal; apply IHt1; auto.
      * inversion Hall1; auto.
      * inversion Hall2; auto.
    + rewrite (Forall_inv Hall1), (Forall_inv Hall2); reflexivity.
Qed.

Lemma byte_to_bits_length: forall x, length (byte_to_bits x) = 8.
Proof.
  intros. unfold byte_to_bits.
  set (p:=(to_bits x)).
  repeat (destruct p as [? p]).
  reflexivity.
Qed.

(*Is this in the stdlib?*)
(*Lemma map_inj {A B: Type} (f: A -> B) (l1 l2: list A):
  (forall x y, In x l1 \/ In x l2 -> f x = f y -> x = y) ->
  map f l1 = map f l2 ->
  l1 = l2.
Proof.
  revert l2. induction l1 as [| h1 t1]; simpl;
  destruct l2 as [| h2 t2]; simpl; auto; try discriminate.
  intros Hinj Heq.
  injection Heq; intros Htl Hhd.
  f_equal.
  - apply Hinj; auto.
  - apply IHt1; auto; intros x y Hin Hf. apply Hinj; auto.
    destruct Hin; auto.
Qed.*)

Lemma to_bits_inj (b1 b2: byte): to_bits b1 = to_bits b2 -> b1 = b2.
Proof.
  intros Heq. apply (f_equal of_bits) in Heq.
  rewrite !of_bits_to_bits in Heq.
  exact Heq.
Qed.

Lemma byte_to_bits_inj (b1 b2: byte): byte_to_bits b1 = byte_to_bits b2 -> b1 = b2.
Proof.
  unfold byte_to_bits. intros Heq.
  apply to_bits_inj. revert Heq.
  set (p1:=(to_bits b1)).
  set (p2:=(to_bits b2)).
  repeat (destruct p1 as [? p1]);
  repeat (destruct p2 as [? p2]); simpl;
  intros Heq; inversion Heq; subst.
  reflexivity.
Qed.

Lemma str_to_pos_inj (s1 s2: string): str_to_pos s1 = str_to_pos s2 -> s1 = s2.
Proof.
  unfold str_to_pos; intros Heq.
  apply bits_to_pos_inj in Heq.
  apply concat_inj with (n:=8) in Heq; try lia;
  try solve[ rewrite Forall_map, Forall_forall; intros;
    apply byte_to_bits_length].
  apply map_inj in Heq;[|apply byte_to_bits_inj].
  apply (f_equal string_of_list_byte) in Heq.
  rewrite !string_of_list_byte_of_string in Heq.
  exact Heq.
Qed.

End StrPos.

Ltac solve_eqb_eq :=
  solve[let Heq := fresh "Heq" in
  split; intros Heq; inversion Heq; destruct_all; subst;
  auto; try discriminate; contradiction].

(*TODO: move from Types to Common*)
Fixpoint list_eqb {A: Type} (eq: A -> A -> bool) (l1 l2: list A) : bool :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => eq x1 x2 && list_eqb eq t1 t2
  | nil, nil => true
  | _, _ => false
  end.

Lemma andb_true (b1 b2: bool) :
  b1 && b2 <-> b1 /\ b2.
Proof.
  unfold is_true. apply andb_true_iff.
Qed.

Lemma list_eqb_eq {A: Type} {eq: A -> A -> bool} 
  (Heq: forall x y, x = y <-> eq x y)
  l1 l2:
  l1 = l2 <-> list_eqb eq l1 l2.
Proof.
  revert l2. induction l1 as [|h1 t1]; simpl;
  intros [| h2 t2]; simpl; auto; try solve_eqb_eq.
  rewrite andb_true, <- Heq, <- IHt1. solve_eqb_eq.
Qed.

Definition isSome {A: Type} (o: option A) : bool :=
  match o with
  | Some _ => true
  | _ => false
  end.

(*TODO: Common?*)
Definition option_eqb {A: Type}(eq: A -> A -> bool) (o1 o2: option A): bool :=
  match o1, o2 with
  | Some x, Some y => eq x y
  | None, None => true
  | _, _ => false
  end.

Lemma option_eqb_eq {A: Type} {eqb: A -> A -> bool}
  (eqb_eq: forall x y, x = y <-> eqb x y)
  o1 o2: o1 = o2 <-> option_eqb eqb o1 o2.
Proof.
  destruct o1 as [x|]; destruct o2 as [y|]; simpl; auto;
  try rewrite <- eqb_eq; solve_eqb_eq.
Qed.

(*TODO: dont repeat with Common*)
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

(*Unlike OCaml, this gives option, not exception*)
Fixpoint fold_right2 {A B C: Type} (f: A -> B -> C -> C) (l1: list A)
  (l2: list B) (accu: C) : option C :=
  match l1, l2 with
  | nil, nil => Some accu
  | a1 :: l1, a2 :: l2 => 
    option_map (f a1 a2) (fold_right2 f l1 l2 accu)
  | _, _ => None
  end.