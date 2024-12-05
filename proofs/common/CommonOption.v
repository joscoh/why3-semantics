Require Export CommonTactics CommonBool.

(*Options*)
Section Option.

Definition option_bind {A B: Type} (o: option A) (f: A -> option B) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Lemma option_bind_id {B: Type} (o: option B):
  option_bind o (fun x => Some x) = o.
Proof.
  destruct o; auto.
Qed.

Lemma option_bind_none {B C: Type} (o: option B):
  @option_bind B C o (fun _ => None) = None.
Proof.
  destruct o; auto.
Qed.

Lemma option_map_comp {B C D: Type} (f: B -> C) (g: C -> D) (o: option B):
  option_map g (option_map f o) =
  option_map (fun x => g (f x)) o.
Proof.
  destruct o; auto.
Qed.

Lemma option_bind_ext {B C: Type} (f1 f2: B -> option C) (o: option B):
  (forall x, f1 x = f2 x) ->
  option_bind o f1 = option_bind o f2.
Proof.
  intros Hf. destruct o; simpl; auto.
Qed.

Lemma option_map_bind {B C D: Type} (f: B -> C) (o: option D) (g: D -> option B):
  option_map f (option_bind o g) =
  option_bind o (fun d => option_map f (g d)).
Proof.
  destruct o; simpl; auto.
Qed.

Lemma option_bind_map {B C: Type} (g: B -> C) (o: option B):
  option_bind o (fun x => Some (g x)) =
  option_map g o.
Proof.
  destruct o; auto.
Qed.

Lemma option_map_some {A B: Type} (f: A -> B) (o: option A) y:
  option_map f o = Some y ->
  exists z, o = Some z /\ y = f z.
Proof.
  destruct o; simpl; try discriminate.
  inv Hsome. exists a; auto.
Qed.

Lemma option_bind_some {A B: Type} (f: A -> option B) (o: option A) y:
  option_bind o f = Some y ->
  exists z, o = Some z /\ f z = Some y.
Proof. destruct o; simpl; [|discriminate]. intros Ha. exists a. auto.
Qed.

(*Technically works for anything associative, can change*)
Lemma option_bind_appcomp {A: Type} (o1 o2: option (list A)) (m: list A):
  option_bind (option_bind o1 (fun x => option_bind o2 (fun y => Some (x ++ y)))) (fun x => Some (m ++ x)) =
  option_bind (option_bind o1 (fun x => Some (m ++ x))) (fun y => option_bind o2 (fun x => Some (y ++ x))).
Proof.
  destruct o1; destruct o2; simpl; auto.
  rewrite app_assoc. reflexivity.
Qed.

Definition isSome {B: Type} (o: option B) : bool :=
  match o with | Some _ => true | _ => false end.

Definition isNone {A: Type} (x: option A) := negb (isSome x).

(*Equality*)
Section Eqb.

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

End Eqb.

(*Opt.fold*)
Definition opt_fold {A B: Type} (f: B -> A -> B) (d: B) (x: option A) : B :=
  match x with
  | None => d
  | Some y => f d y
  end.

(*An alternate version, kind of map/fold *)
Definition option_fold {A B: Type} (none: B) (some: A -> B) (o: option A) : B :=
  opt_fold (fun _ => some) none o.


End Option.

Section OMap.

Definition omap {A B: Type} (f: A -> option B) (l: list A):
list B :=
fold_right (fun x acc => 
  match f x with
  | None => acc
  | Some y => y :: acc
  end) nil l.

Lemma omap_app {A B: Type} (f: A -> option B) (l1 l2: list A):
  omap f (l1 ++ l2) = omap f l1 ++ omap f l2.
Proof.
  induction l1 as [| h t IH]; simpl; auto.
  destruct (f h); auto. rewrite IH. reflexivity.
Qed.

Lemma omap_rev {A B: Type} (f: A -> option B) (l: list A) :
  omap f (rev l) = rev (omap f l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  rewrite omap_app, IH; simpl.
  destruct (f h); simpl; auto. rewrite app_nil_r. reflexivity.
Qed.

Lemma omap_map {A B C: Type} (f: A -> B) (g: B -> option C) (l: list A) :
  omap g (map f l) = omap (fun x => g (f x)) l.
Proof.
  induction l as [| h t IH]; simpl; auto. destruct (g (f h)); rewrite IH; auto.
Qed.

Lemma omap_nil {A B: Type} (f: A -> option B) (l: list A):
  omap f l = nil <-> forall x, In x l -> f x = None.
Proof.
  induction l as [| h t IH]; simpl; auto.
  - split; auto. contradiction.
  - split. 
    + destruct (f h) eqn : Hfh; [discriminate|].
      rewrite IH. intros Hall. intros; destruct_all; subst; auto.
    + intros Hnone. rewrite (Hnone h); auto. apply IH; auto.
Qed.

Lemma omap_in {A B: Type} (f: A -> option B) (l: list A) (x: B):
  In x (omap f l) ->
  exists y, In y l /\ f y = Some x.
Proof.
  induction l as [| h t IH ]; simpl; [contradiction|].
  destruct (f h) as [z|] eqn : Hfh.
  - simpl. intros [Hzx | Hinx]; subst; eauto.
    apply IH in Hinx. destruct_all; eauto.
  - intros Hin. apply IH in Hin; destruct_all; eauto.
Qed.

Lemma in_omap {A B: Type} (f: A -> option B) (l: list A) (x: B) (y: A):
  In y l ->
  f y = Some x ->
  In x (omap f l).
Proof.
  induction l as [| h t IH ]; simpl; [contradiction|].
  intros [Hhy | Hiny] Hfy; subst.
  - rewrite Hfy. simpl; auto.
  - destruct (f h); simpl; auto.
Qed.

Lemma in_omap_iff {A B: Type} (f: A -> option B) (l: list A) (y: B):
  In y (omap f l) <-> exists x, In x l /\ f x = Some y.
Proof.
  split. apply omap_in.
  intros [z [Hiny Hfy]]. apply (in_omap _ _ _ _ Hiny Hfy).
Qed.

End OMap.

(*A generic notion of options being related (Forall2 for options)*)
Section OptRel.

Definition opt_related {A B: Type} (P: A -> B -> Prop) (o1: option A) (o2: option B) : Prop :=
  match o1, o2 with
  | Some x, Some y => P x y
  | None, None => True
  | _, _ => False
  end.

Lemma opt_related_impl {A B: Type} {P1 P2: A -> B -> Prop} 
  {o1: option A} {o2: option B}
  (Himpl: forall a b, P1 a b -> P2 a b):
  opt_related P1 o1 o2 ->
  opt_related P2 o1 o2.
Proof.
  destruct o1 as [x1|]; destruct o2 as [x2|]; simpl; auto.
Qed.

End OptRel.