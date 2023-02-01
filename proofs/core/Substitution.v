Require Import Common.
Require Import Syntax.
Require Import IndTypes.
Require Import Semantics.
Require Import Types.
Require Import Typing.
Require Import Denotational.

Set Bullet Behavior "Strict Subproofs".


(*First, some functions we need*)

Definition split {A: Type} (l: list A) (i: nat) : (list A * list A) :=
  (firstn i l, skipn i l).

(*Split a list into pieces of the appropriate lengths if we can*)
Fixpoint split_lens {A: Type} (l: list A) (lens: list nat) :
  list (list A) :=
  match lens with
  | len :: tl =>
    (fst (split l len)) ::
    split_lens (snd (split l len)) tl
  | nil => nil
  end.

Definition sum (l: list nat) : nat :=
  fold_right (fun x y => x + y) 0 l.

Lemma length_concat {A: Type} (l: list (list A)):
  length (concat l) = sum (map (@length A) l).
Proof.
  induction l; simpl; auto.
  rewrite app_length, IHl; auto.
Qed.

Lemma split_lens_length {A: Type} (l: list A) (lens: list nat) :
  length (split_lens l lens) = length lens.
Proof.
  revert l.
  induction lens; simpl; intros; auto.
Qed.

Lemma split_lens_concat {A: Type} (l: list A) (lens: list nat) :
  sum lens = length l ->
  l = concat (split_lens l lens).
Proof.
  revert l. induction lens; simpl; intros; auto.
  destruct l; auto; inversion H.
  rewrite <- IHlens.
  rewrite firstn_skipn; auto.
  rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
Qed.

Lemma split_lens_nodup {A: Type} (l: list A) (lens: list nat) :
  sum lens = length l ->
  NoDup l ->
  forall (i: nat) (d: list A),
    i < length lens ->
    NoDup (nth i (split_lens l lens) d).
Proof.
  revert l. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - apply NoDup_firstn; assumption.
  - apply IHlens; try lia.
    + rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
    + apply NoDup_skipn; assumption.
Qed. 

Lemma split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) :
  sum lens = length l ->
  i < length lens ->
  length (nth i (split_lens l lens) nil) = nth i lens 0.
Proof.
  revert l i. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - rewrite firstn_length.
    apply Nat.min_l. lia.
  - specialize (IHlens (skipn a l) i).
    rewrite IHlens; auto; try lia.
    rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
Qed.

Lemma in_split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) x (d: list A) :
  sum lens = length l ->
  i < length lens ->
  In x (nth i (split_lens l lens) d) ->
  In x l.
Proof.
  revert l i. induction lens; simpl; intros; auto; destruct i; auto; try lia.
  - apply In_firstn in H1; auto.
  - apply IHlens in H1; try lia.
    + apply In_skipn in H1; auto.
    + rewrite skipn_length, <- H. lia.
Qed.



(*Some tactics that will be useful:*)

(*Solve trivial/repeated goals and simplify*)
Ltac len_tac :=
repeat match goal with
| |- context [length (firstn ?n ?l)] => rewrite firstn_length
| |- context [length (skipn ?n ?l)] => rewrite skipn_length
| H: length ?l = ?x |- context [length ?l] => rewrite H
| |- context [length (?x ++ ?y)] => rewrite app_length
end; try lia.

(*Deal with In (firstn) and similar goals*)
(*TODO*)
Ltac in_tac :=
  repeat match goal with
  | |- In (nth ?i ?l ?x) ?l =>
    apply nth_In
  | H: In ?x (firstn ?n ?l) |- _ => apply In_firstn in H
  | H: In ?x (skipn ?n ?l) |- _ => apply In_skipn in H
  | |- In ?x (map ?g ?l) => rewrite in_map_iff
  | |- In ?x (?l1 ++ ?l2) => rewrite in_app_iff
  | |- In ?x ?l1 \/ In ?x ?l2 => solve[left; in_tac] + solve[right; in_tac]
  end; auto.

  (*TODO: temp*)
  Lemma NoDup_pat_fv (p: pattern) : NoDup (pat_fv p).
Proof.
  induction p; simpl; try constructor; auto.
  - constructor.
  - apply big_union_nodup.
  - apply union_nodup; auto.
  - apply union_nodup; auto. constructor; auto. constructor.
Qed.

Ltac wf_tac :=
  repeat(
  assumption +
  solve[len_tac] +
  solve[lia] +
  solve[in_tac] +
  match goal with
  | |- context [map snd (combine ?l1 ?l2)] =>
    rewrite map_snd_combine
  | |- context [map fst (combine ?l1 ?l2)] =>
    rewrite map_fst_combine
  | |- NoDup (firstn ?n ?l) => apply NoDup_firstn
  | |- NoDup (skipn ?n ?l) => apply NoDup_skipn
  | |- NoDup (nth ?i (split_lens ?a ?b) ?d) =>
    apply split_lens_nodup
  | |- context [length (map ?f ?x)] => rewrite map_length
  | |- context [length (split_lens ?l1 ?l2)] =>
    rewrite split_lens_length
  | |- context [length (firstn ?n ?l)] => rewrite firstn_length
  | |- context [length (skipn ?n ?l)] => rewrite skipn_length
  | |- In (nth ?i ?l ?x) ?l =>
    apply nth_In
  | |- context [length (nth ?l (split_lens ?a ?b) ?d)] =>
    rewrite split_lens_ith
  | |- context [length (map2 ?f ?l1 ?l2)] =>
    rewrite map2_length
  | |- ?i < length ?l -> ?P => intros
  | |- context [Nat.min ?x ?x] =>
    rewrite Nat.min_id
  (*TODO: this is hacky*)
  | |- context [nth ?i (map ?f ?l) ?d] =>
    (rewrite map_nth_inbound with(d2:=tm_d)) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, tm_d))) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, Ftrue))) ||
    (rewrite map_nth_inbound with (d2:=Pwild))
  (*Deal with some "In" goals - TODO improve*)
  | H: In ?x (firstn ?n ?l) |- In ?x ?l => apply In_firstn in H
  | H: In ?x (skipn ?n ?l) |- In ?x ?l => apply In_skipn in H
  | H: In ?x (firstn ?n ?l1) |- In ?x ?l2 => apply In_firstn in H
  (*A special case*)
  | |- NoDup (pat_fv ?p) => apply NoDup_pat_fv
  | |- context [concat (split_lens ?l1 ?l2)] =>
    rewrite <- split_lens_concat
  | |- In ?x (map ?g ?l) => rewrite in_map_iff
  | |- exists y, ?f y = ?f ?x /\ ?P => exists x; split
  (*Solve the sum length goal*)
  | H: length ?l = length (concat (map ?f ?l1)) |-
    sum (map ?g ?l1) = length ?l => rewrite length_concat in H;
    rewrite H; f_equal; rewrite map_map; apply map_ext
  | H: length (?x :: ?l) = ?n |- _ => simpl in H
  | H: ?x = length (?l1 ++ ?l2) |- _ => rewrite app_length in H
  end); auto; try lia. 


Ltac simpl_set_goal :=
  repeat match goal with
  (*remove*)
  | H: In ?x (remove ?e ?y ?l) |- _ => rewrite in_remove_iff in H
  | |- context [ In ?x (remove ?e ?y ?l)] => rewrite in_remove_iff
  (*big_union*)
  | H: In ?x (big_union ?e ?f ?l) |- _ => rewrite <- big_union_elts in H
  | |- context [ In ?x (big_union ?e ?f ?l)] => rewrite <- big_union_elts
  (*union*)
  | H: In ?x (union ?e ?l1 ?l2) |- _ => rewrite union_elts in H
  | |- context [ In ?x (union ?e ?l1 ?l2)] => rewrite union_elts
  (*cons - TODO do without simpl*)
  | H: In ?x (?y :: ?t) |-_ => simpl in H
  | |- context [In ?x (?y :: ?t)] => simpl
  (*remove \/ False from In goals*)
  | H: ?P \/ False |- _ => rewrite or_false_r in H
  | |- context [ ?P \/ False] => rewrite or_false_r
  (*remove_all*)
  | H: In ?x (remove_all ?e ?l1 ?l2) |- _ => rewrite <- remove_all_elts in H
  | |- context [In ?x (remove_all ?e ?l1 ?l2)] => rewrite <- remove_all_elts
  end.

Ltac simpl_set :=
  simpl_set_goal;
  repeat match goal with
  | H: ~ In ?x (remove_all ?e ?l1 ?l2) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (union ?e ?l1 ?l2) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (big_union ?e ?f ?l) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (remove ?e ?y ?l) |- _ => revert H; simpl_set_goal; intros
  end.

Ltac destruct_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | H: exists x, ?P |- _ => destruct H
  | H: ?P \/ ?Q |- _ => destruct H
  end; subst.

Ltac simpl_destruct_set :=
  repeat (progress (simpl_set; destruct_all)).

Ltac triv :=
  let inner := split_all; auto; 
  match goal with
  | |- ~ ?P => let C := fresh in intro C; subst; contradiction
  end
  in
  try solve[inner];
  match goal with
  | |- ?P \/ ?Q => solve[left; inner] + solve[right; inner]
  end.

Ltac not_or name :=
  repeat match goal with 
  | H: ~(?P \/ ?Q) |- _ => let N1 := fresh name in
    let N2 := fresh name in
    apply Decidable.not_or in H;
    
    destruct H as [N1 N2]
  end.

Ltac case_in :=
  repeat match goal with
  | |- context [if in_bool ?e ?x ?l then ?y else ?z] => 
    destruct (in_bool_spec e x l)
  end.

(*First, general and useful results about substitution*)

(*Substitution for patterns - needed for bound variable
  substitution, not free var subs like [sub_t] and [sub_f]*)
Fixpoint sub_p (x y: vsymbol) (p: pattern) :=
  match p with
  | Pvar v =>
    Pvar (if vsymbol_eq_dec v x then y else v)
  | Pwild => Pwild
  | Por p1 p2 => Por (sub_p x y p1) (sub_p x y p2)
  | Pbind p1 v =>
    Pbind (sub_p x y p1) (if vsymbol_eq_dec v x then y else v)
  | Pconstr f tys pats =>
    Pconstr f tys (map (sub_p x y) pats)
  end.

(*Substitute multiple vars according to map*)
Definition sub_mult {A: Type} (sub: vsymbol -> vsymbol -> A -> A) 
  (l: list (vsymbol * string)) (x: A) : A :=
  fold_right (fun x acc => sub (fst x) ((snd x), snd (fst x)) acc) x l.

(*Substitute multiple vars in pattern according to map*)
Definition sub_ps : list (vsymbol * string) -> pattern -> pattern:=
  sub_mult sub_p.
  
(*Substitute multiple vars in term according to map*)
Definition sub_ts: list (vsymbol * string) -> term -> term:=
  sub_mult sub_t.

(*Substitite multiple vars in formula according to map*)
Definition sub_fs: list (vsymbol * string) -> formula -> formula :=
  sub_mult sub_f.

(*We need a lot of results about how substition affects free
  variables*)

(*A few easy results about sub_t/f and free vars:*)

(*If the free var to sub is not in the term, substitution does nothing*)
Lemma sub_notin (t: term) (f: formula) :
  (forall (x y: vsymbol),
    ~ In x (term_fv t) ->
    sub_t x y t = t) /\
    (forall (x y: vsymbol),
    ~ In x (form_fv f) ->
    sub_f x y f = f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros; simpl_set; not_or Hinx.
  - destruct (vsymbol_eq_dec x v); subst; auto; contradiction.
  - f_equal. apply list_eq_ext';
    rewrite map_length; auto.
    intros.
    rewrite (map_nth_inbound) with(d2:=d); auto.
    rewrite Forall_forall in H. apply H; wf_tac.
    intro C. apply H0. simpl_set.  exists (nth n l1 d); split; wf_tac.
  - rewrite H; auto.
    destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with (d2:=d); auto.
    case_in; auto.
    rewrite Forall_forall in H0. rewrite H0; wf_tac.
    destruct (nth n ps d); auto.
    intro Hinx'. apply Hinx0. exists (nth n ps d).
    split; wf_tac. simpl_set. split; auto.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H; auto.
  - f_equal. apply list_eq_ext';
    rewrite map_length; auto.
    intros.
    rewrite (map_nth_inbound) with(d2:=d); auto.
    rewrite Forall_forall in H. apply H; wf_tac.
    intro C. apply H0.  exists (nth n tms d); split; wf_tac.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto.
  - rewrite H; auto.
    destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto.
    f_equal.
    apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with (d2:=d); auto.
    case_in; auto.
    rewrite Forall_forall in H0. rewrite H0; wf_tac.
    destruct (nth n ps d); auto.
    intro Hinx'. apply Hinx0. exists (nth n ps d).
    split; wf_tac. simpl_set. split; auto.
Qed.

Corollary sub_t_notin (t: term):
  (forall (x y: vsymbol),
    ~ In x (term_fv t) ->
    sub_t x y t = t).
Proof. apply sub_notin. apply Ftrue. Qed.

Corollary sub_f_notin (f: formula):
    (forall (x y: vsymbol),
    ~ In x (form_fv f) ->
    sub_f x y f = f).
Proof. apply sub_notin. apply tm_d. Qed.

(*If we substitute x with itself, then nothing changes*)
Lemma sub_eq (t: term) (f: formula) :
  (forall (x: vsymbol),
    sub_t x x t = t) /\
    (forall (x: vsymbol),
    sub_f x x f = f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - destruct (vsymbol_eq_dec x v); subst; auto.
  - f_equal. apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H; apply H; wf_tac.
  - rewrite H. destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal. apply list_eq_ext'; rewrite map_length; auto;
    intros. rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H0; rewrite H0; wf_tac.
    case_in; auto. destruct (nth n ps d); auto.
  - destruct (vsymbol_eq_dec x v); subst; auto. rewrite H; auto.
  - f_equal. apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H; apply H; wf_tac.
  - destruct (vsymbol_eq_dec x v); subst; auto. rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto.
  - rewrite H, H0. destruct (vsymbol_eq_dec x v); auto.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal. apply list_eq_ext'; rewrite map_length; auto;
    intros. rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H0; rewrite H0; wf_tac.
    case_in; auto. destruct (nth n ps d); auto.
Qed.

Corollary sub_t_eq (t: term):
  (forall (x: vsymbol),
    sub_t x x t = t).
Proof. apply sub_eq. apply Ftrue. Qed.

Corollary sub_f_eq (f: formula):
    (forall (x: vsymbol),
    sub_f x x f = f).
Proof. apply sub_eq. apply tm_d. Qed.

(*It is easier to prove some of the lemmas with an alternate
  approach: define when a variable is free rather than show
  the sets of free vars are equal:*)
Fixpoint free_in_t (x: vsymbol) (t: term) {struct t} : bool :=
  match t with
  | Tconst _ => false
  | Tvar v => vsymbol_eq_dec x v
  | Tfun f tys tms => existsb (fun t => free_in_t x t) tms
  | Tlet t1 v t2 =>
    free_in_t x t1 || (negb (vsymbol_eq_dec x v) && free_in_t x t2)
  | Tif f t1 t2 =>
    free_in_f x f || free_in_t x t1 || free_in_t x t2
  | Tmatch tm ty ps =>
    free_in_t x tm ||
    existsb (fun p => negb (in_bool vsymbol_eq_dec x (pat_fv (fst p))) &&
      free_in_t x (snd p)) ps
  | Teps f v => negb (vsymbol_eq_dec x v) && free_in_f x f
  end
with free_in_f (x: vsymbol) (f: formula) {struct f} : bool :=
  match f with
  | Fpred p tys tms => existsb (fun t => free_in_t x t) tms
  | Fquant q v f1 => negb (vsymbol_eq_dec x v) && free_in_f x f1
  | Feq ty t1 t2 => free_in_t x t1 || free_in_t x t2
  | Fbinop b f1 f2 => free_in_f x f1 || free_in_f x f2
  | Fnot f1 => free_in_f x f1
  | Flet tm v f1 => free_in_t x tm || (negb (vsymbol_eq_dec x v) &&
   free_in_f x f1)
  | Fif f1 f2 f3 => free_in_f x f1 || free_in_f x f2 ||
    free_in_f x f3
  | Fmatch tm ty ps =>
    free_in_t x tm ||
    (existsb (fun p => negb (in_bool vsymbol_eq_dec x (pat_fv (fst p)))
      && free_in_f x (snd p)) ps)
  | _ => false
  end.

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
  (*| |- context [negb ?b = true] =>
    rewrite negb_true_iff*)
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
  destruct dec; simpl; split; intros; auto.
Qed.

(*This is equivalent to the other formulation*)
(*TODO: would be easier with ssreflect*)
Lemma free_in_spec (t: term) (f: formula) :
  (forall x, free_in_t x t <-> In x (term_fv t)) /\
  (forall x, free_in_f x f <-> In x (form_fv f)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto; simpl_set; auto;
  try solve[split; auto].
  - rewrite (eq_sym_iff v x), dec_iff; reflexivity. 
  - bool_to_prop. apply ex_in_eq.
    eapply Forall_impl. 2: apply H. simpl; intros; auto. apply H0; auto.
  - rewrite <- H, <- H0. bool_to_prop.
    apply dec_negb_iff.
  - rewrite<- H, <- H0, <- H1.
    bool_to_prop.
  - rewrite <- H. bool_to_prop.
    apply ex_in_eq.
    revert H0. rewrite !Forall_forall; intros. simpl_set.
    bool_to_prop.
    rewrite <- H0; wf_tac. bool_to_prop.
    rewrite <- in_bool_dec.
    apply dec_negb_iff.
  - rewrite <- H; bool_to_prop.
    apply dec_negb_iff.
  - bool_to_prop. apply ex_in_eq.
    eapply Forall_impl. 2: apply H. simpl; intros; auto. apply H0; auto.
  - rewrite <- H; bool_to_prop. apply dec_negb_iff.
  - rewrite <- H, <- H0. bool_to_prop.
  - rewrite <- H, <- H0; bool_to_prop.
  - rewrite <- H, <- H0; bool_to_prop.
    apply dec_negb_iff.
  - rewrite <- H, <- H0, <- H1; bool_to_prop.
  - rewrite <- H. bool_to_prop.
    apply ex_in_eq.
    revert H0. rewrite !Forall_forall; intros. simpl_set.
    bool_to_prop.
    rewrite <- H0; wf_tac. bool_to_prop.
    rewrite <- in_bool_dec.
    apply dec_negb_iff.
Qed.

Corollary free_in_t_spec (t: term):
(forall x, free_in_t x t <-> In x (term_fv t)).
Proof. apply free_in_spec. apply Ftrue. Qed.

Lemma free_in_t_negb (t: term):
forall x, free_in_t x t = false <-> ~In x (term_fv t).
Proof.
  intros. destruct (free_in_t x t) eqn : Hfree; split; intros; auto.
  assert (is_true (free_in_t x t)) by auto.
  apply free_in_t_spec in H0. contradiction.
  intro Hin. apply free_in_t_spec in Hin.
  rewrite Hfree in Hin. inversion Hin.
Qed.

Corollary free_in_f_spec (f: formula):
(forall x, free_in_f x f <-> In x (form_fv f)).
Proof. apply free_in_spec. apply tm_d. Qed.

Lemma free_in_f_negb (f: formula):
forall x, free_in_f x f = false <-> ~In x (form_fv f).
Proof.
  intros. destruct (free_in_f x f) eqn : Hfree; split; intros; auto.
  assert (is_true (free_in_f x f)) by auto.
  apply free_in_f_spec in H0. contradiction.
  intro Hin. apply free_in_f_spec in Hin.
  rewrite Hfree in Hin. inversion Hin.
Qed.

(*Now we can reason about [free_in]*)

(*3 lemmas about free vars and [sub_t]*)

Ltac vsym_eq x y :=
  destruct (vsymbol_eq_dec x y); subst; auto; try contradiction.

Lemma existsb_eq {A: Type} {f1 f2: A -> bool} (l1 l2: list A):
  length l1 = length l2 ->
  Forall (fun x => f1 (fst x) = f2 (snd x)) (combine l1 l2) ->
  existsb f1 l1 = existsb f2 l2.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; simpl; auto.
  inversion H0; subst.
  simpl in H4. rewrite H4, (IHl1 l2); auto.
Qed. 
  

(*1. For any variables which are not x or y, sub_t doesn't change anything*)
Lemma sub_fv_diff (t: term) (f: formula):
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_t z (sub_t x y t) = free_in_t z t) /\
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_f z (sub_f x y f) = free_in_f z f).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v. vsym_eq z y. vsym_eq z v.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H2. 
    rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    wf_tac.
    apply H; wf_tac.
  - rewrite H; auto. f_equal. f_equal.
    vsym_eq x v.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply existsb_eq; wf_tac.
    revert H0.
    rewrite !Forall_forall; intros.
    revert H3.
    rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]; specialize (Hx (Pwild, tm_d) (Pwild, tm_d)); subst; simpl.
    wf_tac. case_in; auto.
    simpl; rewrite H0; wf_tac.
  - vsym_eq x v. simpl. rewrite H; auto.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H2. 
    rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    wf_tac.
    apply H; wf_tac.
  - vsym_eq x v; simpl; rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto. f_equal. f_equal.
    vsym_eq x v.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply existsb_eq; wf_tac.
    revert H0.
    rewrite !Forall_forall; intros.
    revert H3.
    rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]; specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)); subst; simpl.
    wf_tac. case_in; auto.
    simpl; rewrite H0; wf_tac.
Qed.

Corollary sub_t_fv_diff (t: term):
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_t z (sub_t x y t) = free_in_t z t).
Proof. apply sub_fv_diff. apply Ftrue. Qed.

Corollary sub_f_fv_diff (f:formula):
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_f z (sub_f x y f) = free_in_f z f).
Proof. apply sub_fv_diff. apply tm_d. Qed.

Lemma existsb_false {A: Type} (f: A -> bool) (l: list A):
  (existsb f l = false) <-> Forall (fun x => f x = false) l.
Proof.
  induction l; simpl; split; intros; auto.
  - rewrite orb_false_iff in H.
    destruct_all; subst; constructor; auto.
    apply IHl; auto.
  - rewrite orb_false_iff. inversion H; subst.
    split; auto. apply IHl; auto.
Qed.

(*2: If we replace x with y, x is NOT in the resulting free variables*)
Lemma sub_fv_notin (t: term) (f: formula):
  (forall (x y: vsymbol),
    x <> y ->
    free_in_t x (sub_t x y t) = false) /\
  (forall (x y: vsymbol),
    x <> y ->
    free_in_f x (sub_f x y f) = false).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v. vsym_eq v y. vsym_eq x v.
  - apply existsb_false.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_map_iff; intros [t [Ht Hint]]; subst.
    apply H; auto.
  - rewrite !orb_false_iff. split; [apply H; auto|].
    vsym_eq x v. simpl. apply H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; simpl; auto.
    apply existsb_false. revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_map_iff; intros [p1 [Hp1 Hinp1]]; subst.
    case_in; simpl; destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst p1))); simpl; auto;
    try contradiction.
    apply H0; wf_tac.
  - vsym_eq x v; simpl; auto. vsym_eq v v.
    vsym_eq x v; simpl. apply H; auto.
  - apply existsb_false.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_map_iff; intros [t [Ht Hint]]; subst.
    apply H; auto.
  - vsym_eq x v; simpl. vsym_eq v v. vsym_eq x v; simpl.
    apply H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto; simpl. vsym_eq x v; simpl.
    apply H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; simpl; auto.
    apply existsb_false. revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_map_iff; intros [p1 [Hp1 Hinp1]]; subst.
    case_in; simpl; destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst p1))); simpl; auto;
    try contradiction.
    apply H0; wf_tac.
Qed.

Corollary sub_t_fv_notin (t: term):
  (forall (x y: vsymbol),
    x <> y ->
    free_in_t x (sub_t x y t) = false).
Proof. apply sub_fv_notin. apply Ftrue. Qed.

Corollary sub_f_fv_notin (f: formula):
  (forall (x y: vsymbol),
    x <> y ->
    free_in_f x (sub_f x y f) = false).
Proof. apply sub_fv_notin. apply tm_d. Qed.

Lemma existsb_orb {A: Type} (f1 f2: A -> bool) (l: list A):
  existsb f1 l || existsb f2 l =
  existsb (fun x => f1 x || f2 x) l.
Proof.
  induction l; simpl; auto.
  rewrite <- !orb_assoc. f_equal.
  rewrite orb_comm, <- orb_assoc. f_equal.
  rewrite orb_comm; apply IHl.
Qed.

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


(*3. When we substitute x with y, y is in the free variables
  iff either y was before or x was before*)
(*Need the Hbnd assumption for the following: in let t1 = v in t2,
  if y =v, then y will not be in the free variables of
  the substituted term even if x is a free variable in t2*)
Lemma sub_fv_in (t: term) (f: formula):
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (bnd_t t)),
    x <> y ->
    free_in_t y (sub_t x y t) = (free_in_t x t) || (free_in_t y t)) /\
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (bnd_f f)),
    x <> y ->
    free_in_f y (sub_f x y f) = (free_in_f x f) || (free_in_f y f)).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v; simpl.
    vsym_eq y y.
  - rewrite existsb_orb.
    apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    wf_tac. apply H; wf_tac. intro C.
    apply Hbnd. rewrite in_concat. exists (bnd_t (nth i l1 tm_d)); 
    split; wf_tac.
  - rewrite H; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv]. 
    rewrite <- !orb_assoc. f_equal.
    rewrite !orb_andb_distrib_r.
    vsym_eq x v.
    rewrite H0; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv].
    vsym_eq y v. exfalso. apply Hbnd; triv.
    simpl. solve_bool.
  - rewrite H, H0, H1; auto;[solve_bool| | |]; intro C; apply Hbnd;
    rewrite !in_app_iff; triv.
  - (*match is hard case not surprisingly*)
    rewrite H; auto; [|intro C; apply Hbnd; rewrite in_app_iff; triv].
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    (*Now just have the exists goal*)
    rewrite existsb_orb.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_combine_iff; wf_tac; intros [i [Hi Hx]].
    specialize (Hx (Pwild, tm_d) (Pwild, tm_d)); subst; simpl.
    wf_tac. case_in; simpl; auto.
    destruct (in_bool_spec vsymbol_eq_dec y (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl.
    + (*contradiction: y not in bound vars*)
      exfalso. apply Hbnd. rewrite in_app_iff. right.
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, tm_d))))
      ++ (bnd_t (snd (nth i ps (Pwild, tm_d))))).
      split; wf_tac. exists (nth i ps (Pwild, tm_d)). split; wf_tac.
    + rewrite H0; wf_tac. intro C.
      apply Hbnd. rewrite in_app_iff. right. 
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, tm_d))))
      ++ (bnd_t (snd (nth i ps (Pwild, tm_d))))).
      split; wf_tac. exists (nth i ps (Pwild, tm_d)). split; wf_tac.
  - vsym_eq x v; simpl.
    vsym_eq y v; simpl.
    + exfalso; apply Hbnd; triv.
    + rewrite H; auto.
  - rewrite existsb_orb.
    apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    wf_tac. apply H; wf_tac. intro C.
    apply Hbnd. rewrite in_concat. exists (bnd_t (nth i tms tm_d)); 
    split; wf_tac.
  - vsym_eq x v; simpl.
    vsym_eq y v; simpl.
    + exfalso; apply Hbnd; triv.
    + rewrite H; auto.
  - rewrite H, H0; auto; [solve_bool | |]; intro C; apply Hbnd;
    rewrite in_app_iff; triv.
  - rewrite H, H0; auto; [solve_bool | |]; intro C; apply Hbnd;
    rewrite in_app_iff; triv.
  - rewrite H; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv]. 
    rewrite <- !orb_assoc. f_equal.
    rewrite !orb_andb_distrib_r.
    vsym_eq x v.
    rewrite H0; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv].
    vsym_eq y v. exfalso. apply Hbnd; triv.
    simpl. solve_bool.
  - rewrite H, H0, H1; auto;[solve_bool | | |]; intro C;
    apply Hbnd; rewrite !in_app_iff; triv.
  - rewrite H; auto; [|intro C; apply Hbnd; rewrite in_app_iff; triv].
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    (*Now just have the exists goal*)
    rewrite existsb_orb.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_combine_iff; wf_tac; intros [i [Hi Hx]].
    specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)); subst; simpl.
    wf_tac. case_in; simpl; auto.
    destruct (in_bool_spec vsymbol_eq_dec y (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl.
    + (*contradiction: y not in bound vars*)
      exfalso. apply Hbnd. rewrite in_app_iff. right.
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, Ftrue))))
      ++ (bnd_f (snd (nth i ps (Pwild, Ftrue))))).
      split; wf_tac. exists (nth i ps (Pwild, Ftrue)). split; wf_tac.
    + rewrite H0; wf_tac. intro C.
      apply Hbnd. rewrite in_app_iff. right. 
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, Ftrue))))
      ++ (bnd_f (snd (nth i ps (Pwild, Ftrue))))).
      split; wf_tac. exists (nth i ps (Pwild, Ftrue)). split; wf_tac.
Qed. 

Corollary sub_t_fv_in (t: term):
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (bnd_t t)),
    x <> y ->
    free_in_t y (sub_t x y t) = (free_in_t x t) || (free_in_t y t)). 
Proof. apply sub_fv_in. apply Ftrue. Qed.

Corollary sub_f_fv_in (f: formula):
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (bnd_f f)),
    x <> y ->
    free_in_f y (sub_f x y f) = (free_in_f x f) || (free_in_f y f)).
Proof. apply sub_fv_in. apply tm_d. Qed.


(*Alpha equivalence*)

(*Let's try this*)
Print term.
Print map2.

Section Alpha.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
 {pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m)
  {vt: @val_typevar sigma} {pf: pi_funpred gamma_valid pd}.

Notation term_rep := (term_rep gamma_valid pd all_unif vt pf).
Notation formula_rep := (formula_rep gamma_valid pd all_unif vt pf).

(*So Coq can tell l1 decreases*)
Fixpoint all2 {A: Type} (f: A -> A -> bool) (l1: list A) : list A -> bool :=
  match l1 with
  | nil => fun l2 =>
          match l2 with
          | nil => true
          | _ => false
          end
  | x1 :: t1 =>
    fun l2 =>
    match l2 with
    | nil => false
    | x2 :: t2 => f x1 x2 && all2 f t1 t2
    end
  end.
Print sub_t.
(*Definition of alpha equivalence*)
Print pattern.
Print get_assoc_list.

(*Let's see - is this sufficient?
  We only check the "shape" - don't need variable consistency,
  this is given by typing rules*)
(*TODO: show this implies [pat_fv] has same length (with typing)
  OR we can check it in [alpha_equiv_t] - better to show i guess*)
  (*
Fixpoint alpha_equiv_p (p1 p2: pattern) : bool :=
  match p1, p2 with
  | Pvar v1, Pvar v2 => vty_eq_dec (snd v1) (snd v2)
  | Pconstr f1 ty1 ps1, Pconstr f2 ty2 ps2 =>
    (funsym_eq_dec f1 f2) &&
    (length ps1 =? length ps2) &&
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (fix all2 (l1 l2: list pattern) : bool :=
      match l1, l2 with
      | nil, nil => true
      | x1 :: t1, x2 :: t2 => alpha_equiv_p x1 x2 && all2 t1 t2
      | _, _ => false
      end) ps1 ps2
  | Por p1 p3, Por p2 p4 =>
    alpha_equiv_p p1 p2 &&
    alpha_equiv_p p3 p4
  | Pbind p1 v1, Pbind p2 v2 =>
    vty_eq_dec (snd v1) (snd v2) &&
    alpha_equiv_p p1 p2
  | _, _ => false
  end.*)

(*Check that (x, y) binding is at the same point in the list.
  This is equivalent to the old method (proved below, will delete)
  but should be (TODO?) easier to work with*)
  Definition eq_var (vars: list (vsymbol * vsymbol)) v1 v2 :=
    fold_right (fun t acc => (vsymbol_eq_dec v1 (fst t) && vsymbol_eq_dec v2 (snd t)) ||
      (negb (vsymbol_eq_dec v1 (fst t)) && negb (vsymbol_eq_dec v2 (snd t)) &&
      acc)) (vsymbol_eq_dec v1 v2) vars.


(*default vsymbol*)
Definition vs_d : vsymbol := (a, vty_int).

Definition in_first {A B: Type} (x: A * B) (l: list (A * B)) : Prop :=
  exists l1 l2, l = l1 ++ x :: l2 /\
  (~ In (fst x) (map fst l1) /\
  ~ In (snd x) (map snd l1)).

Lemma get_assoc_list_some_first {A B: Set}
  (eq_dec : forall x y : A, {x = y} + {x <> y})
  (l : list (A * B)) (x : A) (res : B):
  get_assoc_list eq_dec l x = Some res ->
  exists l1 l2, l = l1 ++ (x, res) :: l2 /\
  ~ In x (map fst l1).
Proof.
  induction l; simpl;[intro C; inversion C|].
  destruct a; simpl.
  destruct (eq_dec x a); subst.
  - intros Hb; inversion Hb; subst.
    exists nil. exists l. split; auto.
  - intros Hres; apply IHl in Hres. destruct_all.
    exists ((a, b) :: x0). exists x1. split; auto.
    simpl. intro C; destruct_all; subst; auto; contradiction.
Qed.

Lemma app_inv {A: Type} (l1 l2 l3 l4: list A) x :
  l1 ++ x :: l2 = l3 ++ x :: l4 ->
  ~In x l1 ->
  ~ In x l3 ->
  l1 = l3 /\ l2 = l4.
Proof.
  revert l2 l3 l4. induction l1; simpl; intros.
  - destruct l3; inversion H; auto.
    subst. exfalso. apply H1. simpl; auto.
  - destruct l3; simpl in *.
    + inversion H; subst. exfalso. apply H0. triv.
    + inversion H; subst. apply IHl1 in H4; destruct_all; subst; auto.
Qed.
(*
Lemma get_assoc_list_in_first {A: Set}
(eq_dec : forall x y : A, {x = y} + {x <> y})
(l : list (A * A)) (x : A) (y : A):
get_assoc_list eq_dec l x = Some y ->
get_assoc_list eq_dec (flip l) y = Some x ->
in_first (x, y) l.
Proof.
  intros Hx Hy.
  apply get_assoc_list_some_first in Hx.
  apply get_assoc_list_some_first in Hy.
  unfold in_first.
  destruct_all.
  unfold flip in H.
  rewrite !map_app in H. simpl in H.
  apply app_inv in H; destruct_all; subst.
  - exists x2. exists x3. split; auto. split; auto.
    simpl. rewrite map_map in H0. simpl in H0. apply H0.
  - intro C. apply H2. revert C.
    rewrite !in_map_iff; intros; destruct_all.
    inversion H1; subst. exists x4. split; auto.
  - intro C; apply H0; revert C; rewrite !in_map_iff; intros; destruct_all.
    exists (y, x); split; auto.
Qed.*)

Lemma in_first_cons {A B: Type} 
(x1 x2: A) (y1 y2: B) l:
  in_first (x1, y1) ((x2, y2) :: l) <->
  (x1 = x2 /\ y1 = y2) \/ (x1 <> x2 /\ y1 <> y2 /\ in_first (x1, y1) l).
Proof.
  unfold in_first. simpl. split; intros.
  - destruct_all.
    destruct x; simpl in *.
    + inversion H; subst. left; auto.
    + destruct p. inversion H; subst; auto.
      simpl in *. right. split_all; auto. 
      exists x. exists x0. split; auto.
  - destruct_all; subst.
    + exists nil. exists l. auto.
    + exists ((x2, y2) :: x). exists x0. split_all; auto; simpl;
      intro C; destruct_all; auto.
Qed.

(*This gives us a decidable version*)
Definition in_firstb {A B: Type} 
  (eq_dec1: forall (x y: A), {x=y} + {x<>y})
  (eq_dec2: forall (x y: B), {x=y} + {x<>y}) 
  (x: A * B) (l: list (A * B)) : bool :=
  fold_right (fun y acc => 
    (eq_dec1 (fst x) (fst y) && eq_dec2 (snd x) (snd y)) ||
    (negb (eq_dec1 (fst x) (fst y)) && negb (eq_dec2 (snd x) (snd y)) &&
    acc)) false l.

Lemma in_first_in {A B: Type} (t: A * B) l:
  in_first t l ->
  In t l.
Proof.
  unfold in_first. intros [l1 [l2 [Hl [Hnotin1 Hnotin2]]]]; subst.
  in_tac; simpl. triv.
Qed.

Lemma in_first_nil {A B: Type} (t: A * B):
  ~ in_first t nil.
Proof.
  intro C. apply in_first_in in C. inversion C.
Qed.

Lemma in_firstb_spec {A B: Type} 
  (eq_dec1: forall (x y: A), {x=y} + {x<>y})
  (eq_dec2: forall (x y: B), {x=y} + {x<>y}) 
  (x: A * B) (l: list (A * B)):
  reflect (in_first x l) (in_firstb eq_dec1 eq_dec2 x l).
Proof.
  induction l; simpl.
  - apply ReflectF. intro C. apply in_first_nil in C. destruct C.
  - destruct x as [x1 x2]; simpl in *.
    destruct a as [y1 y2]; simpl in *. 
    destruct (eq_dec1 x1 y1); simpl; simpl_bool.
    + destruct (eq_dec2 x2 y2); simpl;
      [apply ReflectT | apply ReflectF].
      * rewrite in_first_cons. left; auto.
      * intro C. rewrite in_first_cons in C.
        destruct_all; subst; auto.
    + destruct (eq_dec2 x2 y2); simpl.
      * apply ReflectF. intro C. rewrite in_first_cons in C.
        destruct_all; subst; auto.
      * destruct IHl.
        -- apply ReflectT. rewrite in_first_cons. right; auto.
        -- apply ReflectF. intro C. rewrite in_first_cons in C.
          destruct_all; subst; auto.
Qed.

Lemma in_first_app {A B: Type} (x: A)(y: B) (l1 l2: list (A * B)) :
  in_first (x, y) (l1 ++ l2) <->
  in_first (x, y) l1 \/ in_first (x, y) l2 /\ ~ In x (map fst l1) /\ ~ In y (map snd l1).
Proof.
  induction l1; simpl.
  - split; intros; try triv.
    destruct_all; auto.
    exfalso. apply (in_first_nil _ H).
  - destruct a as [x1 y1]. rewrite !in_first_cons.
    split; intros; destruct_all; try triv; auto.
    + rewrite IHl1 in H1. destruct_all; try triv. right.
      simpl. split_all; auto; intro C; destruct_all; subst; auto.
    + rewrite IHl1. triv.
    + rewrite IHl1. simpl in *.
      not_or Hinxy. triv.
Qed.

Notation var_in_firstb := (in_firstb vsymbol_eq_dec vsymbol_eq_dec).

(*Hmm think about this - is this correct def?*)
(*We need the condition that [in_firstb] for the Pvar and Pbind case.
  If not, suppose we have the patterns
  Por (Pvar y) (Pvar x) and Por (Pvar x) (Pvar x)
  and vars = [(y, x)] (= combine (pat_fv p1) (pat_fv p2))
  then this would be alpha equivalent
  *)
  (*TODO: could add condition in Pconstr that all lengths are equal
    (and in other inductive cases) but this is really not ideal
    We should have a definition so that mapping result holds*)
Fixpoint alpha_equiv_p (*(vars: vsymbol -> vsymbol) *)
(vars: list (vsymbol * vsymbol)) (p1 p2: pattern)  : bool :=
  match p1, p2 with
  | Pvar v1, Pvar v2 =>
    vty_eq_dec (snd v1) (snd v2) &&
    (*vsymbol_eq_dec v2 (vars v1)*)
    (*eq_var vars v1 v2 (*&&*)*)
    var_in_firstb (v1, v2) vars (*NOTE: we need this, see above*)
  | Pconstr f1 ty1 ps1, Pconstr f2 ty2 ps2 =>
    (funsym_eq_dec f1 f2) &&
    (length ps1 =? length ps2) &&
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (fix all2 (l1 l2: list pattern) : bool :=
      match l1, l2 with
      | nil, nil => true
      | x1 :: t1, x2 :: t2 => alpha_equiv_p vars x1 x2 && all2 t1 t2
      | _, _ => false
      end) ps1 ps2
  | Por p1 p3, Por p2 p4 =>
    alpha_equiv_p vars p1 p2 &&
    alpha_equiv_p vars p3 p4
  | Pbind p1 v1, Pbind p2 v2 =>
    vty_eq_dec (snd v1) (snd v2) &&
    (*vsymbol_eq_dec v2 (vars v1) &&*)
    (*eq_var vars v1 v2 &&*)
    var_in_firstb (v1, v2) vars &&
    alpha_equiv_p vars p1 p2
  | Pwild, Pwild => true
  | _, _ => false
  end.

(*TODO: let's see*)
Lemma map_union {A B: Type} 
  (eq_dec1: forall (x y: A), {x=y} + {x<>y})
  (eq_dec2: forall (x y: B), {x=y} + {x<>y}) 
  (f: A -> B) (l1 l2: list A)
  (Hinj: forall x y, In x (l1 ++ l2) -> In y (l1 ++ l2) ->
    f x = f y -> x = y):
  map f (union eq_dec1 l1 l2) = union eq_dec2 (map f l1) (map f l2).
Proof.
  generalize dependent l2. induction l1; simpl; intros; auto.
  rewrite <- IHl1; auto.
  destruct (in_dec eq_dec1 a (union eq_dec1 l1 l2)).
  - destruct (in_dec eq_dec2 (f a) (map f (union eq_dec1 l1 l2))); auto.
    exfalso. apply n. apply in_map_iff. exists a; auto.
  - simpl. destruct (in_dec eq_dec2 (f a) (map f (union eq_dec1 l1 l2))); auto.
    rewrite in_map_iff in i.
    destruct i as [y [Hxy Hiny]].
    assert (a = y). { apply Hinj; auto; try triv. right.
      rewrite in_app_iff; rewrite union_elts in Hiny; auto.
    }
    subst; contradiction.
Qed.


(*Now we will create the map and show it is injective.*)
(*Could make polymorphic (and subsume ty_subst_fun) but
  we don't want even more eq_decs. Should use ssreflect probably*)
Fixpoint mk_fun (l1 l2: list vsymbol) (x: vsymbol) : vsymbol :=
  match l1, l2 with
  | a :: t1, b :: t2 => if vsymbol_eq_dec x a then b else mk_fun t1 t2 x
  | _, _ => x
  end.

Lemma mk_fun_in l1 l2 x:
  length l1 <= length l2 ->
  In x l1 ->
  In (mk_fun l1 l2 x) l2.
Proof.
  revert l2. induction l1; simpl; intros; auto. destruct H0.
  destruct l2. inversion H. simpl in H.
  vsym_eq x a; simpl; try triv.
  destruct H0; subst; auto.
  contradiction. right. apply IHl1; auto; lia.
Qed.

Lemma mk_fun_inj (l1 l2: list vsymbol):
  NoDup l1 ->
  NoDup l2 ->
  length l1 <= length l2 ->
  (forall x y, In x l1 -> In y l1 -> 
    (mk_fun l1 l2 x) = (mk_fun l1 l2 y) -> x = y).
Proof.
  revert l2. induction l1; simpl; intros. destruct H2.
  destruct l2. inversion H1. simpl in H1.
  inversion H; inversion H0; subst.
  vsym_eq x a.
  - vsym_eq y a.
    destruct H3; subst; auto.
    apply mk_fun_in with(l2:=l2) in H3; auto.
    contradiction. lia.
  - vsym_eq y a.
    + destruct H2; subst; auto.
      apply mk_fun_in with(l2:=l2) in H2; auto. contradiction. lia.
    + destruct H2; subst; auto; try contradiction.
      destruct H3; subst; auto; try contradiction. 
      apply IHl1 with(l2:=l2); auto. lia.
Qed.

(*TODO: move this whole thing*)
Require Import Coq.Logic.FinFun.
Section NoDupsList.

Context {A: Type}.
Variable (f: nat -> A).
(*We have an injection nat -> A*)
Variable (Hinj: forall n1 n2, f n1 = f n2 -> n1 = n2).

(*Generate list with n distinct elements*)
Definition gen_dist (n: nat) : list A :=
  map f (seq 0 n).

Lemma gen_dist_length (n: nat): length (gen_dist n) = n.
Proof.
  unfold gen_dist. rewrite map_length, seq_length. reflexivity.
Qed.

Lemma gen_dist_correct (n: nat): NoDup (gen_dist n).
Proof.
  unfold gen_dist. apply Injective_map_NoDup.
  unfold Injective. apply Hinj.
  apply seq_NoDup.
Qed.

(*Generate list of n distinct elements, all of which are not
  in l*)
Variable eq_dec: forall (x y: A), {x=y} +{x<>y}.
Definition gen_dist_notin (n: nat) (l: list A): list A :=
  firstn n 
    (filter (fun x => negb(in_dec eq_dec x l)) (gen_dist (n + length l))).

Lemma filter_length_le {B: Type} (g: B -> bool) (l: list B):
  length (filter g l) <= length l.
Proof.
  induction l; simpl; auto. destruct (g a); simpl; auto.
  apply le_n_S; auto.
Qed.

Lemma all_filter {B: Type} (g: B -> bool) (l: list B):
  forallb g l <-> filter g l = l.
Proof.
  induction l; simpl; split; intros; auto.
  - destruct (g a) eqn : Hg; try solve[inversion H].
    apply IHl in H. rewrite H; auto.
  - destruct (g a) eqn : Hg; simpl; auto. 
    + inversion H. rewrite H1. apply IHl in H1; auto.
    + assert (length (a :: l) <= length l). {
        rewrite <- H. apply filter_length_le.
      }
      simpl in H0. lia.
Qed.

Lemma in_split (x: A) (l: list A):
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  induction l; simpl; intros. destruct H.
  destruct H; subst.
  - exists nil. exists l. reflexivity.
  - apply IHl in H. destruct H as [l1 [l2 Hl]]; subst.
    exists (a :: l1). exists l2. reflexivity.
Qed. 

Lemma filter_cons (g: A -> bool) (x: A) (l: list A):
  filter g (x :: l) = if g x then x :: filter g l else filter g l.
Proof.
  reflexivity.
Qed.

(*Useful for us*)
Lemma filter_in_notin (l1 l2: list A) (x: A):
  ~ In x l2 ->
  filter (fun y => negb (in_dec eq_dec y (x :: l1))) l2 =
  filter (fun y => negb (in_dec eq_dec y l1)) l2.
Proof.
  intros.
  apply filter_ext_in; intros.
  destruct (in_dec eq_dec a l1); simpl;
  destruct (eq_dec x a); subst; auto;
  destruct (in_dec eq_dec a l1); auto;
  contradiction.
Qed.

(*Proving that this is correct is not trivial*)
(*A version of the pigeonhole principle: given two lists l1 and l2,
  if l2 is larger and has no duplicates, it has at least 
    (length l2) - (length l1) elements that are not in l1*)
Lemma php (l1 l2: list A):
  NoDup l2 -> 
  length l1 <= length l2 ->
  length l2 - length l1 <= 
    length (filter (fun x => negb(in_dec eq_dec x l1)) l2).
Proof.
  (*Try alternate, then go back*)
  revert l2. induction l1; intros; auto.
  - simpl. rewrite Nat.sub_0_r.
    assert ((filter (fun _ : A => true) l2) = l2). {
      apply all_filter. apply forallb_forall. auto.
    }
    rewrite H1. auto.
  - destruct (in_dec eq_dec a l2).
    2: {
      rewrite filter_in_notin; auto; simpl.
      specialize (IHl1 _ H). lia.
    }
    (*For this one, we have to split l2 depending on
      where a appears*)
    apply in_split in i.
    destruct i as [p1 [p2 Hl2]].
    rewrite Hl2, filter_app, filter_cons.
    assert (Hnodup:=H).
    rewrite Hl2 in H.
    rewrite NoDup_app_iff in H. destruct H as [Hn1 [Hn2 [Hnotin1 Hnotin2]]].
    inversion Hn2. subst x l.
    assert (~ In a p1). {
      apply Hnotin2. left; auto.
    } 
    rewrite !filter_in_notin; auto.
    simpl. destruct (eq_dec a a); auto; try contradiction.
    simpl. rewrite <- filter_app.
    assert (Hn3: NoDup (p1 ++ p2)). {
      rewrite NoDup_app_iff. repeat split; auto.
      - intros; intro C. apply (Hnotin1 x H1). right; auto.
      - intros; apply Hnotin2. right; auto.
    }
    specialize (IHl1 _ Hn3).
    rewrite !app_length; simpl. simpl in H0.
    rewrite !app_length in IHl1. lia.
Qed.

(*Now we can prove our function correct*)
Lemma gen_dist_notin_length (n: nat) (l: list A):
  length (gen_dist_notin n l) = n.
Proof.
  unfold gen_dist_notin.
  rewrite firstn_length_le; auto.
  pose proof (php l (gen_dist (n + length l))).
  rewrite gen_dist_length in H.
  specialize (H (gen_dist_correct _)). lia.
Qed.

Lemma gen_dist_notin_nodup (n: nat) (l: list A):
  NoDup (gen_dist_notin n l).
Proof.
  unfold gen_dist_notin.
  apply NoDup_firstn.
  apply NoDup_filter.
  apply gen_dist_correct.
Qed.

Lemma gen_dist_notin_notin (n: nat) (l: list A):
  forall y, In y (gen_dist_notin n l) -> ~ In y l.
Proof.
  intros. unfold gen_dist_notin in H.
  apply In_firstn in H.
  rewrite in_filter in H. destruct H.
  destruct (in_dec eq_dec y l); auto.
Qed.

End NoDupsList.


(*Get a string with n zeroes*)
Fixpoint nth_str (n: nat) : string :=
  match n with
  | O => EmptyString
  | S m => String Ascii.zero (nth_str m)
  end.

Lemma nth_string_inj: forall n1 n2,
  nth_str n1 = nth_str n2 ->
  n1 = n2.
Proof.
  intros n1; induction n1; simpl; intros;
  destruct n2; inversion H; subst; auto.
Qed.

Definition nth_vs (n: nat) : vsymbol :=
  (nth_str n, vty_int).

Lemma nth_vs_inj: forall n1 n2,
  nth_vs n1 = nth_vs n2 ->
  n1 = n2.
Proof.
  intros. unfold nth_vs in H. inversion H; subst.
  apply nth_string_inj in H1; auto.
Qed.

(*Alt approach for proving length*)

(*map over a pattern, changing free vars according to map*)
Fixpoint map_pat (f: vsymbol -> vsymbol) (p: pattern) : pattern :=
  match p with
  | Pvar x => Pvar (f x)
  | Pwild => Pwild
  | Pconstr c tys ps =>
    Pconstr c tys (map (fun x => map_pat f x) ps)
  | Por p1 p2 =>
    Por (map_pat f p1) (map_pat f p2)
  | Pbind p1 x =>
    Pbind (map_pat f p1) (f x)
  end.

Lemma map_pat_free_vars (f: vsymbol -> vsymbol) (p: pattern)
  (Hinj: forall x y, In x (pat_fv p) -> In y (pat_fv p) ->
    f x = f y -> x = y):
  pat_fv (map_pat f p) = map f (pat_fv p).
Proof.
  induction p; simpl; auto.
  - simpl in Hinj.
    induction ps; simpl in *; auto.
    inversion H; subst.
    rewrite map_union with(eq_dec2:=vsymbol_eq_dec).
    + rewrite H2, IHps; auto.
      * intros; apply Hinj; auto; simpl_set; triv.
      * intros; apply Hinj; auto; simpl_set; triv.
    + intros x y. rewrite !in_app_iff; intros; apply Hinj; auto;
      rewrite union_elts; auto.
  - simpl in Hinj. rewrite map_union with(eq_dec2:=vsymbol_eq_dec).
    + rewrite IHp1, IHp2; auto; intros; apply Hinj; simpl_set; auto.
    + intros x y. rewrite !in_app_iff; intros; apply Hinj; simpl_set; auto.
  - simpl in Hinj.
    rewrite map_union with (eq_dec2:=vsymbol_eq_dec); simpl.
    + rewrite IHp; auto.
      intros; apply Hinj; simpl_set; auto.
    + intros x y. rewrite !in_app_iff; simpl.
      rewrite !or_false_r; intros; apply Hinj; simpl_set; auto.
Qed.

Lemma alpha_equiv_p_map vars (p1 p2: pattern) (f: vsymbol -> vsymbol)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hfeq: forall x y,
    var_in_firstb (x, y) vars -> y = f x):
  p2 = map_pat f p1.
Proof.
  generalize dependent p2.
  induction p1; simpl; intros; destruct p2; try solve[inversion Heq]; auto.
  - erewrite <- Hfeq. reflexivity.
    revert Heq; bool_to_prop; intros; destruct Heq; auto.
  - revert Heq; bool_to_prop; intros; destruct_all; repeat simpl_sumbool.
    apply Nat.eqb_eq in H3.
    simpl in Hfeq.
    f_equal.
    generalize dependent l0.
    induction ps; simpl; intros; destruct l0; inversion H3; auto.
    revert H1; bool_to_prop; intros; destruct H1.
    inversion H; subst. rewrite H6 with(p2:=p); auto.
    f_equal. apply IHps; auto.
  - revert Heq; bool_to_prop; intros [Heq1 Heq2].
    simpl in Hfeq.
    rewrite  <- (IHp1_1 p2_1), <- (IHp1_2 p2_2); auto.
  - revert Heq; bool_to_prop; intros; destruct_all.
    simpl in Hfeq.
    rewrite <- (IHp1 p2); auto.
    f_equal. apply Hfeq; simpl_set; triv.
Qed.

Lemma alpha_equiv_p_map_f vars (p1 p2: pattern) (f: vsymbol -> vsymbol)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hfeq: forall x y,
    var_in_firstb (x, y) vars -> y = f x):
  forall x, In x (pat_fv p1) -> snd x = snd (f x).
Proof.
  generalize dependent p2.
  induction p1; simpl; intros; destruct p2; try solve[inversion Heq]; auto.
  - revert Heq; bool_to_prop; intros; destruct Heq as [Htys  Hvar];
    simpl_sumbool. destruct H as [Hvx | []]; subst. 
    erewrite <- Hfeq. apply e. auto.
  - revert Heq; bool_to_prop; intros; destruct_all; repeat simpl_sumbool.
    apply Nat.eqb_eq in H4.
    rename l0 into ps2.
    assert (Hall: forall i, i < length ps ->
      alpha_equiv_p vars (nth i ps Pwild) (nth i ps2 Pwild)). {
      generalize dependent ps2. clear. induction ps; simpl; intros;
      destruct ps2; inversion H4. lia.
      apply andb_true_iff in H2. destruct H2.
      destruct i; simpl; auto. apply IHps; auto. lia.
    }
    clear H2.
    simpl_set.
    destruct H0 as [p [Hinp Hinx]].
    pose proof (In_nth _ _ Pwild Hinp).
    destruct H0 as [i [Hi Hp]]; subst.
    rewrite Forall_forall in H.
    apply (H _ Hinp _ (Hall _ Hi)); auto.
  - destruct H.
  - simpl_set.
    revert Heq; bool_to_prop; intros [Heq1 Heq2].
    destruct H; [apply (IHp1_1 _ Heq1) | apply (IHp1_2 _ Heq2)]; auto.
  - revert Heq; bool_to_prop; intros; destruct_all.
    simpl_set. destruct H.
    + apply (IHp1 _ H1); auto.
    + destruct H as [Hxv | []]; subst.
      apply Hfeq in H2; subst.
      simpl_sumbool.
Qed.

(*So now we need a map that is injective over free vars of p1
  AND maps all var_in_firstb pairs of variables from vars
  together. This is not too hard, using what we have*)

(*Now we provide a new definition of [mk_fun] that does not
  require the lists to be of the same length but still has
  the property we want*)
Definition mk_fun' (l1 l2: list vsymbol) (x: vsymbol) : vsymbol :=
  let n1 := length l1 in
  let n2 := length l2 in
  let l2' := if (n2 <? n1) then l2 ++
    gen_dist_notin nth_vs vsymbol_eq_dec (n1 - n2) l2 else l2 in
  mk_fun l1 l2' x.

Lemma add_notin_nodup (l1: list vsymbol) n:
  NoDup l1 ->
  NoDup (l1 ++ gen_dist_notin nth_vs vsymbol_eq_dec n l1).
Proof.
  intros.
  rewrite NoDup_app_iff; split_all; auto.
  + apply gen_dist_notin_nodup; apply nth_vs_inj.
  + intros. intro C. apply gen_dist_notin_notin in C. contradiction.
  + intros. apply gen_dist_notin_notin in H0. auto.
Qed.

Lemma mk_fun_inj' (l1 l2: list vsymbol):
  NoDup l1 ->
  NoDup l2 ->
  forall x y,
    In x l1 -> In y l1 -> mk_fun' l1 l2 x = mk_fun' l1 l2 y -> x = y.
Proof.
  intros. unfold mk_fun' in H3. apply mk_fun_inj in H3; auto.
  - destruct (length l2 <? length l1); auto.
    apply add_notin_nodup; auto.
  - destruct (Nat.ltb_spec0 (length l2) (length l1)); try lia.
    rewrite app_length, gen_dist_notin_length. lia.
    apply nth_vs_inj.
Qed.

Lemma Nat_eqb_S (n1 n2: nat):
  S n1 <? S n2 = (n1 <? n2).
Proof.
  destruct (Nat.ltb_spec0 n1 n2);
  destruct (Nat.ltb_spec0 (S n1) (S n2)); auto; try lia.
Qed.

Lemma mk_fun_in_firstb (l1 l2 l3: list vsymbol) x y:
  var_in_firstb (x, y) (combine l1 l2) ->
  mk_fun l1 (l2 ++ l3) x = y.
Proof.
  revert l2. induction l1; simpl; intros;[inversion H |].
  destruct l2; [inversion H |]. (*Why we need this and NOT var_eqb!*) 
  simpl. simpl in H.
  vsym_eq x a; simpl in H.
  - vsym_eq y v. inversion H.
  - apply IHl1. revert H; bool_to_prop; intros; apply H.
Qed.

Lemma mk_fun_in_firstb' (l1 l2: list vsymbol):
  forall x y,
    var_in_firstb (x, y) (combine l1 l2) ->
    y = mk_fun' l1 l2 x.
Proof.
  revert l2. induction l1; simpl; intros; auto; [inversion H |].
  destruct l2; [inversion H|].
  simpl in H.
  unfold mk_fun' in *. simpl.
  specialize (IHl1 l2 x y).
  rewrite Nat_eqb_S.
  destruct (length l2 <? length l1) eqn: Hlen.
  - vsym_eq x a; simpl in H.
    + vsym_eq y v. inversion H.
    + vsym_eq y v; try solve[inversion H].
      simpl in H.
      rewrite mk_fun_in_firstb with(y:=y); auto.
  - vsym_eq x a; simpl in H.
    + vsym_eq y v. inversion H.
    + vsym_eq y v.
Qed.

(*Now we put everything together*)
(*We don't really care what the function is, except that it
  is injective*)
Lemma alpha_equiv_p_fv (l1 l2: list vsymbol) 
  (p1 p2: pattern)
  (Hn1: NoDup l1)
  (Hn2: NoDup l2)
  (Hl1: forall x, In x (pat_fv p1) -> In x l1)
  (Heq: alpha_equiv_p (combine l1 l2) p1 p2):
  pat_fv p2 = map (mk_fun' l1 l2) (pat_fv p1).
Proof.
  apply alpha_equiv_p_map with(f:=mk_fun' l1 l2) in Heq.
  - rewrite Heq at 1. 
    rewrite map_pat_free_vars; auto.
    intros. apply mk_fun_inj' in H1; auto.
  - intros. apply mk_fun_in_firstb'; auto.
Qed.

Lemma mk_fun_vars_eq (l1 l2: list vsymbol)
  (p1 p2: pattern)
  (Hn1: NoDup l1)
  (Hn2: NoDup l2)
  (Hl1: forall x, In x (pat_fv p1) -> In x l1)
  (Heq: alpha_equiv_p (combine l1 l2) p1 p2):
  forall x, In x (pat_fv p1) ->
  snd (mk_fun' l1 l2 x) = snd x.
Proof.
  intros. symmetry. 
  eapply alpha_equiv_p_map_f. apply Heq.
  intros; apply mk_fun_in_firstb'; auto.
  auto.
Qed.

(*TDOO: better name than _full*)
Lemma mk_fun_vars_eq_full (p1 p2: pattern)
  (Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2):
  forall x, In x (pat_fv p1) ->
  snd (mk_fun' (pat_fv p1) (pat_fv p2) x) = snd x.
Proof.
  intros. apply (mk_fun_vars_eq _ _ p1 p2); auto;
  apply NoDup_pat_fv.
Qed. 

Lemma combine_eq {A B: Type} (l: list (A * B)):
  combine (map fst l) (map snd l) = l.
Proof.
  induction l; simpl; auto. destruct a; simpl; rewrite IHl; auto.
Qed.

(*Version with vars*)
Corollary alpha_equiv_p_fv' (vars: list (vsymbol * vsymbol))
  (p1 p2: pattern)
  (Hn1: NoDup (map fst vars))
  (Hn2: NoDup (map snd vars))
  (Hl1: forall x, In x (pat_fv p1) -> In x (map fst vars))
  (Heq: alpha_equiv_p vars p1 p2):
  pat_fv p2 = map (mk_fun' (map fst vars) (map snd vars)) (pat_fv p1).
Proof.
  apply alpha_equiv_p_fv; auto.
  rewrite combine_eq; auto.
Qed.

Corollary alpha_equiv_p_fv_len  (l1 l2: list vsymbol) 
(p1 p2: pattern)
(Hn1: NoDup l1)
(Hn2: NoDup l2)
(Hl1: forall x, In x (pat_fv p1) -> In x l1)
(Heq: alpha_equiv_p (combine l1 l2) p1 p2):
length (pat_fv p1) = length (pat_fv p2).
Proof.
  rewrite (alpha_equiv_p_fv l1 l2 p1 p2); wf_tac.
Qed.

Corollary alpha_equiv_p_fv_len' (vars: list (vsymbol * vsymbol))
(p1 p2: pattern)
(Hn1: NoDup (map fst vars))
(Hn2: NoDup (map snd vars))
(Hl1: forall x, In x (pat_fv p1) -> In x (map fst vars))
(Heq: alpha_equiv_p vars p1 p2):
length (pat_fv p1) = length (pat_fv p2).
Proof.
  rewrite (alpha_equiv_p_fv' vars p1 p2); wf_tac.
Qed.

(*For the condition we use in [alpha_equiv_t]*)
Corollary alpha_equiv_p_fv_full (p1 p2: pattern):
  alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2 ->
  pat_fv p2 = map (mk_fun' (pat_fv p1) (pat_fv p2)) (pat_fv p1).
Proof.
  intros.
  apply alpha_equiv_p_fv; auto; apply NoDup_pat_fv.
Qed.

Corollary alpha_equiv_p_fv_len_full (p1 p2: pattern):
  alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2 ->
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  intros.
  rewrite (alpha_equiv_p_fv_full p1 p2); auto. 
  rewrite map_length; auto.
Qed.

(*And we have a version specialized for our particular application *)
(*TODO: see if we need*)

Definition binop_eqb (b1 b2: binop) : bool :=
  match b1, b2 with
  | Tand, Tand => true
  | Tor, Tor => true
  | Timplies, Timplies => true
  | Tiff, Tiff => true
  | _, _ => false
  end.

Lemma binop_eqb_spec (b1 b2: binop):
  reflect (b1 = b2) (binop_eqb b1 b2).
Proof.
  destruct (binop_eqb b1 b2) eqn : Hbinop.
  - apply ReflectT.
    destruct b1; destruct b2; simpl in Hbinop; auto; inversion Hbinop.
  - apply ReflectF. intro C; subst.
    destruct b2; inversion Hbinop.
Qed.

Definition binop_eq_dec (b1 b2: binop) :
  {b1 = b2} + {b1 <> b2} := reflect_dec' (binop_eqb_spec b1 b2).

Fixpoint iter_sub {A: Type} (sub: vsymbol -> vsymbol -> A -> A) 
  (old: list vsymbol) (new: list vsymbol) (t: A) : A :=
  match old, new with
  | o :: t1, n :: t2 => sub o n (iter_sub sub t1 t2 t)
  | _, _ => t
  end.

Definition iter_sub_t := iter_sub sub_t.
Definition iter_sub_f := iter_sub sub_f.

Definition add_vals {A B: Type} (keys: list A) (vals: list B) (assoc: list (A * B)) :
  list (A * B) :=
  combine keys vals ++ assoc.

(*Remove all ocurrences of key from assoc list*)

Definition remove_key  {A B: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(key: A) (assoc: list (A * B)) : list (A * B) :=
filter (fun x => negb(eq_dec key (fst x))) assoc.

Lemma remove_key_in_iff {A B: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(key: A) (assoc: list (A * B)) (x: A) (y: B):
  In (x, y) (remove_key eq_dec key assoc) <->
  In (x, y) assoc /\ x <> key.
Proof.
  unfold remove_key. rewrite filter_In. apply and_iff_compat_l.
  simpl. destruct (eq_dec key x); subst; simpl; auto; split; intros;
  auto.
Qed.

Definition remove_val {A B: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y})
  (val: B) (assoc: list (A * B)) : list (A * B) :=
  filter (fun x => negb(eq_dec val (snd x))) assoc.

Lemma remove_val_in_iff {A B: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y})
(val: B) (assoc: list (A * B)) (x: A) (y: B):
  In (x, y) (remove_val eq_dec val assoc) <->
  In (x, y) assoc /\ y <> val.
Proof.
  unfold remove_val. rewrite filter_In. apply and_iff_compat_l.
  simpl. destruct (eq_dec val y); subst; simpl; auto; split; intros;
  auto.
Qed.

Definition remove_pair {A B: Type} (eq_dec1: forall (x y: A), {x = y} + {x <> y})
  (eq_dec2: forall (x y: B), {x = y} + {x <> y})
  (key: A) (val: B) (assoc: list (A * B)) : list (A * B) :=
  remove_val eq_dec2 val (remove_key eq_dec1 key assoc).

Lemma remove_pair_in_iff {A B: Type} (eq_dec1: forall (x y: A), {x = y} + {x <> y})
  (eq_dec2: forall (x y: B), {x = y} + {x <> y})
  (key: A) (val: B) (assoc: list (A * B)) (x: A) (y: B) :
  In (x, y) (remove_pair eq_dec1 eq_dec2 key val assoc) <->
  In (x, y) assoc /\ x <> key /\ y <> val.
Proof.
  unfold remove_pair. 
  rewrite remove_val_in_iff, remove_key_in_iff, and_assoc. 
  reflexivity.
Qed.

Definition remove_pairs {A B: Type} 
(eq_dec1: forall (x y: A), {x = y} + {x <> y}) 
(eq_dec2: forall (x y: B), {x = y} + {x <> y}) 
(keys: list A) (vals: list B) (assoc: list (A * B)) : list (A * B) :=
fold_right (fun x acc => remove_val eq_dec2 x acc)
  (fold_right (fun y acc => remove_key eq_dec1 y acc) assoc keys) vals.

Lemma remove_pairs_in_iff {A B: Type} 
  (eq_dec1: forall (x y: A), {x = y} + {x <> y}) 
  (eq_dec2: forall (x y: B), {x = y} + {x <> y}) 
  (keys: list A) (vals: list B) (assoc: list (A * B)) x y:
  In (x, y) (remove_pairs eq_dec1 eq_dec2 keys vals assoc) <->
  In (x, y) assoc /\ ~ In x keys /\ ~ In y vals.
Proof.
  unfold remove_pairs. induction vals; simpl.
  - induction keys; simpl.
    + split; auto; intros; destruct_all; auto.
    + rewrite remove_key_in_iff, IHkeys. 
      split; intros; destruct_all; split_all; auto.
      intros [Hax | Hin]; subst; auto.
  - rewrite remove_val_in_iff, IHvals. 
    split; intros; destruct_all; split_all; auto.
    intros [Hay | Hin]; subst; auto.
Qed.

Definition flip {A B: Type} (l: list (A * B)) : list (B * A) :=
  map (fun x => (snd x, fst x)) l.

Lemma map_fst_flip {A B: Type} (l: list (A * B)) :
  map fst (flip l) = map snd l.
Proof.
  induction l; simpl; auto; rewrite IHl; auto.
Qed.

Lemma map_snd_flip {A B: Type} (l: list (A * B)) :
map snd (flip l) = map fst l.
Proof.
induction l; simpl; auto; rewrite IHl; auto.
Qed.

(*TODO; move*)
Definition quant_eqb (q1 q2: quant) : bool :=
  match q1, q2 with
  | Tforall, Tforall => true
  | Texists, Texists => true
  | _, _ => false
  end.

Lemma quant_eqb_spec q1 q2:
  reflect (q1 = q2) (quant_eqb q1 q2).
Proof.
  destruct q1; destruct q2; simpl; try solve[apply ReflectT; auto];
  apply ReflectF; intro C; inversion C.
Qed.

Definition quant_eq_dec q1 q2 := reflect_dec' (quant_eqb_spec q1 q2).
  
Notation remove_bnd := (remove_pair vsymbol_eq_dec vsymbol_eq_dec).
Notation remove_bnds := (remove_pairs vsymbol_eq_dec vsymbol_eq_dec).


Lemma alpha_t_var_equiv: forall (v1 v2: vsymbol) (vars: list (vsymbol * vsymbol)),
  match (get_assoc_list vsymbol_eq_dec vars v1),
      (get_assoc_list vsymbol_eq_dec (flip vars) v2) with
    | Some v3, Some v4 =>
      vsymbol_eq_dec v2 v3 &&
      vsymbol_eq_dec v1 v4
    | None, None => vsymbol_eq_dec v1 v2
    | _, _ => false
    end = eq_var vars v1 v2.
Proof.
  induction vars; simpl; intros; auto.
  vsym_eq v1 (fst a); simpl; simpl_bool.
  - vsym_eq v2 (snd a); simpl.
    + vsym_eq (fst a) (fst a).
    + destruct (get_assoc_list vsymbol_eq_dec (flip vars) v2); auto. 
  - vsym_eq v2 (snd a); simpl.
    destruct (get_assoc_list vsymbol_eq_dec vars v1) eqn: Ha; auto; simpl.
    vsym_eq v1 (fst a). simpl. simpl_bool; auto.
Qed.


(*TODO: need the map version, this doesnt work because of 
  bound/free vars*)
(*We require that vars has each key and each value appear at most once.
  This is because whenever we have a mapping between bound variables,
  it should override all existing mappings*)
Fixpoint alpha_equiv_t (vars: list (vsymbol * vsymbol)) (t1 t2: term) : bool :=
  match t1, t2 with
  | Tconst c1, Tconst c2 => (*TODO: see*) all_dec (c1 = c2)
  | Tvar v1, Tvar v2 =>
    eq_var vars v1 v2
  | Tfun f1 ty1 tm1, Tfun f2 ty2 tm2 =>
    (funsym_eq_dec f1 f2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (fix all2 (l1 l2: list term) : bool :=
      match l1, l2 with
      | nil, nil => true
      | x1 :: t1, x2 :: t2 => alpha_equiv_t vars x1 x2 && all2 t1 t2
      | _, _ => false
      end) tm1 tm2
  | Tlet tm1 x tm2, Tlet tm3 y tm4 =>
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_t vars tm1 tm3 &&
    alpha_equiv_t ((x, y) :: vars) tm2 tm4
  | Tif f1 t1 t3, Tif f2 t2 t4 =>
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_t vars t3 t4
  | Tmatch t1 ty1 ps1, Tmatch t2 ty2 ps2 =>
    alpha_equiv_t vars t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    (fix all2 (l1 l2: list (pattern * term)) : bool :=
    match l1, l2 with
    | nil, nil => true
    | (p1, t1) :: tl1, (p2, t2) :: tl2 =>
      (*(length (pat_fv p1) =? (length (pat_fv p2))) &&*)
      alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2 &&
      alpha_equiv_t (add_vals (pat_fv p1) (pat_fv p2) 
        vars) t1 t2 && all2 tl1 tl2
    | _, _ => false
    end) ps1 ps2
  | Teps f1 x, Teps f2 y => 
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | _, _ => false
  end
  (*TODO: fixc *)
with alpha_equiv_f (vars: list (vsymbol * vsymbol)) (f1 f2: formula) {struct f1} : bool :=
  match f1, f2 with
  | Fpred p1 ty1 tm1, Fpred p2 ty2 tm2 =>
    (predsym_eq_dec p1 p2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (fix all2 (l1 l2: list term) : bool :=
      match l1, l2 with
      | nil, nil => true
      | x1 :: t1, x2 :: t2 => alpha_equiv_t vars x1 x2 && all2 t1 t2
      | _, _ => false
      end) tm1 tm2
  | Fquant q1 x f1, Fquant q2 y f2 =>
    quant_eq_dec q1 q2 &&
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | Feq ty1 t1 t3, Feq ty2 t2 t4 =>
    vty_eq_dec ty1 ty2 &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_t vars t3 t4
  | Fbinop b1 f1 f3, Fbinop b2 f2 f4 =>
    binop_eq_dec b1 b2 &&
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_f vars f3 f4
  | Fnot f1, Fnot f2 =>
    alpha_equiv_f vars f1 f2
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet t1 x f1, Flet t2 y f2 =>
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | Fif f1 f3 f5, Fif f2 f4 f6 =>
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_f vars f3 f4 &&
    alpha_equiv_f vars f5 f6
  | Fmatch t1 ty1 ps1, Fmatch t2 ty2 ps2 =>
    alpha_equiv_t vars t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    (fix all2 (l1 l2: list (pattern * formula)) : bool :=
    match l1, l2 with
    | nil, nil => true
    | (p1, f1) :: tl1, (p2, f2) :: tl2 =>
      (*(length (pat_fv p1) =? (length (pat_fv p2))) &&*)
      alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2 &&
      alpha_equiv_f (add_vals (pat_fv p1) (pat_fv p2) vars) f1 f2
      && all2 tl1 tl2
    | _, _ => false
    end) ps1 ps2
  | _, _ => false
  end.
(*
Fixpoint alpha_equiv_t (t1 t2: term) {struct t1} : bool :=
  match t1, t2 with
  | Tconst c1, Tconst c2 => (*TODO: see*) all_dec (c1 = c2)
  | Tvar v1, Tvar v2 => vsymbol_eq_dec v1 v2
  | Tfun f1 ty1 tm1, Tfun f2 ty2 tm2 =>
    (funsym_eq_dec f1 f2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (fix all2 (l1 l2: list term) : bool :=
      match l1, l2 with
      | nil, nil => true
      | x1 :: t1, x2 :: t2 => alpha_equiv_t x1 x2 && all2 t1 t2
      | _, _ => false
      end) tm1 tm2
  | Tlet tm1 x tm2, Tlet tm3 y tm4 =>
    alpha_equiv_t tm1 tm3 &&
    alpha_equiv_t tm2 (sub_t y x tm4)
  | Tif f1 t1 t3, Tif f2 t2 t4 =>
    alpha_equiv_f f1 f2 &&
    alpha_equiv_t t1 t2 &&
    alpha_equiv_t t3 t4
  | Tmatch t1 ty1 ps1, Tmatch t2 ty2 ps2 =>
    alpha_equiv_t t1 t2 &&
    (length ps1 =? length ps2) &&
    (fix all2 (l1 l2: list (pattern * term)) : bool :=
    match l1, l2 with
    | nil, nil => true
    | (p1, t1) :: tl1, (p2, t2) :: tl2 =>
      alpha_equiv_p p1 p2 &&
      alpha_equiv_t t1 (iter_sub_t (pat_fv p2) (pat_fv p2) t2)
    | _, _ => false
    end) ps1 ps2
  | _, _ => false
  end
with alpha_equiv_f (f1 f2: formula) {struct f1} : bool :=
  match f1, f2 with
  | Fpred p1 ty1 tm1, Fpred p2 ty2 tm2 =>
    (predsym_eq_dec p1 p2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (fix all2 (l1 l2: list term) : bool :=
      match l1, l2 with
      | nil, nil => true
      | x1 :: t1, x2 :: t2 => alpha_equiv_t x1 x2 && all2 t1 t2
      | _, _ => false
      end) tm1 tm2
  | Fquant q1 x f1, Fquant q2 y f2 =>
    alpha_equiv_f f1 (sub_f y x f2)
  | Feq ty1 t1 t3, Feq ty2 t2 t4 =>
    alpha_equiv_t t1 t2 &&
    alpha_equiv_t t3 t4
  | Fbinop b1 f1 f3, Fbinop b2 f2 f4 =>
    binop_eq_dec b1 b2 &&
    alpha_equiv_f f1 f2 &&
    alpha_equiv_f f3 f4
  | Fnot f1, Fnot f2 =>
    alpha_equiv_f f1 f2
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet t1 x f1, Flet t2 y f2 =>
    alpha_equiv_t t1 t2 &&
    alpha_equiv_f f1 (sub_f y x f2)
  | Fif f1 f3 f5, Fif f2 f4 f6 =>
    alpha_equiv_f f1 f2 &&
    alpha_equiv_f f3 f4 &&
    alpha_equiv_f f5 f6
  | Fmatch t1 ty1 ps1, Fmatch t2 ty2 ps2 =>
    alpha_equiv_t t1 t2 &&
    (length ps1 =? length ps2) &&
    (fix all2 (l1 l2: list (pattern * formula)) : bool :=
    match l1, l2 with
    | nil, nil => true
    | (p1, f1) :: tl1, (p2, f2) :: tl2 =>
      alpha_equiv_p p1 p2 &&
      alpha_equiv_f f1 (iter_sub_f (pat_fv p2) (pat_fv p2) f2)
    | _, _ => false
    end) ps1 ps2
  | _, _ => false
  end.
*)
  Require Import Coq.Logic.Eqdep_dec.

(*Why we use [dom_cast] and not a generic cast:*)
Lemma dom_cast_eq aux v1 v2 (H1 H2: v1 = v2) (d: domain aux v1):
  dom_cast aux H1 d =
  dom_cast aux H2 d.
Proof.
  f_equal. apply UIP_dec. apply sort_eq_dec.
Qed.


Ltac simpl_proj :=
  simpl projT1; simpl projT2; simpl proj1_sig; simpl proj2_sig.

Ltac case_match_hyp :=
  repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
Ltac case_match_goal :=
  repeat match goal with 
        |- (match ?p with |Some l => ?x | None => ?y end) = ?z =>
          let Hp := fresh "Hmatch" in 
          destruct p eqn: Hp end; auto.

(*If two patterns are alpha-equivalent, then if the first pattern
  doesn't match, neither does the second.
  The constructor case has giant proof terms and takes a while,
  though it is conceptually simple*)
Lemma match_val_single_alpha_p_none {ty: vty}
(Hval Hval2: valid_type sigma ty)
(d: domain (dom_aux pd) (v_subst (v_typevar vt) ty))
(p1 p2: pattern)
(vars: list (vsymbol * vsymbol))
(Heq: alpha_equiv_p vars p1 p2) :
match_val_single gamma_valid pd all_unif vt ty Hval d p1 = None ->
match_val_single gamma_valid pd all_unif vt ty Hval2 d p2 = None.
Proof.
  revert ty d Hval Hval2.
  generalize dependent p2. induction p1.
  - simpl; intros; destruct p2; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros [Htys Heq].
    simpl_sumbool.
    destruct (vty_eq_dec (snd v) ty); subst; auto.
    + inversion H.
    + cbn. destruct (vty_eq_dec (snd v0) ty); subst; auto.
      rewrite e in n; contradiction.
  - intros; destruct p2; try solve[inversion Heq].
    revert H0.
    simpl in Heq.
    revert Heq; bool_to_prop.
    intros [[[Hfeq Hps] Htys] Hall2]. repeat simpl_sumbool.
    apply Nat.eqb_eq in Hps.
    rename l0 into ps2.
    rename l into tys.
    rename f0 into f.
    (*Get Hall2 into more usable form*)
    assert (Hall: forall i, i < length ps ->
      alpha_equiv_p vars (nth i ps Pwild) (nth i ps2 Pwild)). {
      generalize dependent ps2. clear. induction ps; simpl; intros;
      destruct ps2; inversion Hps. lia.
      apply andb_true_iff in Hall2. destruct Hall2.
      destruct i; simpl; auto. apply IHps; auto. lia.
    }
    clear Hall2.
    (*Now deal with main result*)
    unfold match_val_single; fold (match_val_single gamma_valid).
    (*The hard case: need lots of generalization for dependent types
    and need nested induction*) 
    generalize dependent (is_sort_adt_spec gamma_valid (v_subst (v_typevar vt) ty)).
    generalize dependent ((@adt_srts_length_eq _ _ gamma_valid vt ty)).
    generalize dependent (@adts_srts_valid _ _ gamma_valid vt ty).
    destruct (is_sort_adt (v_subst (v_typevar vt) ty)) eqn : Hisadt; [|solve[auto]].
    intros Hsrtsvalid Hsrtslen Hadtspec.
    destruct p as [[[m adt] ts] srts].
    destruct (Hadtspec m adt ts srts eq_refl) as 
      [Hvaleq [Hinmut [Hincts Htseq]]].
    assert (Hlenpeq : (Hsrtslen m adt ts srts eq_refl Hval) =
    (Hsrtslen m adt ts srts eq_refl Hval2)). {
      apply UIP_dec. apply Nat.eq_dec.
    }
    rewrite <- !Hlenpeq.
    destruct (funsym_eq_dec
    (projT1
      (find_constr_rep gamma_valid m Hincts srts
          (Hsrtslen m adt ts srts eq_refl Hval) (dom_aux pd) adt
          Hinmut (adts pd m srts) (all_unif m Hincts)
          (scast (adts pd m srts adt Hinmut)
            (dom_cast (dom_aux pd) Hvaleq d)))) f);[|solve[auto]].
    clear Hlenpeq.
    (*Need nested induction: simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hincts srts
    (Hsrtslen m adt ts srts eq_refl Hval) 
    (dom_aux pd) adt Hinmut (adts pd m srts)
    (all_unif m Hincts)
    (scast (adts pd m srts adt Hinmut)
      (dom_cast (dom_aux pd) Hvaleq d))).
    intros constr. destruct constr as [f' Hf']. 
    simpl_proj. intros Hf; subst.
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval2 (fst (proj1_sig Hf')))).
    destruct Hf'. simpl_proj. clear e.
    destruct x. generalize dependent a.
    generalize dependent ps2.
    generalize dependent ps. 
    generalize dependent ((funsym_sigma_args f srts)).
    induction l; intros. 
    + destruct ps. inversion H0. destruct ps2; inversion Hps. 
      reflexivity.
    + destruct ps; destruct ps2; inversion Hps; auto.
      revert H0.
      case_match_hyp.
      intro C; inversion C.
      * (*First succeeds, rest fail*)
        intros _.
        case_match_goal.
        (*Contradicts IH*)
        eapply IHl in Hmatch0.
        rewrite Hmatch0 in Hmatch2. inversion Hmatch2.
        -- clear Hmatch Hmatch0 Hmatch1 Hmatch2 IHl.
          inversion H; subst; auto.
        -- assumption.
        -- intros j Hj; apply (Hall (S j)). simpl; lia.
      * (*first fails *) 
        intros _.
        case_match_goal.
        (*Contradicts fact that both need to be equivalent - from
          original IH (behind the giant proof terms)*)
        inversion H; subst.
        eapply H3 in Hmatch.
        rewrite Hmatch in Hmatch0. inversion Hmatch0.
        apply (Hall 0). simpl; lia.
  - intros. destruct p2; try solve[inversion Heq].
    inversion H.
  - simpl; intros. destruct p2; try solve[inversion Heq].
    revert Heq. bool_to_prop; intros [Hp1 Hp2].
    simpl.
    revert H. case_match_hyp; [intro C; inversion C|].
    intros. eapply IHp1_1 in Hmatch. rewrite Hmatch. 2: assumption.
    eapply IHp1_2. auto. apply H.
  - simpl; intros. destruct p2; try solve[inversion Heq]. simpl.
    revert Heq; bool_to_prop; intros [[Htys Heq] Hp12]; simpl_sumbool.
    (*destruct (get_assoc_list vsymbol_eq_dec vars v) eqn : Ha; try solve[inversion Heq].
    simpl_sumbool.*)
    revert H. case_match_hyp.
    + destruct (vty_eq_dec (snd v) ty); [intro C; inversion C |].
      intros _.
      case_match_goal. destruct (vty_eq_dec (snd v0) ty); auto.
      subst. rewrite e in n. contradiction.
    + intros _. erewrite IHp1; auto. apply Hmatch.
Qed.

Lemma in_flip_iff {A B: Type} (x: A) (y: B) (l: list (A * B)) :
  In (y, x) (flip l) <-> In (x, y) l.
Proof.
  unfold flip. rewrite in_map_iff. split; intros;
  destruct_all. inversion H; subst; auto. destruct x0; auto.
  exists (x, y). split; auto.
Qed.

Lemma eq_dec_sym {A: Type} {eq_dec: forall (x y: A), {x = y}+ {x <> y}}
  (x y: A):
  (@eq bool (eq_dec x y) (eq_dec y x)).
Proof.
  destruct (eq_dec x y); simpl; destruct (eq_dec y x); subst; auto.
  contradiction.
Qed.

Lemma eq_var_flip vars x y:
  eq_var vars x y = eq_var (flip vars) y x.
Proof.
  induction vars; simpl.
  - apply eq_dec_sym.
  - rewrite eq_dec_sym. f_equal. solve_bool.
    f_equal. solve_bool. apply IHvars.
Qed.

Lemma var_in_firstb_flip vars x y:
  var_in_firstb (x, y) vars =
  var_in_firstb (y, x) (flip vars).
Proof.
  induction vars; simpl; auto.
  rewrite eq_dec_sym, IHvars, andb_comm, 
  (andb_comm (negb _)). reflexivity.
Qed. 

Lemma alpha_equiv_p_sym (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol)):
  alpha_equiv_p vars p1 p2 = alpha_equiv_p (flip vars) p2 p1.
Proof.
  revert p2. induction p1; simpl; intros; destruct p2; auto; simpl.
  - rewrite eq_dec_sym, var_in_firstb_flip. reflexivity.
  - rewrite eq_dec_sym, Nat.eqb_sym.
    destruct (length l0 =? length ps) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    f_equal; [f_equal; apply eq_dec_sym |].
    generalize dependent l0. induction ps; simpl; intros;
    destruct l0; inversion Hlen; auto; clear Hlen.
    inversion H; subst.
    rewrite H3. f_equal. auto.
  - rewrite IHp1_1, IHp1_2. reflexivity.
  - rewrite eq_dec_sym, IHp1. do 2 f_equal.
    apply var_in_firstb_flip.
Qed.

(*Can we prove this? (to show Some <-> Some)*)
(*
Lemma alpha_equiv_p_sym (p1 p2: pattern) 
  (vars: list (vsymbol * vsymbol))
  (Heq: alpha_equiv_p vars p1 p2)
  (Hnodup1: NoDup (map fst vars))
  (Hnodup2: NoDup (map snd vars)):
  alpha_equiv_p (flip vars) p2 p1.
Proof.
  generalize dependent p2. 
  induction p1; simpl; intros; destruct p2; try solve[inversion Heq];
  simpl;
  revert Heq; bool_to_prop; intros; simpl.
  - destruct Heq as [Htys Hassoc].
    simpl_sumbool. split. simpl_sumbool.
    destruct (get_assoc_list vsymbol_eq_dec vars v) eqn : Ha;
    try solve[inversion Hassoc].
    simpl_sumbool.
    apply get_assoc_list_some in Ha. 
    destruct (get_assoc_list vsymbol_eq_dec (flip vars) v0) eqn : Hb; auto.
    + simpl_sumbool.
      apply get_assoc_list_some in Hb.
      rewrite in_flip_iff in Hb.
      assert (v = v1). apply (nodup_snd_inj Hnodup2 Ha Hb).
      subst; contradiction.
    + apply get_assoc_list_none in Hb.
      rewrite map_fst_flip in Hb.
      exfalso. apply Hb. rewrite in_map_iff. exists (v, v0). auto.
  - destruct_all. repeat simpl_sumbool.
    split_all; try simpl_sumbool. rewrite Nat.eqb_sym; auto.
    apply Nat.eqb_eq in H3.
    rename l0 into ps2.
    rename H3 into Hps.
    generalize dependent ps2. induction ps; simpl; intros;
    destruct ps2; inversion Hps; auto.
    inversion H; subst.
    revert H1; bool_to_prop; intros [Hap Hall]. split.
    + apply H4. apply Hap.
    + apply IHps; auto.
  - auto.
  - destruct Heq. rewrite IHp1_1, IHp1_2; auto.
  - destruct Heq as [[Htys Hassoc] Hp12]. simpl_sumbool.
    split_all; [simpl_sumbool; auto | | apply IHp1; auto].
    destruct (get_assoc_list vsymbol_eq_dec vars) eqn : Ha; try solve[inversion Hassoc].
    simpl_sumbool.
    apply get_assoc_list_some in Ha.
    destruct (get_assoc_list vsymbol_eq_dec (flip vars) v0) eqn : Hb.
    + apply get_assoc_list_some in Hb.
      rewrite in_flip_iff in Hb.
      assert (v = v1).  apply (nodup_snd_inj Hnodup2 Ha Hb).
      simpl_sumbool.
    + apply get_assoc_list_none in Hb.
      rewrite map_fst_flip in Hb.
      exfalso. apply Hb. rewrite in_map_iff; exists (v, v0); auto.
Qed.*)

Lemma flip_flip {A B: Type} (l: list (A * B)):
  flip (flip l) = l.
Proof.
  induction l; simpl; auto. rewrite IHl. f_equal.
  destruct a; auto.
Qed.

(*An alternate form - TODO: try to prove directly, might be
  easier*)
  (*
Lemma alpha_equiv_p_sym_eq (p1 p2: pattern) 
  (vars: list (vsymbol * vsymbol))
  (Hnodup1: NoDup (map fst vars))
  (Hnodup2: NoDup (map snd vars)):
  alpha_equiv_p vars p1 p2 = alpha_equiv_p (flip vars) p2 p1.
Proof.
  destruct (alpha_equiv_p vars p1 p2) eqn : Heq.
  - symmetry. apply alpha_equiv_p_sym; auto.
  - destruct (alpha_equiv_p (flip vars) p2 p1) eqn : Heq'; auto.
    apply alpha_equiv_p_sym in Heq'; auto.
    rewrite flip_flip in Heq'. rewrite Heq' in Heq. inversion Heq.
    rewrite map_fst_flip; auto.
    rewrite map_snd_flip; auto.
Qed.*)

(*From the symmetry, we get that [match_val_single] are either
  always both None or both Some*)
Lemma match_val_single_alpha_p_none_iff {ty: vty}
  (Hval Hval2: valid_type sigma ty)
  (d: domain (dom_aux pd) (v_subst (v_typevar vt) ty))
  (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol))
  (Heq: alpha_equiv_p vars p1 p2):
  match_val_single gamma_valid pd all_unif vt ty Hval d p1 = None <->
  match_val_single gamma_valid pd all_unif vt ty Hval2 d p2 = None.
Proof.
  split; intros.
  - apply (match_val_single_alpha_p_none Hval _ _ _ _ _ Heq); auto.
  - apply (match_val_single_alpha_p_none Hval2 _ _ p2 _ (flip vars)); auto.
    rewrite <- alpha_equiv_p_sym; auto.
Qed.

Lemma or_iff (P1 P2 P3 P4: Prop) :
  (P1 <-> P3) ->
  (P2 <-> P4) ->
  (P1 \/ P2) <-> (P3 \/ P4).
Proof.
  intros. split; intros; destruct_all; intuition.
Qed.

Lemma in_app_iff_simpl {A: Type} (l1 l2 l3 l4 : list A) x y :
  (In x l1 <-> In y l3) ->
  (In x l2 <-> In y l4) ->
  (In x (l1 ++ l2) <-> In y (l3 ++ l4)).
Proof.
  intros. 
  rewrite !in_app_iff. apply or_iff; auto.
Qed. 

Lemma in_firstb_in_eq l x y z:
  NoDup (map fst l) ->
  var_in_firstb (x, y) l ->
  In (x, z) l ->
  y = z.
Proof.
  induction l; simpl; intros. inversion H1.
  vsym_eq x (fst a); simpl in H0.
  - vsym_eq y (snd a); inversion H0; subst. clear H0.
    destruct H1; [rewrite H0 |]; auto.
    inversion H; subst. exfalso.
    apply H3. rewrite in_map_iff. exists (fst a, z); auto.
  - vsym_eq y (snd a); simpl in H0; try solve[inversion H0].
    inversion H; subst.
    destruct H1; subst; auto.
    contradiction.
Qed.

Lemma in_firstb_in_eq_r l x y z:
  NoDup (map snd l) ->
  var_in_firstb (y, x) l ->
  In (z, x) l ->
  y = z.
Proof.
  intros.
  assert (NoDup (map fst (flip l))). rewrite map_fst_flip; auto.
  assert (var_in_firstb (x, y) (flip l)) by
    (rewrite var_in_firstb_flip, flip_flip; auto).
  assert (In (x, z) (flip l)). rewrite in_flip_iff; auto.
  apply (in_firstb_in_eq _ _ _ _ H2 H3 H4).
Qed.

(*Now we will (try to) do the Some case*)
(*TODO: first we will admit this and see if it works, then we 
  will prove it*)
  Lemma match_val_single_alpha_p_some {ty: vty}
  (Hval Hval2: valid_type sigma ty)
  (d: domain (dom_aux pd) (v_subst (v_typevar vt) ty))
  (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol))
  (Heq: alpha_equiv_p vars p1 p2)
  (Hnodup1: NoDup (map fst vars))
  (Hnodup2: NoDup (map snd vars))
  l1 l2 x y t (def: vsymbol):
  match_val_single gamma_valid pd all_unif vt ty Hval d p1 = Some l1 ->
  match_val_single gamma_valid pd all_unif vt ty Hval2 d p2 = Some l2 ->
  (*In x (pat_fv p1) ->
  In y (pat_fv p2) ->*)
  In (x, y) vars ->
  In (x, t) l1 <-> In (y, t) l2.
Proof.
  (*I really don't know if this is true, so i need to prove*)
  revert ty d Hval Hval2 l1 l2.
  generalize dependent p2. induction p1.
  - simpl; intros; destruct p2; try solve[inversion Heq].
    simpl in *.
    revert Heq; bool_to_prop; intros [Htys Heq].
    repeat simpl_sumbool.
    destruct (vty_eq_dec (snd v) ty); subst; inversion H.
    destruct (vty_eq_dec (snd v0) (snd v)); subst; inversion H0.
    subst. clear H. clear H0. simpl.
    apply or_iff_compat_r. split; intros Heq'; inversion Heq'; subst;
    f_equal.
    + apply (in_firstb_in_eq _ _ _ _ Hnodup1 Heq); auto.
    + apply (in_firstb_in_eq_r _ _ _ _ Hnodup2 Heq); auto.
  - (*Constr case, let's see how awful this is*)
    intros; destruct p2; try solve[inversion Heq].
    revert H0 H1.
    simpl in Heq.
    revert Heq; bool_to_prop.
    intros [[[Hfeq Hps] Htys] Hall2]. repeat simpl_sumbool.
    apply Nat.eqb_eq in Hps.
    rename l0 into ps2.
    rename l into tys.
    rename f0 into f.
    (*Get Hall2 into more usable form*)
    assert (Hall: forall i, i < length ps ->
      alpha_equiv_p vars (nth i ps Pwild) (nth i ps2 Pwild)). {
      generalize dependent ps2. clear. induction ps; simpl; intros;
      destruct ps2; inversion Hps. lia.
      apply andb_true_iff in Hall2. destruct Hall2.
      destruct i; simpl; auto. apply IHps; auto. lia.
    }
    clear Hall2.
    (*Now deal with main result*)
    unfold match_val_single; fold (match_val_single gamma_valid).
    (*The hard case: need lots of generalization for dependent types
    and need nested induction*) 
    generalize dependent (is_sort_adt_spec gamma_valid (v_subst (v_typevar vt) ty)).
    generalize dependent ((@adt_srts_length_eq _ _ gamma_valid vt ty)).
    generalize dependent (@adts_srts_valid _ _ gamma_valid vt ty).
    destruct (is_sort_adt (v_subst (v_typevar vt) ty)) eqn : Hisadt;[|intros; solve[inversion H0]].
    intros Hsrtsvalid Hsrtslen Hadtspec.
    destruct p as [[[m adt] ts] srts].
    destruct (Hadtspec m adt ts srts eq_refl) as 
      [Hvaleq [Hinmut [Hincts Htseq]]].
    assert (Hlenpeq : (Hsrtslen m adt ts srts eq_refl Hval) =
    (Hsrtslen m adt ts srts eq_refl Hval2)). {
      apply UIP_dec. apply Nat.eq_dec.
    }
    rewrite <- !Hlenpeq.
    destruct (funsym_eq_dec
    (projT1
      (find_constr_rep gamma_valid m Hincts srts
          (Hsrtslen m adt ts srts eq_refl Hval) (dom_aux pd) adt
          Hinmut (adts pd m srts) (all_unif m Hincts)
          (scast (adts pd m srts adt Hinmut)
            (dom_cast (dom_aux pd) Hvaleq d)))) f);[|intros; solve[inversion H0]].
    clear Hlenpeq.
    (*Need nested induction: simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hincts srts
    (Hsrtslen m adt ts srts eq_refl Hval) 
    (dom_aux pd) adt Hinmut (adts pd m srts)
    (all_unif m Hincts)
    (scast (adts pd m srts adt Hinmut)
      (dom_cast (dom_aux pd) Hvaleq d))).
    intros constr. destruct constr as [f' Hf']. 
    simpl_proj. intros Hf; subst.
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval2 (fst (proj1_sig Hf')))).
    destruct Hf'. simpl_proj. clear e.
    destruct x0. generalize dependent a.
    generalize dependent ps2.
    generalize dependent ps. 
    revert l1. revert l2.
    generalize dependent ((funsym_sigma_args f srts)).
    induction l; intros. 
    + destruct ps; [|inversion H0]. destruct ps2; inversion Hps.
      inversion H0; inversion H1; subst. reflexivity. 
    + destruct ps; destruct ps2; inversion Hps; auto.
      inversion H0.
      revert H0 H1.
      case_match_hyp.
      all: intro Hls; inversion Hls. subst.
      case_match_hyp.
      all: intro Hls2; inversion Hls2. subst.
      (*We handle the first case and the IH separately*)
      apply in_app_iff_simpl.
      * (*from original IH*) clear Hmatch2 Hmatch0 Hls Hls2.
        inversion H; subst.
        eapply H3.
        2: apply Hmatch.
        2: apply Hmatch1.
        2: auto.
        apply (Hall 0). simpl; lia.
      * (*from constr IH*) clear Hmatch Hmatch1. 
        inversion H; subst.
        eapply IHl.
        4: apply Hmatch0.
        4: apply Hmatch2.
        all: auto.
        intros j Hj; apply (Hall (S j)). simpl; lia.
  - (*hard case done, now we can do the rest*)
    intros. destruct p2; try solve[inversion Heq].
    inversion H; inversion H0; subst. reflexivity.
  - simpl; intros. destruct p2; try solve[inversion Heq]. 
    revert Heq.  bool_to_prop; intros [Hp1 Hp2].
    simpl.
    revert H H0; simpl. case_match_hyp.
    + intro Hl; inversion Hl; subst.
      case_match_hyp.
      * intros Hl'; inversion Hl'; subst.
        eapply IHp1_1. apply Hp1. apply Hmatch. apply Hmatch0. auto.
      * assert (match_val_single gamma_valid pd all_unif vt ty Hval d p1_1 = None).
        rewrite match_val_single_alpha_p_none_iff. apply Hmatch0. apply Hp1. all: auto.
        rewrite H in Hmatch; inversion Hmatch.
    + intros Hmatch1. case_match_hyp.
      * (*another contradiction, both should be None*)
        rewrite match_val_single_alpha_p_none_iff in Hmatch.
        2: apply Hp1. rewrite Hmatch in Hmatch0. inversion Hmatch0.
        all: auto.
      * intros.
        eapply IHp1_2. apply Hp2. apply Hmatch1. apply H0. auto.
  - simpl; intros. destruct p2; try solve[inversion Heq].
    simpl in H0.
    revert Heq; bool_to_prop; intros [[Htys Heq] Hp12]; simpl_sumbool.
    revert H H0. case_match_hyp; [|intro C; inversion C].
    destruct (vty_eq_dec (snd v) ty); [| intro C; inversion C].
    intros Hl1; inversion Hl1; subst.
    case_match_hyp; [|intro C; inversion C].
    destruct (vty_eq_dec (snd v0) (snd v)); subst. 2: { rewrite e in n; contradiction. }
    simpl. intros Hl2; inversion Hl2; subst. simpl.
    apply or_iff.
    + split; intros Heq'; inversion Heq'; subst; f_equal.
      apply (in_firstb_in_eq _ _ _ _ Hnodup1 Heq); auto.
      apply (in_firstb_in_eq_r _ _ _ _ Hnodup2 Heq); auto.
    + eapply IHp1. apply Hp12. apply Hmatch. apply Hmatch0. auto.
Qed.

Lemma big_union_disjoint {A B: Type}
  (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (f: B -> list A) (l: list B)
  (Hnodup: forall b, In b l -> NoDup (f b)) (d: B):
  (forall i j x, i < length l -> j < length l -> i <> j ->
    ~ (In x (f (nth i l d)) /\ In x (f (nth j l d)))) ->
  big_union eq_dec f l =
  concat (map f l).
Proof.
  induction l; intros; simpl; auto.
  rewrite union_app_disjoint; auto.
  - f_equal. apply IHl; intros. apply Hnodup; simpl; triv.
    apply (H (S i) (S j) x); auto; simpl; lia.
  - intros. intros [Hinx1 Hinx2].
    rewrite <- big_union_elts in Hinx2.
    destruct Hinx2 as [y [Hiny Hinx2]].
    pose proof (In_nth _ _ d Hiny). destruct H0 as [n [Hn Hy]]; subst.
    apply (H 0 (S n) x); simpl; auto; lia.
  - apply Hnodup. simpl; triv.
Qed. 
(*Let's try to prove this, would be better than adding it as condition.
  If too hard, just add it*)
(*Two alpha-equivalent, well-typed patterns have the same
  number of free variables*)
(*TODO: prove this WITHOUT typing conditions*)
(*
Lemma alpha_equiv_p_fv (p1 p2: pattern) vars x
  (Heq: alpha_equiv_p vars p1 p2):
  In x (pat_fv p1) <-> exists y, eq_var vars x y /\ In y (pat_fv p2).
Proof.
  generalize dependent p2. induction p1; simpl; intros;
  destruct p2; try solve[inversion Heq]; simpl.
  - split; intros.
    + destruct H as [Heq' | []]; subst.
      revert Heq; bool_to_prop; intros; destruct_all.
      exists v0. split; auto.
    + destruct H as [y [Heq' [Heq'' | []]]]; subst.
(*TODO: prove this if needed*)
Admitted.

Lemma alpha_equiv_p_fv_len (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol))
  (Heq: alpha_equiv_p vars p1 p2):
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  generalize dependent p2.
  induction p1; simpl; intros;
  destruct p2; try solve[inversion Heq]; simpl; auto.
  - (*Need to know something about which free vars are in which*)
    (*TODO: this*)
  
  
  
  inversion Hty1; subst.
    clear Hty1 H3 H4 H7.
    inversion Hty2; subst.
    clear Hty2 H3 H4 H8. subst sigma0 sigma1.
    rename l0 into ps2.
    assert (Hlen1: length ps = 
      length (map (ty_subst (s_params f) vs) (s_args f))) by wf_tac.
    assert (Hlen2: length ps2 =
      length (map (ty_subst (s_params f0) l) (s_args f0))) by wf_tac.
    clear H5 H6.
    revert Heq; bool_to_prop; intros [[[Hf Hps] Hvs] Hall2]; 
    repeat simpl_sumbool.
    apply Nat.eqb_eq in Hps.
    assert (Hall: forall i, i < length ps ->
      alpha_equiv_p vars (nth i ps Pwild) (nth i ps2 Pwild)). {
      clear -Hps Hall2. generalize dependent ps2; induction ps; simpl;
      intros; destruct ps2; inversion Hps; try lia.
      revert Hall2; bool_to_prop; intros [Hap Hall2].
      destruct i; simpl; auto.
      apply IHps; auto. lia.
    }
    clear Hall2.
    rewrite !big_union_disjoint with(d:=Pwild); auto; intros; wf_tac.
    rewrite !length_concat.
    rewrite !map_map.
    f_equal. apply list_eq_ext'; wf_tac.
    intros. wf_tac.
    rewrite Forall_forall in H9.
    rewrite Forall_forall in H12.
    generalize dependent (map (ty_subst (s_params f0) l) (s_args f0));
    intros a; intros.
    specialize (H9 (nth n ps Pwild, nth n a vty_int)).
    specialize (H12 (nth n ps2 Pwild, nth n a vty_int)).
    simpl in *.
    rewrite Forall_forall in H; eapply H; wf_tac;
    [apply H9 | apply H12];
    rewrite in_combine_iff; wf_tac; exists n; split; wf_tac;
    intros; f_equal; apply nth_indep; wf_tac.
  - inversion Hty1; subst.
    inversion Hty2; subst. 
    rewrite !union_subset; wf_tac.
    + eapply IHp1_2. apply H3. apply H6. revert Heq; bool_to_prop;
      intros [Hp1 Hp2]; auto.
    + intros; apply H8; auto.
    + intros; apply H5; auto.
  - inversion Hty1; subst.
    inversion Hty2; subst.
    rewrite !union_app_disjoint; wf_tac.
    + rewrite !app_length; simpl. f_equal.
      revert Heq; bool_to_prop; intros [_ Hps].
      eapply IHp1; auto. apply H4. apply H6.
    + intros; intros [Hinx1 [Heq' | []]]; subst; contradiction.
    + intros; intros [Hinx1 [Heq' | []]]; subst; contradiction.
Qed. *)

(*TODO: do we still need this?*)
(*
Lemma alpha_equiv_p_fv_len_typed (p1 p2: pattern) (ty1 ty2: vty) 
  (vars: list (vsymbol * vsymbol))
  (Hty1: pattern_has_type sigma p1 ty1)
  (Hty2: pattern_has_type sigma p2 ty2)
  (Heq: alpha_equiv_p vars p1 p2):
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  generalize dependent p2. revert ty2. generalize dependent ty1. 
  induction p1; simpl; intros;
  destruct p2; try solve[inversion Heq]; simpl; auto.
  - inversion Hty1; subst.
    clear Hty1 H3 H4 H7.
    inversion Hty2; subst.
    clear Hty2 H3 H4 H8. subst sigma0 sigma1.
    rename l0 into ps2.
    assert (Hlen1: length ps = 
      length (map (ty_subst (s_params f) vs) (s_args f))) by wf_tac.
    assert (Hlen2: length ps2 =
      length (map (ty_subst (s_params f0) l) (s_args f0))) by wf_tac.
    clear H5 H6.
    revert Heq; bool_to_prop; intros [[[Hf Hps] Hvs] Hall2]; 
    repeat simpl_sumbool.
    apply Nat.eqb_eq in Hps.
    assert (Hall: forall i, i < length ps ->
      alpha_equiv_p vars (nth i ps Pwild) (nth i ps2 Pwild)). {
      clear -Hps Hall2. generalize dependent ps2; induction ps; simpl;
      intros; destruct ps2; inversion Hps; try lia.
      revert Hall2; bool_to_prop; intros [Hap Hall2].
      destruct i; simpl; auto.
      apply IHps; auto. lia.
    }
    clear Hall2.
    rewrite !big_union_disjoint with(d:=Pwild); auto; intros; wf_tac.
    rewrite !length_concat.
    rewrite !map_map.
    f_equal. apply list_eq_ext'; wf_tac.
    intros. wf_tac.
    rewrite Forall_forall in H9.
    rewrite Forall_forall in H12.
    generalize dependent (map (ty_subst (s_params f0) l) (s_args f0));
    intros a; intros.
    specialize (H9 (nth n ps Pwild, nth n a vty_int)).
    specialize (H12 (nth n ps2 Pwild, nth n a vty_int)).
    simpl in *.
    rewrite Forall_forall in H; eapply H; wf_tac;
    [apply H9 | apply H12];
    rewrite in_combine_iff; wf_tac; exists n; split; wf_tac;
    intros; f_equal; apply nth_indep; wf_tac.
  - inversion Hty1; subst.
    inversion Hty2; subst. 
    rewrite !union_subset; wf_tac.
    + eapply IHp1_2. apply H3. apply H6. revert Heq; bool_to_prop;
      intros [Hp1 Hp2]; auto.
    + intros; apply H8; auto.
    + intros; apply H5; auto.
  - inversion Hty1; subst.
    inversion Hty2; subst.
    rewrite !union_app_disjoint; wf_tac.
    + rewrite !app_length; simpl. f_equal.
      revert Heq; bool_to_prop; intros [_ Hps].
      eapply IHp1; auto. apply H4. apply H6.
    + intros; intros [Hinx1 [Heq' | []]]; subst; contradiction.
    + intros; intros [Hinx1 [Heq' | []]]; subst; contradiction.
Qed. *)

(*OTOD: move*)
Lemma extend_val_with_list_lookup (v: val_vars pd vt) l x t:
  NoDup (map fst l) ->
  In (x, t) l ->
  extend_val_with_list pd vt v l x =
    match vty_eq_dec (snd x) (projT1 t) with
    | left Heq =>
        dom_cast (dom_aux pd) (f_equal (v_subst (v_typevar vt)) (eq_sym Heq))
          (projT2 t)
    | right _ => v x
    end.
Proof.
  intros. unfold extend_val_with_list.
  destruct (get_assoc_list vsymbol_eq_dec l x) eqn : ha.
  - apply get_assoc_list_some in ha.
    assert (t = s). apply (nodup_fst_inj H H0 ha). subst.
    reflexivity.
  - apply get_assoc_list_none in ha.
    exfalso. apply ha. rewrite in_map_iff. exists (x, t). auto.
Qed.

Lemma eq_var_in_first vars x y:
  eq_var vars x y <->
  in_first (x, y) vars \/ ~ In x (map fst vars) /\ ~ In y (map snd vars) /\ x = y.
Proof.
  induction vars; simpl. split; intros.
  - right. split_all; auto. vsym_eq x y. inversion H.
  - destruct_all; auto. apply in_first_nil in H. destruct H.
    vsym_eq y y.
  - vsym_eq x (fst a); simpl; simpl_bool.
    + vsym_eq y (snd a); simpl; simpl_bool.
      * split; intros; auto. left. destruct a; simpl in *.
        rewrite in_first_cons. left; auto.
      * split; auto. intro C. inversion C.
        intros. destruct_all.
        destruct a; simpl in *. rewrite in_first_cons in H.
        destruct_all; subst; auto.
        not_or Heq. contradiction.
    + vsym_eq y (snd a); simpl; simpl_bool.
      * split; intros. inversion H.
        destruct a; simpl in *.
        rewrite in_first_cons in H. destruct_all; subst; auto.
      * rewrite IHvars. destruct a; simpl in *.
        rewrite in_first_cons. split; intros; destruct_all; auto;
        try contradiction.
        -- right. split_all; auto; intro C; destruct_all; subst; auto.
        -- not_or A. auto.
Qed. 

Require Import FunctionalExtensionality.

(*Now, we show that terms/formulas which are alpha equivalent
  have equivalent denotations. This is very annoying to prove.
  The pattern match case, understandably, is the hardest.*)
Lemma alpha_equiv_equiv (t: term) (f: formula) :
  (forall (t2: term) (vars: list (vsymbol * vsymbol)) 
  (v1 v2: val_vars pd vt) (ty: vty)
  (Hty: term_has_type sigma t ty)
  (Hty2: term_has_type sigma t2 ty)
  (Heq: alpha_equiv_t vars t t2)
  (Hvals: forall x y (Heq: snd x = snd y),
    (*This is the first binding for x and for y*)
    in_first (x, y) vars ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq))
    (v2 y)))
  (Hvals2: forall x,
    (~In x (map fst vars) /\ ~ In x (map snd vars)) ->
    v1 x = v2 x),
  term_rep v1 t ty Hty =
  term_rep v2 t2 ty Hty2) /\
  (forall (f2: formula) (vars: list (vsymbol * vsymbol))  
  (v1 v2: val_vars pd vt)
  (Hval: valid_formula sigma f)
  (Hval2: valid_formula sigma f2)
  (Heq: alpha_equiv_f vars f f2)
  (Hvals: forall x y (Heq: snd x = snd y),
    in_first (x, y) vars ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq))
    (v2 y)))
  (Hvals2: forall x,
    (~In x (map fst vars) /\ ~ In x (map snd vars)) ->
    v1 x = v2 x),
  formula_rep v1 f Hval =
  formula_rep v2 f2 Hval2).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - (*Tconst - TODO*) 
    destruct t2; try solve[inversion Heq].
    rewrite simpl_all_dec in Heq. subst.
    erewrite term_fv_agree. apply term_rep_irrel.
    simpl. intros; destruct H.
  - (*Tvar - harder*) 
    destruct t2; try solve [inversion Heq].
    apply eq_var_in_first in Heq.
    destruct_all; subst; auto.
    + inversion Hty; inversion Hty2; subst.
      specialize (Hvals _ _ (eq_sym H7) H).
      rewrite !tvar_rep. unfold var_to_dom.
      rewrite Hvals.
      (*Now need to deal with casts: this is annoying*)
      unfold dom_cast.
      destruct v0; simpl in *.
      subst. simpl.
      assert ((ty_var_inv (has_type_eq eq_refl Hty)) = eq_refl) by
        (apply UIP_dec; apply vty_eq_dec).
      rewrite H0. simpl.
      assert ((ty_var_inv (has_type_eq eq_refl Hty2)) = eq_refl) by
        (apply UIP_dec; apply vty_eq_dec).
      rewrite H1. reflexivity.
    + erewrite term_fv_agree. apply term_rep_irrel. simpl.
      intros. destruct H1 as [Heq | []]; subst.
      apply Hvals2. split; auto.
  - (*Tfun*) destruct t2; try solve[inversion Heq]. 
    revert Heq. bool_to_prop.
    intros [[[Hfeq Hleneq] Htyeq] Hall]. repeat simpl_sumbool.
    apply Nat.eqb_eq in Hleneq.
    rewrite !tfun_rep.
    (*Deal with casting*)
    f_equal; [apply UIP_dec; apply vty_eq_dec |].
    f_equal; [apply UIP_dec; apply sort_eq_dec |].
    f_equal.
    (*Now prove that arg_lists equivalent*)
    apply get_arg_list_ext; wf_tac.
    (*Use Hall to prove this*)
    assert (forall i,
      i < length l1 ->
      alpha_equiv_t vars (nth i l1 tm_d) (nth i l2 tm_d)). {
      revert Hall Hleneq. clear. revert l2. 
      induction l1; simpl; intros; auto. lia.
      destruct l2; inversion Hleneq.
      revert Hall. bool_to_prop. intros [Hhd Htl].
      destruct i; simpl; auto.
      apply IHl1; auto. lia.
    }
    intros. rewrite Forall_forall in H. apply H with(vars:=vars); wf_tac.
  - (*Tlet - harder case*) 
    destruct t2; try solve[inversion Heq].
    rename t2_1 into tm3. rename t2_2 into tm4.
    rename v into x. rename v0 into y.
    revert Heq; bool_to_prop; intros [[Htyeq Ha1] Ha2].
    simpl_sumbool.
    rewrite !tlet_rep.
    inversion Hty; inversion Hty2; subst.
    apply H0 with (vars:=(x, y) :: vars); auto.
    + simpl. intros.
      rewrite in_first_cons in H1.
      destruct H1 as [Hxy | Hinxy].
      * unfold substi. destruct Hxy; subst.
        destruct (vsymbol_eq_dec x x); subst; 
        [|contradiction].
        destruct (vsymbol_eq_dec y y); subst;
        [|contradiction].
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast. simpl.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H1, H2. simpl. clear e0 e1 H1 H2.
        destruct x; destruct y; simpl in *; subst.
        assert (Heq = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H1; simpl.
        apply H with(vars:=vars); auto.
      * unfold substi.
        destruct_all.
        destruct (vsymbol_eq_dec x0 x); subst; try contradiction.
        destruct (vsymbol_eq_dec y0 y); subst; try contradiction.
        apply Hvals; auto.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H1 as [Hnotx Hnoty].
      destruct (vsymbol_eq_dec x0 x); subst; [exfalso; apply Hnotx; left; auto |].
      destruct (vsymbol_eq_dec x0 y); subst; [exfalso; apply Hnoty; left;auto |].
      not_or Hnotx. clear Hnotx2 Hnotx0.
      apply Hvals2; auto.
  - (*Tif*) destruct t0; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    rewrite !tif_rep.
    rewrite (H _ _ _ v2 _ (proj2 (proj2 (ty_if_inv (has_type_eq eq_refl Hty2)))) H2); auto.
    rewrite (H0 _ _ _ v2 _ _ (proj1 (ty_if_inv (has_type_eq eq_refl Hty2))) H4); auto.
    rewrite (H1 _ _ _ v2 _ _ (proj1 (proj2 (ty_if_inv (has_type_eq eq_refl Hty2)))) H3); auto.
  - (*Tmatch - predictably, this is the hard case*)
    destruct t2; try solve[inversion Heq].
    rename t2 into tm2.
    rename v into tys.
    rename v0 into tys2.
    rename l into ps2.
    revert Heq; bool_to_prop; intros; destruct Heq as [[[Htm Hps] Htyeq] Hall].
    simpl_sumbool.
    (*Get Hall into something more usable*)
    apply Nat.eqb_eq in Hps.
    assert (Hall2: forall i, i < length ps ->
      let t1 := nth i ps (Pwild, tm_d) in
      let t2 := nth i ps2 (Pwild, tm_d) in
      alpha_equiv_p (combine (pat_fv (fst t1)) (pat_fv(fst t2)))
        (fst t1)(fst t2)  /\
      alpha_equiv_t (add_vals (pat_fv (fst t1)) (pat_fv (fst t2)) vars)
        (snd t1) (snd t2)). {
      clear Hty2.
      generalize dependent ps2.
      clear. induction ps; simpl; intros. lia.
      destruct ps2; inversion Hps.
      destruct a; destruct p; simpl in Hall.
      revert Hall; bool_to_prop; intros; destruct Hall as [[ Hp Ht] Hall].
      destruct i; simpl; auto.
      apply IHps; auto; try lia.
    }
    clear Hall.
    rewrite !tmatch_rep.
    (*Need nested induction here*)
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty))).
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty2))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty2))).
    inversion Hty2; subst. clear H4 H8 H9 Hty2.
    inversion Hty; subst. clear H4 H9 H10 Hty.
    generalize dependent tys2.
    generalize dependent ps2.
    
    induction ps; simpl; intros; destruct ps2; inversion Hps; auto.
    destruct a. simpl.
    destruct p. simpl.
    rewrite <- (H _ _ v1 v2 _ t0 t Htm) at 1; auto.
    (*Now need to know [match_val_single] is same - separate lemmas*)
    destruct (match_val_single gamma_valid pd all_unif vt tys2
    (has_type_valid gamma_valid tm tys2 t0) (term_rep v1 tm tys2 t0) p0) eqn : Hmatch1.
    + (*In Some case, need to know how lists relate*)

      (*First, get some info we need*)
      assert (Htyp: pattern_has_type sigma p tys2) by
        (apply (H6 (p, t2)); simpl; triv).
      assert (Htyp0: pattern_has_type sigma p0 tys2) by
        (apply (H7 (p0, t1)); simpl; triv).
      assert (Hpeq: alpha_equiv_p (combine (pat_fv p0) (pat_fv p)) p0 p). {
        specialize (Hall2 0); simpl in Hall2. apply Hall2. lia.
      }
      assert (Hpfvs: length (pat_fv p0) = length (pat_fv p)). {
        apply alpha_equiv_p_fv_len_full; auto.
      }
      destruct (match_val_single gamma_valid pd all_unif vt tys2
      (has_type_valid gamma_valid tm2 tys2 t) (term_rep v1 tm tys2 t0) p) eqn : Hmatch2.
      * assert (A:=Hall2). specialize (A 0); simpl in A.
        assert (0 < S (length ps)) by lia.
        specialize (A H1); clear H1; destruct A as [Hp Ht12].
        inversion H0; subst. eapply H4. apply Ht12.
        -- intros. 
          unfold add_vals in H1.
          apply in_first_app in H1.
          destruct H1 as [Hinfv | [Hinvars [Hxnotv Hynotv]]].
          ++ (*Case 1: (x, y) are in free vars of p0 and p respectively.
            Then we use [match_val_single_alpha_p_some] and
            [match_val_single_nodup] to show that their valuations
            are the same.*)
            apply in_first_in in Hinfv.
            assert (Hincom:=Hinfv).
            rewrite in_combine_iff in Hinfv; wf_tac.
            destruct Hinfv as [i [Hi Hith]].
            specialize (Hith vs_d vs_d). inversion Hith.
            (*Now, we know that x is in l by 
              [match_val_single_free_var]*)
            assert (Hinxl: In x (map fst l)). {
              apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
              auto.
              apply Hmatch1. subst. wf_tac.
            }
            rewrite in_map_iff in Hinxl. destruct Hinxl as [bnd [Hx Hinbnd]].
            destruct bnd as [x' t']. simpl in Hx. subst x'.
            (*Now, we use [match_val_single_alpha_p_some] to show
              that (y, t') is in l0*)
            assert (Hinyl: In (y, t') l0). {
              eapply match_val_single_alpha_p_some in Hmatch2.
              rewrite <- Hmatch2. apply Hinbnd. apply Hp.
              all: wf_tac. apply Hmatch1. 
            }
            (*Finally, we use NoDup of l, l0 
              (from [match_val_single_nodup]) to give the binding*)
            assert (Hnodup1: NoDup (map fst l)). {
              eapply match_val_single_nodup in Hmatch1.
              apply Hmatch1. apply Htyp0.
            }
            assert (Hnodup2: NoDup (map fst l0)). {
              eapply match_val_single_nodup in Hmatch2.
              apply Hmatch2. apply Htyp.
            }
            rewrite !extend_val_with_list_lookup with(t:=t'); auto.
            (*Now handle all the casting*)
            destruct (vty_eq_dec (snd x) (projT1 t')).
            ** destruct (vty_eq_dec (snd y) (projT1 t')).
              {
                destruct x. destruct y. simpl in *; subst. simpl.
                assert (e0 = eq_refl). apply UIP_dec. apply vty_eq_dec.
                rewrite H1. reflexivity. 
              }
              { 
                exfalso.
                rewrite Heq in e. contradiction.
              }
            ** (*contradiction case - types match in output
              by [match_val_single_typs]*)
              apply match_val_single_typs with(x:=x)(t:=t') in Hmatch1;
              auto. exfalso. rewrite Hmatch1 in n. contradiction.
              (*And we are done!*)
          ++ (*Now in the other case, neither are free vars, so
            we use Hvals2*)
            rewrite map_fst_combine in Hxnotv; wf_tac.
            rewrite map_snd_combine in Hynotv; wf_tac.
            assert (Hxl: ~ In x (map fst l)). {
              intro C. 
              apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
              auto.
              apply Hmatch1 in C. contradiction.
            }
            assert (Hyl0: ~ In y (map fst l0)). {
              intro C.
              apply match_val_single_free_var with(x:=y)(ty':=tys2) in Hmatch2;
              auto.
              apply Hmatch2 in C; contradiction.
            }
            rewrite !extend_val_with_list_notin'; wf_tac.
        -- (*Here, we must show preservation of [Hvals2]*) 
          unfold add_vals.
          intros x. rewrite !map_app, !in_app_iff;
          intros [Hnotx1 Hnotx2].
          not_or Hnotx. rewrite map_fst_combine in Hnotx2; wf_tac.
          rewrite map_snd_combine in Hnotx; wf_tac.
          rewrite !extend_val_with_list_notin'; wf_tac;
          intro C.
          ++ apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch2;
            auto.
            apply Hmatch2 in C; contradiction.
          ++ apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
            auto.
            apply Hmatch1 in C; contradiction.
      * (*Contradiction: both are Some or both are None*)
        exfalso.
        rewrite <- match_val_single_alpha_p_none_iff in Hmatch2.
        rewrite Hmatch2 in Hmatch1. inversion Hmatch1. apply Hpeq.
        all: wf_tac.
    + (*In None case, both None, use IH*) 
      assert (match_val_single gamma_valid pd all_unif vt tys2
      (has_type_valid gamma_valid tm2 tys2 t) (term_rep v1 tm tys2 t0) p
      = None). {
        eapply match_val_single_alpha_p_none. 2: apply Hmatch1.
        apply (Hall2 0). simpl; lia.
      }
      rewrite H1. apply IHps; auto; clear IHps.
      * inversion H0; subst; auto.
      * intros j Hj; apply (Hall2 (S j)); lia.
      * intros; apply H6; simpl; triv.
  - (*Teps - similar to Tlet*) 
    destruct t2; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros [Hvs Heq]; simpl_sumbool.
    rewrite !teps_rep. f_equal. apply functional_extensionality_dep; intros.
    erewrite H. reflexivity. apply Heq.
    + (*Prove Hvals preserved*)
      intros. rewrite in_first_cons in H0.
      destruct H0 as [Hxy | Hinxy].
      * unfold substi. destruct Hxy; subst.
        (*Just annoying casting stuff*)
        destruct (vsymbol_eq_dec v v); [|contradiction].
        destruct (vsymbol_eq_dec v0 v0); [|contradiction].
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H0, H1. simpl. clear e0 e1 H0 H1.
        generalize dependent (proj2 (ty_eps_inv (has_type_eq eq_refl Hty))).
        generalize dependent (proj2 (ty_eps_inv (has_type_eq eq_refl Hty2))).
        intros. subst. destruct v; simpl in *; subst; simpl.
        assert (e1 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        assert (Heq0 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H0, H1. reflexivity.
      * unfold substi. destruct_all. 
        destruct (vsymbol_eq_dec x0 v); subst; try contradiction.
        destruct (vsymbol_eq_dec y v0); subst; try contradiction.
        apply Hvals; auto.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H0 as [Hnotx Hnoty].
      destruct (vsymbol_eq_dec x0 v); subst; [exfalso; apply Hnotx; left; auto |].
      destruct (vsymbol_eq_dec x0 v0); subst; [exfalso; apply Hnoty; left;auto |].
      not_or Hnotx. clear Hnotx2 Hnotx0.
      apply Hvals2; auto.
  - (*Fpred - similar as Tfun*)
    destruct f2; try solve[inversion Heq]. 
    revert Heq. bool_to_prop.
    intros [[[Hfeq Hleneq] Htyeq] Hall]. repeat simpl_sumbool.
    apply Nat.eqb_eq in Hleneq.
    rewrite !fpred_rep.
    f_equal.
    (*Now prove that arg_lists equivalent*)
    apply get_arg_list_pred_ext; wf_tac.
    (*Use Hall to prove this*)
    assert (forall i,
      i < length tms ->
      alpha_equiv_t vars (nth i tms tm_d) (nth i l0 tm_d)). {
      revert Hall Hleneq. clear. revert l0. 
      induction tms; simpl; intros; auto. lia.
      destruct l0; inversion Hleneq.
      revert Hall. bool_to_prop. intros [Hhd Htl].
      destruct i; simpl; auto.
      apply IHtms; auto. lia.
    }
    intros. rewrite Forall_forall in H. apply H with(vars:=vars); wf_tac.
  - (*Fquant - similar to let cases*)
    destruct f2; try solve[inversion Heq]; simpl.
    revert Heq; bool_to_prop; intros [[Hqeq Htys] Heq]; repeat simpl_sumbool.
    destruct v; destruct v0; simpl in *; subst.
    (*So we don't have to repeat proofs*)
    assert (Halleq: forall d,
      formula_rep (substi pd vt v1 (s, v0) d) f
        (valid_quant_inj (valid_formula_eq eq_refl Hval)) =
      formula_rep (substi pd vt v2 (s0, v0) d) f2
        (valid_quant_inj (valid_formula_eq eq_refl Hval2))). {
      intros. eapply H. apply Heq.
      - (*Prove Hval*) 
        intros. rewrite in_first_cons in H0.
        destruct H0 as [Hxy | Hinxy].
        + unfold substi. destruct Hxy; subst.
          (*Just annoying casting stuff*)
          destruct (vsymbol_eq_dec (s, v0) (s, v0)); [|contradiction].
          destruct (vsymbol_eq_dec (s0, v0) (s0, v0)); [|contradiction].
          unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
          assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
          assert (e = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
          assert (Heq0 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
          rewrite H0, H1, H2. reflexivity.
        + unfold substi. destruct_all. 
          destruct (vsymbol_eq_dec x (s, v0)); subst; try contradiction.
          destruct (vsymbol_eq_dec y (s0, v0)); subst; try contradiction.
          apply Hvals; auto.
      - (*prove Hvals2*)
        simpl. intros.
        unfold substi. destruct H0 as [Hnotx Hnoty].
        destruct (vsymbol_eq_dec x (s, v0)); subst; [exfalso; apply Hnotx; left; auto |].
        destruct (vsymbol_eq_dec x (s0, v0)); subst; [exfalso; apply Hnoty; left;auto |].
        not_or Hnotx. clear Hnotx2 Hnotx0.
        apply Hvals2; auto.
    }
    destruct q0.
    + (*Tforall*)
      rewrite !fforall_rep. simpl.
      apply all_dec_eq. split; intros.
      * rewrite <- Halleq; auto.
      * rewrite Halleq; auto.
    + (*Texists*)
      rewrite !fexists_rep; simpl.
      apply all_dec_eq; split; intros [d Hrep]; exists d.
      * rewrite <- Halleq; auto.
      * rewrite Halleq; auto.
  - (*Feq*)
    destruct f2; try solve[inversion Heq]; simpl.
    revert Heq; bool_to_prop; intros [[Htys Heq1] Heq2]; simpl_sumbool.
    rewrite !feq_rep.
    rewrite H with(t2:=t)(vars:=vars)(v2:=v2)
    (Hty2:=(proj1 (valid_eq_inj (valid_formula_eq eq_refl Hval2)))); auto.
    rewrite H0 with(t2:=t0)(vars:=vars)(v2:=v2)
    (Hty2:=(proj2 (valid_eq_inj (valid_formula_eq eq_refl Hval2)))); auto.
  - (*Fbinop*)
    destruct f0; try solve[inversion Heq]; simpl.
    revert Heq; bool_to_prop; intros [[Hb Heq1] Heq2]; simpl_sumbool.
    rewrite !fbinop_rep.
    rewrite H with(f2:=f0_1)(vars:=vars)(v2:=v2)
    (Hval2:=(proj1 (valid_binop_inj (valid_formula_eq eq_refl Hval2)))); auto.
    rewrite H0 with(f2:=f0_2)(vars:=vars)(v2:=v2)
    (Hval2:=(proj2 (valid_binop_inj (valid_formula_eq eq_refl Hval2)))); auto.
  - (*Fnot*)
    destruct f2; try solve[inversion Heq].
    rewrite !fnot_rep. f_equal. apply H with(vars:=vars); auto.
  - (*Ftrue*)
    destruct f2; try solve[inversion Heq].
    reflexivity.
  - (*Ffalse*)
    destruct f2; try solve[inversion Heq].
    reflexivity.
  - (*Flet - just like Tlet*)
    destruct f2; try solve[inversion Heq].
    rename t into tm2.
    rename v into x. rename v0 into y.
    revert Heq; bool_to_prop; intros [[Htyeq Ha1] Ha2].
    simpl_sumbool.
    rewrite !flet_rep.
    apply H0 with(vars:=(x, y) :: vars); auto.
    + simpl. intros.
      rewrite in_first_cons in H1.
      destruct H1 as [Hxy | Hinxy].
      * unfold substi. destruct Hxy; subst.
        destruct (vsymbol_eq_dec x x); subst; 
        [|contradiction].
        destruct (vsymbol_eq_dec y y); subst;
        [|contradiction].
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast. simpl.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H1, H2. simpl. clear e0 e1 H1 H2.
        destruct x; destruct y; simpl in *. subst.
        assert (Heq = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H1. simpl.
        apply H with(vars:=vars); auto.
      * unfold substi.
        destruct_all.
        destruct (vsymbol_eq_dec x0 x); subst; try contradiction.
        destruct (vsymbol_eq_dec y0 y); subst; try contradiction.
        apply Hvals; auto.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H1 as [Hnotx Hnoty].
      destruct (vsymbol_eq_dec x0 x); subst; [exfalso; apply Hnotx; left; auto |].
      destruct (vsymbol_eq_dec x0 y); subst; [exfalso; apply Hnoty; left;auto |].
      not_or Hnotx. clear Hnotx2 Hnotx0.
      apply Hvals2; auto.
  - (*Fif*)
    destruct f0; try solve[inversion Heq]; simpl.
    revert Heq; bool_to_prop; intros [[Heq1 Heq2] Heq3].
    rewrite !fif_rep.
    rewrite H with(f2:=f0_1)(vars:=vars)(v2:=v2)
      (Hval2:=(proj1 (valid_if_inj (valid_formula_eq eq_refl Hval2)))); auto.
    rewrite H0 with (f2:=f0_2)(vars:=vars)(v2:=v2)
      (Hval2:=(proj1 (proj2 (valid_if_inj (valid_formula_eq eq_refl Hval2))))); auto.
    rewrite H1 with (f2:=f0_3)(vars:=vars) (v2:=v2)
      (Hval2:=(proj2 (proj2 (valid_if_inj (valid_formula_eq eq_refl Hval2))))); auto.
  - (*Fmatch - similar to Tmatch*)
    destruct f2; try solve[inversion Heq].
    rename t into tm2.
    rename v into tys.
    rename v0 into tys2.
    rename l into ps2.
    revert Heq; bool_to_prop; intros; destruct Heq as [[[Htm Hps] Htyeq] Hall].
    simpl_sumbool.
    (*Get Hall into something more usable*)
    apply Nat.eqb_eq in Hps.
    assert (Hall2: forall i, i < length ps ->
      let t1 := nth i ps (Pwild, Ftrue) in
      let t2 := nth i ps2 (Pwild, Ftrue) in
      alpha_equiv_p (combine (pat_fv (fst t1)) (pat_fv(fst t2)))
        (fst t1)(fst t2)  /\
      alpha_equiv_f (add_vals (pat_fv (fst t1)) (pat_fv (fst t2)) vars)
        (snd t1) (snd t2)). {
      clear Hval2.
      generalize dependent ps2.
      clear. induction ps; simpl; intros. lia.
      destruct ps2; inversion Hps.
      destruct a; destruct p; simpl in Hall.
      revert Hall; bool_to_prop; intros; destruct Hall as [[Hp Ht] Hall].
      destruct i; simpl; auto.
      apply IHps; auto; try lia.
    }
    clear Hall.
    rewrite !fmatch_rep.
    (*Need nested induction here*)
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval))).
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval2))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval2))).
    inversion Hval2; subst. clear H4 H7 H8 Hval2.
    inversion Hval; subst. clear H4 H8 H9 Hval.
    generalize dependent tys2.
    generalize dependent ps2.
    
    induction ps; simpl; intros; destruct ps2; inversion Hps; auto.
    destruct a. simpl.
    destruct p. simpl.
    rewrite <- (H _ _ v1 v2 _ t0 t Htm) at 1; auto.
    (*Now need to know [match_val_single] is same - separate lemmas*)
    destruct (match_val_single gamma_valid pd all_unif vt tys2
    (has_type_valid gamma_valid tm tys2 t0) (term_rep v1 tm tys2 t0) p0) eqn : Hmatch1.
    + (*In Some case, need to know how lists relate*)

      (*First, get some info we need*)
      assert (Htyp: pattern_has_type sigma p tys2) by
        (inversion H6; subst; auto).
      assert (Htyp0: pattern_has_type sigma p0 tys2) by
        (inversion H7; subst; auto).
      assert (Hpeq: alpha_equiv_p (combine (pat_fv p0) (pat_fv p)) p0 p). {
        specialize (Hall2 0); simpl in Hall2. apply Hall2. lia.
      }
      assert (Hpfvs: length (pat_fv p0) = length (pat_fv p)). {
        eapply alpha_equiv_p_fv_len_full; auto.
      }
      destruct (match_val_single gamma_valid pd all_unif vt tys2
      (has_type_valid gamma_valid tm2 tys2 t) (term_rep v1 tm tys2 t0) p) eqn : Hmatch2.
      * assert (A:=Hall2). specialize (A 0); simpl in A.
        assert (0 < S (length ps)) by lia.
        specialize (A H1); clear H1; destruct A as [Hp Ht12].
        inversion H0; subst. eapply H4. apply Ht12.
        -- intros. 
          unfold add_vals in H1.
          apply in_first_app in H1.
          destruct H1 as [Hinfv | [Hinvars [Hxnotv Hynotv]]].
          ++ (*Case 1: (x, y) are in free vars of p0 and p respectively.
            Then we use [match_val_single_alpha_p_some] and
            [match_val_single_nodup] to show that their valuations
            are the same.*)
            apply in_first_in in Hinfv.
            assert (Hincom:=Hinfv).
            rewrite in_combine_iff in Hinfv; wf_tac.
            destruct Hinfv as [i [Hi Hith]].
            specialize (Hith vs_d vs_d). inversion Hith.
            (*Now, we know that x is in l by 
              [match_val_single_free_var]*)
            assert (Hinxl: In x (map fst l)). {
              apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
              auto.
              apply Hmatch1. subst. wf_tac.
            }
            rewrite in_map_iff in Hinxl. destruct Hinxl as [bnd [Hx Hinbnd]].
            destruct bnd as [x' t']. simpl in Hx. subst x'.
            (*Now, we use [match_val_single_alpha_p_some] to show
              that (y, t') is in l0*)
            assert (Hinyl: In (y, t') l0). {
              eapply match_val_single_alpha_p_some in Hmatch2.
              rewrite <- Hmatch2. apply Hinbnd. apply Hp.
              all: wf_tac. apply Hmatch1. 
            }
            (*Finally, we use NoDup of l, l0 
              (from [match_val_single_nodup]) to give the binding*)
            assert (Hnodup1: NoDup (map fst l)). {
              eapply match_val_single_nodup in Hmatch1.
              apply Hmatch1. apply Htyp0.
            }
            assert (Hnodup2: NoDup (map fst l0)). {
              eapply match_val_single_nodup in Hmatch2.
              apply Hmatch2. apply Htyp.
            }
            rewrite !extend_val_with_list_lookup with(t:=t'); auto.
            (*Now handle all the casting*)
            destruct (vty_eq_dec (snd x) (projT1 t')).
            ** destruct (vty_eq_dec (snd y) (projT1 t')).
              {
                destruct x. destruct y. simpl in *; subst. simpl.
                assert (e0 = eq_refl). apply UIP_dec. apply vty_eq_dec.
                rewrite H1. reflexivity. 
              }
              { 
                exfalso.
                rewrite Heq in e. contradiction.
              }
            ** (*contradiction case - types match in output
              by [match_val_single_typs]*)
              apply match_val_single_typs with(x:=x)(t:=t') in Hmatch1;
              auto. exfalso. rewrite Hmatch1 in n. contradiction.
              (*And we are done!*)
          ++ (*Now in the other case, neither are free vars, so
            we use Hvals2*)
            rewrite map_fst_combine in Hxnotv; wf_tac.
            rewrite map_snd_combine in Hynotv; wf_tac.
            assert (Hxl: ~ In x (map fst l)). {
              intro C. 
              apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
              auto.
              apply Hmatch1 in C. contradiction.
            }
            assert (Hyl0: ~ In y (map fst l0)). {
              intro C.
              apply match_val_single_free_var with(x:=y)(ty':=tys2) in Hmatch2;
              auto.
              apply Hmatch2 in C; contradiction.
            }
            rewrite !extend_val_with_list_notin'; wf_tac.
        -- (*Here, we must show preservation of [Hvals2]*) 
          unfold add_vals.
          intros x. rewrite !map_app, !in_app_iff;
          intros [Hnotx1 Hnotx2].
          not_or Hnotx. rewrite map_fst_combine in Hnotx2; wf_tac.
          rewrite map_snd_combine in Hnotx; wf_tac.
          rewrite !extend_val_with_list_notin'; wf_tac;
          intro C.
          ++ apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch2;
            auto.
            apply Hmatch2 in C; contradiction.
          ++ apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
            auto.
            apply Hmatch1 in C; contradiction.
      * (*Contradiction: both are Some or both are None*)
        exfalso.
        rewrite <- match_val_single_alpha_p_none_iff in Hmatch2.
        rewrite Hmatch2 in Hmatch1. inversion Hmatch1. apply Hpeq.
        all: wf_tac.
    + (*In None case, both None, use IH*) 
      assert (match_val_single gamma_valid pd all_unif vt tys2
      (has_type_valid gamma_valid tm2 tys2 t) (term_rep v1 tm tys2 t0) p
      = None). {
        eapply match_val_single_alpha_p_none. 2: apply Hmatch1.
        apply (Hall2 0). simpl; lia.
      }
      rewrite H1. apply IHps; auto; clear IHps.
      * inversion H0; subst; auto.
      * intros j Hj; apply (Hall2 (S j)); lia.
      * inversion H6; subst; auto.
      * inversion H7; subst; auto.
Qed.

(*Corollaries*)
Definition alpha_equiv_t_equiv (t: term) :=
  proj1(alpha_equiv_equiv t Ftrue). 

Definition alpha_equiv_f_equiv (f: formula) :=
  proj2(alpha_equiv_equiv tm_d f).

(*Full alpha equivalence: when there are no vars in the
  context*)
Definition a_equiv_t: term -> term -> bool :=
  alpha_equiv_t nil.
Definition a_equiv_f: formula -> formula -> bool :=
  alpha_equiv_f nil.

(*And the correctness theorems*)
Corollary a_equiv_t_equiv (t1 t2: term) (v: val_vars pd vt)
  (ty: vty)
  (Hty1: term_has_type sigma t1 ty)
  (Hty2: term_has_type sigma t2 ty)
  (Heq: a_equiv_t t1 t2):
  term_rep v t1 ty Hty1 = term_rep v t2 ty Hty2.
Proof.
  apply alpha_equiv_t_equiv with(vars:=nil); auto.
  intros. exfalso. apply (in_first_nil _ H).
Qed.

Corollary a_equiv_f_equiv (f1 f2: formula) (v: val_vars pd vt)
  (Hval1: valid_formula sigma f1)
  (Hval2: valid_formula sigma f2)
  (Heq: a_equiv_f f1 f2):
  formula_rep v f1 Hval1 = formula_rep v f2 Hval2.
Proof.
  apply alpha_equiv_f_equiv with(vars:=nil); auto.
  intros. exfalso. apply (in_first_nil _ H).
Qed.

(*Can we prove this one?*)
(*Adding (x, x) to the list does not change alpha
  equivalence as long as x appears or not in both terms*)
  (*I'm not sure this is true, and the precondition is very hard to prove*)
  (*
Lemma alpha_equiv_same (t: term) (f: formula):
  (forall x t1 vars
  (Hfree: In x (term_fv t) <-> In x (term_fv t1))
  (Heq: alpha_equiv_t vars t t1),
  alpha_equiv_t ((x, x) :: vars) t t1) /\
  (forall x f1 vars
  (Hfree: In x (form_fv f) <-> In x (form_fv f1))
  (Heq: alpha_equiv_f vars f f1),
  alpha_equiv_f ((x, x) :: vars) f f1).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - destruct t1; auto.
    apply or_cancel_r in Hfree; auto.
    vsym_eq v x.
    + vsym_eq v0 x; auto. vsym_eq x x.
      exfalso. apply n. apply Hfree; auto.
    + vsym_eq v0 x.
      exfalso. apply n. apply Hfree. auto.
  - destruct t1; auto.
    assert (Hlen: length l1 = length l2). {
      revert Heq; bool_to_prop; intros [[[_ Hlen] _ ] _].
      apply Nat.eqb_eq in Hlen; auto. 
    }
    revert Heq; bool_to_prop.
    generalize dependent l2; induction l1; simpl; intros; auto.
    reflexivity.
    destruct l2; inversion Hlen. simpl in Hfree.
    rewrite !union_elts in Hfree.
    Search (?x \/ ?y)

    revert Hfree; simpl_set; intros Hfree.

    simpl_set.
  
  
  
  simpl. simpl in Heq.



      destruct (get_assoc_list vsymbol_eq_dec vars v) eqn : Ha.
      * vsym_eq v0 x. exfalso. apply n. apply Hfree; auto.
      * vsym_eq v0 x. 
  
  
  /\
  
  snd x = snd y)
  (Hbnd: ~ In y (bnd_t t))
  (Hfree: ~ In y (term_fv t)),
  alpha_equiv_t [(x, y)] t (sub_t x y t)) /\
  (forall x y
  (Htys: snd x = snd y)
  (Hbnd: ~ In y (bnd_f f))
  (Hfree: ~ In y (form_fv f)),
  alpha_equiv_f [(x, y)] f (sub_f x y f)).
*)

Lemma in_firstb_refl: forall x l,
  (forall x, In x l -> fst x = snd x) ->
  In x (map fst l) ->
  var_in_firstb (x, x) l.
Proof.
  induction l; simpl; intros; [destruct H0 |].
  vsym_eq x (fst a); simpl; simpl_bool.
  - vsym_eq (fst a) (snd a). simpl.
    rewrite H in n; auto.
  - vsym_eq x (snd a); simpl; auto.
    + rewrite H in n; auto.
    + apply IHl; auto. destruct H0; subst; auto.
      contradiction.
Qed.

Lemma eq_var_refl: forall v vars,
  (forall x, In x vars -> fst x = snd x) ->
  eq_var vars v v.
Proof.
  induction vars; simpl; intros. vsym_eq v v.
  vsym_eq v (fst a); simpl; simpl_bool.
  - vsym_eq (fst a) (snd a).
    specialize (H a). exfalso. rewrite H in n. contradiction. auto.
  - vsym_eq v (snd a); simpl.
    rewrite H in n; auto.
Qed.


Lemma alpha_equiv_p_same (p: pattern) 
  (vars: list (vsymbol * vsymbol))
  (Hvars: forall x, In x vars -> fst x = snd x)
  (Hallin: forall x, In x (pat_fv p) -> In x (map fst vars)):
  alpha_equiv_p vars p p.
Proof.
  induction p; simpl; auto.
  - bool_to_prop; split; [simpl_sumbool |].
    apply in_firstb_refl; auto.
    apply Hallin; simpl; auto.
  - bool_to_prop; split_all; 
    [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |]. 
    simpl in Hallin. induction ps; simpl; auto;
    bool_to_prop; inversion H; subst; split; auto.
    + apply H2; intros. apply Hallin. simpl; simpl_set; triv.
    + apply IHps; auto. intros. apply Hallin. simpl; simpl_set; triv.
  - rewrite IHp1, IHp2; auto; intros; apply Hallin; simpl; simpl_set; triv.
  - bool_to_prop; split_all; [simpl_sumbool | | apply IHp; simpl; auto].
    + apply in_firstb_refl; auto. apply Hallin; simpl; simpl_set; auto.
    + intros; apply Hallin; simpl; simpl_set; triv.
Qed.

Lemma alpha_equiv_same (t: term) (f: formula):
  (forall vars
  (Hvars: forall x, In x vars -> fst x = snd x),
  alpha_equiv_t vars t t) /\
  (forall vars
  (Hvars: forall x, In x vars -> fst x = snd x),
  alpha_equiv_f vars f f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - simpl_sumbool.
  - apply eq_var_refl; auto. 
  - bool_to_prop. split_all; [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |].
    induction l1; simpl; auto; intros.
    bool_to_prop. inversion H; subst.
    split; [apply H2 |]; auto.
  - bool_to_prop. split_all; [simpl_sumbool | apply H| apply H0]; auto.
    simpl; intros. destruct H1; subst; auto.
  - bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - bool_to_prop. split_all; [apply H | apply Nat.eqb_refl | simpl_sumbool |]; auto.
    clear H.
    induction ps; simpl; intros; auto.
    inversion H0; subst. 
    destruct a. bool_to_prop; split_all; auto.
    + apply alpha_equiv_p_same; auto.
      * intros. rewrite in_combine_iff in H; auto.
        destruct H as [i [Hi Hx]].
        specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
      * intros. rewrite map_fst_combine; auto.
    + apply H2. intros. 
      unfold add_vals in H. rewrite in_app_iff in H.
      destruct H; auto.
      rewrite in_combine_iff in H; auto.
      destruct H as [i [Hi Hx]].
      specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
  - bool_to_prop; split; [simpl_sumbool | apply H]; auto;
    simpl; intros. destruct H0; subst; auto.
  - bool_to_prop. split_all; [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |].
    induction tms; simpl; auto; intros.
    bool_to_prop. inversion H; subst.
    split; [apply H2 |]; auto.
  - bool_to_prop; split_all; try simpl_sumbool; apply H; simpl; intros;
    destruct H0; subst; auto.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; triv.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; triv.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; try triv.
    destruct H1; subst; auto.
  - bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - bool_to_prop. split_all; [apply H | apply Nat.eqb_refl | simpl_sumbool |]; auto.
    clear H.
    induction ps; simpl; intros; auto.
    inversion H0; subst. 
    destruct a. bool_to_prop; split_all; auto.
    + apply alpha_equiv_p_same; auto.
      * intros. rewrite in_combine_iff in H; auto.
        destruct H as [i [Hi Hx]].
        specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
      * intros. rewrite map_fst_combine; auto.
    + apply H2. intros. 
      unfold add_vals in H. rewrite in_app_iff in H.
      destruct H; auto.
      rewrite in_combine_iff in H; auto.
      destruct H as [i [Hi Hx]].
      specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
Qed.

Corollary alpha_t_equiv_same (t: term):
  (forall vars
  (Hvars: forall x, In x vars -> fst x = snd x),
  alpha_equiv_t vars t t).
Proof.
  apply alpha_equiv_same. apply Ftrue.
Qed.

Corollary alpha_f_equiv_same (f: formula):
  (forall vars
  (Hvars: forall x, In x vars -> fst x = snd x),
  alpha_equiv_f vars f f).
Proof.
  apply alpha_equiv_same. apply tm_d.
Qed.

Lemma get_assoc_list_app {A B: Set} 
  (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (l1 l2: list (A * B)) (x: A):
  get_assoc_list eq_dec (l1 ++ l2) x =
  match (get_assoc_list eq_dec l1 x) with
  | Some y => Some y
  | None => get_assoc_list eq_dec l2 x
  end.
Proof.
  induction l1; simpl; auto.
  destruct (eq_dec x (fst a)); subst; auto.
Qed.

Lemma flip_app {A B: Type} (l1 l2: list (A * B)) :
  flip (l1 ++ l2) = flip l1 ++ flip l2.
Proof.
  unfold flip. rewrite map_app. auto.
Qed.

Ltac case_inner_match :=
  let rec inner t :=
  match t with
  | match ?x with | Some l => ?a | None => ?b end =>
    inner x
  | _ => let Hp := fresh "Hmatch" in destruct t eqn : Hp
  end in
  match goal with
  | |- match ?t with | Some l => ?a | None => ?b end = ?e =>
    inner t
  end.

Lemma eq_var_app l1 l2 x y :
  eq_var (l1 ++ l2) x y =
  (in_firstb vsymbol_eq_dec vsymbol_eq_dec (x, y) l1) ||
  (negb (in_dec vsymbol_eq_dec x (map fst l1)) &&
  negb (in_dec vsymbol_eq_dec y (map snd l1)) &&
  eq_var l2 x y).
Proof.
  induction l1; simpl; [simpl_bool |]; auto.
  destruct a as [a1 a2]; simpl in *.
  vsym_eq x a1; simpl; simpl_bool.
  - vsym_eq y a2; simpl; auto.
    vsym_eq a1 a1.
  - vsym_eq y a2; simpl.
    + vsym_eq a1 x. vsym_eq a2 a2. simpl. simpl_bool; auto.
    + simpl_bool. vsym_eq a1 x. vsym_eq a2 y.
      rewrite IHl1. f_equal. f_equal. f_equal.
      destruct (in_dec vsymbol_eq_dec x (map fst l1)); auto.
      destruct (in_dec vsymbol_eq_dec y (map snd l1)); auto.
Qed.
   

(*We can ignore the second binding for a variable if it is
  not present in t2. This is very annoying to prove.*)
Lemma alpha_equiv_dup (t: term) (f: formula):
  (forall t1 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (term_fv t1))
    (Hbnd: ~ In y2 (bnd_t t1)) (*shouldn't need this, but proof becomes awful*),
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) t t1 =
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ v3) t t1) /\
  (forall f1 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (form_fv f1))
    (Hbnd: ~In y2 (bnd_f f1)),
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) f f1 =
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ v3) f f1).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  (*TODO: improve this*)
  - destruct t1; auto.
    (*TODO: start here*)
    rewrite !eq_var_app. simpl.
    rewrite !eq_var_app. simpl.
    destruct (in_firstb_spec vsymbol_eq_dec vsymbol_eq_dec (v, v0) v1); simpl; auto.
    destruct (in_dec vsymbol_eq_dec v (map fst v1)); auto; simpl.
    destruct (in_dec vsymbol_eq_dec v0 (map snd v1)); auto; simpl.
    vsym_eq v x; simpl. vsym_eq v0 y1; simpl.
    destruct (in_firstb_spec vsymbol_eq_dec vsymbol_eq_dec (v, v0) v2); simpl; auto.
    destruct (in_dec vsymbol_eq_dec v (map fst v2)); simpl; auto.
    destruct (in_dec vsymbol_eq_dec v0 (map snd v2)); simpl; auto.
    vsym_eq v0 y2; simpl.
    exfalso. apply Hfree. left; auto.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    f_equal.
    simpl in Hfree, Hbnd. generalize dependent l2. induction l1; simpl;
    auto; intros; destruct l2; inversion Hlen.
    inversion H; subst.
    simpl_set. simpl in Hbnd. rewrite in_app_iff in Hbnd.
    f_equal.
    + apply H3; intro C; auto. apply Hfree. exists t.
      split; auto. simpl; triv.
    + apply IHl1; auto. simpl_set. intro C.
      apply Hfree. destruct C as [y [Hiny Hiny2]].
      exists y. split; auto. simpl; triv.
  - destruct t1; auto.
    simpl in Hfree, Hbnd. simpl_set.
    rewrite in_app_iff in Hbnd. f_equal; [f_equal |];
    [apply H |]; auto.
    (*Why we need such a weird IH*) 
    apply (H0 t1_2 x y1 y2 ((v, v0) :: v1)); auto.
    (*Why we need the Hbnd hypothesis*)
    intro C; apply Hfree; right; split; auto.
  - destruct t0; auto.
    simpl in Hfree, Hbnd. simpl_set.
    rewrite !in_app_iff in Hbnd.
    rewrite H, H0, H1; auto.
  - destruct t1; auto.
    simpl in Hfree, Hbnd. simpl_set.
    rewrite in_app_iff in Hbnd.
    destruct (length ps =? length l) eqn : Hlen; simpl;
    simpl_bool; auto. apply Nat.eqb_eq in Hlen.
    f_equal.
    + f_equal. apply H; auto.
    + not_or Hiny2. clear Hiny1 Hiny2. generalize dependent l.
      induction ps; simpl; intros; auto.
      destruct l; inversion Hlen. destruct a.
      destruct p. f_equal.
      * f_equal. inversion H0; subst.
        unfold add_vals.
        specialize (H4 t0 x y1 y2 (combine (pat_fv p0) (pat_fv p) ++ v1) v2 v3).
        rewrite <- !app_assoc in H4. apply H4.
        -- intro C; apply Hiny0. exists (p, t0). split; simpl; auto.
          simpl_set. split; auto. intro Hinpat.
          apply Hiny3. simpl. in_tac.
        -- intro C; apply Hiny3. simpl. in_tac.
      * apply IHps; auto.
        -- inversion H0; subst; auto.
        -- intro C; apply Hiny3; simpl; in_tac.
        -- intro C; apply Hiny0; simpl_set; in_tac.
          destruct C as [y [Hiny Hiny2]].
          exists y. split; simpl; [in_tac | auto].
  - destruct t1; auto. 
    f_equal. 
    simpl in Hfree, Hbnd. simpl_set.
    apply (H _ x y1 y2 ((v, v0) :: v1) v2 v3); auto.
    intro C; apply Hfree; auto.
  - destruct f1; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    f_equal.
    simpl in Hfree, Hbnd. generalize dependent l0. induction tms; simpl;
    auto; intros; destruct l0; inversion Hlen.
    inversion H; subst.
    simpl_set. simpl in Hbnd. rewrite in_app_iff in Hbnd.
    f_equal.
    + apply H3; intro C; auto. apply Hfree. exists t.
      split; auto. simpl; triv.
    + apply IHtms; auto. simpl_set. intro C.
      apply Hfree. destruct C as [y [Hiny Hiny2]].
      exists y. split; auto. simpl; triv.
  - destruct f1; auto. f_equal.
    simpl in Hfree, Hbnd. simpl_set.
    apply (H _ x y1 y2 ((v, v0) :: v1)); auto.
    intro C; apply Hfree; split; auto.
  - destruct f1; auto. simpl in Hfree, Hbnd. simpl_set.
    rewrite in_app_iff in Hbnd. f_equal; [f_equal |];
    [apply H | apply H0]; auto.
  - destruct f0; auto. simpl in Hfree, Hbnd. simpl_set.
    rewrite in_app_iff in Hbnd. f_equal; [f_equal |];
    [apply H | apply H0]; auto.
  - destruct f1; auto.
  - destruct f1; auto.
    simpl in Hfree, Hbnd. simpl_set.
    rewrite in_app_iff in Hbnd. f_equal; [f_equal |];
    [apply H |]; auto.
    apply (H0 f1 x y1 y2 ((v, v0) :: v1)); auto.
    intro C; apply Hfree; right; split; auto.
  - destruct f0; auto. simpl in Hfree, Hbnd.
    simpl_set. rewrite !in_app_iff in Hbnd. 
    f_equal; [f_equal |]; [apply H | apply H0 | apply H1]; auto.
  - destruct f1; auto.
    simpl in Hfree, Hbnd. simpl_set.
    rewrite in_app_iff in Hbnd.
    destruct (length ps =? length l) eqn : Hlen; simpl;
    simpl_bool; auto. apply Nat.eqb_eq in Hlen.
    f_equal.
    + f_equal. apply H; auto.
    + not_or Hiny2. clear Hiny1 Hiny2. generalize dependent l.
      induction ps; simpl; intros; auto.
      destruct l; inversion Hlen. destruct a.
      destruct p. f_equal.
      * f_equal. inversion H0; subst.
        unfold add_vals.
        specialize (H4 f0 x y1 y2 (combine (pat_fv p0) (pat_fv p) ++ v1) v2 v3).
        rewrite <- !app_assoc in H4. apply H4.
        -- intro C; apply Hiny0. exists (p, f0). split; simpl; auto.
          simpl_set. split; auto. intro Hinpat.
          apply Hiny3. simpl. in_tac.
        -- intro C; apply Hiny3. simpl. in_tac.
      * apply IHps; auto.
        -- inversion H0; subst; auto.
        -- intro C; apply Hiny3; simpl; in_tac.
        -- intro C; apply Hiny0; simpl_set; in_tac.
          destruct C as [y [Hiny Hiny2]].
          exists y. split; simpl; [in_tac | auto].
Qed.

Corollary alpha_t_equiv_dup (t: term):
  (forall t1 (x y1 y2: vsymbol) (v1 v2 v3: list (vsymbol * vsymbol))
    (Hfree: ~ In y2 (term_fv t1))
    (Hbnd: ~ In y2 (bnd_t t1)),
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) t t1 =
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ v3) t t1).
Proof.
  apply alpha_equiv_dup. apply Ftrue.
Qed.

Corollary alpha_f_equiv_dup (f: formula):
  (forall f1 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (form_fv f1))
    (Hbnd: ~In y2 (bnd_f f1)),
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) f f1 =
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ v3) f f1).
Proof.
  apply alpha_equiv_dup. apply tm_d.
Qed.

(*We can add a redundant binding (x, x) as long as x does not
  appear later in the list. Again we need a stronger lemma
  to get a good enough IH*)
Lemma alpha_equiv_redundant (t: term) (f: formula):
  (forall (t1: term) (x: vsymbol) (v1 v2: list (vsymbol * vsymbol))
    (Hnotinx1: ~ In x (map fst v2))
    (Hnotinx2: ~ In x (map snd v2)),
    alpha_equiv_t (v1 ++ (x, x) :: v2) t t1 =
    alpha_equiv_t (v1 ++ v2) t t1) /\
  (forall (f1: formula) (x: vsymbol) (v1 v2: list (vsymbol * vsymbol))
    (Hnotinx1: ~ In x (map fst v2))
    (Hnotinx2: ~ In x (map snd v2)),
    alpha_equiv_f (v1 ++ (x, x) :: v2) f f1 =
    alpha_equiv_f (v1 ++ v2) f f1).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  (*There has to be a better way to do this*)
  - destruct t1; auto.
    rewrite !eq_var_app. simpl.
    destruct (in_firstb_spec vsymbol_eq_dec vsymbol_eq_dec (v, v0) v1); simpl; auto.
    destruct (in_dec vsymbol_eq_dec v (map fst v1)); simpl; auto.
    destruct (in_dec vsymbol_eq_dec v0 (map snd v1)); simpl; auto.
    vsym_eq v x; simpl; simpl_bool.
    + vsym_eq v0 x; simpl.
      * symmetry. apply eq_var_in_first. right. auto.
      * destruct (eq_var v2 x v0) eqn : Heq; auto.
        apply eq_var_in_first in Heq.
        destruct_all; subst; auto.
        apply in_first_in in H.
        exfalso. apply Hnotinx1. rewrite in_map_iff. exists (x, v0); auto.
    + vsym_eq v0 x; simpl; auto.
      destruct (eq_var v2 v x) eqn: Heq; auto.
      apply eq_var_in_first in Heq. destruct_all; subst; auto.
      apply in_first_in in H. exfalso. apply Hnotinx2. rewrite in_map_iff.
      exists (v, x). auto.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    f_equal. generalize dependent l2. induction l1; simpl; intros; auto;
    destruct l2; inversion Hlen.
    inversion H; subst. f_equal; auto. 
  - destruct t1; auto.
    f_equal; [f_equal |].
    + apply H; auto.
    + apply (H0 _ _ ((v, v0) :: v1)); auto.
  - destruct t0; auto.
    f_equal; [f_equal |];
    [apply H | apply H0 | apply H1]; auto.
  - destruct t1; auto.
    destruct (length ps =? length l) eqn: Hlen;
    simpl_bool; auto. 
    f_equal; [f_equal |].
    + apply H; auto.
    + apply Nat.eqb_eq in Hlen.
      clear H.
      generalize dependent l.
      induction ps; simpl; auto; intros.
      destruct a; destruct l; inversion Hlen.
      destruct p0. inversion H0; subst.
      f_equal; [f_equal |]; auto.
      unfold add_vals. 
      specialize (H3 t0 x (combine (pat_fv p) (pat_fv p0) ++ v1) v2).
      rewrite <- !app_assoc in H3. apply H3; auto.
  - destruct t1; auto. f_equal.
    apply (H _ _ ((v, v0) :: v1)); auto.
  - destruct f1; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    f_equal. generalize dependent l0. induction tms; simpl; intros; auto;
    destruct l0; inversion Hlen.
    inversion H; subst. f_equal; auto.
  - destruct f1; auto.
    f_equal. apply (H _ _ ((v, v0) :: v1)); auto.
  - destruct f1; auto.
    f_equal; [f_equal |]; [apply H | apply H0]; auto.
  - destruct f0; auto.
    f_equal; [f_equal |]; [apply H | apply H0]; auto.
  - destruct f1; auto.
  - destruct f1; auto. f_equal; [f_equal |]; 
    [apply H | apply (H0 _ _ ((v, v0) :: v1))]; auto.
  - destruct f0; auto.
    f_equal; [f_equal |]; [apply H | apply H0 | apply H1]; auto.
  - destruct f1; auto.
    destruct (length ps =? length l) eqn: Hlen;
    simpl_bool; auto. 
    f_equal; [f_equal |].
    + apply H; auto.
    + apply Nat.eqb_eq in Hlen.
      clear H.
      generalize dependent l.
      induction ps; simpl; auto; intros.
      destruct a; destruct l; inversion Hlen.
      destruct p0. inversion H0; subst.
      f_equal; [f_equal |]; auto.
      unfold add_vals. 
      specialize (H3 f0 x (combine (pat_fv p) (pat_fv p0) ++ v1) v2).
      rewrite <- !app_assoc in H3. apply H3; auto.
Qed.

Corollary alpha_equiv_t_redundant (t: term):
  (forall (t1: term) (x: vsymbol) (v1 v2: list (vsymbol * vsymbol))
    (Hnotinx1: ~ In x (map fst v2))
    (Hnotinx2: ~ In x (map snd v2)),
    alpha_equiv_t (v1 ++ (x, x) :: v2) t t1 =
    alpha_equiv_t (v1 ++ v2) t t1).
Proof.
  apply alpha_equiv_redundant. apply Ftrue.
Qed.

Corollary alpha_equiv_f_redundant (f: formula):
  (forall (f1: formula) (x: vsymbol) (v1 v2: list (vsymbol * vsymbol))
    (Hnotinx1: ~ In x (map fst v2))
    (Hnotinx2: ~ In x (map snd v2)),
    alpha_equiv_f (v1 ++ (x, x) :: v2) f f1 =
    alpha_equiv_f (v1 ++ v2) f f1).
Proof.
  apply alpha_equiv_redundant. apply tm_d.
Qed.

(*We can remove a redundant list *)
Corollary alpha_equiv_t_redundant' (t1 t2: term) 
  (v1 v2: list (vsymbol * vsymbol))
  (Halleq: forall x, In x v1 -> fst x = snd x)
  (Hnodup: NoDup v1)
  (Hnotin1: forall x, In x (map fst v1) -> ~ In x (map fst v2))
  (Hnotin2: forall x, In x (map fst v1) -> ~ In x (map snd v2)):
  alpha_equiv_t (v1 ++ v2) t1 t2 =
  alpha_equiv_t v2 t1 t2.
Proof.
  induction v1; simpl; auto.
  destruct a.
  assert (fst (v, v0) = snd (v, v0)). apply Halleq. left; auto.
  simpl in H; subst.
  inversion Hnodup; subst.
  rewrite alpha_equiv_t_redundant with(x:=v0)(v1:=nil)(v2:=(v1 ++ v2));
  simpl; auto.
  - apply IHv1; auto; intros; 
    [apply Halleq | apply Hnotin1 | apply Hnotin2]; simpl; triv.
  - rewrite map_app. rewrite in_app_iff. intros [Hin1 | Hin2].
    + (*From NoDups*)
      rewrite in_map_iff in Hin1.
      destruct Hin1 as [y [Hy Hin1]]; subst.
      assert (fst y = snd y). {
        apply Halleq. right; triv.
      }
      apply H1. destruct y; simpl in *; subst; auto.
    + (*From assumption*)
      apply (Hnotin1 v0); auto. left; auto.
  - (*similar*) 
   rewrite map_app. rewrite in_app_iff. intros [Hin1 | Hin2].
   + (*From NoDups*)
      rewrite in_map_iff in Hin1.
      destruct Hin1 as [y [Hy Hin1]]; subst.
      assert (fst y = snd y). {
        apply Halleq. right; triv.
      }
      apply H1. destruct y; simpl in *; subst; auto.
    + (*From assumption*)
      apply (Hnotin2 v0); auto. left; auto.
Qed.

(*TODO: how to avoid repeating? Proof is same*)
Corollary alpha_equiv_f_redundant' (f1 f2: formula) 
  (v1 v2: list (vsymbol * vsymbol))
  (Halleq: forall x, In x v1 -> fst x = snd x)
  (Hnodup: NoDup v1)
  (Hnotin1: forall x, In x (map fst v1) -> ~ In x (map fst v2))
  (Hnotin2: forall x, In x (map fst v1) -> ~ In x (map snd v2)):
  alpha_equiv_f (v1 ++ v2) f1 f2 =
  alpha_equiv_f v2 f1 f2.
Proof.
  induction v1; simpl; auto.
  destruct a.
  assert (fst (v, v0) = snd (v, v0)). apply Halleq. left; auto.
  simpl in H; subst.
  inversion Hnodup; subst.
  rewrite alpha_equiv_f_redundant with(x:=v0)(v1:=nil)(v2:=(v1 ++ v2));
  simpl; auto.
  - apply IHv1; auto; intros; 
    [apply Halleq | apply Hnotin1 | apply Hnotin2]; simpl; triv.
  - rewrite map_app. rewrite in_app_iff. intros [Hin1 | Hin2].
    + (*From NoDups*)
      rewrite in_map_iff in Hin1.
      destruct Hin1 as [y [Hy Hin1]]; subst.
      assert (fst y = snd y). {
        apply Halleq. right; triv.
      }
      apply H1. destruct y; simpl in *; subst; auto.
    + (*From assumption*)
      apply (Hnotin1 v0); auto. left; auto.
  - (*similar*) 
   rewrite map_app. rewrite in_app_iff. intros [Hin1 | Hin2].
   + (*From NoDups*)
      rewrite in_map_iff in Hin1.
      destruct Hin1 as [y [Hy Hin1]]; subst.
      assert (fst y = snd y). {
        apply Halleq. right; triv.
      }
      apply H1. destruct y; simpl in *; subst; auto.
    + (*From assumption*)
      apply (Hnotin2 v0); auto. left; auto.
Qed.

Lemma in_combine_same {A: Type} (l: list A):
  forall (x: A * A), In x (combine l l) -> fst x = snd x.
Proof.
  intros. rewrite in_combine_iff in H; auto.
  destruct H as [i [Hi Hx]].
  destruct x; simpl.
  specialize (Hx a a). inversion Hx; subst; auto.
  apply nth_indep; auto.
Qed. 

Lemma NoDup_combine: forall {A B: Type} (l1: list A) (l2: list B)
  (Hl1: NoDup l1) (Hl2: NoDup l2),
  NoDup (combine l1 l2).
Proof.
  intros; generalize dependent l2; induction l1; simpl; intros. 
  constructor.
  destruct l2. constructor.
  inversion Hl1; inversion Hl2; subst.
  constructor. intros Hin.
  apply in_combine_r in Hin. auto.
  apply IHl1; auto.
Qed.

(*The key structural lemma we need about substitution and
  alpha equivalence*)
Theorem alpha_equiv_sub (t: term) (f: formula):
  (forall (x y: vsymbol)
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (bnd_t t))
    (Hfree: ~ In y (term_fv t)),
    alpha_equiv_t [(x, y)] t (sub_t x y t)) /\
  (forall (x y: vsymbol)
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (bnd_f f))
    (Hfree: ~ In y (form_fv f)),
    alpha_equiv_f [(x, y)] f (sub_f x y f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - (*Tconst*) simpl_sumbool.
  - (*Tvar*) not_or Hvy. clear Hbnd Hvy0.
    vsym_eq v x; simpl.
    + vsym_eq x x. vsym_eq y y.
    + vsym_eq x v. vsym_eq v y. vsym_eq v v.
  - (*Tfun*) bool_to_prop. split_all; [simpl_sumbool | wf_tac | simpl_sumbool |];
    [apply Nat.eqb_refl|].
    induction l1; simpl in *; auto.
    inversion H; subst.
    bool_to_prop; split.
    + apply H2; auto.
      * intro C. apply Hbnd. wf_tac.
      * intro C. apply Hfree. simpl_set. wf_tac.
    + apply IHl1; auto.
      * intro C. apply Hbnd. wf_tac.
      * intro C. apply Hfree. simpl_set. wf_tac.
  - (*The Tlet case requires lots of previous lemmas*) 
    bool_to_prop; split_all; [simpl_sumbool | |].
    + apply H; auto.
      * intro C. apply Hbnd. right. wf_tac.
      * intro C. apply Hfree. simpl_set. wf_tac.
    + rewrite in_app_iff in Hbnd. simpl_set.
      vsym_eq x v.
      * (*Why we needed the previous lemmas*)
        pose proof (alpha_t_equiv_dup tm2 tm2 v v y nil nil nil).
        simpl in H1.
        rewrite H1; auto.
        -- apply alpha_t_equiv_same. simpl; intros.
          destruct H2 as [? | []]; subst; auto.
        -- intro C; apply Hfree. simpl_set. right. auto.
      * rewrite alpha_equiv_t_redundant with(x:=v)(v1:=nil)(v2:=(x, y) :: nil); simpl;
        try (intro C; destruct C as [Heq' | []]; subst; auto).
        apply H0; auto. intro C. apply Hfree. right.
        split; auto.
  - (*Tif*) simpl_set. rewrite !in_app_iff in Hbnd. 
    rewrite H, H0, H1; auto.
  - (*Tmatch - basically iterated Tlet, we need the many previous results*) 
    rewrite map_length, Nat.eqb_refl. simpl_bool.
    rewrite union_elts in Hfree.
    rewrite in_app_iff in Hbnd.
    rewrite H; auto. destruct (vty_eq_dec v v); auto; simpl.
    not_or Hiny. clear Hiny1 Hiny.
    rename Hiny0 into Hfree.
    rename Hiny2 into Hbnd.
    induction ps; simpl; auto.
    destruct a.
    inversion H0; subst. 
    case_in.
    + unfold add_vals.
      (*Can use existing lemmas*)
      rewrite alpha_equiv_p_same; simpl;
      [|apply in_combine_same | intros; rewrite map_fst_combine; auto].
      assert (alpha_equiv_t (combine (pat_fv p) (pat_fv p) ++ [(x, y)]) t t). {
        simpl in i.
        pose proof (In_nth _ _ vs_d i).
        destruct H1 as [n [Hn Hx]].
        assert (In (x, x) (combine (pat_fv p) (pat_fv p))). {
          rewrite in_combine_iff; auto. exists n.
          split; auto.
          intros. subst. f_equal; apply nth_indep; auto. 
        }
        apply in_split in H1. destruct H1 as [v1 [v2 Hcomb]].
        rewrite Hcomb.
        rewrite <- app_assoc.
        simpl.
        rewrite alpha_t_equiv_dup; auto.
        - rewrite app_nil_r, <- Hcomb.
          apply alpha_t_equiv_same; simpl.
          apply in_combine_same.
        - intro C; apply Hfree. simpl_set.
          exists (p, t); simpl; split; simpl_set; auto.
          split; auto. intro C1. apply Hbnd.
          rewrite in_concat. exists (pat_fv p ++ bnd_t t).
          simpl. split; auto. in_tac.
        - intro C; apply Hbnd. rewrite in_concat.
          exists (pat_fv p ++ bnd_t t). simpl; split; auto.
          in_tac.
      }
      rewrite H1; simpl.
      apply IHps; auto.
      * intro C. apply Hbnd. simpl. in_tac.
      * intro C. apply Hfree. simpl. simpl_set; auto.
    + (*In this case, we need to do substitution*)
      simpl.
      rewrite alpha_equiv_p_same; simpl;
      [|apply in_combine_same | intros; rewrite map_fst_combine; auto].
      (*We can remove all the redundant variables at the start of
        the list with previous lemmas*)
      unfold add_vals.
      rewrite alpha_equiv_t_redundant' with(v1:=(combine (pat_fv p) (pat_fv p))).
      * rewrite H3; auto. simpl. apply IHps; auto.
        -- intro C; apply Hbnd. simpl; in_tac.
        -- intro C; apply Hfree; simpl_set; auto.
          destruct C as [t' [Hint Hiny]].
          exists t'. split; auto. simpl; triv.
        -- intro C; apply Hbnd. simpl. in_tac.
        -- intro C; apply Hfree. simpl_set. exists (p, t). split; simpl; auto.
          simpl_set. split; auto. intro C1. apply Hbnd.
          simpl. in_tac.
      * apply in_combine_same.
      * apply NoDup_combine; apply NoDup_pat_fv.
      * intros. rewrite map_fst_combine in H1; auto.
        simpl. intros [Hxx0 | []]; subst. contradiction.
      * intros. rewrite map_fst_combine in H1; auto.
        simpl. intros [Hxx0 | []]; subst. simpl in n.
        apply Hbnd. simpl. in_tac.
  - (*Teps - Similar to let, a bit simpler*) 
    simpl_set.  
    vsym_eq x v; destruct (vty_eq_dec (snd v) (snd v)); simpl; auto.
    + pose proof (alpha_f_equiv_dup f f v v y nil nil nil).
      simpl in H0. rewrite H0; auto.
      * apply alpha_f_equiv_same.
        simpl; intros. destruct H1 as [Hx | []]; subst; auto.
      * intro C; apply Hfree. simpl_set. split; auto.
    + rewrite alpha_equiv_f_redundant with(x:=v)(v1:=nil)(v2:=(x, y) :: nil); simpl;
        try (intro C; destruct C as [Heq' | []]; subst; auto).
      apply H; auto. intro C. apply Hfree. split; auto. 
  - (*Fpred*) 
    bool_to_prop. split_all; [simpl_sumbool | wf_tac | simpl_sumbool |];
    [apply Nat.eqb_refl|].
    induction tms; simpl in *; auto.
    inversion H; subst.
    bool_to_prop; split.
    + apply H2; auto.
      * intro C. apply Hbnd. wf_tac.
      * intro C. apply Hfree. simpl_set. wf_tac.
    + apply IHtms; auto.
      * intro C. apply Hbnd. wf_tac.
      * intro C. apply Hfree. simpl_set. wf_tac.
  - (*Fquant - like Teps*)
    simpl_set.  
    vsym_eq x v; destruct (quant_eq_dec q q); 
    destruct (vty_eq_dec (snd v) (snd v)); simpl; auto.
    + pose proof (alpha_f_equiv_dup f f v v y nil nil nil).
      simpl in H0. rewrite H0; auto.
      * apply alpha_f_equiv_same.
        simpl; intros. destruct H1 as [Hx | []]; subst; auto.
      * intro C; apply Hfree. simpl_set. split; auto.
    + rewrite alpha_equiv_f_redundant with(x:=v)(v1:=nil)(v2:=(x, y) :: nil); simpl;
        try (intro C; destruct C as [Heq' | []]; subst; auto).
      apply H; auto. intro C. apply Hfree. split; auto.
  - (*Feq*)
    destruct (vty_eq_dec v v); simpl; auto.
    simpl_set. rewrite in_app_iff in Hbnd.
    rewrite H, H0; auto.
  - (*Fbinop*)
    destruct (binop_eq_dec b b); simpl; auto.
    simpl_set. rewrite in_app_iff in Hbnd.
    rewrite H, H0; auto.
  - (*Flet*)
    bool_to_prop; split_all; [simpl_sumbool | |].
    + apply H; auto.
      * intro C. apply Hbnd. right. wf_tac.
      * intro C. apply Hfree. simpl_set. wf_tac.
    + rewrite in_app_iff in Hbnd. simpl_set.
      vsym_eq x v.
      * pose proof (alpha_f_equiv_dup f f v v y nil nil nil).
        simpl in H1.
        rewrite H1; auto.
        -- apply alpha_f_equiv_same. simpl; intros.
          destruct H2 as [? | []]; subst; auto.
        -- intro C; apply Hfree. simpl_set. right. auto.
      * rewrite alpha_equiv_f_redundant with(x:=v)(v1:=nil)(v2:=(x, y) :: nil); simpl;
        try (intro C; destruct C as [Heq' | []]; subst; auto).
        apply H0; auto. intro C. apply Hfree. right.
        split; auto.
  - (*Fif*)
    simpl_set. rewrite !in_app_iff in Hbnd.
    rewrite H, H0, H1; auto.
  - (*Fmatch*)
    rewrite map_length, Nat.eqb_refl. simpl_bool.
    rewrite union_elts in Hfree.
    rewrite in_app_iff in Hbnd.
    rewrite H; auto. destruct (vty_eq_dec v v); auto; simpl.
    not_or Hiny. clear Hiny1 Hiny.
    rename Hiny0 into Hfree.
    rename Hiny2 into Hbnd.
    induction ps; simpl; auto.
    destruct a.
    inversion H0; subst. 
    case_in.
    + unfold add_vals.
      rewrite alpha_equiv_p_same; simpl;
      [|apply in_combine_same | intros; rewrite map_fst_combine; auto].
      assert (alpha_equiv_f (combine (pat_fv p) (pat_fv p) ++ [(x, y)]) f f). {
        simpl in i.
        pose proof (In_nth _ _ vs_d i).
        destruct H1 as [n [Hn Hx]].
        assert (In (x, x) (combine (pat_fv p) (pat_fv p))). {
          rewrite in_combine_iff; auto. exists n.
          split; auto.
          intros. subst. f_equal; apply nth_indep; auto. 
        }
        apply in_split in H1. destruct H1 as [v1 [v2 Hcomb]].
        rewrite Hcomb.
        rewrite <- app_assoc.
        simpl.
        rewrite alpha_f_equiv_dup; auto.
        - rewrite app_nil_r, <- Hcomb.
          apply alpha_f_equiv_same; simpl.
          apply in_combine_same.
        - intro C; apply Hfree. simpl_set.
          exists (p, f); simpl; split; simpl_set; auto.
          split; auto. intro C1. apply Hbnd.
          rewrite in_concat. exists (pat_fv p ++ bnd_f f).
          simpl. split; auto. in_tac.
        - intro C; apply Hbnd. rewrite in_concat.
          exists (pat_fv p ++ bnd_f f). simpl; split; auto.
          in_tac.
      }
      rewrite H1; simpl.
      apply IHps; auto.
      * intro C. apply Hbnd. simpl. in_tac.
      * intro C. apply Hfree. simpl. simpl_set; auto.
    + (*In this case, we need to do substitution*)
      simpl.
      rewrite alpha_equiv_p_same; simpl;
      [|apply in_combine_same | intros; rewrite map_fst_combine; auto].
      (*We can remove all the redundant variables at the start of
        the list with previous lemmas*)
      unfold add_vals.
      rewrite alpha_equiv_f_redundant' with(v1:=(combine (pat_fv p) (pat_fv p))).
      * rewrite H3; auto. simpl. apply IHps; auto.
        -- intro C; apply Hbnd. simpl; in_tac.
        -- intro C; apply Hfree; simpl_set; auto.
          destruct C as [t' [Hint Hiny]].
          exists t'. split; auto. simpl; triv.
        -- intro C; apply Hbnd. simpl. in_tac.
        -- intro C; apply Hfree. simpl_set. exists (p, f). split; simpl; auto.
          simpl_set. split; auto. intro C1. apply Hbnd.
          simpl. in_tac.
      * apply in_combine_same.
      * apply NoDup_combine; apply NoDup_pat_fv.
      * intros. rewrite map_fst_combine in H1; auto.
        simpl. intros [Hxx0 | []]; subst. contradiction.
      * intros. rewrite map_fst_combine in H1; auto.
        simpl. intros [Hxx0 | []]; subst. simpl in n.
        apply Hbnd. simpl. in_tac.
Qed.

(*TODO: automate "Corollary" process*)
Definition alpha_equiv_sub_t (t: term) := proj1(alpha_equiv_sub t Ftrue).
Definition alpha_equiv_sub_f (f: formula) :=
  proj2 (alpha_equiv_sub tm_d f).

(*Now that we have our structural results, we prove results
  about alpha equivalence of let, quantifiers, and match statements.
  This means that we should never again need to unfold the
  definition of alpha equivalence or work inductively over the list
  (TODO: except to prove transitivity and stuff)*)
(*These results, with all our work, are easy*)
Lemma alpha_convert_quant
  (q: quant) (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (f: formula)
  (Hbnd: ~In v2 (bnd_f f))
  (Hfree: ~In v2 (form_fv f)):
  a_equiv_f (Fquant q v1 f) (Fquant q v2 (sub_f v1 v2 f)).
Proof.
  unfold a_equiv_f. simpl.
  bool_to_prop; split_all; try solve[simpl_sumbool].
  apply alpha_equiv_sub_f; auto.
Qed.

Lemma alpha_convert_tlet 
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (tm1 tm2: term)
  (Hbnd: ~In v2 (bnd_t tm2))
  (Hfree: ~In v2 (term_fv tm2)):
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm1 v2 (sub_t v1 v2 tm2)).
Proof.
  unfold a_equiv_t.
  simpl. destruct (vty_eq_dec (snd v1) (snd v2)); simpl; auto.
  bool_to_prop. split.
  - apply alpha_t_equiv_same; simpl; intros. destruct H.
  - apply alpha_equiv_sub_t; auto.
Qed.

Lemma alpha_convert_flet 
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (t1: term) (f2: formula)
  (Hbnd: ~In v2 (bnd_f f2))
  (Hfree: ~In v2 (form_fv f2)):
  a_equiv_f (Flet t1 v1 f2) (Flet t1 v2 (sub_f v1 v2 f2)).
Proof.
  unfold a_equiv_f.
  simpl. destruct (vty_eq_dec (snd v1) (snd v2)); simpl; auto.
  bool_to_prop. split.
  - apply alpha_t_equiv_same; simpl; intros. destruct H.
  - apply alpha_equiv_sub_f; auto.
Qed.

(*Prove Equivalence Relation (TODO: move, put after or before
  all inductive cases)*)

(*We proved refl already*)
Lemma a_equiv_t_refl (t: term):
  a_equiv_t t t.
Proof.
  unfold a_equiv_t.
  apply alpha_t_equiv_same. intros. inversion H.
Qed.

Lemma a_equiv_f_refl (f: formula):
  a_equiv_f f f.
Proof.
  unfold a_equiv_f.
  apply alpha_f_equiv_same; intros; inversion H.
Qed.

(*Need this to avoid length arguments*)
Lemma map_fst_combine_nodup {A B: Type} (l1: list A) (l2: list B):
  NoDup l1 ->
  NoDup (map fst (combine l1 l2)).
Proof.
  intros. revert l2. induction l1; simpl; intros; auto.
  inversion H; subst. destruct l2; simpl; constructor.
  - intro C. rewrite in_map_iff in C.
    destruct C as [t [Ha Hint]]; subst.
    destruct t.
    apply in_combine_l in Hint. simpl in H2. contradiction.
  - apply IHl1; auto.
Qed.

Lemma map_snd_combine_nodup {A B: Type} (l1: list A) (l2: list B):
  NoDup l2 ->
  NoDup (map snd (combine l1 l2)).
Proof.
  intros. generalize dependent l2. induction l1; simpl; intros; auto.
  constructor. 
  destruct l2; simpl; inversion H; subst; constructor.
  - intro C. rewrite in_map_iff in C.
    destruct C as [t [Ha Hint]]; subst.
    destruct t.
    apply in_combine_r in Hint. simpl in H2. contradiction.
  - apply IHl1; auto.
Qed.

Lemma flip_combine {A B: Type} (l1: list A) (l2: list B):
  flip (combine l1 l2) = combine l2 l1.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; auto.
  simpl.
  rewrite IHl1; auto.
Qed.



(*Symmetry*)
Lemma alpha_equiv_sym (t: term) (f: formula):
  (forall t1 l,
    alpha_equiv_t l t t1 = alpha_equiv_t (flip l) t1 t) /\
  (forall f1 l,
    alpha_equiv_f l f f1 = alpha_equiv_f (flip l) f1 f).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - destruct t1; auto; simpl.
    destruct (all_dec (c = c0)); subst; simpl.
    + destruct (all_dec (c0 = c0)); auto. contradiction.
    + destruct (all_dec (c0 = c)); subst; auto.
  - destruct t1; auto; simpl.
    apply eq_var_flip.
  - destruct t1; auto; simpl.
    rewrite Nat.eqb_sym.
    destruct (length l3 =? length l1) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    f_equal.
    + rewrite eq_dec_sym. f_equal. apply eq_dec_sym.
    + generalize dependent l3. induction l1; simpl; intros; auto;
      destruct l3; inversion Hlen; auto.
      inversion H; subst.
      f_equal; auto.
  - destruct t1; auto; simpl. rewrite H, H0, eq_dec_sym. reflexivity. 
  - destruct t0; auto; simpl.
    rewrite H, H0, H1; auto.
  - destruct t1; auto; simpl.
    rewrite Nat.eqb_sym.
    destruct (length l0 =? length ps) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    rewrite H, eq_dec_sym. f_equal. clear H.
    generalize dependent l0. induction ps; simpl; intros; auto; 
    destruct l0; inversion Hlen; auto.
    destruct p; destruct a.
    rewrite alpha_equiv_p_sym.
    rewrite flip_combine.
    inversion H0; subst. f_equal; auto.
    rewrite H3. unfold add_vals.
    rewrite flip_app, flip_combine; auto.
  - destruct t1; auto; simpl.
    rewrite H, eq_dec_sym. reflexivity.
  - destruct f1; auto; simpl.
    rewrite Nat.eqb_sym.
    destruct (length l1 =? length tms) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    f_equal.
    + rewrite eq_dec_sym. f_equal. apply eq_dec_sym.
    + generalize dependent l1. induction tms; simpl; intros; auto;
      destruct l1; inversion Hlen; auto.
      inversion H; subst.
      f_equal; auto.
  - destruct f1; auto; simpl.
    rewrite H, eq_dec_sym. f_equal. f_equal.
    apply eq_dec_sym.
  - destruct f1; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f0; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f1; auto; simpl.
    apply H.
  - destruct f1; auto.
  - destruct f1; auto.
  - destruct f1; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f0; auto; simpl.
    rewrite H, H0, H1; reflexivity.
  - destruct f1; auto; simpl.
    rewrite Nat.eqb_sym.
    destruct (length l0 =? length ps) eqn : Hlen; simpl_bool; auto.
    apply Nat.eqb_eq in Hlen.
    rewrite H, eq_dec_sym. f_equal. clear H.
    generalize dependent l0. induction ps; simpl; intros; auto; 
    destruct l0; inversion Hlen; auto.
    destruct p; destruct a.
    rewrite alpha_equiv_p_sym, flip_combine.
    inversion H0; subst. f_equal; auto.
    f_equal. rewrite H3. unfold add_vals.
    rewrite flip_app, flip_combine; auto.
Qed.

Definition alpha_t_equiv_sym (t: term):= proj1(alpha_equiv_sym t Ftrue).
Definition alpha_f_equiv_sym (f: formula) :=
  proj2 (alpha_equiv_sym tm_d f).

Corollary a_equiv_t_sym (t1 t2: term):
  a_equiv_t t1 t2 = a_equiv_t t2 t1.
Proof.
  unfold a_equiv_t. rewrite alpha_t_equiv_sym. reflexivity.
Qed.

Corollary a_equiv_f_sym (f1 f2: formula):
  a_equiv_f f1 f2 = a_equiv_f f2 f1.
Proof.
  unfold a_equiv_f. rewrite alpha_f_equiv_sym. reflexivity.
Qed.

(*Transitivity*)

Definition alist_trans (l1 l2: list (vsymbol * vsymbol)) :=
  map2 (fun x y => (fst x, snd y)) l1 l2.

  (*
Lemma eq_var_trans v1 v2 x y z:
  eq_var v1 x y ->
  eq_var v2 y z ->
  eq_var (alist_trans v1 v2) x z.
Proof.
  revert v2. induction v1; simpl; intros; destruct v2.
  - simpl in H0. vsym_eq x y.
  - simpl in H0. vsym_eq x y.
    vsym_eq y (fst p); simpl in H0.
    + vsym_eq z (snd p). simpl in H0. rewrite orb_false_r in H0.
  
  
  inversion H; subst.
  - simpl in H1. vsym_eq x y.
  - simpl. clear H. simpl in H1.
    vsym_eq x (fst a); simpl in *; auto; revert H0; simpl_bool; intros.
    + vsym_eq y (snd a). vsym_eq (snd a) (fst p); auto; simpl in *.
      vsym_eq z (snd p).
    + vsym_eq y (snd a); simpl in H0.
      vsym_eq y (fst p); simpl in *.
      vsym_eq z (snd p); simpl in *.
      apply IHv1; auto.
Qed.*)

Lemma eq_var_trans v1 v2 x y z:
  map snd v1 = map fst v2 ->
  eq_var v1 x y ->
  eq_var v2 y z ->
  eq_var (alist_trans v1 v2) x z.
Proof.
  revert v2. induction v1; simpl; intros; destruct v2; inversion H; subst.
  - simpl in H1. vsym_eq x y.
  - simpl. clear H. simpl in H1.
    vsym_eq x (fst a); simpl in *; auto; revert H0; simpl_bool; intros.
    + vsym_eq y (snd a). vsym_eq (snd a) (fst p); auto; simpl in *.
      vsym_eq z (snd p).
    + vsym_eq y (snd a); simpl in H0.
      vsym_eq y (fst p); simpl in *.
      vsym_eq z (snd p); simpl in *.
      apply IHv1; auto.
Qed.

(*Same proof: TODO fix*)
Lemma in_firstb_trans v1 v2 x y z:
  map snd v1 = map fst v2 ->
  var_in_firstb (x, y) v1 ->
  var_in_firstb (y, z) v2 ->
  var_in_firstb (x, z) (alist_trans v1 v2).
Proof.
  revert v2. induction v1; simpl; intros; destruct v2; inversion H; subst;
  [inversion H0 |].
  simpl. clear H. simpl in H1.
  vsym_eq x (fst a); simpl in *; auto; revert H0; simpl_bool; intros.
  + vsym_eq y (snd a). vsym_eq (snd a) (fst p); auto; simpl in *.
    vsym_eq z (snd p).
  + vsym_eq y (snd a); simpl in H0.
    vsym_eq y (fst p); simpl in *.
    vsym_eq z (snd p); simpl in *.
    apply IHv1; auto.
Qed.

(*As long as the vars list includes all free vars of p1
  and has no duplicates, any two patterns that are
  alpha equivalent are well-typed if the other is*)
Lemma alpha_equiv_p_type (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol)) (ty: vty)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hn1: NoDup (map fst vars))
  (Hn2: NoDup (map snd vars))
  (Hallin: forall x, In x (pat_fv p1) -> In x (map fst vars))
  (Hty: pattern_has_type sigma p1 ty):
  pattern_has_type sigma p2 ty.
Proof.
  generalize dependent ty.
  generalize dependent p2.
  induction p1; simpl; intros; auto; 
  destruct p2; try solve[inversion Heq];
  revert Heq; bool_to_prop; intros; destruct_all;
  repeat simpl_sumbool.
  - inversion Hty; subst. rewrite e. constructor.
    rewrite <- e; assumption.
  - (*This case is hard because we have to show that the free
    variable sets are disjoint. This follows from [alpha_equiv_p_fv']
    which describes the relationship between the free variables
    of alpha-equivalent patterns*)
    apply Nat.eqb_eq in H3.
    inversion Hty; subst.
    (*Get something useful out of H1 so we only need induction once*)
    rename l0 into ps2.
    assert (Hall: forall i, i < length ps ->
      alpha_equiv_p vars (nth i ps Pwild) (nth i ps2 Pwild)). {
      generalize dependent ps2. clear. induction ps; simpl; 
      intros ps2 Hps Hall2 i Hi;
      destruct ps2; inversion Hps. lia.
      apply andb_true_iff in Hall2. destruct Hall2.
      destruct i; simpl; auto. apply IHps; auto. lia.
    }
    clear H1.
    constructor; auto; try lia.
    + assert (length (map (ty_subst (s_params f0) l) (s_args f0)) = length ps2). {
        rewrite map_length; lia.
      }
      subst sigma0.
      generalize dependent ((map (ty_subst (s_params f0) l) (s_args f0))).
      intros a Hall2 Hlen2.
      revert Hall2 H.
      rewrite !Forall_forall; intros.
      rewrite in_combine_iff in H0; auto.
      destruct H0 as [i [Hi Hx]].
      specialize (Hx Pwild vty_int). subst. simpl.
      eapply H.
      3: apply Hall; lia.
      wf_tac.
      * intros; apply Hallin. simpl. simpl_set. 
        exists (nth i ps Pwild); split; wf_tac.
      * specialize (Hall2 (nth i ps Pwild, nth i a vty_int));
        apply Hall2.
        rewrite in_combine_iff; try lia.
        exists i. split; try lia. intros.
        f_equal; apply nth_indep; lia.
    + intros. intros [Hin1 Hin2].
      assert (Hi:=Hall).
      specialize (Hi i ltac:(lia)).
      specialize (Hall j ltac:(lia)).
      (*Crucially, we need [alpha_equiv_p_fv'] here*)
      apply alpha_equiv_p_fv' in Hall; auto.
      apply alpha_equiv_p_fv' in Hi; auto.
      2: { intros; apply Hallin. simpl. simpl_set. exists (nth i ps Pwild).
        split; wf_tac. }
      2: { intros; apply Hallin. simpl. simpl_set. exists (nth j ps Pwild).
        split; wf_tac. }
      rewrite nth_indep with(d':=Pwild) in Hin1 by lia.
      rewrite nth_indep with(d':=Pwild) in Hin2 by lia.
      rewrite Hall in Hin2.
      rewrite Hi in Hin1.
      rewrite in_map_iff in Hin1.
      destruct Hin1 as [y1 [Hx Hiny1]].
      subst.
      rewrite in_map_iff in Hin2.
      destruct Hin2 as [y2 [Hx Hy2]].
      (*What we have to show: y1 = y2, 
        follows from injectivity of mk_fun'
        Really all we need is that the mapping function is
        injective, we don't care that is it specifically mk_fun'*)
      apply mk_fun_inj' in Hx; auto.
      2: { apply Hallin. simpl. simpl_set. 
        exists (nth j ps (Pwild)); split; wf_tac. }
      2: { apply Hallin; simpl; simpl_set.
        exists (nth i ps Pwild); split; wf_tac. }
      subst. apply (H12 i j Pwild y1 ltac:(lia) ltac:(lia) H2).
      split; auto.
  - assumption.
  - inversion Hty; subst.
    simpl in Hallin.
    constructor; auto.
    + apply IHp1_1; auto. intros; apply Hallin; simpl_set; triv.
    + apply IHp1_2; auto. intros; apply Hallin; simpl_set; triv.
    + (*Again we need the relationship between the free variables,
        but equivalence is much easier than disjointness*)
      intros x.
      apply alpha_equiv_p_fv' in H; auto.
      apply alpha_equiv_p_fv' in H0; auto.
      * rewrite H, H0. rewrite !in_map_iff.
        split; intros [y [Hx Hiny]]; subst; exists y; split; auto;
        apply H7; auto.
      * intros; apply Hallin; simpl_set; triv.
      * intros; apply Hallin; simpl_set; triv.
  - inversion Hty; subst.
    rewrite e. constructor; auto.
    + apply alpha_equiv_p_fv' in H0; auto.
      * rewrite H0. rewrite in_map_iff.
        intros [y [Hv0 Hiny]]; subst.
        (*Again, follows from injectivity of [mk_fun']*)
        rewrite <- (combine_eq vars) in H1 at 3.
        apply mk_fun_in_firstb' in H1.
        apply mk_fun_inj' in H1; auto.
        -- subst; contradiction.
        -- apply Hallin; simpl; simpl_set; triv.
        -- apply Hallin; simpl; simpl_set; triv.
      * intros; apply Hallin; simpl; simpl_set; triv.
    + apply IHp1; auto.
      * intros; apply Hallin; simpl; simpl_set; triv.
      * rewrite <- e; assumption.
Qed.

(*Lemma in_map_fst_combine {A B: Type} (l1: list A) (l2: list B)
  (x: A):
  In x *)

(*A more specific version
  TODO: better name than _full*)
Lemma alpha_equiv_p_type_full (p1 p2: pattern) (ty: vty)
  (Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2)
  (Hlens: length (pat_fv p1) = length(pat_fv p2))
  (Hty: pattern_has_type sigma p1 ty):
  pattern_has_type sigma p2 ty.
Proof.
  apply alpha_equiv_p_type with(ty:=ty) in Heq; auto.
  - apply map_fst_combine_nodup; apply NoDup_pat_fv.
  - apply map_snd_combine_nodup; apply NoDup_pat_fv.
  - intros. rewrite map_fst_combine; auto.
Qed.

(*TODO: move*)
Lemma mk_fun_nth l1 l2 i d1 d2
  (Hlen: length l1 = length l2)
  (Hn1: NoDup l1)
  (Hi: i < length l1):
  mk_fun l1 l2 (nth i l1 d1) = nth i l2 d2.
Proof.
  generalize dependent l2.
  generalize dependent i.
  induction l1; simpl; intros; destruct l2; inversion Hlen; [lia|].
  destruct i.
  - vsym_eq a a.
  - inversion Hn1; subst.
    vsym_eq (nth i l1 d1) a; simpl.
    + exfalso. apply H2. wf_tac.
    + apply IHl1; auto. lia.
Qed.

Corollary mk_fun_nth' l1 l2 i d1 d2
  (Hlen: length l1 = length l2)
  (Hn1: NoDup l1)
  (Hi: i < length l1):
  mk_fun' l1 l2 (nth i l1 d1) = nth i l2 d2.
Proof.
  unfold mk_fun'. rewrite Hlen, Nat.ltb_irrefl.
  apply mk_fun_nth; auto.
Qed.
    
(*Another key property of alpha equivalence: it preserves
  well-typedness*)
Lemma alpha_equiv_type (t: term) (f: formula):
  (forall t1 (vars: list (vsymbol * vsymbol)) (ty: vty)
    (Heq: alpha_equiv_t vars t t1)
    (Hvars: forall x y, In (x, y) vars -> snd x = snd y),
    term_has_type sigma t ty ->
    term_has_type sigma t1 ty) /\
  (forall f1 (vars: list (vsymbol * vsymbol))
    (Heq: alpha_equiv_f vars f f1)
    (Hvars: forall x y, In (x, y) vars -> snd x = snd y),
    valid_formula sigma f ->
    valid_formula sigma f1).
Proof.
  revert t f; apply term_formula_ind; simpl; intros.
  - destruct t1; try solve[inversion Heq].
    destruct (all_dec (c = c0)); subst; auto. inversion Heq.
  - destruct t1; try solve[inversion Heq].
    apply eq_var_in_first in Heq.
    destruct_all; subst; auto.
    apply in_first_in in H0.
    apply Hvars in H0.
    inversion H; subst.
    rewrite H0. constructor. rewrite <- H0; auto.
  - destruct t1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    simpl_sumbool. simpl_sumbool.
    apply Nat.eqb_eq in H4.
    inversion H0; subst. constructor; auto; try lia.
    clear -H13 H2 H H10 H4 Hvars.
    assert (length l1 = length (map (ty_subst (s_params f) l0) (s_args f))) by wf_tac.
    generalize dependent (map (ty_subst (s_params f) l0) (s_args f)).
    intros typs; revert typs.
    clear H10. generalize dependent l2. induction l1; simpl; intros; auto;
    destruct typs; inversion H0.
    + destruct l2; inversion H4. constructor.
    + destruct l2; inversion H4. inversion H13; subst.
      inversion H; subst.
      revert H2; bool_to_prop; intros; destruct_all. 
      constructor; auto; simpl.
      eapply H9. apply H1. auto. apply H7.
  - destruct t1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    simpl_sumbool.
    inversion H1; subst. constructor; auto.
    + eapply H. apply H4. intros; auto. rewrite <- e; auto.
    + eapply H0. apply H3. 2: auto. simpl; intros x y [Heq | Hin].
      * inversion Heq; subst; auto.
      * auto.
  - destruct t0; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    inversion H2; subst.
    constructor; [apply (H _ _ H3) | apply (H0 _ _ _ H5) | apply (H1 _ _ _ H4)]; auto.
  - destruct t1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all. simpl_sumbool.
    apply Nat.eqb_eq in H5.
    inversion H1; subst.
    assert (forall i, i < length ps ->
        let t1 := (nth i ps (Pwild, tm_d)) in
        let t2 := (nth i l (Pwild, tm_d)) in
        length (pat_fv (fst t1)) = length (pat_fv (fst t2)) /\
        alpha_equiv_p (combine (pat_fv (fst t1)) (pat_fv (fst t2))) 
          (fst t1) (fst t2) /\
        alpha_equiv_t (add_vals (pat_fv (fst t1)) (pat_fv (fst t2)) vars)
          (snd t1) (snd t2)
    ). 
    {
      clear -H5 H3. generalize dependent l.
      induction ps; simpl; intros; try lia; destruct l; inversion H5.
      clear H5.
      destruct a; destruct p.
      revert H3; bool_to_prop; intros; destruct_all.
      destruct i; simpl.
      - split_all; auto. apply alpha_equiv_p_fv_len_full; auto.
      - apply IHps; auto. lia.
    }
    constructor; auto; [apply (H _ _ _ H2); auto | | |
      destruct l; destruct ps; auto; inversion H5].
    + intros. pose proof (In_nth _ _ (Pwild, tm_d) H6).
      destruct H7 as [n [Hn Hx]]; subst.
      specialize (H4 n ltac:(lia)).
      simpl in H4.
      destruct H4 as [ Heql [Heqp Heqt]].
      apply alpha_equiv_p_type_full with(ty:=v0) in Heqp; auto.
      apply H10. wf_tac.
    + intros. pose proof (In_nth _ _ (Pwild, tm_d) H6).
      destruct H7 as [n [Hn Hx]]; subst.
      specialize (H4 n ltac:(lia)).
      simpl in H4.
      destruct H4 as [ Heql [Heqp Heqt]].
      rewrite Forall_forall in H0.
      eapply H0. 2: apply Heqt.
      * wf_tac.
      * unfold add_vals.
        intros. rewrite in_app_iff in H4.
        destruct H4; auto.
        assert (Heqp':=Heqp).
        apply alpha_equiv_p_fv_full in Heqp. rewrite Heqp in H4.
        rewrite in_combine_iff in H4; wf_tac.
        destruct H4 as [i [Hi Hxy]].
        specialize (Hxy vs_d vs_d). inversion Hxy; subst. clear Hxy.
        rewrite map_nth_inbound with(d2:=vs_d); auto.
        rewrite mk_fun_vars_eq_full; auto.
        wf_tac.
      * apply H12. wf_tac.
  - (*Teps*)
    destruct t1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros [Htys Heq].
    simpl_sumbool.
    inversion H0; subst.
    rewrite e. constructor.
    + apply H in Heq; auto. simpl; intros x y [Hxy | Hinxy]; auto.
      inversion Hxy; subst; auto.
    + rewrite <- e; assumption.
  - (*Fpred*)
    destruct f1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    simpl_sumbool. simpl_sumbool.
    apply Nat.eqb_eq in H4.
    inversion H0; subst. constructor; auto; try lia.
    clear -H11 H2 H H9 H4 Hvars. subst sigma0.
    assert (length l0 = length (map (ty_subst (p_params p0) l) (p_args p0))) by wf_tac.
    generalize dependent (map (ty_subst (p_params p0) l) (p_args p0)).
    intros typs; revert typs.
    clear H9. rename l0 into tms2. generalize dependent tms2. 
    induction tms; simpl; intros; auto;
    destruct typs; inversion H0;
    destruct tms2; inversion H4; simpl; try solve[constructor].
    inversion H11; subst.
    inversion H; subst.
    revert H2; bool_to_prop; intros; destruct_all. 
    constructor; auto; simpl.
    eapply H9. apply H1. auto. apply H7.
  - (*Fquant*)
    destruct f1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all; repeat simpl_sumbool.
    inversion H0; subst.
    constructor; [rewrite <- e |]; auto.
    apply H in H2; auto. simpl; intros x y [Hxy | Hinxy]; auto.
    inversion Hxy; subst; auto.
  - (*Feq*)
    destruct f1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    inversion H1; subst.
    simpl_sumbool.
    constructor; [apply H with(ty:=v0) in H4 | 
      apply H0 with(ty:=v0) in H3]; auto.
  - (*Fbinop - same*)
    destruct f0; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    inversion H1; subst.
    simpl_sumbool.
    constructor; [apply H in H4 | apply H0 in H3]; auto.
  - (*Fnot*)
    destruct f1; try solve[inversion Heq].
    inversion H0; subst.
    constructor.
    apply H in Heq; auto.
  - (*Ftrue*)
    destruct f1; try solve[inversion Heq]. constructor.
  - (*Ffalse*)
    destruct f1; try solve[inversion Heq]. constructor.
  - (*Flet*)
    destruct f1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    simpl_sumbool.
    inversion H1; subst. constructor; auto.
    + eapply H. apply H4. intros; auto. rewrite <- e; auto.
    + eapply H0. apply H3. 2: auto. simpl; intros x y [Heq | Hin].
      * inversion Heq; subst; auto.
      * auto.
  - (*Fif*) destruct f0; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all.
    inversion H2; subst.
    constructor; [apply (H _ _ H3) | apply (H0 _ _  H5) | apply (H1 _ _ H4)]; auto.
  - (*Fmatch*) destruct f1; try solve[inversion Heq].
    revert Heq; bool_to_prop; intros; destruct_all. simpl_sumbool.
    apply Nat.eqb_eq in H5.
    inversion H1; subst.
    assert (forall i, i < length ps ->
        let t1 := (nth i ps (Pwild, Ftrue)) in
        let t2 := (nth i l (Pwild, Ftrue)) in
        length (pat_fv (fst t1)) = length (pat_fv (fst t2)) /\
        alpha_equiv_p (combine (pat_fv (fst t1)) (pat_fv (fst t2))) 
          (fst t1) (fst t2) /\
        alpha_equiv_f (add_vals (pat_fv (fst t1)) (pat_fv (fst t2)) vars)
          (snd t1) (snd t2)
    ). 
    {
      clear -H5 H3. generalize dependent l.
      induction ps; simpl; intros; try lia; destruct l; inversion H5.
      clear H5.
      destruct a; destruct p.
      revert H3; bool_to_prop; intros; destruct_all.
      destruct i; simpl.
      - split_all; auto. apply alpha_equiv_p_fv_len_full; auto.
      - apply IHps; auto. lia.
    }
    constructor; auto; [apply (H _ _ _ H2); auto | | |
      destruct l; destruct ps; auto; inversion H5].
    + rewrite Forall_forall; intros. 
      pose proof (In_nth _ _ (Pwild, Ftrue) H6).
      destruct H7 as [n [Hn Hx]]; subst.
      specialize (H4 n ltac:(lia)).
      simpl in H4.
      destruct H4 as [ Heql [Heqp Heqt]].
      apply alpha_equiv_p_type_full with(ty:=v0) in Heqp; auto.
      rewrite Forall_forall in H10.
      apply H10. wf_tac.
    + rewrite Forall_forall; intros. 
      pose proof (In_nth _ _ (Pwild, Ftrue) H6).
      destruct H7 as [n [Hn Hx]]; subst.
      specialize (H4 n ltac:(lia)).
      simpl in H4.
      destruct H4 as [ Heql [Heqp Heqt]].
      rewrite Forall_forall in H0.
      eapply H0. 2: apply Heqt.
      * wf_tac.
      * unfold add_vals.
        intros. rewrite in_app_iff in H4.
        destruct H4; auto.
        assert (Heqp':=Heqp).
        apply alpha_equiv_p_fv_full in Heqp. rewrite Heqp in H4.
        rewrite in_combine_iff in H4; wf_tac.
        destruct H4 as [i [Hi Hxy]].
        specialize (Hxy vs_d vs_d). inversion Hxy; subst. clear Hxy.
        rewrite map_nth_inbound with(d2:=vs_d); auto.
        rewrite mk_fun_vars_eq_full; auto.
        wf_tac.
      * rewrite Forall_forall in H11. apply H11. wf_tac.
Qed. 

Definition alpha_equiv_t_type (t: term) := proj1 (alpha_equiv_type t Ftrue).
Definition alpha_equiv_f_valid (f: formula) := proj2 (alpha_equiv_type tm_d f).

Corollary a_equiv_t_type (t1 t2: term) (ty: vty):
  a_equiv_t t1 t2 ->
  term_has_type sigma t1 ty ->
  term_has_type sigma t2 ty.
Proof.
  unfold a_equiv_t. intros Heq.
  apply alpha_equiv_t_type with(vars:=nil); auto.
  simpl; intros ? ? [].
Qed.

Corollary a_equiv_f_valid (f1 f2: formula):
  a_equiv_f f1 f2 ->
  valid_formula sigma f1 ->
  valid_formula sigma f2.
Proof.
  unfold a_equiv_f. intros Heq.
  apply alpha_equiv_f_valid with(vars:=nil); auto.
  simpl; intros ? ? [].
Qed.

(*Now, let's prove transitivity*)

(*The pattern case is easy, but its use relies on the lengths of
  the free vars lists being the same (in the map assumption)
  which comes from [alpha_equiv_p_fv_len_full]*)
Lemma alpha_equiv_p_trans (p1 p2 p3: pattern)
  (v1 v2: list (vsymbol * vsymbol))
  (Hl: map snd v1 = map fst v2)
  (Heq1: alpha_equiv_p v1 p1 p2)
  (Heq2: alpha_equiv_p v2 p2 p3):
  alpha_equiv_p (alist_trans v1 v2) p1 p3.
Proof.
  generalize dependent p3.
  generalize dependent p2. 
  induction p1; simpl; intros;
  destruct p2; try solve[inversion Heq1];
  destruct p3; try solve[inversion Heq2];
  simpl in Heq2; revert Heq1 Heq2;
  bool_to_prop; intros; destruct_all;
  repeat simpl_sumbool; simpl; auto.
  - split; [simpl_sumbool; simpl; rewrite e0 in n; contradiction | ].
    apply in_firstb_trans with(y:=v0); auto.
  - apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. split_all; auto.
    rename l0 into ps2.
    rename l2 into ps3.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1;
    destruct ps3; inversion Hlen2; auto.
    revert H1 H5; bool_to_prop; intros; destruct_all.
    inversion H; subst.
    split.
    + apply (H8 p); auto.
    + apply (IHps H9 ps2); auto.
  - split; [apply (IHp1_1 p2_1) | apply (IHp1_2 p2_2)]; auto.
  - split_all; [simpl_sumbool; simpl; rewrite e0 in n; contradiction |
    | apply (IHp1 p2); auto].
    apply in_firstb_trans with(y:=v0); auto.
Qed.

Lemma combine_alist_trans l1 l2 l3:
  length l1 = length l2 ->
  length l2 = length l3 ->
  alist_trans (combine l1 l2) (combine l2 l3) = combine l1 l3.
Proof.
  intros Hlen1 Hlen2.
  generalize dependent l3.
  generalize dependent l2.
  induction l1; simpl; intros; destruct l2; inversion Hlen1;
  destruct l3; inversion Hlen2; auto; simpl.
  f_equal. apply IHl1; auto.
Qed.

Lemma alist_trans_app l1 l2 l3 l4:
  length l1 = length l2 ->
  alist_trans l1 l2 ++ alist_trans l3 l4 =
  alist_trans (l1 ++ l3) (l2 ++ l4).
Proof.
  intros Hlen.
  generalize dependent l2.
  induction l1; simpl; intros;
  destruct l2; inversion Hlen; simpl; auto.
  f_equal. apply IHl1; auto.
Qed.

Lemma alpha_equiv_trans (t: term) (f: formula) :
  (forall t1 t2 (v1 v2: list (vsymbol * vsymbol))
    (Hl: map snd v1 = map fst v2)
    (Heq1: alpha_equiv_t v1 t t1)
    (Heq2: alpha_equiv_t v2 t1 t2),
    alpha_equiv_t (alist_trans v1 v2) t t2) /\
  (forall f1 f2 (v1 v2: list (vsymbol * vsymbol))
    (Hl: map snd v1 = map fst v2)
    (Heq1: alpha_equiv_f v1 f f1)
    (Heq2: alpha_equiv_f v2 f1 f2),
    alpha_equiv_f (alist_trans v1 v2) f f2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros.
  - (*Tconst*) 
    destruct t1; try solve[inversion Heq1].
    destruct t2; try solve[inversion Heq2].
    simpl in Heq2.
    destruct (all_dec (c = c0)); auto.
    destruct (all_dec (c0 = c1)); auto.
    subst.
    destruct (all_dec (c1 = c1)); auto.
  - (*Tvar*)
    destruct t1; try solve[inversion Heq1].
    destruct t2; try solve [inversion Heq2].
    simpl in Heq2.
    eapply eq_var_trans.
    apply Hl. apply Heq1. apply Heq2.
  - (*Tfun*)
    destruct t1; try solve[inversion Heq1].
    destruct t2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool; simpl.
    apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. split_all; auto.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent l2.
    generalize dependent l4.
    induction l1; simpl; intros; destruct l2; inversion Hlen1;
    destruct l4; inversion Hlen2; auto.
    revert H5 H1; bool_to_prop; intros; destruct_all.
    inversion H; subst.
    split.
    + apply H8 with(t1:=t); auto.
    + apply IHl1 with(l2:=l2); auto.
  - (*Tlet*)
    destruct t1; try solve[inversion Heq1].
    destruct t2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool.
    split_all.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + apply H with(t1:=t1_1); auto.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto. 
      }
      apply (H0 _ _ _ _ Hmap H5 H2).
  - (*Tif*)
    destruct t0; try solve[inversion Heq1].
    destruct t3; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all.
    split_all; [apply (H f0) | apply (H0 t0_1) | apply (H1 t0_2)]; auto.
  - (*Tmatch*)
    destruct t1; try solve[inversion Heq1].
    destruct t2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool.
    apply Nat.eqb_eq in H8, H4.
    split_all; auto.
    + apply (H t1); auto.
    + rewrite H8, H4; apply Nat.eqb_refl.
    + clear H H5 H1.
      rename l into ps2.
      rename l0 into ps3.
      rename H8 into Hlen1.
      rename H4 into Hlen2.
      generalize dependent ps2.
      generalize dependent ps3.
      induction ps; intros;
      destruct ps2; inversion Hlen1;
      destruct ps3; inversion Hlen2; auto.
      destruct a as [p1 tm1].
      destruct p as [p2 tm2].
      destruct p0 as [p3 tm3].
      revert H6 H2; bool_to_prop; intros;
      destruct_all.
      assert (Hlenp1: length (pat_fv p1) = length (pat_fv p2)) by
        (apply alpha_equiv_p_fv_len_full; auto).
      assert (Hlenp2: length (pat_fv p2) = length (pat_fv p3)) by
        (apply alpha_equiv_p_fv_len_full; auto).
      inversion H0; subst.
      split_all.
      * rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
        apply alpha_equiv_p_trans with(p2:=p2); auto.
        rewrite map_snd_combine, map_fst_combine; auto.
      * unfold add_vals.
        rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
        rewrite alist_trans_app.
        -- apply H10 with(t1:=tm2); auto.
          rewrite !map_app, Hl, map_fst_combine, map_snd_combine; auto.
        -- rewrite !combine_length. lia.
      * apply IHps with(ps2:=ps2); auto.
  - (*Teps*)
    destruct t1; try solve[inversion Heq1].
    destruct t2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool.
    split.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto.
      }
      apply (H _ _ _ _ Hmap H3 H1).
  - (*Fpred*)
    destruct f1; try solve[inversion Heq1].
    destruct f2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool; simpl.
    apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. split_all; auto.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent l2.
    generalize dependent l0.
    induction tms; simpl; intros; destruct l0; inversion Hlen1;
    destruct l2; inversion Hlen2; auto.
    revert H5 H1; bool_to_prop; intros; destruct_all.
    inversion H; subst.
    split.
    + apply H8 with (t1:=t); auto.
    + apply IHtms with(l0:=l0); auto.
  - (*Fquant*)
    destruct f1; try solve[inversion Heq1].
    destruct f2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool.
    split_all; auto.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto.
      }
      apply (H _ _ _ _ Hmap H4 H1).
  - (*Feq*)
    destruct f1; try solve[inversion Heq1].
    destruct f2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool.
    split_all; auto; [apply (H t) | apply (H0 t0)]; auto.
  - (*Fbinop*)
    destruct f0; try solve[inversion Heq1].
    destruct f3; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool.
    split_all; auto; [apply (H f0_1) | apply (H0 f0_2)]; auto.
  - (*Fnot*)
    destruct f1; try solve[inversion Heq1].
    destruct f2; try solve[inversion Heq2].
    simpl in Heq2.
    apply (H f1); auto.
  - (*Ftrue*)
    destruct f1; try solve[inversion Heq1].
    destruct f2; try solve[inversion Heq2].
    auto.
  - (*Ffalse*) 
    destruct f1; try solve[inversion Heq1].
    destruct f2; try solve[inversion Heq2].
    auto.
  - (*Flet*)
    destruct f1; try solve[inversion Heq1].
    destruct f2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool.
    split_all.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + apply (H t); auto.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto. 
      }
      apply (H0 _ _ _ _ Hmap H5 H2).
  - (*Tif*)
    destruct f0; try solve[inversion Heq1].
    destruct f4; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all.
    split_all; [apply (H f0_1) | apply (H0 f0_2) | apply (H1 f0_3)]; auto.
  - (*Tmatch*)
    destruct f1; try solve[inversion Heq1].
    destruct f2; try solve[inversion Heq2].
    simpl in Heq2.
    revert Heq1 Heq2; bool_to_prop; intros;
    destruct_all; repeat simpl_sumbool.
    apply Nat.eqb_eq in H8, H4.
    split_all; auto.
    + apply (H t); auto.
    + rewrite H8, H4; apply Nat.eqb_refl.
    + clear H H5 H1.
      rename l into ps2.
      rename l0 into ps3.
      rename H8 into Hlen1.
      rename H4 into Hlen2.
      generalize dependent ps2.
      generalize dependent ps3.
      induction ps; intros;
      destruct ps2; inversion Hlen1;
      destruct ps3; inversion Hlen2; auto.
      destruct a as [p1 tm1].
      destruct p as [p2 tm2].
      destruct p0 as [p3 tm3].
      revert H6 H2; bool_to_prop; intros;
      destruct_all.
      assert (Hlenp1: length (pat_fv p1) = length (pat_fv p2)) by
        (apply alpha_equiv_p_fv_len_full; auto).
      assert (Hlenp2: length (pat_fv p2) = length (pat_fv p3)) by
        (apply alpha_equiv_p_fv_len_full; auto).
      inversion H0; subst.
      split_all.
      * rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
        apply alpha_equiv_p_trans with(p2:=p2); auto.
        rewrite map_snd_combine, map_fst_combine; auto.
      * unfold add_vals.
        rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
        rewrite alist_trans_app.
        -- apply (H10 tm2); auto.
          rewrite !map_app, Hl, map_fst_combine, map_snd_combine; auto.
        -- rewrite !combine_length. lia.
      * apply IHps with(ps2:=ps2); auto.
Qed.

Definition alpha_equiv_t_trans (t: term) :=
  proj1 (alpha_equiv_trans t Ftrue).
Definition alpha_equiv_f_trans (f: formula) :=
  proj2 (alpha_equiv_trans tm_d f).

Corollary a_equiv_t_trans (t1 t2 t3: term):
  a_equiv_t t1 t2 ->
  a_equiv_t t2 t3 ->
  a_equiv_t t1 t3.
Proof.
  unfold a_equiv_t. apply alpha_equiv_t_trans; reflexivity.
Qed.

Corollary a_equiv_f_trans (f1 f2 f3: formula):
  a_equiv_f f1 f2 ->
  a_equiv_f f2 f3 ->
  a_equiv_f f1 f3.
Proof.
  unfold a_equiv_f. apply alpha_equiv_f_trans; reflexivity.
Qed.

(*Congruences (TODO)*)

Lemma alpha_tlet_congr v1 tm1 tm2 tm3 tm4:
  a_equiv_t tm1 tm3 ->
  a_equiv_t tm2 tm4 ->
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm3 v1 tm4).
Proof.
  unfold a_equiv_t; simpl; intros.
  rewrite H; simpl_bool.
  destruct (vty_eq_dec (snd v1) (snd v1)); auto.
  simpl.
  rewrite (alpha_equiv_t_redundant _ _ v1 nil nil); auto.
Qed.

(*And from transitivity:*)
Lemma alpha_convert_tlet':
forall v1 v2 : vsymbol,
  snd v1 = snd v2 ->
  forall tm1 tm2 tm3 tm4 : term,
  ~ In v2 (bnd_t tm4) ->
  ~ In v2 (term_fv tm4) ->
  a_equiv_t tm1 tm3 ->
  a_equiv_t tm2 tm4 ->
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm3 v2 (sub_t v1 v2 tm4)).
Proof.
  intros.
  eapply a_equiv_t_trans.
  2: apply alpha_convert_tlet; auto.
  apply alpha_tlet_congr; auto.
Qed.

(*Next: do all congruence lemmas, then see what
  case we need for match.
  With these, we should not ever have to unfold the
  definition of alpha equivalence in future lemmas
  (ie: to prove that substitution function is alpha equiv)*)

Lemma alpha_tfun_congr f tys tms1 tms2:
  length tms1 = length tms2 ->
  Forall (fun x => a_equiv_t (fst x) (snd x)) (combine tms1 tms2) ->
  a_equiv_t (Tfun f tys tms1) (Tfun f tys tms2).
Proof.
  unfold a_equiv_t. simpl. intros Hlen Hall.
  bool_to_prop; split_all; try simpl_sumbool; 
    [rewrite Hlen; apply Nat.eqb_refl |].
  generalize dependent tms2.
  induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto.
  inversion Hall; subst.
  bool_to_prop; split; auto.
Qed.


(*TODO: do corollaries, prove transitivity*)

(*TODO: start with match*)
(*TODO: see what we need*)
(*
Lemma alpha_convert_tmatch_single
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (t: term) ty
  (ps: list (pattern * term)):
  a_equiv_t (Tmatch t ty ps) (Tmatch t ty (map (fun x => (sub_p v1 v2 (fst x), sub_t v1 v2 (snd x))) ps)).
Proof.
  unfold a_equiv_t. simpl.
  rewrite map_length.
  (*TODO: start here*)
  rewrite length_map.
  simpl.
  (Hbnd: ~In v2 (bnd_f f2))
  (Hfree: ~In v2 (form_fv f2)):
  a_equiv_f (Flet t1 v1 f2) (Flet t1 v2 (sub_f v1 v2 f2)).
*)

(*Now we want to define a function to rename bound variables to unique
  values such that terms and formulas have no duplicate bound
  variables and no clashes between free and bound variable names.
  This makes many transformations easier.*)

Section Sub.
(*Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma).*)
  

(*Alpha substitute for patterns only in the given term/formula*)
(*Here, we need to keep the dependencies between pattern variables
  (as, for instance, an "or" pattern should have the same free
  vars on each side, so we use an association list)*)
  (*
  Fixpoint alpha_p_aux {A: Type} (sub: vsymbol -> vsymbol -> A -> A) 
  (p: pattern) (x: A) (l: list (vsymbol * string)) : (pattern * A) :=
  match p with
  | Pvar v => 
    match (get_assoc_list vsymbol_eq_dec l v) with
    | Some str => 
      let v' := (str, snd v) in
      (Pvar v', sub v v' x)
    | None => (p, x)
    end
  | Pwild => (p, x)
  | Por p1 p2 =>
    (*NOTE: must have same free vars*)
    let t1 := alpha_p_aux sub p1 x l in
    let t2 := alpha_p_aux sub p2 x l in
    (Por (fst t1) (fst t2), (snd t2))
  | Pbind p1 v =>
    match (get_assoc_list vsymbol_eq_dec l v) with
    | Some str =>
      let v' := (str, snd v) in
      let t := (alpha_p_aux sub p1 x l) in
      (Pbind (fst t) v', sub v v' (snd t))
    | None => (p, x)
    end
  | Pconstr f tys pats =>
    let t := 
    ((fix alpha_ps_aux (l1: list pattern) (y: A) : list pattern * A :=
      match l1 with
      | ph :: pt =>
        let t1 := alpha_p_aux sub ph y l in
        let t2 := alpha_ps_aux pt (snd t1) in
        ((fst t1) :: (fst t2), (snd t2))
      | nil => (nil, y)
      end) pats x) in
    (Pconstr f tys (fst t), (snd t))
    end.
(*Proving this correct will not be too fun, but let's see*)
*)

Definition mk_fun_str (l: list vsymbol) (l2: list string) :
  vsymbol -> vsymbol :=
  mk_fun l (combine l2 (map snd l)).

Fixpoint alpha_t_aux (t: term) (l: list string) {struct t} : term :=
  (*We only care about the bound variable and inductive cases*)
  match t with
  | Tlet t1 x t2 => 
    match l with
    | str :: tl =>
      let (l1, l2) := split tl (length (bnd_t t1)) in 
      Tlet (alpha_t_aux t1 l1) (str, snd x) (sub_t x (str, snd x) 
      (alpha_t_aux t2 l2))
    | _ => t
    end
  | Tfun fs tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (bnd_t tm))*)
    let lens := map (fun tm => length (bnd_t tm)) tms in
    let l_split := split_lens l lens in
    Tfun fs tys (map2 (fun (tm: term) (l': list string) =>
    alpha_t_aux tm l') tms l_split)
  | Tif f t1 t2 =>
    let f_sz := length (bnd_f f) in
    let t1_sz := length (bnd_t t1) in
    let (l1, lrest) := split l f_sz in
    let (l2, l3) := split lrest t1_sz in
    Tif (alpha_f_aux f l1) 
      (alpha_t_aux t1 l2)
      (alpha_t_aux t2 l3)
  | Tmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (pat_fv (fst x)) + 
      length (bnd_t (snd x))) ps in
    let t1_sz := length (bnd_t t1) in
    let (l1, l2) := split l (t1_sz) in
    let l_split := split_lens l2 lens in
    
    Tmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * term) (strs: list string) =>
        let p_sz := length (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let t2 := alpha_t_aux (snd x) l2 in
        let vars := combine (pat_fv (fst x)) l1 in
        (map_pat (mk_fun_str (pat_fv (fst x)) l1) (fst x), sub_ts vars t2)) ps l_split)
        (*(sub_ps vars (fst x), sub_ts vars t2)) ps l_split)*)
  | Teps f v =>
    match l with
    | nil => t
    | str :: tl =>
      let v' := (str, snd v) in
      Teps (sub_f v v' (alpha_f_aux f tl)) v'
    end
  | _ => t (*no other bound variables/recursive cases*)
  end
with alpha_f_aux (f: formula) (l: list string) {struct f} : formula :=
  match f with
  | Fpred ps tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (bnd_t tm))*)
    let lens := map (fun tm => length (bnd_t tm)) tms in
    let l_split := split_lens l lens in
    Fpred ps tys (map2 (fun (t: term) (l': list string) =>
      alpha_t_aux t l') tms l_split)
  | Fquant q v f1 =>
      match l with
      | str :: tl =>
        let v' := (str, snd v) in
        Fquant q v' (sub_f v v' (alpha_f_aux f1 tl))
      | _ => f
      end
  | Feq ty t1 t2 =>
    let t_sz := length (bnd_t t1) in
    let (l1, l2) := split l t_sz in
    Feq ty (alpha_t_aux t1 l1)
      (alpha_t_aux t2 l2)
  | Fbinop b f1 f2 =>
    let f_sz := length (bnd_f f1) in
    let (l1, l2) := split l f_sz in
    Fbinop b (alpha_f_aux f1 l1)
      (alpha_f_aux f2 l2)
  | Fnot f1 =>
    Fnot (alpha_f_aux f1 l)
  | Flet t v f1 =>
    match l with
    | str :: tl =>
      let (l1, l2) := split tl (length (bnd_t t)) in 
      Flet (alpha_t_aux t l1) (str, snd v) (sub_f v (str, snd v) 
      (alpha_f_aux f1 l2))
    | _ => f
    end
  | Fif f1 f2 f3 =>
    let f1_sz := length (bnd_f f1) in
    let f2_sz := length (bnd_f f2) in
    let (l1, lrest) := split l f1_sz in
    let (l2, l3) := split lrest f2_sz in
    Fif (alpha_f_aux f1 l1) 
      (alpha_f_aux f2 l2)
      (alpha_f_aux f3 l3)
  | Fmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (pat_fv (fst x)) + 
    length (bnd_f (snd x))) ps in
    let t1_sz := length (bnd_t t1) in
    let (l1, l2) := split l t1_sz in
    let l_split := split_lens l2 lens in
    
    Fmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * formula) (strs: list string) =>
        let p_sz := length (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let f2 := alpha_f_aux (snd x) l2 in
        let vars := combine (pat_fv (fst x)) l1 in
        (map_pat (mk_fun_str (pat_fv (fst x)) l1) (fst x), sub_fs vars f2)) ps l_split)
        (*(sub_ps vars (fst x), sub_fs vars f2)) ps l_split)*)
  | _ => f (*No other bound/recursive cases*)
  end.
(*Prove correctness: 3 lemmas
  1. results in wf term/fmla
  2. preserves interp
  3. has same "shape" (and corollaries: ind form, positive, etc)*)

(*TODO: move*)


(*Need free var lemmas for [sub_ts]. These are all easy corollaries
  of the appropriate result for [sub_t]*)

(*We prove iterated version of the free vars lemmas for
  sub_ts and sub_fs. We do it generically first so we prove both
  at once*)
Section IterFvar.

  Context {A: Type}.
  Variable sub: vsymbol -> vsymbol -> A -> A.
  Variable free_in: vsymbol -> A -> bool.
  Variable sub_notin: forall (t: A) (x y: vsymbol), x <> y ->
    free_in x (sub x y t) = false.
  Variable sub_diff: forall (t: A) (x y z: vsymbol),
    z <> x -> z <> y -> free_in z (sub x y t) = free_in z t.
  Notation subs := (sub_mult sub).
  (*For bound vars*)
  Variable bnd: A -> list vsymbol.
  Variable bnd_sub : forall (t: A) (x y: vsymbol),
    bnd (sub x y t) = bnd t.
  
  (*The iterated version of [sub_fv_notin]. Awkward to state so
    that we can prove term and formula versions together*)
  Lemma sub_mult_fv_notin
    (vars: list (vsymbol * string)) (t: A)
    (Hn: NoDup (map fst vars))
    (Huniq: forall x, In x (map fst vars) -> ~ In (fst x) (map snd vars)):
    forall x, In x (map fst vars) -> free_in x (subs vars t) = false.
  Proof.
    induction vars; simpl; intros. destruct H.
    destruct H; subst.
    - rewrite sub_notin; auto.
      destruct a as[v str]; destruct v as [nm ty]; simpl in *; intro C;
      inversion C; subst.
      apply (Huniq (str, ty)); simpl; triv.
    - inversion Hn; subst. 
      rewrite sub_diff; auto.
      + apply IHvars; auto.
        intros. intro C.
        apply (Huniq x0); simpl; triv.
      + intro C; subst. contradiction.
      + destruct a; destruct v; simpl in *; intro C; inversion C; subst.
        apply (Huniq (s, v)); triv.
  Qed.
  
  Lemma sub_mult_fv_diff (vars: list (vsymbol * string)) (t: A):
    forall x, ~ In x (map fst vars) -> 
      ~ In x (combine (map snd vars) (map snd (map fst vars))) ->
    free_in x (subs vars t) = free_in x t.
  Proof.
    intros x Hn1 Hn2.
    induction vars; simpl; auto.
    simpl in Hn1, Hn2. not_or Hn.
    rewrite sub_diff; auto.
  Qed.

  Lemma bnd_subs vars (t: A):
    bnd (subs vars t) = bnd t.
  Proof.
    induction vars; simpl; auto.
    rewrite bnd_sub; assumption.
  Qed.
  
End IterFvar.
  
Definition sub_ts_fv_notin := sub_mult_fv_notin _ _ 
  sub_t_fv_notin sub_t_fv_diff.
Definition sub_fs_fv_notin := sub_mult_fv_notin _ _
  sub_f_fv_notin sub_f_fv_diff.
Definition sub_ts_fv_diff := sub_mult_fv_diff _ _
  sub_t_fv_diff.
Definition sub_fs_fv_diff := sub_mult_fv_diff _ _
  sub_f_fv_diff.
Definition bnd_sub_ts := bnd_subs _ _ bnd_sub_t.
Definition bnd_sub_fs := bnd_subs _ _ bnd_sub_f.


Lemma NoDup_combine_l {A B: Type} (l1: list A) (l2: list B):
  NoDup l1 ->
  NoDup (combine l1 l2).
Proof.
  revert l2. induction l1; simpl; intros. constructor.
  destruct l2. constructor.
  inversion H; subst.
  constructor; auto.
  intro Hin.
  apply in_combine_l in Hin. contradiction.
Qed.

Lemma map_pat_str_fv (strs: list string) (p: pattern) :
  length (pat_fv p) = length strs ->
  NoDup strs ->
  pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p) = map (mk_fun_str (pat_fv p) strs) (pat_fv p).
Proof.
  intros.
  apply map_pat_free_vars. intros.
  unfold mk_fun_str in H3.
  apply mk_fun_inj in H3; auto.
  - apply NoDup_pat_fv.
  - apply NoDup_combine_l; auto.
  - rewrite H.
    unfold vsymbol. (*otherwise rewrite fails*)
    rewrite combine_length, map_length, <- H, Nat.min_id.
    apply Nat.le_refl.
Qed.

Lemma in_map_pat_str_fv_iff (strs: list string) (p: pattern):
  length (pat_fv p) = length strs ->
  NoDup strs ->
  forall x, In x (pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p)) <->
    In x (combine strs (map snd (pat_fv p))).
Proof.
  intros. rewrite map_pat_str_fv; auto.
  rewrite in_map_iff.
  split; intros.
  - destruct H1 as [y [Hx Hiny]]; subst.
    unfold mk_fun_str.
    pose proof (mk_fun_in (pat_fv p) (combine strs (map snd (pat_fv p))) y).
    unfold vsymbol in H, H1.
    rewrite H, combine_length, map_length, <- H, Nat.min_id in H1.
    apply H1; auto.
  - unfold vsymbol in H1. 
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    specialize (Hx EmptyString vty_int). 
    unfold mk_fun_str.
    exists (nth i (pat_fv p) vs_d).
    split; wf_tac.
    rewrite mk_fun_nth with(d2:=vs_d); unfold vsymbol in *; wf_tac.
    + unfold vs_d.
      rewrite combine_nth; wf_tac.
      subst. f_equal; auto. apply nth_indep; auto.
    + rewrite combine_length, map_length. lia.
Qed.

Corollary in_map_pat_str_fv (strs: list string) (p: pattern):
  length (pat_fv p) = length strs ->
  NoDup strs ->
  forall x, In x (pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p)) ->
    In (fst x) strs.
Proof.
  intros. apply in_map_pat_str_fv_iff in H1; auto.
  unfold vsymbol in H1.
  rewrite in_combine_iff in H1; wf_tac.
  destruct H1 as [i [Hi Hx]].
  specialize (Hx EmptyString vty_int); subst; simpl.
  wf_tac.
Qed.

(*The bound variables of our substitution are unique
  and all from the original list.
  TODO: automate this proof more, it is very repetitive*)
Lemma alpha_aux_wf_aux (t: term) (f: formula) :
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_t t) ->
    NoDup (bnd_t (alpha_t_aux t l)) /\
    (forall x, In x (bnd_t (alpha_t_aux t l)) -> In (fst x) l)) /\
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_f f) ->
    NoDup (bnd_f (alpha_f_aux f l)) /\
    (forall x, In x (bnd_f (alpha_f_aux f l)) -> In (fst x) l)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto.
  - split; [constructor | intros x []]. 
  - split; [constructor | intros x []].
  - (*Tfun case*) 
    split.
    + rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l0 (map (fun t => length (bnd_t t)) l1)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst x)); wf_tac.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l0 (map (fun t => length (bnd_t t)) l1));
      [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Tlet case*)
    destruct l; inversion H2; simpl.
    inversion H1; subst.
    split.
    + constructor.
      * (*TODO: automate the "In" part*) 
        intro Hin.
        apply in_app_or in Hin.
        destruct Hin.
        -- apply H in H3; wf_tac.
        -- rewrite bnd_sub_t in H3.
          apply H0 in H3; wf_tac. 
      * rewrite NoDup_app_iff'.
        split_all.
        -- apply H; wf_tac.
        -- rewrite bnd_sub_t. apply H0; wf_tac.
        -- intros x.
          rewrite bnd_sub_t.
          intros [Hinx1 Hinx2].
          apply H in Hinx1; wf_tac.
          apply H0 in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); auto.
    + intros x [Hx | Hinx]; subst;[left; auto|].
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite bnd_sub_t in Hinx. apply H0 in Hinx; wf_tac.
  - (*Tif case*)
    split.
    + rewrite !NoDup_app_iff'.
      split_all.
      * apply H; wf_tac.
      * apply H0; wf_tac.
      * apply H1; wf_tac.
      * intros x [Hinx1 Hinx2].
        apply H0 in Hinx1; wf_tac.
        apply H1 in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac. 
      * intros x [Hinx1 Hinx2].
        apply H in Hinx1; wf_tac.
        apply in_app_or in Hinx2. destruct Hinx2.
        -- apply H0 in H4; wf_tac.
          apply (nodup_firstn_skipn Hinx1); wf_tac. 
        -- apply H1 in H4; wf_tac.
          apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      repeat (apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx]).
      * apply H in Hinx; wf_tac.
      * apply H0 in Hinx; wf_tac.
      * apply H1 in Hinx; wf_tac. 
  - (*Tmatch case*)
    assert (Hsum: sum (map
        (fun x : pattern * term =>
        Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
        ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
          wf_tac. rewrite H2,length_concat, 
        map_map, Nat.add_comm, Nat.add_sub. f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    split.
    + rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, tm_d) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ simpl. rewrite bnd_sub_ts.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x. simpl.
            rewrite bnd_sub_ts. 
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply in_map_pat_str_fv in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, tm_d)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          apply in_app_or in Hini1, Hini2.
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply in_map_pat_str_fv in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2.
              rewrite bnd_sub_ts in Hini2.
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ simpl in Hini1. 
            rewrite bnd_sub_ts in Hini1.
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2.
              rewrite bnd_sub_ts in Hini2.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
      * intros x.
        rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
        apply H in Hinx1; wf_tac.
        rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        (*And now we have to show these are distinct, will be similar*)
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx2 | Hinx2].
        -- apply in_map_pat_str_fv in Hinx2; wf_tac.
          revert Hinx2; wf_tac; intros.
          apply In_firstn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- simpl in Hinx2.
          rewrite bnd_sub_ts in Hinx2.
          rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
          apply In_skipn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - TODO very similar to previous*)
      intros x Hinx.
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite in_concat in Hinx.
        destruct Hinx as [l1 [Hinl1 Hinxl1]].
        rewrite in_map_iff in Hinl1.
        destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with (d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx | Hinx].
        -- apply in_map_pat_str_fv in Hinx; wf_tac.
          revert Hinx; wf_tac; intros.
          apply in_split_lens_ith in Hinx; wf_tac.
        -- simpl in Hinx.
          rewrite bnd_sub_ts in Hinx.
          rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
          apply In_skipn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
  - (*Epsilon case*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_f.
    split.
    + constructor; [|apply H; wf_tac].
      intro Hin. apply H in Hin; wf_tac.
    + intros. destruct H2; subst; [left; auto | right].
      apply H in H2; wf_tac.
  - (*Fpred case - same as Tfun*)
    split.
    + rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l (map (fun t => length (bnd_t t)) tms)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst x)); wf_tac.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l (map (fun t => length (bnd_t t)) tms));
        [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Fquant*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_f.
    split.
    + constructor; [intro C; apply H in C |apply H]; wf_tac.
    + intros. destruct H2; subst;[left | right]; auto.
      apply H in H2; wf_tac.
  - (*Feq*)
    split.
    + rewrite NoDup_app_iff'; split_all;[apply H | apply H0 |]; wf_tac.
      intros x [Hinx1 Hinx2].
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx. destruct Hinx as [Hinx | Hinx]; 
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*Fbinop*)
    split.
    + rewrite NoDup_app_iff'; split_all;[apply H|apply H0|]; wf_tac.
      intros x [Hinx1 Hinx2].
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*trivial*)
    split;[constructor | intros x []].
  - split;[constructor | intros x []].
  - (*Flet*)
    destruct l; inversion H2; subst.
    inversion H1; subst; simpl; rewrite bnd_sub_f.
    split.
    + constructor.
      * intro C. apply in_app_or in C.
        destruct C as [Hins | Hins];
        [apply H in Hins | apply H0 in Hins]; wf_tac.
      * rewrite NoDup_app_iff'; split_all; [apply H | apply H0 |];wf_tac.
        intros x [Hinx1 Hinx2]; apply H in Hinx1; apply H0 in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x [Hx | Hinx]; subst;[left | right]; auto.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx]; wf_tac.
  - (*Fif*)
    split.
    + rewrite !NoDup_app_iff'; split_all;
      [apply H | apply H0 | apply H1 | |]; wf_tac;
      intros x; [| rewrite in_app_iff];
      intros [Hinx1 Hinx2];[|destruct Hinx2 as [Hinx2 | Hinx2]];
      [apply H0 in Hinx1; apply H1 in Hinx2 | apply H in Hinx1; 
        apply H0 in Hinx2 | apply H in Hinx1; apply H1 in Hinx2]; wf_tac;
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x.
      rewrite ! in_app_iff; intros [Hinx | [Hinx | Hinx]];
      [apply H in Hinx | apply H0 in Hinx | apply H1 in Hinx]; wf_tac.
  - (*Fmatch case - very similar to Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite H2,length_concat, 
      map_map, Nat.add_comm, Nat.add_sub. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    split.
    + rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, Ftrue) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ simpl. rewrite bnd_sub_fs.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x.
            simpl. rewrite bnd_sub_fs.
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply in_map_pat_str_fv in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, Ftrue)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          apply in_app_or in Hini1, Hini2.
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply in_map_pat_str_fv in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2; rewrite bnd_sub_fs in Hini2. 
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ simpl in Hini1; rewrite bnd_sub_fs in Hini1. 
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2; rewrite bnd_sub_fs in Hini2. 
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
    * intros x.
      rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
      apply H in Hinx1; wf_tac.
      rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
      subst.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
      destruct Hinp1 as [i [Hi Hp1]]; subst.
      (*And now we have to show these are distinct, will be similar*)
      apply in_app_or in Hinxl1.
      destruct Hinxl1 as [Hinx2 | Hinx2].
      -- apply in_map_pat_str_fv in Hinx2; wf_tac.
        revert Hinx2; wf_tac; intros.
        apply In_firstn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
      -- simpl in Hinx2; rewrite bnd_sub_fs in Hinx2. 
        rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
        apply In_skipn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - TODO very similar to previous*)
    intros x Hinx.
    apply in_app_or in Hinx.
    destruct Hinx as [Hinx | Hinx].
    * apply H in Hinx; wf_tac.
    * rewrite in_concat in Hinx.
      destruct Hinx as [l1 [Hinl1 Hinxl1]].
      rewrite in_map_iff in Hinl1.
      destruct Hinl1 as [p1 [Hl1 Hinp1]].
      subst.
      rewrite in_map2_iff with (d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
      destruct Hinp1 as [i [Hi Hp1]]; subst.
      apply in_app_or in Hinxl1.
      destruct Hinxl1 as [Hinx | Hinx].
      -- apply in_map_pat_str_fv in Hinx; wf_tac.
        revert Hinx; wf_tac; intros.
        apply in_split_lens_ith in Hinx; wf_tac.
      -- simpl in Hinx; rewrite bnd_sub_fs in Hinx. 
        rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
        apply In_skipn in Hinx.
        apply in_split_lens_ith in Hinx; wf_tac.
Qed.

Definition alpha_t_aux_wf (t: term) := proj1 (alpha_aux_wf_aux t Ftrue).
Definition alpha_f_aux_wf (f: formula) := proj2 (alpha_aux_wf_aux tm_d f).

Ltac prove_hyp H :=
  match goal with
  | H: ?P -> ?Q |- _ => let N := fresh in assert (N: P); [|specialize (H N); clear N]
  end.

Ltac prove_hyps n H :=
  match constr:(n) with
  | O => idtac
  | (S ?m) => prove_hyp H; [|prove_hyps m H]
  end.

Ltac vsym_eq2 x y z :=
  let H := fresh in
  assert (H: x = y \/ (x <> y /\ x = z) \/ (x <> y /\ x <> z)) by
  (vsym_eq x y; right; vsym_eq x z);
  destruct H as [? | [[? ?]|[? ?]]].

(*A big lemma we want: the free vars of [alpha_t_aux] and
  [alpha_f_aux] are the same as those of the original terms.
  This is very hard to prove, though very intuitive*)
Lemma alpha_aux_fv (t: term) (f: formula) :
  (forall (l: list string)
    (Hnodupl: NoDup l)
    (Hlen: length l = length (bnd_t t))
    (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
    forall x,
    free_in_t x (alpha_t_aux t l) = free_in_t x t) /\
  (forall (l: list string)  
    (Hnodupl: NoDup l)
    (Hlen: length l = length (bnd_f f))
    (Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
    forall x,
    free_in_f x (alpha_f_aux f l) = free_in_f x f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros; try reflexivity.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H0. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d).
    subst; simpl. rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac; intros y Hiny C; apply in_split_lens_ith in Hiny; wf_tac.
    + apply (Hfree y); simpl_set; auto.
      exists (nth i l1 tm_d). split; wf_tac.
    + apply (Hbnd y); auto. rewrite in_concat.
      exists (bnd_t (nth i l1 tm_d)). split; wf_tac.
  - (*Let - this case is complicated because we are binding variables*) 
    destruct l; inversion Hlen.
    simpl. inversion Hnodupl; subst.
    rewrite H; wf_tac; try(intros y Hiny C); [|apply (Hfree y) | apply (Hbnd y)];
    try(simpl; right; wf_tac); [|simpl_set; triv].
    f_equal.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H0 (skipn (Datatypes.length (bnd_t tm1)) l)).
    prove_hyps 4 H0; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    [simpl_set; right; split; auto; intro Heq; subst;
      apply (Hbnd v); [right; wf_tac | left; auto]
    | ].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_t_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_t_fv_in; auto.
      * rewrite !H0.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_t_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_t_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_t_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H0.
  - (*If case - hypotheses for IH's are annoying *)
    rewrite H, H0, H1; wf_tac; intros y Hiny C;
    [apply (Hfree y) | apply (Hbnd y) | apply (Hfree y) | apply (Hbnd y) |
    apply (Hfree y) | apply (Hbnd y)];
    try(apply (Hfree y)); try(apply (Hbnd y));
    try (apply In_skipn in Hiny); try (apply In_firstn in Hiny);
    wf_tac; simpl_set; try (rewrite !in_app_iff); triv.
  - (*Match case - let's see*)
    specialize (H (firstn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H; wf_tac; try(intros y Hiny C);
    [apply (Hfree y) | apply (Hbnd y) |]; wf_tac;
    [simpl_set; triv | ].
    rewrite H. f_equal.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, tm_d) (Pwild, tm_d)).
    subst; simpl.
    rewrite map2_nth with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
    assert (Hsum: sum
    (map
       (fun x0 : pattern * term =>
        Datatypes.length (pat_fv (fst x0)) + Datatypes.length (bnd_t (snd x0)))
       ps) = Datatypes.length l - Datatypes.length (bnd_t tm)). {
      rewrite Hlen, length_concat, map_map, Nat.add_comm, Nat.add_sub.
      f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    match goal with
    | |- context [in_bool ?e ?x ?l] => destruct (in_bool_spec e x l)
    end; simpl.
    + (*If x is in the pattern free vars, then it is in l*)
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl; auto.
      symmetry. apply free_in_t_negb. intro Hinfree.
      simpl in i0.
      apply in_map_pat_str_fv in i0; wf_tac.
      apply In_firstn in i0.
      apply in_split_lens_ith in i0; wf_tac.
      apply (Hfree x); wf_tac. simpl_set.
      right. exists (nth i ps (Pwild, tm_d)).
      split; wf_tac.
      simpl_set. split; auto.
    + (*Otherwise, x not in pattern free vars*)
      (*Need this result in 2 places*)
      assert (Hnotfree: forall x0 : string * vty,
      In (fst x0)
           (nth i
              (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
                 (map
                    (fun x1 : pattern * term =>
                     Datatypes.length (pat_fv (fst x1)) +
                     Datatypes.length (bnd_t (snd x1))) ps)) []) ->
      ~ (In x0 (term_fv (snd (nth i ps (Pwild, tm_d)))) \/
        In x0 (pat_fv (fst (nth i ps (Pwild, tm_d)))))). {
        intros y Hy C.
        apply in_split_lens_ith in Hy; wf_tac.
        (*Do [pat_fv] first*)
        assert (~In y (pat_fv (fst (nth i ps (Pwild, tm_d))))). {
          (*Contradiction: y in l, so not bound in pattern,
            which is same as pattern free var*)
          intro Hnot.
          apply (Hbnd y); wf_tac.
          rewrite in_app_iff. right.
          rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, tm_d))) ++
            bnd_t (snd (nth i ps (Pwild, tm_d)))). split; wf_tac.
          exists (nth i ps (Pwild, tm_d)); split; wf_tac.
        }
        destruct C; try contradiction.
        (*Here, contradicts [Hfree], need [pat_fv result]*)
        apply (Hfree y); simpl_set; wf_tac.
        right. exists (nth i ps (Pwild, tm_d)). split;
        auto; simpl_set; wf_tac. 
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl.
      * apply sub_ts_fv_notin; wf_tac.
        intros y Hiny Hiny2.
        apply In_firstn in Hiny2. apply Hnotfree in Hiny2.
        not_or Hiny. contradiction.
      * simpl in n.
        rewrite sub_ts_fv_diff; wf_tac. 
        -- rewrite H0; wf_tac.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply Hnotfree in Hy. apply Hy; triv.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply in_split_lens_ith in Hy; wf_tac.
            apply (Hbnd y); wf_tac.
            rewrite in_app_iff; right.
            rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, tm_d))) ++
              bnd_t (snd (nth i ps (Pwild, tm_d)))). split; wf_tac.
            exists (nth i ps (Pwild, tm_d)); split; wf_tac.
        -- intro C.
          apply n. simpl.
          apply in_map_pat_str_fv_iff; wf_tac.
  - (*Teps - basically same as let*) 
    destruct l; inversion Hlen. simpl.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    inversion Hnodupl; subst.
    specialize (H l).
    prove_hyps 4 H; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    simpl_set; auto.
    split; auto; intro Heq; subst.
    apply (Hbnd v); [right; wf_tac | left; auto].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H.
        vsym_eq (s, snd v) v. simpl.
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H.
  - (*Fpred*)
    apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H0. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d).
    subst; simpl. rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac; intros y Hiny C; apply in_split_lens_ith in Hiny; wf_tac.
    + apply (Hfree y); simpl_set; auto.
      exists (nth i tms tm_d). split; wf_tac.
    + apply (Hbnd y); auto. rewrite in_concat.
      exists (bnd_t (nth i tms tm_d)). split; wf_tac.
  - (*Fquant -similar to let/eps*)
    destruct l; inversion Hlen.
    inversion Hnodupl;subst.
    simpl.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H l).
    prove_hyps 4 H; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    simpl_set; auto.
    split; auto; intro Heq; subst.
    apply (Hbnd v); [right; wf_tac | left; auto].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H.
  - (*Feq*)
    rewrite H, H0; wf_tac; intros y Hiny C;
    try solve[(apply (Hfree y); wf_tac; simpl_set; triv)];
    apply (Hbnd y); wf_tac; rewrite in_app_iff; triv.
  - (*Fbinop*)
    rewrite H, H0; wf_tac; intros y Hiny C;
    try solve[(apply (Hfree y); wf_tac; simpl_set; triv)];
    apply (Hbnd y); wf_tac; rewrite in_app_iff; triv.
  - (*Flet*)
    destruct l; inversion Hlen.
    simpl. inversion Hnodupl; subst.
    rewrite H; wf_tac; try(intros y Hiny C); [|apply (Hfree y) | apply (Hbnd y)];
    try(simpl; right; wf_tac); [|simpl_set; triv].
    f_equal.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H0 (skipn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H0; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    [simpl_set; right; split; auto; intro Heq; subst;
      apply (Hbnd v); [right; wf_tac | left; auto]
    | ].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H0.
        vsym_eq (s, snd v) v. simpl.
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H0.
  - (*Fif*)
    rewrite H, H0, H1; wf_tac; intros y Hiny C;
    [apply (Hfree y) | apply (Hbnd y) | apply (Hfree y) | apply (Hbnd y) |
    apply (Hfree y) | apply (Hbnd y)];
    try(apply (Hfree y)); try(apply (Hbnd y));
    try (apply In_skipn in Hiny); try (apply In_firstn in Hiny);
    wf_tac; simpl_set; try (rewrite !in_app_iff); triv.
  - (*Fmatch - copied and pasted*)
    specialize (H (firstn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H; wf_tac; try(intros y Hiny C);
    [apply (Hfree y) | apply (Hbnd y) |]; wf_tac;
    [simpl_set; triv | ].
    rewrite H. f_equal.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)).
    subst; simpl.
    rewrite map2_nth with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
    assert (Hsum: sum
    (map
      (fun x0 : pattern * formula =>
        Datatypes.length (pat_fv (fst x0)) + Datatypes.length (bnd_f (snd x0)))
      ps) = Datatypes.length l - Datatypes.length (bnd_t tm)). {
      rewrite Hlen, length_concat, map_map, Nat.add_comm, Nat.add_sub.
      f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    match goal with
    | |- context [in_bool ?e ?x ?l] => destruct (in_bool_spec e x l)
    end; simpl.
    + (*If x is in the pattern free vars, then it is in l*)
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl; auto.
      symmetry. apply free_in_f_negb. intro Hinfree.
      simpl in i0.
      apply in_map_pat_str_fv in i0; wf_tac.
      apply In_firstn in i0.
      apply in_split_lens_ith in i0; wf_tac.
      apply (Hfree x); wf_tac. simpl_set.
      right. exists (nth i ps (Pwild, Ftrue)).
      split; wf_tac.
      simpl_set. split; auto.
    + (*Otherwise, x not in pattern free vars*)
      (*Need this result in 2 places*)
      assert (Hnotfree: forall x0 : string * vty,
      In (fst x0)
          (nth i
              (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
                (map
                    (fun x1 : pattern * formula =>
                    Datatypes.length (pat_fv (fst x1)) +
                    Datatypes.length (bnd_f (snd x1))) ps)) []) ->
      ~ (In x0 (form_fv (snd (nth i ps (Pwild, Ftrue)))) \/
        In x0 (pat_fv (fst (nth i ps (Pwild, Ftrue)))))). {
        intros y Hy C.
        apply in_split_lens_ith in Hy; wf_tac.
        (*Do [pat_fv] first*)
        assert (~In y (pat_fv (fst (nth i ps (Pwild, Ftrue))))). {
          (*Contradiction: y in l, so not bound in pattern,
            which is same as pattern free var*)
          intro Hnot.
          apply (Hbnd y); wf_tac.
          rewrite in_app_iff. right.
          rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, Ftrue))) ++
            bnd_f (snd (nth i ps (Pwild, Ftrue)))). split; wf_tac.
          exists (nth i ps (Pwild, Ftrue)); split; wf_tac.
        }
        destruct C; try contradiction.
        (*Here, contradicts [Hfree], need [pat_fv result]*)
        apply (Hfree y); simpl_set; wf_tac.
        right. exists (nth i ps (Pwild, Ftrue)). split;
        auto; simpl_set; wf_tac. 
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl.
      * (*If x in orig pattern free vars, need to show false*)
        apply sub_fs_fv_notin; wf_tac.
        intros y Hiny Hiny2.
        apply In_firstn in Hiny2. apply Hnotfree in Hiny2.
        not_or Hiny. contradiction.
      * simpl in n.
        rewrite sub_fs_fv_diff; wf_tac. 
        -- rewrite H0; wf_tac.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply Hnotfree in Hy. apply Hy; triv.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply in_split_lens_ith in Hy; wf_tac.
            apply (Hbnd y); wf_tac.
            rewrite in_app_iff; right.
            rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, Ftrue))) ++
              bnd_f (snd (nth i ps (Pwild, Ftrue)))). split; wf_tac.
            exists (nth i ps (Pwild, Ftrue)); split; wf_tac.
        -- intro C.
          apply n. simpl.
          apply in_map_pat_str_fv_iff; wf_tac.
Qed.

Definition alpha_t_aux_fv (t: term) :=
  proj1 (alpha_aux_fv t Ftrue).
Definition alpha_f_aux_fv (f: formula) :=
  proj2 (alpha_aux_fv tm_d f).

Corollary alpha_t_aux_fv' (t: term):
  (forall (l: list string)
  (Hnodupl: NoDup l)
  (Hlen: length l = length (bnd_t t))
  (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
  (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
  forall x, In x (term_fv (alpha_t_aux t l)) <-> In x (term_fv t)).
Proof.
  intros. rewrite <- !free_in_t_spec, alpha_t_aux_fv; auto.
  reflexivity.
Qed. 

Theorem alpha_t_aux_equiv (t: term) (f: formula):
  (forall l
    (Hn: NoDup l)
    (Hlen: length l = length (bnd_t t))
    (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
    a_equiv_t t (alpha_t_aux t l)) /\
  (forall l
    (Hn: NoDup l)
    (Hlen: length l = length (bnd_f f))
    (Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
    length l = length (bnd_f f) ->
    a_equiv_f f (alpha_f_aux f l)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto;
  try solve[apply a_equiv_t_refl].
  - (*Tfun*)
    apply alpha_tfun_congr; wf_tac.
    revert H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; wf_tac.
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d tm_d); subst. simpl.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac.
    + intros. intro C.
      apply in_split_lens_ith in H0; wf_tac.
      apply (Hfree x); wf_tac.
      simpl_set. exists (nth i l1 tm_d). split; wf_tac.
    + intros. intro C.
      apply in_split_lens_ith in H0; wf_tac.
      apply (Hbnd x); wf_tac.
      rewrite in_concat. exists (bnd_t (nth i l1 tm_d)).
      split; wf_tac.
  - (*Tlet*)
    destruct l; inversion Hlen.
    apply alpha_convert_tlet'; wf_tac.
    + intro C.
      inversion Hn; subst.
      apply alpha_t_aux_wf in C; wf_tac.
    + intro C.
      inversion Hn; subst.
      rewrite alpha_t_aux_fv' in C; wf_tac.
      * apply (Hfree (s, snd v)); simpl; simpl_set; auto.
        right. split; auto. intro Heq.
        apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
      * intros x Hinx1 Hinx2. apply (Hfree x); simpl; simpl_set; wf_tac.
        right. split; auto.
        intro Heq; subst.
        apply (Hbnd v); simpl; try triv. right. wf_tac.
      * intros x Hinx1 Hinx2. apply (Hbnd x); simpl; wf_tac.
        right. in_tac.
    + (*ugh, more annoying obligations - need way to automate this*)
      
    
    apply H; wf_tac. apply H0.
    
    
    rewrite in_tac.
      
      
      simpl; try triv.
      triv.

      
      
      Search bnd_t alpha_t_aux.
  
  
  (*TODO: inductive case for fun, pred*) admit.
  - destruct l; inversion Hlen.




(*TODO: see if we need*)
Lemma alpha_p_aux_wf_aux_gen {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    (*NoDup (map snd l) ->*)
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (*NoDup (map fst l) ->*)
    (forall x v, In v (pat_fv (fst (alpha_p_aux sub p x l))) ->
      exists v', In (v', (fst v)) l /\
        In v' (pat_fv p))).
Proof.
  intros l (*Hnodups*) Hfvs (*Hnodupf*).
  induction p; simpl; auto; intros.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
    + simpl in H. destruct H as [Heq | []]; subst; simpl.
      apply get_assoc_list_some in Ha.
      exists v. auto.
    + apply get_assoc_list_none in Ha. simpl in H.
      destruct H as [Heq | []]; subst.
      exfalso. apply Ha. apply (Hfvs v0); auto. simpl; auto.
  - generalize dependent x. induction ps; simpl in *; auto; intros. 
    destruct H0.
    inversion H; subst.
    rewrite union_elts in H0. destruct H0.
    + assert (Hv: exists v', In (v', fst v) l /\ In v' (pat_fv a)). {
        apply H3 with(x:=x); auto. intros. apply Hfvs.
        rewrite union_elts. left; auto.
      }
      destruct Hv as [v' [Hinl Hinv']].
      exists v'. split; auto. rewrite union_elts. left; auto.
    + assert (Hv: exists v' : vsymbol,
        In (v', fst v) l /\ In v' (big_union vsymbol_eq_dec pat_fv ps)). {
        apply IHps with (x:=(snd (alpha_p_aux sub a x l))); auto.
        intros. apply Hfvs. rewrite union_elts. right; auto.
      }
      destruct Hv as [v' [Hinl Hinv']]; subst.
      exists v'. split; auto. rewrite union_elts. right; auto.
  - destruct H.
  - rewrite union_elts in H.
    destruct H.
    + assert (Hv: exists v' : vsymbol, In (v', fst v) l /\ In v' (pat_fv p1)). {
        apply IHp1 with(x:=x); auto. intros. apply Hfvs; simpl;
        rewrite union_elts; left; auto.
      }
      destruct Hv as [v' [Hinl Hinv']].
      exists v'. split; auto. rewrite union_elts. left; auto.
    + assert (Hv: exists v' : vsymbol, In (v', fst v) l /\ In v' (pat_fv p2)). {
        apply IHp2 with(x:=x); auto.
        intros; apply Hfvs; simpl; rewrite union_elts; right; auto.
      } destruct Hv as [v' [Hinl Hinv']]; subst.
      exists v'. split; auto. rewrite union_elts; right; auto. 
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
    + simpl in H. rewrite union_elts in H.
      destruct H as [Hinv | [Heq | []]]; subst.
      * apply IHp with(x:=x) in Hinv.
        destruct Hinv as [v' [Hl Hv']].
        exists v'; split; auto. rewrite union_elts; left; auto.
        intros. apply Hfvs; simpl; rewrite union_elts; left; auto.
      * apply get_assoc_list_some in Ha.
        exists v. split; auto. rewrite union_elts; right; auto.
        left; auto.
    + simpl in H. apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hfvs. simpl. auto.
      rewrite union_elts. right; left; auto.
Qed. 

(*Other direction*)
Lemma alpha_p_aux_wf_aux_gen' {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    NoDup (map fst l) ->
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (forall x d, 
      In x (pat_fv (fst (alpha_p_aux sub p d l))) <->
      exists v str, 
        In (v, str) l /\
        In v (pat_fv p) /\
        snd x = snd v /\
        fst x = str)).
Proof.
  intros l Hnodup Hfvs (*Hnodupf*).
  induction p; simpl; auto; intros.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl; split; intros.
    + destruct H as [Heq | []]; subst; simpl.
      apply get_assoc_list_some in Ha.
      exists v. exists s. split; auto.
    + destruct H as [v1 [str [Hinl [[Heq | []] [Hsnd Hfst]]]]]; subst.
      left. destruct x; simpl in *; subst.
      f_equal. symmetry.
      apply get_assoc_list_some in Ha. 
      apply (nodup_fst_inj Hnodup Hinl Ha).
    + apply get_assoc_list_none in Ha.
      destruct H as [Heq | []]; subst.
      exfalso. apply Ha. apply Hfvs. left; auto.
    + apply get_assoc_list_none in Ha.
      destruct H as [v1 [str [Hinl [[Heq | []] [Hsnd Hfst]]]]]; subst.
      exfalso. apply Ha. rewrite in_map_iff. exists (v1, fst x); auto.
  - generalize dependent d. induction ps; simpl in *; auto; intros; 
    [split; simpl; intros; auto |].
    + destruct H0.
    + destruct H0 as [v1 [str [Hinl [[] _]]]].
    + assert (Hfvs': (forall v : vsymbol,
      In v (big_union vsymbol_eq_dec pat_fv ps) -> In v (map fst l))).
      {
        intros; apply Hfvs; simpl; rewrite union_elts; right; auto.
      } inversion H; subst. split; simpl; intros; auto.  
      rewrite union_elts in H0. inversion H; subst.
      destruct H0.
      * apply H2 in H0; auto.
        destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts; left; auto.
        intros. apply Hfvs. rewrite union_elts. left; auto.
      * specialize (IHps H3 Hfvs' (snd (alpha_p_aux sub a d l))).
        apply IHps in H0; clear IHps.
        destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts. right; auto.
      * destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        rewrite union_elts in Hinv.
        rewrite union_elts.
        destruct Hinv as [Hinv1 | Hinv1]; [left | right].
        -- apply H2; auto. intros; apply Hfvs; simpl; rewrite union_elts;
          left; auto.
          exists v1. exists (fst x). auto.
        -- apply IHps; auto.
          exists v1. exists (fst x). auto.
  - split; intros; auto. destruct H. 
    destruct H as [_ [_ [_ [[] _]]]].
  - rewrite union_elts. split; intros.
    + destruct H; [apply IHp1 in H | apply IHp2 in H];
      try (intros; apply Hfvs; simpl; rewrite union_elts;
        try(solve[left; auto]); right; auto);
      destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst;
      exists v1; exists (fst x); split_all; auto;
      rewrite union_elts; [left | right]; auto.
    + destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
      rewrite union_elts in Hinv. destruct Hinv; 
      [left; apply IHp1 | right; apply IHp2]; try (intros; apply Hfvs;
      simpl; rewrite union_elts; try(solve[left; auto]); right; auto);
      exists v1; exists (fst x); split_all; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl;
    rewrite union_elts; [split; intros|].
    + destruct H as [Hinx | [Heq | []]]; subst.
      * apply IHp in Hinx.
        destruct Hinx as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts; left; auto.
        intros; apply Hfvs; simpl; rewrite union_elts; left; auto.
      * apply get_assoc_list_some in Ha.
        exists v. exists s. split_all; auto. rewrite union_elts.
        right; left;auto.
    + destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
      rewrite union_elts in Hinv. destruct Hinv as [Hinv | [Heq | []]]; subst;
      [left | right; left]; auto.
      * apply IHp. intros. apply Hfvs; simpl; rewrite union_elts; left; auto.
        exists v1. exists (fst x). split_all; auto.
      * apply get_assoc_list_some in Ha.
        destruct x; simpl in *; subst. f_equal.
        apply (nodup_fst_inj Hnodup Ha Hinl).
    + apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hfvs. simpl. rewrite union_elts; right; left;
      auto.
Qed.

Lemma alpha_p_aux_wf_aux {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    NoDup (map fst l) ->
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (forall x v, In v (pat_fv (fst (alpha_p_aux sub p x l))) ->
      In (fst v) (map snd l))).
Proof.
  intros. pose proof (alpha_p_aux_wf_aux_gen' p sub l H H0 v x).
  apply H2 in H1. destruct H1 as [v1 [str [Hinl [Hinv1 [Hsnd Hfst]]]]]; subst.
  rewrite in_map_iff. exists (v1, fst v). split; auto.
Qed.

(*Second: need to know that [alpha_p_aux] does not change any bound
  variables in t/f*)

Lemma alpha_p_aux_bnd_t_eq  (p: pattern) (t: term) (l: list (vsymbol * string)) :
  bnd_t (snd (alpha_p_aux sub_t p t l)) =
  bnd_t t.
Proof.
  revert t.
  induction p; simpl; intros; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_t; auto.
  - generalize dependent t. induction ps; simpl; intros; auto. 
    inversion H; subst.
    rewrite IHps; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_t; auto.
Qed.

Lemma alpha_p_aux_bnd_f_eq (p: pattern) (f: formula) (l: list (vsymbol * string)) :
  bnd_f (snd (alpha_p_aux sub_f p f l)) =
  bnd_f f.
Proof.
  revert f.
  induction p; simpl; intros; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_f; auto.
  - generalize dependent f0. induction ps; simpl; intros; auto. 
    inversion H; subst.
    rewrite IHps; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_f; auto.
Qed.

(*TODO: move this stuff probably*)

(*First, sub_ts does not change bound vars*)
Lemma bnd_sub_ts l t :
  bnd_t (sub_ts l t) = bnd_t t.
Proof.
  induction l; simpl; auto.
  rewrite bnd_sub_t; auto.
Qed.

(*Need free vars of [sub_ps]*)

(*Let's do similar to [sub_t]*)
Fixpoint free_in_p (x: vsymbol) (p: pattern) : bool :=
  match p with
  | Pvar v => vsymbol_eq_dec x v
  | Pwild => false
  | Pbind p1 v => vsymbol_eq_dec x v || free_in_p x p1
  | Por p1 p2 => free_in_p x p1 || free_in_p x p2
  | Pconstr f tys ps =>
    existsb (fun p => free_in_p x p) ps
  end.

Lemma free_in_p_spec (p: pattern) (x: vsymbol):
  free_in_p x p <-> In x (pat_fv p).
Proof.
  induction p; simpl; simpl_set; auto; try solve[split; auto].
  - rewrite (eq_sym_iff v x), dec_iff; reflexivity.
  - bool_to_prop. apply ex_in_eq.
    apply H.
  - bool_to_prop. rewrite IHp1, IHp2; reflexivity.
  - bool_to_prop. rewrite IHp. bool_to_prop.
    rewrite (eq_sym_iff v x).
    vsym_eq x v; simpl; split; auto; intros; inversion H.
Qed.


(*we only need a subset of the results, because we work with
  vars guaranteed to be in [pat_fv p] and different than existing
  vars*)


(*1. For any variables which are not x or y, sub_p doesn't change anything*)
Lemma sub_p_fv_diff (p: pattern):
  forall (x y z: vsymbol),
  z <> x -> z <> y ->
  free_in_p z (sub_p x y p) = free_in_p z p.
Proof.
  induction p; simpl; intros; auto.
  - vsym_eq v x. vsym_eq z y. vsym_eq z x.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H2. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx Pwild Pwild); subst; simpl.
    wf_tac. apply H; wf_tac.
  - rewrite IHp1, IHp2; wf_tac.
  - rewrite IHp; wf_tac. vsym_eq v x.
    vsym_eq z y. vsym_eq z x.
Qed. 

(*2: If we replace x with y, x is NOT in the resulting free variables*)
Lemma sub_p_fv_notin (p: pattern) :
  forall (x y: vsymbol),
  x <> y ->
  free_in_p x (sub_p x y p) = false.
Proof.
  intros; induction p; simpl; auto.
  - vsym_eq v x. vsym_eq x y. vsym_eq x v.
  - apply existsb_false.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_map_iff; intros [t [Ht Hint]]; subst.
    apply H0; auto.
  - rewrite IHp1, IHp2. auto.
  - rewrite IHp. simpl_bool.
    vsym_eq v x. vsym_eq x y. vsym_eq x v.
Qed.

(*3. When we substitute x with y, y is in the free variables
  iff either y was before or x was before*)
Lemma sub_p_fv_in (p: pattern):
  forall (x y: vsymbol),
  x <> y ->
  free_in_p y (sub_p x y p) = (free_in_p x p) || (free_in_p y p).
Proof.
  intros; induction p; simpl; auto.
  - vsym_eq x v; simpl. vsym_eq v v. vsym_eq y y. vsym_eq v x.
  - rewrite existsb_orb. apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1; rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx Pwild Pwild); subst; simpl.
    wf_tac. apply H0; wf_tac.
  - rewrite IHp1, IHp2; solve_bool.
  - rewrite IHp. vsym_eq v x.
    + vsym_eq y y. vsym_eq x x.
    + vsym_eq x v. vsym_eq y v. solve_bool; auto.
Qed.

(*TODO: prove result for [sub_ps] that we end up with only
  the domain of the list (basically what we need i think)*)
  (*TODO: START*)

(*TODO: may need stronger lemma later - look at sub_t and sub_f 
  for this*)
  (*hmm look at sub_t tbh*)
  (*
Lemma pat_fv_sub_p x y p:
  In x (pat_fv p) ->
  x <> y ->
  forall v,
  In v (pat_fv (sub_p x y p)) <-> v = y \/ (v <> x /\ In v (pat_fv p)).
Proof.
  induction p; simpl; simpl_set; intros; subst; simpl_set.
  - destruct (vsymbol_eq_dec x x); try contradiction.
    split; intros; destruct_all; auto. contradiction.
  - split; intros.
    + destruct_all.
      rewrite in_map_iff in H2. destruct_all.
      rewrite Forall_forall in H. apply H in H3; auto.


    split; intros; destruct_all; try split; auto.
    + right. split; auto. intro; subst.



Lemma pat_fv_sub_p x y p :
  x <> y ->
  forall v,
  In v (pat_fv (sub_p x y p)) <->
  (v <> x /\ (In x (pat_fv p) /\ v = y) \/ (In v (pat_fv p))).
Proof.
  intros. induction p; simpl; simpl_set.
  - destruct (vsymbol_eq_dec v0 x); subst; split; intros.
    + subst. triv.
    + destruct_all; auto.
    destruct_all.
  subst. split; intros. left; auto. destruct H. subst; split; intros; 
    destruct_all; subst; auto.
*)
(*TODO: add to this*)

Lemma alpha_aux_wf_aux (t: term) (f: formula) :
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_t t) ->
    NoDup (bnd_t (alpha_t_aux t l)) /\
    (forall x, In x (bnd_t (alpha_t_aux t l)) -> In (fst x) l)) /\
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_f f) ->
    NoDup (bnd_f (alpha_f_aux f l)) /\
    (forall x, In x (bnd_f (alpha_f_aux f l)) -> In (fst x) l)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto.
  - split; [constructor | intros x []]. 
  - split; [constructor | intros x []].
  - (*Tfun case*) 
    split.
    + rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l0 (map (fun t => length (bnd_t t)) l1)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst x)); wf_tac.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l0 (map (fun t => length (bnd_t t)) l1));
      [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Tlet case*)
    destruct l; inversion H2; simpl.
    inversion H1; subst.
    split.
    + constructor.
      * (*TODO: automate the "In" part*) 
        intro Hin.
        apply in_app_or in Hin.
        destruct Hin.
        -- apply H in H3; wf_tac.
        -- rewrite bnd_sub_t in H3.
          apply H0 in H3; wf_tac. 
      * rewrite NoDup_app_iff'.
        split_all.
        -- apply H; wf_tac.
        -- rewrite bnd_sub_t. apply H0; wf_tac.
        -- intros x.
          rewrite bnd_sub_t.
          intros [Hinx1 Hinx2].
          apply H in Hinx1; wf_tac.
          apply H0 in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); auto.
    + intros x [Hx | Hinx]; subst;[left; auto|].
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite bnd_sub_t in Hinx. apply H0 in Hinx; wf_tac.
  - (*Tif case*)
    split.
    + rewrite !NoDup_app_iff'.
      split_all.
      * apply H; wf_tac.
      * apply H0; wf_tac.
      * apply H1; wf_tac.
      * intros x [Hinx1 Hinx2].
        apply H0 in Hinx1; wf_tac.
        apply H1 in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac. 
      * intros x [Hinx1 Hinx2].
        apply H in Hinx1; wf_tac.
        apply in_app_or in Hinx2. destruct Hinx2.
        -- apply H0 in H4; wf_tac.
          apply (nodup_firstn_skipn Hinx1); wf_tac. 
        -- apply H1 in H4; wf_tac.
          apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      repeat (apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx]).
      * apply H in Hinx; wf_tac.
      * apply H0 in Hinx; wf_tac.
      * apply H1 in Hinx; wf_tac. 
  - (*Tmatch case*)
    assert (Hsum: sum (map
        (fun x : pattern * term =>
        Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
        ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
          wf_tac. rewrite H2,length_concat, 
        map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    split.
    + rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, tm_d) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ simpl. rewrite bnd_sub_ts.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x. simpl.
            rewrite bnd_sub_ts. 
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply alpha_p_aux_wf_aux in Hinx1; wf_tac.
            rewrite map_snd_combine in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, tm_d)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          apply in_app_or in Hini1, Hini2.
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply alpha_p_aux_wf_aux in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_t_eq in Hini2.
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ rewrite alpha_p_aux_bnd_t_eq in Hini1.
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_t_eq in Hini2.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
      * intros x.
        rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
        apply H in Hinx1; wf_tac.
        rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        (*And now we have to show these are distinct, will be similar*)
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx2 | Hinx2].
        -- apply alpha_p_aux_wf_aux in Hinx2; wf_tac.
          revert Hinx2; wf_tac; intros.
          apply In_firstn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- rewrite alpha_p_aux_bnd_t_eq in Hinx2.
          rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
          apply In_skipn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - TODO very similar to previous*)
      intros x Hinx.
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite in_concat in Hinx.
        destruct Hinx as [l1 [Hinl1 Hinxl1]].
        rewrite in_map_iff in Hinl1.
        destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with (d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx | Hinx].
        -- apply alpha_p_aux_wf_aux in Hinx; wf_tac.
          revert Hinx; wf_tac; intros.
          apply In_firstn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
        -- rewrite alpha_p_aux_bnd_t_eq in Hinx.
          rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
          apply In_skipn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
  - (*Epsilon case*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_f.
    split.
    + constructor; [|apply H; wf_tac].
      intro Hin. apply H in Hin; wf_tac.
    + intros. destruct H2; subst; [left; auto | right].
      apply H in H2; wf_tac.
  - (*Fpred case - same as Tfun*)
    split.
    + rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l (map (fun t => length (bnd_t t)) tms)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst x)); wf_tac.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l (map (fun t => length (bnd_t t)) tms));
        [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Fquant*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_f.
    split.
    + constructor; [intro C; apply H in C |apply H]; wf_tac.
    + intros. destruct H2; subst;[left | right]; auto.
      apply H in H2; wf_tac.
  - (*Feq*)
    split.
    + rewrite NoDup_app_iff'; split_all;[apply H | apply H0 |]; wf_tac.
      intros x [Hinx1 Hinx2].
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx. destruct Hinx as [Hinx | Hinx]; 
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*Fbinop*)
    split.
    + rewrite NoDup_app_iff'; split_all;[apply H|apply H0|]; wf_tac.
      intros x [Hinx1 Hinx2].
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*trivial*)
    split;[constructor | intros x []].
  - split;[constructor | intros x []].
  - (*Flet*)
    destruct l; inversion H2; subst.
    inversion H1; subst; simpl; rewrite bnd_sub_f.
    split.
    + constructor.
      * intro C. apply in_app_or in C.
        destruct C as [Hins | Hins];
        [apply H in Hins | apply H0 in Hins]; wf_tac.
      * rewrite NoDup_app_iff'; split_all; [apply H | apply H0 |];wf_tac.
        intros x [Hinx1 Hinx2]; apply H in Hinx1; apply H0 in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x [Hx | Hinx]; subst;[left | right]; auto.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx]; wf_tac.
  - (*Fif*)
    split.
    + rewrite !NoDup_app_iff'; split_all;
      [apply H | apply H0 | apply H1 | |]; wf_tac;
      intros x; [| rewrite in_app_iff];
      intros [Hinx1 Hinx2];[|destruct Hinx2 as [Hinx2 | Hinx2]];
      [apply H0 in Hinx1; apply H1 in Hinx2 | apply H in Hinx1; 
        apply H0 in Hinx2 | apply H in Hinx1; apply H1 in Hinx2]; wf_tac;
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x.
      rewrite ! in_app_iff; intros [Hinx | [Hinx | Hinx]];
      [apply H in Hinx | apply H0 in Hinx | apply H1 in Hinx]; wf_tac.
  - (*Fmatch case - very similar to Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite H2,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    split.
    + rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, Ftrue) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ rewrite alpha_p_aux_bnd_f_eq.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x.
            rewrite alpha_p_aux_bnd_f_eq.
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply alpha_p_aux_wf_aux in Hinx1; wf_tac.
            rewrite map_snd_combine in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, Ftrue)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          apply in_app_or in Hini1, Hini2.
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply alpha_p_aux_wf_aux in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_f_eq in Hini2.
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ rewrite alpha_p_aux_bnd_f_eq in Hini1.
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_f_eq in Hini2.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
    * intros x.
      rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
      apply H in Hinx1; wf_tac.
      rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
      subst.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
      destruct Hinp1 as [i [Hi Hp1]]; subst.
      (*And now we have to show these are distinct, will be similar*)
      apply in_app_or in Hinxl1.
      destruct Hinxl1 as [Hinx2 | Hinx2].
      -- apply alpha_p_aux_wf_aux in Hinx2; wf_tac.
        revert Hinx2; wf_tac; intros.
        apply In_firstn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
      -- rewrite alpha_p_aux_bnd_f_eq in Hinx2.
        rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
        apply In_skipn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - TODO very similar to previous*)
    intros x Hinx.
    apply in_app_or in Hinx.
    destruct Hinx as [Hinx | Hinx].
    * apply H in Hinx; wf_tac.
    * rewrite in_concat in Hinx.
      destruct Hinx as [l1 [Hinl1 Hinxl1]].
      rewrite in_map_iff in Hinl1.
      destruct Hinl1 as [p1 [Hl1 Hinp1]].
      subst.
      rewrite in_map2_iff with (d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
      destruct Hinp1 as [i [Hi Hp1]]; subst.
      apply in_app_or in Hinxl1.
      destruct Hinxl1 as [Hinx | Hinx].
      -- apply alpha_p_aux_wf_aux in Hinx; wf_tac.
        revert Hinx; wf_tac; intros.
        apply In_firstn in Hinx.
        apply in_split_lens_ith in Hinx; wf_tac.
      -- rewrite alpha_p_aux_bnd_f_eq in Hinx.
        rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
        apply In_skipn in Hinx.
        apply in_split_lens_ith in Hinx; wf_tac.
Qed.

Corollary alpha_t_aux_wf (t: term):
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_t t) ->
    NoDup (bnd_t (alpha_t_aux t l)) /\
    (forall x, In x (bnd_t (alpha_t_aux t l)) -> In (fst x) l)).
Proof.
  apply alpha_aux_wf_aux. apply Ftrue.
Qed.

Corollary alpha_f_aux_wf (f: formula):
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_f f) ->
    NoDup (bnd_f (alpha_f_aux f l)) /\
    (forall x, In x (bnd_f (alpha_f_aux f l)) -> In (fst x) l)).
Proof.
  apply alpha_aux_wf_aux. apply tm_d.
Qed.


(*Need to know that all patterns in constrs are valid*)

(*Generalized so it works for terms and formulas*)
Lemma alpha_p_aux_valid {A B: Type} (sub: vsymbol -> vsymbol -> A -> A)
  (valid: A -> B -> Prop)(p: pattern) (a: A)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l))
  (sub_valid: forall a x y b,
    valid a b ->
    snd x = snd y ->
    valid (sub x y a) b):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub p a l)) ty) /\
  (forall b, valid a b ->
    valid (snd (alpha_p_aux sub p a l)) b).
Proof.
  revert a.
  (*revert l t Hnodup1 Hnodup2.*) induction p; simpl; auto; intros.
  - (*Pvar*) 
    destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; 
    simpl; split; intros; auto.
    inversion H0; subst.
    replace (snd v) with (snd ((s, snd v))) at 2 by auto.
    constructor; auto.
  - (*Pconstr*)
    split; intros.
    + inversion H1; subst. subst sigma0.
      assert (Hlen: 
      Datatypes.length
      (fst
         ((fix alpha_ps_aux (l1 : list pattern) (y : A) {struct l1} :
               list pattern * A :=
             match l1 with
             | [] => ([], y)
             | ph :: pt =>
                 (fst (alpha_p_aux sub ph y l)
                  :: fst (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))),
                 snd (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))))
             end) ps a)) = Datatypes.length (s_args f)). {
        rewrite <- H7. clear. revert a. induction ps; simpl; auto.
      }
      constructor; auto.
      * revert H11. rewrite !Forall_forall.
        assert (length (map (ty_subst (s_params f) vs) (s_args f)) = length ps) by wf_tac.
        generalize dependent (map (ty_subst (s_params f) vs) (s_args f)).
        clear -H H0.
        revert a. induction ps; simpl; auto ; intros; destruct l0.
        -- inversion H1.
        -- inversion H; subst. simpl in H1. destruct H1; subst; simpl.
          ++ apply H5; auto.
            intros. apply H0. simpl. rewrite union_elts. left; auto.
            specialize (H11 (a, v)); simpl in H11.
            apply H11; left; auto.
          ++ apply (IHps H6) with (a:=(snd (alpha_p_aux sub a a0 l))) (l:=l0); auto.
            intros. apply H0. simpl. rewrite union_elts. right; auto.
            intros.
            apply H11; right; auto.
      * rewrite Hlen, <- H7.
        clear Hlen. clear -H12 H0 H Hnodup2. revert a.
        (*We need a separate inductive lemma:*)
        assert (Hinnth: forall (ps: list pattern) (j : nat) (x : vsymbol) (d : pattern) (a : A),
        j < Datatypes.length ps ->
        (forall v : vsymbol,
         In v (big_union vsymbol_eq_dec pat_fv ps) -> In v (map fst l)) ->
        In x
          (pat_fv
             (nth j
                (fst
                   ((fix alpha_ps_aux (l1 : list pattern) (y : A) {struct l1} :
                         list pattern * A :=
                       match l1 with
                       | [] => ([], y)
                       | ph :: pt =>
                           (fst (alpha_p_aux sub ph y l)
                            :: fst (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))),
                           snd (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))))
                       end) ps a)) d)) ->
        exists v' : vsymbol, In (v', fst x) l /\ In v' (pat_fv (nth j ps Pwild))). {
          clear.
          induction ps; simpl; auto; intros; try lia.
            destruct j.
            - apply alpha_p_aux_wf_aux_gen in H1; auto.
              intros. apply H0. rewrite union_elts. left; auto.
            - eapply IHps; try lia; auto. 2: apply H1.
              intros. apply H0. rewrite union_elts. right; auto.
        }
        intros t i j d x Hi Hj Hij [Hinx1 Hinx2].
        apply Hinnth in Hinx1; auto.
        apply Hinnth in Hinx2; auto.
        destruct Hinx1 as [v1 [Hinl1 Hinv1]].
        destruct Hinx2 as [v2 [Hinl2 Hinv2]].
        assert (v1 = v2) by apply (nodup_snd_inj Hnodup2 Hinl1 Hinl2). 
        subst.
        (*This contradicts the disjointness of free vars*)
        apply (H12 i j Pwild v2); try lia; auto.
    + (*term goal*)
      generalize dependent a.
      revert H. clear - H0.
      induction ps; simpl; auto; intros.
      inversion H; subst.
      apply IHps; auto.
      * intros. apply H0. simpl. rewrite union_elts. right; auto.
      * apply H4; auto. intros. apply H0. simpl. rewrite union_elts.
        left; auto.
  - (*Por case*)
    split; intros.
    + inversion H0; subst.
      constructor; auto.
      * apply IHp1; auto.
        intros. apply H. rewrite union_elts; left; auto.
      * apply IHp2; auto.
        intros; apply H; rewrite union_elts; right; auto.
      * intros x. rewrite !alpha_p_aux_wf_aux_gen'; auto;
        try (intros; apply H; simpl; rewrite union_elts;
          try(solve[left; auto]); right; auto).
        setoid_rewrite H7. reflexivity.
    + apply IHp2; auto.
      intros. apply H. rewrite union_elts; right; auto.
  - (*Pbind case*)
    split; intros.
    + inversion H0; subst. 
      destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha;
      simpl; auto.
      replace (snd v) with (snd ((s, snd v))) at 2 by auto.
      constructor; simpl.
      * intro. 
        rewrite alpha_p_aux_wf_aux_gen' in H1; auto.
        destruct H1 as [v1 [str [Hinl [Hinv1 [Hsnd Hfst]]]]];
        simpl in *; subst.
        apply get_assoc_list_some in Ha.
        assert (v = v1) by apply (nodup_snd_inj Hnodup2 Ha Hinl); subst.
        apply H4. wf_tac.
        intros. apply H. rewrite union_elts; left; auto.
      * apply IHp; auto. intros.
        apply H; rewrite union_elts; left; auto.
    + destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl; auto.
      apply sub_valid; auto.
      apply IHp; auto.
      intros. apply H. rewrite union_elts; left; auto.
Qed.


Lemma alpha_p_aux_valid_t (p: pattern) (t: term)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l)):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub_t p t l)) ty) /\
  (forall ty, term_has_type sigma t ty ->
    term_has_type sigma (snd (alpha_p_aux sub_t p t l)) ty).
Proof.
  apply alpha_p_aux_valid; auto.
  apply sub_t_valid.
Qed.

Lemma alpha_p_aux_valid_f (p: pattern) (f: formula)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l)):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub_f p f l)) ty) /\
  (valid_formula sigma f ->
    valid_formula sigma (snd (alpha_p_aux sub_f p f l))).
Proof.
  intros Hinfv.
  pose proof (alpha_p_aux_valid sub_f 
    (fun f' (u: unit) => valid_formula sigma f') 
      p f l Hnodup1 Hnodup2);
  split; apply H; auto; try(intros; apply sub_f_valid; auto).
  exact tt.
Qed.

(*Part 2: [alpha_t_aux] and [alpha_f_aux] form well-typed
  terms and formulas*)
Lemma alpha_aux_valid (t: term) (f: formula):
  (forall (l: list string) (ty: vty)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_t t)),
    term_has_type sigma t ty ->
    term_has_type sigma (alpha_t_aux t l) ty) /\
  (forall (l: list string)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_f f)),
    valid_formula sigma f ->
    valid_formula sigma (alpha_f_aux f l)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; simpl; intros.
  - (*Tfun*)
    inversion H0; subst. constructor; auto.
    wf_tac. revert H11 H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    revert Hi; wf_tac.
    specialize (Hx tm_d vty_int); subst; simpl.
    rewrite map2_nth with(d1:=tm_d) (d2:=nil); wf_tac.
    apply H; wf_tac.
    rewrite map_nth_inbound with(d2:=vty_int); try lia.
    apply (H11 (nth i l1 tm_d, 
      (ty_subst (s_params f1) l (nth i (s_args f1) vty_int)))).
    rewrite in_combine_iff; wf_tac.
    exists i. split; auto. intros.
    f_equal.
    + apply nth_indep; auto.
    + rewrite map_nth_inbound with (d2:=vty_int); auto. lia.
  - (*Tlet*) destruct l; auto; simpl.
    inversion H1; subst.
    inversion Hnodup; subst.
    wf_tac. inversion Hlenl.
    constructor.
    + apply H; wf_tac.
    + apply sub_t_valid; auto. apply H0; wf_tac.
  - (*Tif*) inversion H2; subst.
    constructor; auto.
    apply H; wf_tac.
    apply H0; wf_tac.
    apply H1; wf_tac.
  - (*Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * term =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite Hlenl,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    inversion H1; subst.
    constructor.
    + apply H; auto; wf_tac.
    + intros x.
      rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_t; wf_tac.
      apply H7; wf_tac.
    + intros x.
      rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_t; wf_tac.
      rewrite Forall_forall in H0. apply H0; wf_tac.
      apply H9; wf_tac.
    + rewrite null_map2; auto; wf_tac.
  - (*Teps*)
    destruct l; inversion Hlenl.
    inversion H0; subst.
    replace (snd v) with (snd (s, snd v)) at 3 by auto.
    constructor; auto.
    apply sub_f_valid; auto. inversion Hnodup. apply H; wf_tac.
  - (*Fpred*)
    inversion H0; subst.
    constructor; auto; wf_tac.
    revert H9 H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    revert Hi; wf_tac.
    specialize (Hx tm_d vty_int); subst; simpl.
    rewrite map2_nth with(d1:=tm_d) (d2:=nil); wf_tac.
    apply H; wf_tac.
    rewrite map_nth_inbound with(d2:=vty_int); try lia.
    apply (H9 (nth i tms tm_d, 
      (ty_subst (p_params p) tys (nth i (p_args p) vty_int)))).
    rewrite in_combine_iff; wf_tac.
    exists i. split; auto. intros.
    f_equal.
    + apply nth_indep; auto.
    + rewrite map_nth_inbound with (d2:=vty_int); auto. lia.
  - (*Fquant*)
    destruct l; inversion Hlenl.
    inversion H0; subst.
    constructor; auto.
    apply sub_f_valid; auto.
    apply H; auto. inversion Hnodup; auto.
  - (*Feq*)
    inversion H1; subst.
    constructor; [apply H | apply H0]; wf_tac.
  - (*Fbinop*)
    inversion H1; subst.
    constructor; [apply H | apply H0]; wf_tac.
  - (*Fnot*)
    inversion H0; subst.
    constructor. apply H; wf_tac.
  - (*Flet*)
    destruct l; inversion Hlenl; simpl.
    inversion H1; subst.
    inversion Hnodup; subst.
    constructor; [apply H | apply sub_f_valid]; wf_tac.
    apply H0; wf_tac.
  - (*Fif*)
    inversion H2; subst.
    constructor; [apply H | apply H0 | apply H1]; wf_tac.
  - (*Fmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite Hlenl,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    inversion H1; subst.
    constructor.
    + apply H; auto; wf_tac.
    + rewrite Forall_forall; intros x.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_f; wf_tac.
      rewrite Forall_forall in H7;
      apply H7; wf_tac.
    + rewrite Forall_forall; intros x.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_f; wf_tac.
      rewrite Forall_forall in H0. apply H0; wf_tac.
      rewrite Forall_forall in H8; apply H8; wf_tac.
    + rewrite null_map2; auto; wf_tac.
Qed.

Corollary alpha_t_aux_type (t: term) :
  (forall (l: list string) (ty: vty)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_t t)),
    term_has_type sigma t ty ->
    term_has_type sigma (alpha_t_aux t l) ty).
Proof.
  apply alpha_aux_valid. apply Ftrue.
Qed.

Lemma alpha_f_aux_type (f: formula):
  (forall (l: list string)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_f f)),
    valid_formula sigma f ->
    valid_formula sigma (alpha_f_aux f l)).
Proof.
  apply alpha_aux_valid. apply tm_d.
Qed.

(*Part 2.5 We need to know that this substitution does not
  change the free variables. This is very hard to show, particularly
  due to the patterns and their dependencies*)

(*Analagous lemmas for term/formula in [alpha_p_aux]. These 
  are much harder*)

(*1. For any vsymbol not in the free vars of p and not in
  the free vars of the resulting pattern,  
  [alpha_p_aux] does not change the result*)

Lemma alpha_p_aux_diff {A: Type} (sub: vsymbol -> vsymbol -> A -> A)
(p: pattern) (t: A) (l: list (vsymbol * string))
(free_in: vsymbol -> A -> bool)
(Hsub: forall a x y z, z <> x -> z <> y -> 
  free_in z (sub x y a) = free_in z a)
(Hnodup: NoDup(map fst l))
(Hallin: forall v, In v (pat_fv p) -> In v (map fst l)):
forall x, ~In x (pat_fv p) ->
  ~ In x (pat_fv (fst (alpha_p_aux sub p t l))) ->
   free_in x (snd (alpha_p_aux sub p t l)) = free_in x t.
Proof.
  intros x.
  (*This makes it usable with our IH for constr case*)
  rewrite alpha_p_aux_wf_aux_gen'; auto.
  generalize dependent t.
  induction p; simpl in *; intros; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : ha; auto.
    simpl. rewrite Hsub; auto.
    intro Heq; subst.
    apply get_assoc_list_some in ha.
    apply H0. simpl. exists v. exists s. split_all; auto.
  - generalize dependent t. induction ps; simpl; intros; auto.
    inversion H; subst.
    rewrite IHps; auto.
    + simpl in H0. simpl_set. rewrite H4; auto.
      * intros. apply Hallin. simpl; simpl_set; triv.
      * intros [v [str [Hinvst [Hinv [Hsnd Hfst]]]]]; subst.
        apply H1. exists v. exists (fst x). split_all; auto.
        simpl; simpl_set; triv.
    + intros. apply Hallin. simpl; simpl_set; triv.
    + simpl in H0. rewrite union_elts in H0.
      intro C. apply H0. triv.
    + intros [v [str [Hinvstr [Hinv [Hsnd Hfst]]]]]; subst.
      apply H1. exists v. exists (fst x). split_all; auto.
      simpl. simpl_set; triv.
  - rewrite IHp2; auto.
    + intros. apply Hallin. simpl_set; triv.
    + intro C. apply H. simpl_set; triv.
    + intros [v [str [Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
      apply H0. exists v. exists (fst x). split_all; auto.
      simpl_set; triv.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; auto.
    simpl. rewrite Hsub; auto.
    + apply IHp.
      * intros; apply Hallin; simpl_set; triv.
      * intro C. apply H. simpl_set; triv.
      * intros [v' [str [Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
        apply H0. exists v'. exists (fst x). split_all; auto.
        simpl_set; triv.
    + intro Heq; subst. apply H. simpl_set; triv.
    + intro Heq; subst. apply H0. simpl.
      apply get_assoc_list_some in Ha.
      exists v. exists s. split_all; auto. simpl_set; triv.
Qed.

(*TODO: move these*)
Lemma sub_t_in_implies (t: term): forall z x y,
  free_in_t z (sub_t x y t) ->
  (free_in_t z t /\ z <> x) \/ z = y.
Proof.
  intros. vsym_eq x y.
  - rewrite sub_t_eq in H. vsym_eq z y.
  - vsym_eq z x.
    + rewrite (sub_t_fv_notin _ _ _ n) in H. inversion H.
    + vsym_eq z y.
      rewrite sub_t_fv_diff in H; auto.
Qed.

Lemma sub_f_in_implies (f: formula): forall z x y,
  free_in_f z (sub_f x y f) ->
  (free_in_f z f /\ z <> x) \/ z = y.
Proof.
  intros. vsym_eq x y.
  - rewrite sub_f_eq in H. vsym_eq z y.
  - vsym_eq z x.
    + rewrite (sub_f_fv_notin _ _ _ n) in H. inversion H.
    + vsym_eq z y.
      rewrite sub_f_fv_diff in H; auto.
Qed.

(*1.5: Every variable free in the result is free in the term or
  is free in the new pattern*)
Lemma alpha_p_aux_in_implies {A: Type} (sub: vsymbol -> vsymbol -> A -> A)
  (p: pattern) (t: A) (l: list (vsymbol * string))
  (free_in: vsymbol -> A -> bool) (ty: vty)
  (Hty: pattern_has_type sigma p ty)
  (Hsub: forall z x y a, free_in z (sub x y a) ->
    (free_in z a /\ z <> x) \/ z = y)
  (Hallin: forall x, In x (pat_fv p) -> In x (map fst l))
  (Hnodup: NoDup (map fst l)) :
  forall x, free_in x (snd (alpha_p_aux sub p t l)) ->
    (free_in x t /\ ~In x (pat_fv p)) \/ 
      In x (pat_fv(fst (alpha_p_aux sub p t l))).
Proof.
  intros.
  rewrite alpha_p_aux_wf_aux_gen'; auto.
  intros; generalize dependent ty; generalize dependent t; induction p; simpl in *; intros.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha;
    simpl in H.
    + apply Hsub in H. destruct H as [[Hfree Hneq] | Heq]; subst; try triv.
      * left. split; auto. intro C; destruct_all; subst; auto; try contradiction.
      * right. simpl. exists v. exists s. split_all; auto.
        apply get_assoc_list_some in Ha; auto.
    + apply get_assoc_list_none in Ha. exfalso. apply Ha. apply Hallin.
      triv. 
  - generalize dependent t.
    inversion Hty; subst.
    revert H9. clear H3 H4 H7 H10 Hty.
    assert (length ps = length (map sigma0 (s_args f))) by (rewrite map_length; auto).
    revert H0; clear H5.
    generalize dependent (map sigma0 (s_args f)).
    induction ps; simpl; intros; auto.
    inversion H; subst.
    destruct l0; inversion H0.
    inversion H9; subst. simpl in H7.
    eapply IHps in H1; auto. 3: apply H3.
    + destruct H1.
      * destruct H1. eapply H4 in H1. 3: apply H7.
        -- destruct H1.
          ++ destruct H1. left. split; auto.
            simpl_set. intro C. destruct C; contradiction.
          ++ right. destruct H1 as [v' [str[Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
            exists v'. exists (fst x). split_all; auto.
            simpl_set; triv.
        -- intros; apply Hallin; simpl; simpl_set; triv.
      * right. destruct H1 as [v' [str[Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
        exists v'. exists (fst x). split_all; auto. simpl_set; triv.
    + intros; apply Hallin; simpl; simpl_set; triv.
    + auto. 
  - triv. 
  - inversion Hty; subst. 
    eapply IHp2 in H. 3: apply H4.
    + destruct H; try triv.
      * destruct H. left. split; auto. simpl_set.
        intros [Hinx | Hinx]; try contradiction.
        (*Need typing to know that free vars the same*)
        rewrite H6 in Hinx. contradiction.
      * right. destruct H as [v' [str[Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
        exists v'; exists (fst x); split_all; auto; simpl_set; triv.
    + intros; apply Hallin; simpl; simpl_set; triv.
  - inversion Hty; subst. 
    destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha;
    simpl in H.
    + apply Hsub in H. destruct H; subst; simpl; try triv.
      * destruct H. eapply IHp in H. 3: apply H5.
        -- destruct_all; try triv.
          ++ left.
            split; auto; simpl_set. intros [C | C]; subst; auto.
          ++ right. exists x0. exists (fst x). split_all; auto. simpl_set; triv. 
        -- intros; apply Hallin; simpl; simpl_set; triv.
      * right. apply get_assoc_list_some in Ha.
        exists v. exists s. split_all; auto. simpl_set. triv.
    + apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hallin. simpl_set. triv.
Qed.

(*2. For any vsymbol in the free vars of p, and the free vars
  of the new pattern. it is not free in the result. This is quite
  hard to show*)
Lemma alpha_p_aux_notin {A: Type} (sub: vsymbol -> vsymbol -> A -> A)
  (p: pattern) (t: A) (l: list (vsymbol * string))
  (free_in: vsymbol -> A -> bool) ty
  (Hty: pattern_has_type sigma p ty)
  (Hsub1: forall x y a, x <> y -> free_in x (sub x y a) = false)
  (Hsub2: forall z x y a, free_in z (sub x y a) ->
    (free_in z a /\ z <> x) \/ z = y)
  (Hfree: forall x, In (fst x) (map snd l) -> ~ In x (pat_fv p))
  (Hallin: forall x, In x (pat_fv p) -> In x (map fst l))
  (Hnodup: NoDup (map fst l)):
  forall x, In x (pat_fv p) ->
  ~In x (pat_fv (fst (alpha_p_aux sub p t l))) ->
  free_in x (snd (alpha_p_aux sub p t l)) = false.
Proof.
  intros. rewrite alpha_p_aux_wf_aux_gen' in H0; auto.
  generalize dependent ty. 
  generalize dependent t.
  induction p; intros; simpl in H; simpl.
  - destruct H as [Heq | []]; subst.
    destruct (get_assoc_list vsymbol_eq_dec l x) eqn : Ha.
    + simpl. apply Hsub1. intro Hx.
      apply (Hfree x); simpl; try triv.
      rewrite Hx. simpl.
      apply get_assoc_list_some in Ha.
      rewrite in_map_iff. exists (x, s); auto.
    + apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hallin; simpl; triv.
  - assert (In x (big_union vsymbol_eq_dec pat_fv ps) \/ free_in x t = false) by triv.
    clear H. (*Need weaker statement for IH*)
    inversion Hty; subst.
    revert H11. clear H5 H6 H9 H12 Hty.
    assert (length ps = length (map sigma0 (s_args f))) by (rewrite map_length; auto).
    revert H; clear H7.
    generalize dependent (map sigma0 (s_args f)). clear sigma0.
    generalize dependent t.  induction ps; simpl; intros; auto.
    + destruct H2 as [[] |]; auto.
    + simpl in *.
      destruct l0; inversion H.
      inversion H11; subst. simpl in H6.
    (*TODO: think need separate lemma for base case see*)
      destruct H2.
      * inversion H1; subst. eapply IHps; [| | | | |apply H4 |]; auto.
        -- intros y Hiny C.
          apply (Hfree y); auto. simpl_set; triv.
        -- intros. apply Hallin. simpl_set; triv.
        -- intros [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
          apply H0. exists v'. exists (fst x). split_all; auto.
          simpl_set; triv.
        -- rewrite union_elts in H2.
          destruct H2.
          (*Why we need weaker IH*)
          ++ right. eapply H8; [| | | | apply H6]; auto.
            ** intros y Hiny C.
              apply (Hfree y); auto. simpl_set; triv.
            ** intros; apply Hallin; simpl_set; triv.
            ** intros [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
              apply H0. exists v'. exists (fst x). split_all; auto.
              simpl_set; triv.
          ++ left; auto.
      * (*Prove this by separate inductive lemma - this is annoying*)
        (*We need to prove this part twice - can we improve?*)
        destruct (free_in x (snd (alpha_p_aux sub a t l))) eqn : Hfreext.
        {
          eapply alpha_p_aux_in_implies in Hfreext; [| apply H6 | | |]; auto.
          - exfalso. destruct Hfreext.
            + destruct H3; rewrite H3 in H2; inversion H2.
            + rewrite alpha_p_aux_wf_aux_gen' in H3; auto.
              apply H0. destruct H3 as [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
              exists v'. exists (fst x). split_all; auto. 
              simpl_set; triv.
              intros; apply Hallin. simpl_set; triv.
          - intros. apply Hallin. simpl_set; triv.
          }
        (*Also need to know type*)
        generalize dependent (snd (alpha_p_aux sub a t l)).
        revert H7. revert H4. 
        assert (~
        (exists (v : vsymbol) (str : string),
           In (v, str) l /\
           In v
                (big_union vsymbol_eq_dec pat_fv ps) /\
           snd x = snd v /\ fst x = str)). {
            intros [v' [str [Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
            apply H0. exists v'. exists (fst x). split_all; auto.
            simpl_set; triv.
           }
          revert H3.
          clear -sigma Hnodup Hallin Hsub2. (*TODO: see if we need anything*)
          revert l0.
          induction ps; simpl; intros; auto.
          destruct l0; inversion H4.
          inversion H7; subst.
          eapply IHps; [| | apply H0 | |]; auto.
          -- intros. apply Hallin. simpl. simpl_set. 
            destruct H; try triv. simpl_set. triv.
          -- intros [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
            apply H3. exists v'. exists (fst x). split_all; auto.
            simpl_set; triv.
          -- (*TODO: prev lemma - can we avoid repeating?*)
            destruct (free_in x (snd (alpha_p_aux sub a0 a1 l))) eqn : Hfree; auto.
            eapply alpha_p_aux_in_implies in Hfree; [| apply H2 | | |]; auto.
            ++ exfalso. destruct Hfree.
              ** destruct H; rewrite Hfreext in H; auto.
              ** rewrite alpha_p_aux_wf_aux_gen' in H; auto.
                apply H3. destruct H as [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
                exists v'. exists (fst x). split_all; auto. 
                simpl_set; triv.
                intros; apply Hallin. simpl; simpl_set; triv.
            ++ intros. apply Hallin. simpl; simpl_set; triv.
  - destruct H.
  - inversion Hty; subst.
    simpl_set.
    eapply IHp2; [| | | | apply H5]; auto.
    + intros y Hiny C; apply (Hfree y); auto; simpl; simpl_set; triv.
    + intros; apply Hallin; simpl; simpl_set; triv.
    + destruct H; auto. apply H7; auto.
    + intros [v [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
      apply H0. exists v. exists (fst x). split_all; auto.
      simpl. simpl_set; triv.
  - inversion Hty; subst. 
    destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
    + simpl.
      simpl_set. destruct H as [Hinx | [Hxv | []]]; subst.
      * destruct (free_in x (sub v (s, snd v) (snd (alpha_p_aux sub p t l)))) eqn : Hfreex; auto.
        apply Hsub2 in Hfreex. destruct Hfreex.
        -- destruct H.
          eapply alpha_p_aux_in_implies in H; [| apply H6 | | |]; auto.
          destruct H.
          ++ destruct H; contradiction.
          ++ rewrite alpha_p_aux_wf_aux_gen' in H; auto.
            ** destruct H as [v1 [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
              exfalso. apply H0. exists v1. exists (fst x).
              split_all; auto. simpl. simpl_set; triv.
            ** intros; apply Hallin; simpl; simpl_set; triv.
          ++ intros; apply Hallin; simpl; simpl_set; triv.
        -- subst. apply get_assoc_list_some in Ha.
          exfalso. apply H0. exists v. exists s. split_all; auto.
          simpl; simpl_set; triv.
      * rewrite Hsub1; auto. intro; subst.
        apply H0.
        apply get_assoc_list_some in Ha.
        exists x. exists s. split_all; auto. simpl; simpl_set; triv.
        rewrite H; auto.
    + simpl. apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hallin; simpl; simpl_set; triv.
Qed.

Ltac prove_hyp H :=
  match goal with
  | H: ?P -> ?Q |- _ => let N := fresh in assert (N: P); [|specialize (H N); clear N]
  end.

Ltac prove_hyps n H :=
  match constr:(n) with
  | O => idtac
  | (S ?m) => prove_hyp H; [|prove_hyps m H]
  end.

Ltac vsym_eq2 x y z :=
  let H := fresh in
  assert (H: x = y \/ (x <> y /\ x = z) \/ (x <> y /\ x <> z)) by
  (vsym_eq x y; right; vsym_eq x z);
  destruct H as [? | [[? ?]|[? ?]]].

(*The big lemma we want: the free vars of [alpha_t_aux] and
  [alpha_f_aux] are the same as those of the original terms.
  This is very hard to prove, though very intuitive*)
Lemma alpha_aux_fv (t: term) (f: formula) :
  (forall (ty: vty)
    (Hty: term_has_type sigma t ty)
    (l: list string)
    (Hnodupl: NoDup l)
    (Hlen: length l = length (bnd_t t))
    (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
    forall x,
    free_in_t x (alpha_t_aux t l) = free_in_t x t) /\
  (forall 
    (Hval: valid_formula sigma f)
    (l: list string)  
    (Hnodupl: NoDup l)
    (Hlen: length l = length (bnd_f f))
    (Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
    forall x,
    free_in_f x (alpha_f_aux f l) = free_in_f x f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros; try reflexivity.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H0. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d).
    subst; simpl. rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    assert (term_has_type sigma (nth i l1 tm_d) (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int)).
    {
      inversion Hty; subst. rewrite Forall_forall in H10.

      specialize (H10 (nth i l1 tm_d, (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
      apply H10. rewrite in_combine_iff; wf_tac.
      exists i. split; auto; intros; f_equal; apply nth_indep; wf_tac. 
    }
    eapply H; [| apply H0 | | | |]; wf_tac; intros y Hiny C; apply in_split_lens_ith in Hiny; wf_tac.
    + apply (Hfree y); simpl_set; auto.
      exists (nth i l1 tm_d). split; wf_tac.
    + apply (Hbnd y); auto. rewrite in_concat.
      exists (bnd_t (nth i l1 tm_d)). split; wf_tac.
  - (*Let - this case is complicated because we are binding variables*) 
    destruct l; inversion Hlen.
    simpl. inversion Hnodupl; subst.
    inversion Hty; subst.
    erewrite H; [| apply H9 | | | |]; wf_tac; try(intros y Hiny C); [|apply (Hfree y) | apply (Hbnd y)];
    try(simpl; right; wf_tac); [|simpl_set; triv].
    f_equal.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H0 ty H10 (skipn (Datatypes.length (bnd_t tm1)) l)).
    prove_hyps 4 H0; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    [simpl_set; right; split; auto; intro Heq; subst;
      apply (Hbnd v); [right; wf_tac | left; auto]
    | ].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_t_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_t_fv_in; auto.
      * rewrite !H0.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_t_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_t_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_t_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H0.
  - (*If case - hypotheses for IH's are annoying *)
    inversion Hty; subst.
    rewrite H, (H0 _ H8), (H1 _ H9); wf_tac; intros y Hiny C;
    [apply (Hfree y) | apply (Hbnd y) | apply (Hfree y) | apply (Hbnd y) |
    apply (Hfree y) | apply (Hbnd y)];
    try(apply (Hfree y)); try(apply (Hbnd y));
    try (apply In_skipn in Hiny); try (apply In_firstn in Hiny);
    wf_tac; simpl_set; try (rewrite !in_app_iff); triv.
  - (*Match case - let's see*)
    inversion Hty; subst.
    specialize (H _ H4 (firstn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H; wf_tac; try(intros y Hiny C);
    [apply (Hfree y) | apply (Hbnd y) |]; wf_tac;
    [simpl_set; triv | ].
    rewrite H. f_equal.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, tm_d) (Pwild, tm_d)).
    subst; simpl.
    rewrite map2_nth with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
    assert (Hsum: sum
    (map
       (fun x0 : pattern * term =>
        Datatypes.length (pat_fv (fst x0)) + Datatypes.length (bnd_t (snd x0)))
       ps) = Datatypes.length l - Datatypes.length (bnd_t tm)). {
      rewrite Hlen, length_concat, map_map, minus_plus.
      f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    (*Ok, so we are back where we were before*)
    match goal with
    | |- context [in_bool ?e ?x ?l] => destruct (in_bool_spec e x l)
    end; simpl.
    + (*If x is in the pattern free vars, then it is in l*)
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl; auto.
      symmetry. apply free_in_t_negb. intro Hinfree.
      apply alpha_p_aux_wf_aux in i0.
      * rewrite map_snd_combine in i0; wf_tac.
        apply In_firstn in i0.
        apply in_split_lens_ith in i0; wf_tac.
        apply (Hfree x); wf_tac. simpl_set.
        right. exists (nth i ps (Pwild, tm_d)).
        split; wf_tac.
        simpl_set. split; auto.
      * rewrite map_fst_combine; wf_tac.
      * intros. rewrite map_fst_combine; wf_tac.
    + (*Otherwise, x not in pattern free vars*)
      (*Need this result in 2 places*)
      assert (Hnotfree: forall x0 : string * vty,
      In (fst x0)
           (nth i
              (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
                 (map
                    (fun x1 : pattern * term =>
                     Datatypes.length (pat_fv (fst x1)) +
                     Datatypes.length (bnd_t (snd x1))) ps)) []) ->
      ~ (In x0 (term_fv (snd (nth i ps (Pwild, tm_d)))) \/
        In x0 (pat_fv (fst (nth i ps (Pwild, tm_d)))))). {
        intros y Hy C.
        apply in_split_lens_ith in Hy; wf_tac.
        (*Do [pat_fv] first*)
        assert (~In y (pat_fv (fst (nth i ps (Pwild, tm_d))))). {
          (*Contradiction: y in l, so not bound in pattern,
            which is same as pattern free var*)
          intro Hnot.
          apply (Hbnd y); wf_tac.
          rewrite in_app_iff. right.
          rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, tm_d))) ++
            bnd_t (snd (nth i ps (Pwild, tm_d)))). split; wf_tac.
          exists (nth i ps (Pwild, tm_d)); split; wf_tac.
        }
        destruct C; try contradiction.
        (*Here, contradicts [Hfree], need [pat_fv result]*)
        apply (Hfree y); simpl_set; wf_tac.
        right. exists (nth i ps (Pwild, tm_d)). split;
        auto; simpl_set; wf_tac. 
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl.
      * (*If x in orig pattern free vars, need to show false*)
        assert (Hty': pattern_has_type sigma (fst (nth i ps (Pwild, tm_d))) v). {
          apply H6. wf_tac.
        }
        eapply alpha_p_aux_notin; [apply Hty' | | | | | | |]; wf_tac.
        -- intros; apply sub_t_fv_notin; auto.
        -- intros; apply sub_t_in_implies; auto.
        -- intros. apply In_firstn in H1. apply Hnotfree in H1.
          intro C; apply H1; triv.
      * rewrite alpha_p_aux_diff; wf_tac.
        assert (Hty': term_has_type sigma (snd (nth i ps (Pwild, tm_d))) ty). {
          apply H8; wf_tac.
        }
        -- erewrite H0; [| | apply Hty' | | | |]; wf_tac.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply Hnotfree in Hy. apply Hy; triv.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply in_split_lens_ith in Hy; wf_tac.
            apply (Hbnd y); wf_tac.
            rewrite in_app_iff; right.
            rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, tm_d))) ++
              bnd_t (snd (nth i ps (Pwild, tm_d)))). split; wf_tac.
            exists (nth i ps (Pwild, tm_d)); split; wf_tac.
        -- apply sub_t_fv_diff.
  - (*Teps - basically same as let*) 
    destruct l; inversion Hlen. inversion Hty; subst. simpl.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    inversion Hnodupl; subst.
    specialize (H H4 l).
    prove_hyps 4 H; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    simpl_set; auto.
    split; auto; intro Heq; subst.
    apply (Hbnd v); [right; wf_tac | left; auto].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H.
  - (*Fpred*)
    apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H0. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d).
    subst; simpl. rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    assert (term_has_type sigma (nth i tms tm_d) (nth i (map (ty_subst (p_params p) tys) (p_args p)) vty_int)).
    {
      inversion Hval; subst. rewrite Forall_forall in H8.

      specialize (H8 (nth i tms tm_d, (nth i (map (ty_subst (p_params p) tys) (p_args p)) vty_int))).
      apply H8. rewrite in_combine_iff; wf_tac.
      exists i. split; auto; intros; f_equal; apply nth_indep; wf_tac. 
    }
    eapply H; [| apply H0 | | | |]; wf_tac; intros y Hiny C; apply in_split_lens_ith in Hiny; wf_tac.
    + apply (Hfree y); simpl_set; auto.
      exists (nth i tms tm_d). split; wf_tac.
    + apply (Hbnd y); auto. rewrite in_concat.
      exists (bnd_t (nth i tms tm_d)). split; wf_tac.
  - (*Fquant -similar to let/eps*)
    destruct l; inversion Hlen.
    inversion Hnodupl;subst.
    inversion Hval; subst.
    simpl.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H H8 l).
    prove_hyps 4 H; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    simpl_set; auto.
    split; auto; intro Heq; subst.
    apply (Hbnd v); [right; wf_tac | left; auto].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H.
  - (*Feq*)
    inversion Hval; subst.
    rewrite (H _ H4), (H0 _ H6); wf_tac; intros y Hiny C;
    try solve[(apply (Hfree y); wf_tac; simpl_set; triv)];
    apply (Hbnd y); wf_tac; rewrite in_app_iff; triv.
  - (*Fbinop*)
    inversion Hval; subst.
    rewrite (H  H4), (H0 H6); wf_tac; intros y Hiny C;
    try solve[(apply (Hfree y); wf_tac; simpl_set; triv)];
    apply (Hbnd y); wf_tac; rewrite in_app_iff; triv.
  - apply H; wf_tac. inversion Hval; subst; auto.
  - (*Flet*)
    destruct l; inversion Hlen.
    simpl. inversion Hnodupl; subst.
    inversion Hval; subst.
    erewrite H; [| apply H7 | | | |]; wf_tac; try(intros y Hiny C); [|apply (Hfree y) | apply (Hbnd y)];
    try(simpl; right; wf_tac); [|simpl_set; triv].
    f_equal.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H0 H9 (skipn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H0; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    [simpl_set; right; split; auto; intro Heq; subst;
      apply (Hbnd v); [right; wf_tac | left; auto]
    | ].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H0.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H0.
  - (*Fif*)
    inversion Hval; subst.
    rewrite H, H0, H1; wf_tac; intros y Hiny C;
    [apply (Hfree y) | apply (Hbnd y) | apply (Hfree y) | apply (Hbnd y) |
    apply (Hfree y) | apply (Hbnd y)];
    try(apply (Hfree y)); try(apply (Hbnd y));
    try (apply In_skipn in Hiny); try (apply In_firstn in Hiny);
    wf_tac; simpl_set; try (rewrite !in_app_iff); triv.
  - (*Fmatch - copied and pasted*)
    inversion Hval; subst.
    specialize (H _ H4 (firstn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H; wf_tac; try(intros y Hiny C);
    [apply (Hfree y) | apply (Hbnd y) |]; wf_tac;
    [simpl_set; triv | ].
    rewrite H. f_equal.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)).
    subst; simpl.
    rewrite map2_nth with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
    assert (Hsum: sum
    (map
      (fun x0 : pattern * formula =>
        Datatypes.length (pat_fv (fst x0)) + Datatypes.length (bnd_f (snd x0)))
      ps) = Datatypes.length l - Datatypes.length (bnd_t tm)). {
      rewrite Hlen, length_concat, map_map, minus_plus.
      f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    (*Ok, so we are back where we were before*)
    match goal with
    | |- context [in_bool ?e ?x ?l] => destruct (in_bool_spec e x l)
    end; simpl.
    + (*If x is in the pattern free vars, then it is in l*)
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl; auto.
      symmetry. apply free_in_f_negb. intro Hinfree.
      apply alpha_p_aux_wf_aux in i0.
      * rewrite map_snd_combine in i0; wf_tac.
        apply In_firstn in i0.
        apply in_split_lens_ith in i0; wf_tac.
        apply (Hfree x); wf_tac. simpl_set.
        right. exists (nth i ps (Pwild, Ftrue)).
        split; wf_tac.
        simpl_set. split; auto.
      * rewrite map_fst_combine; wf_tac.
      * intros. rewrite map_fst_combine; wf_tac.
    + (*Otherwise, x not in pattern free vars*)
      (*Need this result in 2 places*)
      assert (Hnotfree: forall x0 : string * vty,
      In (fst x0)
          (nth i
              (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
                (map
                    (fun x1 : pattern * formula =>
                    Datatypes.length (pat_fv (fst x1)) +
                    Datatypes.length (bnd_f (snd x1))) ps)) []) ->
      ~ (In x0 (form_fv (snd (nth i ps (Pwild, Ftrue)))) \/
        In x0 (pat_fv (fst (nth i ps (Pwild, Ftrue)))))). {
        intros y Hy C.
        apply in_split_lens_ith in Hy; wf_tac.
        (*Do [pat_fv] first*)
        assert (~In y (pat_fv (fst (nth i ps (Pwild, Ftrue))))). {
          (*Contradiction: y in l, so not bound in pattern,
            which is same as pattern free var*)
          intro Hnot.
          apply (Hbnd y); wf_tac.
          rewrite in_app_iff. right.
          rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, Ftrue))) ++
            bnd_f (snd (nth i ps (Pwild, Ftrue)))). split; wf_tac.
          exists (nth i ps (Pwild, Ftrue)); split; wf_tac.
        }
        destruct C; try contradiction.
        (*Here, contradicts [Hfree], need [pat_fv result]*)
        apply (Hfree y); simpl_set; wf_tac.
        right. exists (nth i ps (Pwild, Ftrue)). split;
        auto; simpl_set; wf_tac. 
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl.
      * (*If x in orig pattern free vars, need to show false*)
        assert (Hty': pattern_has_type sigma (fst (nth i ps (Pwild, Ftrue))) v). {
          rewrite Forall_forall in H6; apply H6. wf_tac.
        }
        eapply alpha_p_aux_notin; [apply Hty' | | | | | | |]; wf_tac.
        -- intros; apply sub_f_fv_notin; auto.
        -- intros; apply sub_f_in_implies; auto.
        -- intros. apply In_firstn in H1. apply Hnotfree in H1.
          intro C; apply H1; triv.
      * rewrite alpha_p_aux_diff; wf_tac.
        assert (Hty': valid_formula sigma (snd (nth i ps (Pwild, Ftrue)))). {
          rewrite Forall_forall in H7; apply H7; wf_tac.
        }
        -- erewrite H0; [| | apply Hty' | | | |]; wf_tac.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply Hnotfree in Hy. apply Hy; triv.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply in_split_lens_ith in Hy; wf_tac.
            apply (Hbnd y); wf_tac.
            rewrite in_app_iff; right.
            rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, Ftrue))) ++
              bnd_f (snd (nth i ps (Pwild, Ftrue)))). split; wf_tac.
            exists (nth i ps (Pwild, Ftrue)); split; wf_tac.
        -- apply sub_f_fv_diff.
Qed.

Corollary alpha_t_aux_fv (t: term) :
  (forall (ty: vty)
  (Hty: term_has_type sigma t ty)
  (l: list string)
  (Hnodupl: NoDup l)
  (Hlen: length l = length (bnd_t t))
  (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
  (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
  forall x,
  free_in_t x (alpha_t_aux t l) = free_in_t x t).
Proof.
  apply alpha_aux_fv. apply Ftrue.
Qed.

Corollary alpha_f_aux_fv (f: formula):
(forall 
(Hval: valid_formula sigma f)
(l: list string)  
(Hnodupl: NoDup l)
(Hlen: length l = length (bnd_f f))
(Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
(Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
forall x,
free_in_f x (alpha_f_aux f l) = free_in_f x f).
Proof.
  apply alpha_aux_fv. apply tm_d.
Qed.

Corollary alpha_t_aux_fv' (t: term):
  (forall (ty: vty)
  (Hty: term_has_type sigma t ty)
  (l: list string)
  (Hnodupl: NoDup l)
  (Hlen: length l = length (bnd_t t))
  (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
  (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
  forall x, In x (term_fv (alpha_t_aux t l)) <-> In x (term_fv t)).
Proof.
  intros. rewrite <- !free_in_t_spec, (alpha_t_aux_fv _ ty); auto.
  reflexivity.
Qed. 

(*Finally, we need to prove that the [alpha] functions
  do not change the meaning of the term/formula (since we
  only rename bound variables)*)





TODO: maybe alpha equiv later


(*our lemma should say something like:
suppose that [match_val_single] on (t, p) gives Some l
then [match_val_single] on t, (fst (alpha_p_aux sub_t p _ l')) gives
Some l2 where
(x, y) is in l iff exists x' such that (x, x') in l' and (x', y) is in l2
(might also need, NoDup (map fst)) for each)

and then say: if gives None, then other gives None also (maybe prove first)

then from this, need to prove that [extend_val_with_list] is equivalent
in each case, because we do all the substitutions for the term
(need to reason about (snd (alpha_p_aux)))

*)
Require Import Coq.Logic.Eqdep_dec.



Lemma match_val_single_alpha_p_none {A: Type} (vv: val_vars pd vt) {ty: vty}
(Hval Hval2: valid_type sigma ty)
(d: IndTypes.domain (dom_aux pd) (v_subst (v_typevar vt) ty))
(p: pattern)
(sub: vsymbol -> vsymbol -> A -> A)
(tm: A)
(vars: list (vsymbol * string)) :
match_val_single gamma_valid pd all_unif vt ty Hval d p = None ->
match_val_single gamma_valid pd all_unif vt ty Hval2 d
  (fst (alpha_p_aux sub p tm vars)) = None.
Proof.
  induction p.
  - simpl. destruct (vty_eq_dec (snd v) ty); simpl; subst.
    intro C; inversion C. intros _.
    destruct (get_assoc_list vsymbol_eq_dec vars v) eqn : Ha; simpl;
    destruct (vty_eq_dec (snd v) ty); subst; auto; contradiction.
  - (*hard case*)
    simpl alpha_p_aux. simpl fst.
    unfold match_val_single; repeat fold (match_val_single gamma_valid).
    (*The hard case: need lots of generalization for dependent types
    and need nested induction*) 
    generalize dependent (is_sort_adt_spec gamma_valid (v_subst (v_typevar vt) ty)).
    generalize dependent ((@adt_srts_length_eq _ _ gamma_valid vt ty)).
    generalize dependent (@adts_srts_valid _ _ gamma_valid vt ty).
    destruct (is_sort_adt (v_subst (v_typevar vt) ty)) eqn : Hisadt; [|solve[auto]].
    intros Hsrtsvalid Hsrtslen Hadtspec.
    destruct p as [[[m adt] ts] srts].
    destruct (Hadtspec m adt ts srts eq_refl) as 
      [Hvaleq [Hinmut [Hincts Htseq]]].
    assert (Hlenpeq : (Hsrtslen m adt ts srts eq_refl Hval) =
    (Hsrtslen m adt ts srts eq_refl Hval2)). {
      apply UIP_dec. apply Nat.eq_dec.
    }
    rewrite <- !Hlenpeq.
    destruct (funsym_eq_dec
    (projT1
      (find_constr_rep gamma_valid m Hincts srts
          (Hsrtslen m adt ts srts eq_refl Hval) (dom_aux pd) adt
          Hinmut (adts pd m srts) (all_unif m Hincts)
          (scast (adts pd m srts adt Hinmut)
            (dom_cast (dom_aux pd) Hvaleq d)))) f);[|solve[auto]].
    clear Hlenpeq.
    (*Need nested induction: simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hincts srts
    (Hsrtslen m adt ts srts eq_refl Hval) 
    (dom_aux pd) adt Hinmut (adts pd m srts)
    (all_unif m Hincts)
    (scast (adts pd m srts adt Hinmut)
      (dom_cast (dom_aux pd) Hvaleq d))).
    intros constr. destruct constr as [f' Hf'].
    simpl_proj.  intros Hf; subst.
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval2 (fst (proj1_sig Hf')))).
    destruct Hf'. simpl_proj. clear e.
    destruct x. generalize dependent a.
    generalize dependent ps. 
    generalize dependent ((funsym_sigma_args f srts)).
    induction l; intros. 
    + destruct ps. inversion H0. reflexivity.
    + revert H0. destruct ps. reflexivity. simpl fst. simpl snd. 
      cbv iota. cbv beta. cbv match. (*simpl freezes*)
      repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
      all: try solve[intro C; inversion C].
      * intros _. eapply IHl in Hmatch0. apply Hmatch0.
      subst.
      apply IHl.
      apply in_app_or in H1. destruct H1.
      * inversion H; subst.
        apply H3 with(x:=x) (t:=t) in Hmatch; auto.
      * apply IHl with(x:=x) (t:=t) in Hmatch0; auto.
        inversion H; subst. auto.
  - simpl; auto.
  - simpl. destruct (match_val_single gamma_valid pd all_unif vt ty Hval d p1) eqn : Hm1;
    [intro C; inversion C|].
    rewrite IHp1; auto.
  - simpl. destruct (match_val_single gamma_valid pd all_unif vt ty Hval d p) eqn : Hm.
    + destruct (vty_eq_dec (snd v) ty); subst; auto; [intro C; inversion C|].
      intros _. destruct (get_assoc_list vsymbol_eq_dec vars v) eqn : Ha; simpl.
      * destruct (match_val_single gamma_valid pd all_unif vt ty Hval2 d
        (fst (alpha_p_aux sub p tm vars))); auto.
        destruct (vty_eq_dec (snd v) ty); subst; auto; contradiction.
      * destruct (match_val_single gamma_valid pd all_unif vt ty Hval2 d p); auto.
        destruct (vty_eq_dec (snd v) ty); subst; auto; contradiction.
    + intros _. destruct (get_assoc_list vsymbol_eq_dec vars v) eqn : Ha; simpl.
      * rewrite IHp; auto.
      * rewrite match_val_single_irrel with (Hval2:=Hval).
        rewrite Hm; auto.
(*TODO: constr case*)
      
      [intros C; inversion C|]; auto.
      ; simpl simpl.
    + auto.


Lemma alpha_aux_rep (t: term) (f: formula) :
  (forall (vv: val_vars pd vt) (l: list string) (ty: vty)
  (Hty: term_has_type sigma t ty)
  (Hty2: term_has_type sigma (alpha_t_aux t l) ty)
  (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
  (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
  NoDup l ->
  length l = length (bnd_t t) ->
  term_rep vv t ty Hty =
  term_rep vv (alpha_t_aux t l) ty Hty2) /\
  (forall (vv: val_vars pd vt) (l: list string)
  (Hval: valid_formula sigma f)
  (Hval2: valid_formula sigma (alpha_f_aux f l))
  (Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
  (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
  NoDup l ->
  length l = length (bnd_f f) ->
  formula_rep vv f Hval =
  formula_rep vv (alpha_f_aux f l) Hval2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try solve[apply term_rep_irrel].
  - rewrite !tfun_rep.
    f_equal.
    apply UIP_dec. apply vty_eq_dec.
    f_equal. apply UIP_dec. apply sort_eq_dec.
    (*casting is done*)
    f_equal.
    apply get_arg_list_ext; wf_tac.
    intros i Hi ty' Htya Htyb.
    revert Htyb.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); simpl; intros; wf_tac.
    rewrite Forall_forall in H; apply H; wf_tac.
    all: intros x Hinx C; apply in_split_lens_ith in Hinx; wf_tac.
    + apply (Hfree _ Hinx). simpl_set. exists (nth i l1 tm_d). 
      split; wf_tac.
    + apply (Hbnd _ Hinx). rewrite in_concat. exists (bnd_t (nth i l1 tm_d)).
      split; wf_tac.
  - destruct l; [apply term_rep_irrel|].
    inversion H2; subst.
    inversion H1; subst.
    assert (Hty3: term_has_type sigma
    (Tlet (alpha_t_aux tm1 (firstn (Datatypes.length (bnd_t tm1)) l)) v
       (alpha_t_aux tm2 (skipn (Datatypes.length (bnd_t tm1)) l))) ty). {
        inversion Hty; subst.
        constructor; apply alpha_t_aux_type; wf_tac.
    }
    rewrite <- alpha_convert_tlet with(Hty1:=Hty3); wf_tac.
    + rewrite !tlet_rep.
      rewrite (H vv (firstn (length (bnd_t tm1)) l) (snd v)
      (proj1 (ty_let_inv (has_type_eq eq_refl Hty)))
      (proj1 (ty_let_inv (has_type_eq eq_refl Hty2)))); wf_tac.
      erewrite H0 with(Hty2:=(proj2 (ty_let_inv (has_type_eq eq_refl Hty3)))); wf_tac.
      erewrite (term_rep_irrel _ _ _ _ _ _ (alpha_t_aux tm1 _)).
      reflexivity.
      * intros x Hinx C. apply (Hfree x); simpl; [right |]; wf_tac.
        simpl_set. right. split; auto. intro Heq; subst.
        apply (Hbnd v). simpl. right; wf_tac. left; auto.
      * intros x Hinx C. apply (Hbnd x); simpl; right; wf_tac. 
      * intros x Hinx C. apply (Hfree x); simpl. right; wf_tac.
        simpl_set. triv.
      * intros x Hinx C. apply (Hbnd x); simpl. right; wf_tac.
        right. wf_tac.
    + intro C. apply alpha_t_aux_wf in C; wf_tac.
    + intro C.
      (*TODO: prove that [alpha_t_aux] does not change free variables*)
      inversion Hty; subst.
      (*Get contradiction because [alpha_t_aux] doesnt change free vars*)
      rewrite alpha_t_aux_fv' in C; wf_tac. 2: apply H12.
      * apply (Hfree (s, snd v)); simpl. triv.
        simpl_set. right. split; try triv.
        intro Heq; subst.
        apply (Hbnd v). simpl. left. rewrite <- Heq; auto. triv.
      * intros x Hinx C'. apply (Hfree x); simpl. right; wf_tac.
        simpl_set. right. split; auto. intro Heq; subst.
        apply (Hbnd v); simpl; try triv. right; wf_tac.
        (*TODO: automate this stuff for sure*)
      * intros x Hinx C'. apply (Hbnd x); simpl. right; wf_tac.
        right. wf_tac.
  - rewrite !tif_rep.
    inversion Hty2; subst; auto.
    rewrite H with(l:=(firstn (length (bnd_f f)) l))
    (Hval2:=(proj2 (proj2 (ty_if_inv (has_type_eq eq_refl Hty2))))); wf_tac.
    rewrite H0 with(l:=(firstn (Datatypes.length (bnd_t t1))
    (skipn (Datatypes.length (bnd_f f)) l)))
    (Hty2:=(proj1 (ty_if_inv (has_type_eq eq_refl Hty2)))); wf_tac.
    rewrite H1 with (l:=(skipn (Datatypes.length (bnd_t t1))
    (skipn (Datatypes.length (bnd_f f)) l))) 
    (Hty2:=(proj1 (proj2 (ty_if_inv (has_type_eq eq_refl Hty2))))); wf_tac.
    (*Deal with all the free/bnd goals - TODO automate*)
    all: intros x Hinx C;
    try(solve[apply (Hfree x); wf_tac; simpl_set; triv]);
    try(solve[apply (Hbnd x); wf_tac]).
  - (*Tmatch case*)
    rewrite !tmatch_rep.
    (*Need nested induction here*)
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty))).
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty2))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty2))).
    induction ps; simpl; intros;[reflexivity |].
    destruct a. simpl.
    revert f. simpl.
    destruct (alpha_p_aux sub_t p
    (alpha_t_aux t1
       (skipn (Datatypes.length (pat_fv p))
          (firstn
             (Datatypes.length (pat_fv p) + Datatypes.length (bnd_t t1))
             (skipn (Datatypes.length (bnd_t tm)) l))))
    (combine (pat_fv p)
       (firstn (Datatypes.length (pat_fv p))
          (firstn
             (Datatypes.length (pat_fv p) + Datatypes.length (bnd_t t1))
             (skipn (Datatypes.length (bnd_t tm)) l))))) eqn : Hap.
    simpl. intros.
    rewrite H with(l:=(firstn (Datatypes.length (bnd_t tm)) l))
      (Hty2:=t); wf_tac.
    (*Need to know that [match_val_single] is same - or at least
      the relationship here - separate lemma?*)
    Check match_val_single.

    match_val_single gamma_valid pd all_unif vt v
    (has_type_valid gamma_valid tm v t0)
    (term_rep vv (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v
       t) p

    match_val_single gamma_valid pd all_unif vt v
    (has_type_valid gamma_valid
      (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v t)
    (term_rep vv (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v
      t) p0

(*think: pattern (fst part) unaffected by term arg*)

(*our lemma should say something like:
suppose that [match_val_single] on (t, p) gives Some l
then [match_val_single] on t, (fst (alpha_p_aux sub_t p _ l')) gives
Some l2 where
(x, y) is in l iff exists x' such that (x, x') in l' and (x', y) is in l2
(might also need, NoDup (map fst)) for each)

and then say: if gives None, then other gives None also (maybe prove first)

then from this, need to prove that [extend_val_with_list] is equivalent
in each case, because we do all the substitutions for the term
(need to reason about (snd (alpha_p_aux)))

*)

    p0 = fst (alpha_p_aux sub_t p
    (alpha_t_aux t1
       (skipn (Datatypes.length (pat_fv p))
          (firstn
             (Datatypes.length (pat_fv p) + Datatypes.length (bnd_t t1))
             (skipn (Datatypes.length (bnd_t tm)) l))))
    (combine (pat_fv p)
       (firstn (Datatypes.length (pat_fv p))
          (firstn
             (Datatypes.length (pat_fv p) + Datatypes.length (bnd_t t1))
             (skipn (Datatypes.length (bnd_t tm)) l)))))


    match_val_single gamma_valid pd all_unif vt v
    (has_type_valid gamma_valid
       (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v t)
    (term_rep vv tm v t0) p0



      match_val_single gamma_valid pd all_unif vt v
      (has_type_valid gamma_valid tm v t0) (term_rep vv tm v t0) p


      match_val_single gamma_valid pd all_unif vt v
    (has_type_valid gamma_valid
       (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v t)
    (term_rep vv (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v
       t) p0



    + rewrite H with(l:=(firstn (Datatypes.length (bnd_t tm)) l))
      (Hty2:=t).
      destruct (match_val_single gamma_valid pd all_unif vt v
      (has_type_valid gamma_valid tm v t0)
      (term_rep vv (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v
         t) p) eqn : Hm.
      
      
      (has_type_valid gamma_valid
      (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v t)).


    match_val_single gamma_valid pd all_unif vt v
    (has_type_valid gamma_valid tm v t0) (term_rep vv tm v t0) p



    match_val_single gamma_valid pd all_unif vt v
     (has_type_valid gamma_valid
        (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v t)
     (term_rep vv (alpha_t_aux tm (firstn (Datatypes.length (bnd_t tm)) l)) v
        t) p0
    
    
    
    reflexivity.





    + apply (Hfree x); wf_tac. simpl_set. triv.
    + apply (Hbnd x); wf_tac.
    + apply (Hfree x); wf_tac. simpl_set. triv.
    + apply (Hbnd x); wf_tac.
    
    
    [apply (Hfree x) | | | | |].


        right. rewrite in_app_iff.