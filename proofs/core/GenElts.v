(*Here we show that for any countable type (which injects into
  the natural numbers), we can generate a list of distinct
  elements of the type not present in some input list.
  This is useful for generating new free variables and
  unique names.*)
(*TODO: could make this more efficient with a BFS search of the ptree. Is it worth it?*)
Require Import Coq.Lists.List.
Require Import Coq.Logic.FinFun.
Require Import Coq.Arith.PeanoNat.
Require Import Common.
Set Bullet Behavior "Strict Subproofs".

(*TODO: just use "fresh" from stdpp, repeat n times*)

(*NOTE: have 2 versions: old, which has structure where we have prefix followed by number,
  and version using "fresh", which we can just use directly*)

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
  unfold gen_dist. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma gen_dist_correct (n: nat): NoDup (gen_dist n).
Proof.
  unfold gen_dist. apply Injective_map_NoDup.
  unfold Injective. apply Hinj.
  apply seq_NoDup.
Qed.

(*Generate list of n distinct elements, all of which are not
  in l*)
Context `{A_count: countable.Countable A} (*`{A_inf: base.Infinite A}*).
Definition gen_notin (n: nat) (s: aset A): list A :=
(*   aset_fresh_list n s. *)
  firstn n 
    (filter (fun x => negb(aset_mem_dec x s)) (gen_dist (n + aset_size s))).

(*Should we generate set or list? list prob OK for now, just not symmetric wihch is annoying*)

(*Proving that this is correct is not trivial*)
(*A version of the pigeonhole principle: given two lists l1 and l2,
  if l2 is larger and has no duplicates, it has at least 
    (length l2) - (length l1) elements that are not in l1*)
Lemma php (s: aset A) (l2: list A):
  NoDup l2 -> 
  aset_size s <= length l2 ->
  length l2 - aset_size s <= 
    length (filter (fun x => negb(aset_mem_dec x s)) l2).
Proof.
  (*Try alternate, then go back*)
  revert l2.
  (*TODO: write induction principle on ssets based on theirs*)
  apply aset_ind with (P:=(fun s => forall l2, NoDup l2 -> aset_size s <= length l2 -> length l2 - aset_size s <=
    length (filter (fun x => negb (aset_mem_dec x s)) l2))); clear s.
  - intros l2 Hl2. rewrite aset_size_empty, Nat.sub_0_r.
    assert (Hl2': filter (fun x => negb (aset_mem_dec x aset_empty)) l2 = l2).
    {
      apply all_filter, forallb_forall. intros x Hinx.
      destruct (aset_mem_dec _ _); auto. exfalso.
      apply (aset_mem_empty x); auto.
    }
    rewrite Hl2'. auto.
  - intros x s Hnotin IH l2 Hlnodup.
    rewrite size_union_singleton.
    destruct (in_dec EqDecision0 x l2).
    2: {
      rewrite filter_in_notin; auto; simpl.
      specialize (IH _ Hlnodup). lia.
    }
    (*For this one, we have to split l2 depending on
      where a appears*)
    apply in_split in i.
    destruct i as [p1 [p2 Hl2]].
    rewrite Hl2, filter_app, filter_cons.
    assert (Hnodup:=Hlnodup).
    rewrite Hl2 in Hnodup.
    rewrite NoDup_app_iff in Hnodup. destruct Hnodup as [Hn1 [Hn2 [Hnotin1 Hnotin2]]].
    inversion Hn2. subst x0 l.
    assert (~ In x p1). {
      apply Hnotin2. left; auto.
    } 
    rewrite !filter_in_notin; auto.  (*destruct (eq_dec a a); auto; try contradiction.
    simpl.*) (*rewrite <- filter_app.*)
    assert (Hn3: NoDup (p1 ++ p2)). {
      rewrite NoDup_app_iff. repeat split; auto.
      - intros; intro C. apply (Hnotin1 x0 H0). right; auto.
      - intros; apply Hnotin2. right; auto.
    }
    specialize (IH _ Hn3).
    rewrite !length_app.
    rewrite !length_app in IH.
    destruct (aset_mem_dec x (aset_union (aset_singleton x) s)); simpl.
    2: { exfalso. apply n. simpl_set_small. auto. }
    rewrite filter_app, length_app in IH.
    destruct (aset_mem_dec x s); try lia.
    contradiction.
Qed.

(*Now we can prove our function correct*)
Lemma gen_notin_length (n: nat) (s: aset A):
  length (gen_notin n s) = n.
Proof.
  unfold gen_notin.
  rewrite firstn_length_le; auto.
  pose proof (php s (gen_dist (n + aset_size s))) as Hp.
  rewrite gen_dist_length in Hp.
  specialize (Hp (gen_dist_correct _)). lia.
Qed.

Lemma gen_notin_nodup (n: nat) (s: aset A):
  NoDup (gen_notin n s).
Proof.
  unfold gen_notin.
  apply NoDup_firstn.
  apply NoDup_filter.
  apply gen_dist_correct.
Qed.

Lemma gen_notin_notin (n: nat) (s: aset A):
  forall y, In y (gen_notin n s) -> ~ aset_mem y s.
Proof.
  intros y Hiny. unfold gen_notin in Hiny.
  apply In_firstn in Hiny.
  rewrite in_filter in Hiny. destruct Hiny.
  destruct (aset_mem_dec y s); auto. discriminate.
Qed.

(*TODO: see if we need version of this*)
(*
Lemma add_notin_nodup (: list A) n:
  NoDup l1 ->
  NoDup (l1 ++ gen_notin n l1).
Proof.
  intros.
  rewrite NoDup_app_iff; split_all; auto.
  + apply gen_notin_nodup; apply nth_vs_inj.
  + intros. intro C. apply gen_notin_notin in C. contradiction.
  + intros. apply gen_notin_notin in H0. auto.
Qed.*)

(*We can change the list in question as long as it has equivalent elements (even if a different
  length, although this is not trivial to show*)
(*NOTE: this is now almost trivial by extensionality*)
Lemma gen_notin_ext (s1 s2: aset A) (n: nat):
  (forall x, aset_mem x s1 <-> aset_mem x s2) ->
  gen_notin n s1 = gen_notin n s2.
Proof.
  intros Hin.
  assert (Hs1: s1 = s2). {
    apply aset_ext; auto.
  }
  subst. reflexivity.
Qed.
(* Lemma gen_notin_ext_aux (l1 l2: list A) (n: nat):
  (forall x, In x l1 <-> In x l2) ->
  length l1 <= length l2 ->
  gen_notin n l1 = gen_notin n l2.
Proof.
  intros Hiff Hlen.
  pose proof (gen_notin_length n l1) as Hgen. revert Hgen.
  unfold gen_notin. 
  replace (n + length l2) with ((n + length l1) + (length l2 - length l1)) by lia.
  unfold gen_dist.
  rewrite length_firstn.
  rewrite Nat.min_l_iff.
  intros Hlenge.
  (*Now prove that this prefix is equivalent to the longer one*)
  rewrite (seq_app (n+ length l1)).
  rewrite filter_ext with (f:=fun x => negb(in_dec eq_dec x l2)) (g:=fun x => negb (in_dec eq_dec x l1)).
  2: { intros. repeat (destruct (in_dec _ _); simpl); auto; apply Hiff in i; contradiction. }
  rewrite map_app, filter_app.
  rewrite firstn_app.
  replace (n - length _) with 0.
  2: { symmetry; apply Nat.sub_0_le; auto. }
  rewrite firstn_O, app_nil_r.
  reflexivity.
Qed. *)

(* Lemma gen_notin_ext (l1 l2: list A) (n: nat):
  (forall x, In x l1 <-> In x l2) ->
  gen_notin n l1 = gen_notin n l2.
Proof.
  intros Hiff.
  unfold gen_notin.
  destruct (Nat.le_ge_cases (length l1) (length l2)); [|symmetry]; apply gen_notin_ext_aux; auto.
  intros; rewrite Hiff; reflexivity.
Qed. *)

End NoDupsList.

(*We want to apply this to strings and vsymbols.
  To do this, we want to give decent names (at least
  x0, x1, etc) and not just 0, 00, 000 or something
  easy to define and prove injective. Converting 
  nats to strings is surprisingly difficult*)

(*Apply this to vsymbols*)
(*TODO: likely delete this*)
Require Import Types.
Require Import Syntax.
Require Import Coq.Strings.String.
Require Import FunInd.
Require Import Recdef.
From mathcomp Require Import all_ssreflect ssrnat div.

Set Bullet Behavior "Strict Subproofs".

Section NatToStr.

Local Open Scope string_scope.

Definition nat_to_digit (n : nat) : string :=
  match n with
    | 0 => "0"%string
    | 1 => "1"%string
    | 2 => "2"%string
    | 3 => "3"%string
    | 4 => "4"%string
    | 5 => "5"%string
    | 6 => "6"%string
    | 7 => "7"%string
    | 8 => "8"%string
    | _ => "9"%string
  end.

(*Gives list of digits in reverse order*)
Function nat_to_digits (n : nat) {measure (fun x => x) n} : list string :=
  if n < 10 then [nat_to_digit (n %% 10)] else 
  nat_to_digit (n %% 10) :: nat_to_digits (n %/ 10).
Proof.
  move=> n Hn10. apply /ltP.
  apply ltn_Pdiv=>//.
  move: Hn10. by case: n.
Defined.

Lemma nat_to_digits_simpl n :
  nat_to_digits n = nat_to_digit (n %% 10) :: if n < 10 then nil else 
    nat_to_digits (n %/ 10).
Proof.
  rewrite nat_to_digits_equation.
  by case: (n < 10).
Qed.

(*Injectivity*)

Ltac solve_or :=
  match goal with
  | |- ?P \/ ?Q => solve[left; solve_or] + solve[right; solve_or] 
  | |- _ => auto
  end.

(*Makes things easier*)
Lemma nat_lt10 (n: nat):
  n < 10 ->
  n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n =4 \/
  n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n= 9.
Proof.
  move=> Hn.
  do 10 (destruct n as [| n]; solve_or). inversion Hn.
Qed.

Ltac case_or :=
  repeat match goal with
  | H: ?P \/ ?Q |- _ => destruct H
  end.

(*Just do all 100 cases*)
Lemma nat_to_digit_inj (n1 n2: nat):
  n1 < 10 ->
  n2 < 10 ->
  nat_to_digit n1 = nat_to_digit n2 ->
  n1 = n2.
Proof.
  move=>Hn1 Hn2.
  apply nat_lt10 in Hn1; apply nat_lt10 in Hn2.
  case_or; subst; simpl; auto; intros H; inversion H.
Qed.

Lemma nat_to_digits_nil n:
  ~ (nat_to_digits n = nil).
Proof. 
  by rewrite nat_to_digits_simpl.
Qed.

Lemma modn_inj (m n d: nat):
  m < d ->
  n < d ->
  m = n %[mod d] ->
  m = n.
Proof.
  move=> Hm Hn Hmod.
  by rewrite (divn_eq m d) (divn_eq n d) !divn_small.
Qed.

Lemma nat_to_digits_inj n1 n2:
  nat_to_digits n1 = nat_to_digits n2 ->
  n1 = n2.
Proof.
  move: n2.
  apply nat_to_digits_ind with
    (P:=fun m1 m2 => forall n2, m2 = nat_to_digits n2 -> m1 = n2).
  - move=> n Hn n2.
    rewrite nat_to_digits_simpl => [[]].
    case Hn2: (n2 < 10).
    + move=> Hdig _.
      apply nat_to_digit_inj in Hdig; try by
      apply ltn_pmod.
      by apply (modn_inj _ _ _ Hn).
    + by rewrite nat_to_digits_simpl.
  - move=> n2 [//| Hn2 _ Hdigits n3].
    rewrite (nat_to_digits_simpl n3).
    case Hn3: (n3 < 10).
    + move=> []. by rewrite nat_to_digits_simpl.
    + move=> [Heq1 Heq2].
      apply Hdigits in Heq2.
      apply nat_to_digit_inj in Heq1; try by
      apply ltn_pmod.
      by rewrite (divn_eq n2 10) (divn_eq n3 10) Heq1 Heq2.
Qed.

(*Convert digits to string*)
Definition digits_to_string (l: list string) : string :=
  concat "" l.

(*How is this not in the stdlib?*)
Lemma append_length s1 s2:
  length (s1 ++ s2) = length s1 + length s2.
Proof.
  elim: s1 =>//=a s IH. by rewrite IH.
Qed.

(*Intermediate cases for injectivity - concat is annoying*)

Lemma concat_nil l:
  (forall x, In x l -> length x = 1) -> 
  concat "" l = "" -> l = nil.
Proof.
  case: l => //= x l Hallin Heq.
  have //: 1 <= length "".
  rewrite -Heq {Heq}. move: Hallin.
  by case: l =>//=[Hallin | y l Hallin];
  [|rewrite append_length]; rewrite Hallin; auto.
Qed.

Lemma concat_cons_case x1 x2 y1 l1:
  length x1 = 1 ->
  length x2 = 1 ->
  length y1 = 1 ->
  x1 ++ concat "" (y1 :: l1) <> x2.
Proof.
  move=> Hlen1 Hlen2 Hlen3.
  rewrite /=. case: l1=>[| z1 l1].
  - move=> Heq.
    have: length x1 + length y1 = length x2 by 
      rewrite -Heq append_length.
    by rewrite Hlen1 Hlen2 Hlen3.
  - move=> Heq.
    have: length x1 + length y1 + length (concat "" (z1 :: l1)) =
      length x2 by rewrite -Heq !append_length !addnA.
    rewrite Hlen1 Hlen2 Hlen3 => Heq2. 
    by have: 1 + 1 <= 1 by rewrite -{3}Heq2.
Qed.

Lemma concat_cons x1 x2 l1 l2:
  (forall x, In x (x1 :: l1) -> length x = 1) ->
  (forall x, In x (x2 :: l2) -> length x = 1) ->
  concat "" (x1 :: l1) = concat "" (x2 :: l2) ->
  x1 = x2 /\ concat "" l1 = concat "" l2.
Proof.
  rewrite /=. case: l1 =>[| y1 l1]; case: l2 =>[| y2 l2] //.
  - move=>/= Hall1 Hall2 Heq. symmetry in Heq.
    by apply concat_cons_case in Heq; auto.
  - move=>/= Hall1 Hall2 Heq.
    by apply concat_cons_case in Heq; auto.
  - move=> Hall1 Hall2 Heq.
    by apply append_inj in Heq; last by
      rewrite Hall1; auto; rewrite Hall2; auto.
Qed.


Lemma digits_to_string_inj (l1 l2: list string):
  (forall x, In x l1 -> length x = 1) ->
  (forall x, In x l2 -> length x = 1) ->
  digits_to_string l1 = digits_to_string l2 ->
  l1 = l2.
Proof.
  revert l2. rewrite /digits_to_string.
  elim: l1=>[/=| x1 l1 IHl [|x2 l2]].
  - move=>l2 _ Hallin Heq.
    symmetry in Heq. by apply concat_nil in Heq.
  - move=> Hallin _ Heq. by apply concat_nil in Heq.
  - move=> Hall1 Hall2 Heq.
    apply concat_cons in Heq=>//.
    case: Heq => [Hxeq Hceq].
    rewrite Hxeq. f_equal. by apply IHl=>//;
    [intros; apply Hall1 | intros; apply Hall2]=>/=; auto.
Qed.

Lemma rev_inj {A: Type} (l1 l2: list A):
  rev l1 = rev l2 ->
  l1 = l2.
Proof.
  move=> Hrev.
  by rewrite -(revK l1) Hrev revK.
Qed.

(*All things in digit list have length 1*)
Lemma nat_to_digit_len n:
  length (nat_to_digit n) = 1.
Proof.
  repeat (destruct n; auto).
Qed.

Lemma nat_to_digits_len n:
  forall x, In x (nat_to_digits n) -> length x = 1.
Proof.
  apply nat_to_digits_ind with (P:=fun m1 m2 => forall x, In x m2 -> length x = 1).
  - move=> n1 Hn1 x/= [Hx | []]. by rewrite -Hx nat_to_digit_len.
  - move=> n1 [//| Hn1 _] IH x/= [Hh | Htl].
    + by rewrite -Hh nat_to_digit_len.
    + by apply IH.
Qed.

Lemma in_rev {A: Type} x (l: list A):
  In x l <-> In x (rev l).
Proof.
  elim: l=>//= y l IH.
  by rewrite IH rev_cons -cats1 in_app_iff /= or_false_r or_comm.
Qed.

(*Finally, the full function and theorem*)
Definition nat_to_string (n: nat) : string :=
  digits_to_string (rev (nat_to_digits n)).

(*Some tests*)
Eval compute in (nat_to_string 654).
Eval compute in (nat_to_string 0).
Eval compute in (nat_to_string 1000).

Lemma nat_to_string_inj n1 n2:
  nat_to_string n1 = nat_to_string n2 ->
  n1 = n2.
Proof.
  rewrite /nat_to_string.
  move=> Hn.
  apply digits_to_string_inj in Hn;
  try (move=> x; rewrite -in_rev; apply nat_to_digits_len).
  apply rev_inj in Hn.
  by apply nat_to_digits_inj in Hn.
Qed.

End NatToStr.

(*Get the string xn*)
Definition nth_str (n: nat) : string :=
  "x" ++ nat_to_string n.

Lemma nth_str_inj: forall n1 n2,
  nth_str n1 = nth_str n2 ->
  n1 = n2.
Proof.
  intros n1 n2. unfold nth_str.
  intros. inversion H.
  apply nat_to_string_inj in H1; auto.
Qed.

Definition nth_vs (n: nat) : vsymbol :=
  (nth_str n, vty_int).

Lemma nth_vs_inj: forall n1 n2,
  nth_vs n1 = nth_vs n2 ->
  n1 = n2.
Proof.
  intros. unfold nth_vs in H. inversion H; subst.
  apply nat_to_string_inj in H1; auto.
Qed.

(*We give a specific function for generating n distinct
  vsymbols not in list l*)
(*TODO: is this useful (vs generating names?)*)
Definition gen_vars (n: nat) (s: aset vsymbol) :=
  gen_notin nth_vs n s.

Lemma gen_vars_length (n: nat) (s: aset vsymbol):
  List.length (gen_vars n s) = n.
Proof.
  apply gen_notin_length. apply nth_vs_inj.
Qed.

Lemma gen_vars_nodup (n: nat) (s: aset vsymbol):
  NoDup (gen_vars n s).
Proof.
  apply gen_notin_nodup. apply nth_vs_inj.
Qed.

Lemma gen_vars_notin (n: nat) (s: aset vsymbol):
  forall x, In x (gen_vars n s) -> ~ aset_mem x s.
Proof.
  apply gen_notin_notin.
Qed.

(*And one to generate new variable names*)
Definition gen_strs (n: nat) (s: aset vsymbol) : list string :=
  gen_notin nth_str n (aset_map fst s).

Lemma gen_strs_length n s:
  List.length (gen_strs n s) = n.
Proof.
  apply gen_notin_length. apply nth_str_inj.
Qed.

Lemma gen_strs_nodup n s:
  NoDup (gen_strs n s).
Proof.
  apply gen_notin_nodup. apply nth_str_inj.
Qed.

Lemma gen_strs_notin (n: nat) (s: aset vsymbol):
  forall (x: vsymbol), In (fst x) (gen_strs n s) -> ~ aset_mem x s.
Proof.
  intros x Hin. apply gen_notin_notin in Hin.
  rewrite aset_mem_map in Hin.
  intro Hin1.
  apply Hin. exists x. split; auto.
Qed.

Lemma gen_strs_notin' (n: nat) (s: aset vsymbol):
forall (str: string), In str (gen_strs n s) -> ~ aset_mem str (aset_map fst s).
Proof.
  intros str Hin. apply gen_notin_notin in Hin. auto.
Qed.

Lemma gen_strs_ext (n: nat) (s1 s2: aset vsymbol)
  (Hl12: forall x, aset_mem x s1 <-> aset_mem x s2):
  gen_strs n s1 = gen_strs n s2.
Proof.
  unfold gen_strs.
  apply gen_notin_ext.
  intros x. apply aset_ext in Hl12. subst. reflexivity.
Qed.

(*No variables, just names with a prefix*)
Definition gen_names (n: nat) (pref: string) (s: aset string) : list string :=
  gen_notin (fun x => (pref ++ nat_to_string x)%string) n s.

Lemma gen_names_inj pref: forall (n1 n2: nat),
  (pref ++ nat_to_string n1)%string =
  (pref ++ nat_to_string n2)%string ->
  n1 = n2.
Proof.
  intros. apply append_inj in H; auto. destruct H; subst.
  apply nat_to_string_inj in H0; auto.
Qed.

Lemma gen_names_length n p s:
  List.length (gen_names n p s) = n.
Proof.
  apply gen_notin_length, gen_names_inj.
Qed.

Lemma gen_names_nodup n p s:
  NoDup (gen_names n p s).
Proof.
  apply gen_notin_nodup, gen_names_inj. 
Qed.

Lemma gen_names_notin (n: nat) p (s: aset string):
  forall x, In x (gen_names n p s) -> ~ aset_mem x s.
Proof.
  intros x Hinx. apply gen_notin_notin in Hinx. auto.
Qed.

Definition gen_name (p: string) (s: aset string) : string :=
  List.nth 0 (gen_names 1 p s) EmptyString.

Lemma gen_name_notin p (s: aset string):
  ~ aset_mem (gen_name p s) s.
Proof.
  unfold gen_name.
  pose proof (gen_names_length 1 p s) as Hlen.
  destruct (gen_names 1 p s) eqn : Heqs;
  inversion Hlen.
  destruct l; try discriminate.
  simpl. 
  pose proof (gen_names_notin 1 p s s0) as Hnotin.
  apply Hnotin. rewrite Heqs; simpl; auto.
Qed.